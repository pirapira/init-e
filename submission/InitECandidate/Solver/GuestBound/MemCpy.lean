import InitECandidate.Solver.GuestBound.Bytes
import InitECandidate.Solver.GuestBound.HtabDel

/-!
# `memcpy`

`memcpy(dst, src, n)` on disjoint ranges copies `n` bytes: afterwards the
bytes of `[dst, dst + n)` are those `[src, src + n)` had, and nothing else
has changed (`CopyInv`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A loop whose body keeps an invariant and neither breaks nor returns. -/
theorem WPs.loop {I : St σ → Prop} {c : Exp Word} {body : Prog Word} (hinit : I s)
    (hbody : ∀ a, I a → CondTrue E a c →
      WPs E a body (fun r => ∃ l g m f, r = .normal l g m f ∧ I ⟨l, g, m, f⟩))
    (hexit : ∀ a k, I a → E.cond a c = some (0, k) →
      Q (.normal a.locals a.globals a.memory a.ffi)) :
    WPs E s (.while c body) Q := by
  intro r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  refine while_inv (I := I) (Q := fun r => Stopped r ∨ Q r)
    (fun r hr => Or.inl (Stopped.of_error hr)) (fun a k hI hc => Or.inr (hexit a k hI hc)) ?_
    fuel s r n hinit hrun
  intro fuel' a r' n' hI hct hrun'
  rcases hbody a hI hct r' (Runs.of_run hrun') with hst | ⟨l, g, m, f, rfl, hI'⟩
  · cases r' with
    | error l g m f => exact Or.inl trivial
    | raised l g m f ex val => exact Or.inl trivial
    | finalFfi l g m f ev => exact Or.inl trivial
    | _ => exact absurd hst (fun h => h)
  · exact hI'

/-- The ranges of a copy: no wrap, disjoint, and a length below `2^63`. -/
structure CpPre (dst src nW : Word) : Prop where
  hd : dst.toNat + nW.toNat < 2 ^ 64
  hs : src.toNat + nW.toNat < 2 ^ 64
  disj : src.toNat + nW.toNat ≤ dst.toNat ∨ dst.toNat + nW.toNat ≤ src.toNat
  hn : nW.toNat < 2 ^ 63

/-- State of `memcpy` with `i = jb` and `j` bytes copied. -/
def CpS (m0 : Word → Option (PanValue Word)) (dst src nW : Word)
    (g : VarName → Option (PanValue Word)) (f : FfiState σ) (jb j : Nat) (s : St σ) : Prop :=
  s.globals = g ∧ s.ffi = f ∧ s.locals "dst" = some (.word dst) ∧
    s.locals "src" = some (.word src) ∧ s.locals "n" = some (.word nW) ∧
    s.locals "i" = some (.word (BitVec.ofNat 64 jb)) ∧ CopyInv m0 dst src j s.memory

variable {m0 : Word → Option (PanValue Word)} {dst src nW : Word}
  {g : VarName → Option (PanValue Word)} {f : FfiState σ} {jb j : Nat}

theorem off_add (a : Word) (j : Nat) (k : Word) :
    a + BitVec.ofNat 64 j + k = off a (j + k.toNat) := by
  unfold off
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem eval_off0 (hE : GuestEnv E) {x : VarName} {a : Word} (hx : s.locals x = some (.word a))
    (hi : s.locals "i" = some (.word (BitVec.ofNat 64 j))) :
    E.eval s (.op .add [.var .local x, .var .local "i"]) = some (.word (off a j)) := by
  unfold off
  ev [hx, hi]

theorem eval_offk (hE : GuestEnv E) {x : VarName} {a : Word} (k : Word)
    (hx : s.locals x = some (.word a))
    (hi : s.locals "i" = some (.word (BitVec.ofNat 64 jb))) :
    E.eval s (.op .add [.var .local x, .var .local "i", .const k]) =
      some (.word (off a (jb + k.toNat))) := by
  rw [← off_add]
  ev [hx, hi, BitVec.add_assoc]

/-- `st ea, lds 1 eb; rest` copying the aligned word at offset `j`. -/
theorem cp_wstore (hE : GuestEnv E) (P : CpPre dst src nW) {ea eb : Exp Word}
    {rest : Prog Word} (hS : CpS m0 dst src nW g f jb j s)
    (hea : E.eval s ea = some (.word (off dst j))) (heb : E.eval s eb = some (.word (off src j)))
    (hj : j + 8 ≤ nW.toNat) (hd8 : (dst.toNat + j) % 8 = 0) (hs8 : (src.toNat + j) % 8 = 0)
    (h : ∀ a, CpS m0 dst src nW g f jb (j + 8) a → WPs E a rest Q) :
    WPs E s (.seq (.store ea (.load .one eb)) rest) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  obtain ⟨fuel, n, hrun⟩ := h1
  rcases store_word_inv hE.mem hrun with herr | ⟨addr, val, m, ha', hv', rfl, hm⟩
  · cases r1 with
    | error l g m f => simp only at hrest; subst hrest; exact Or.inl trivial
    | _ => cases herr
  rw [hea] at ha'
  simp only [Option.some.injEq, PanValue.word.injEq] at ha'
  subst ha'
  obtain ⟨baddr, w, hb', rfl, hmem⟩ := eval_load_one hE.mem hv'
  rw [heb] at hb'
  simp only [Option.some.injEq, PanValue.word.injEq] at hb'
  subst hb'
  rw [hm w rfl] at hrest
  obtain ⟨hg, hf, h1', h2', h3', h4', hci⟩ := hS
  exact h ⟨s.locals, s.globals, setCell s.memory (off dst j) w, s.ffi⟩
    ⟨hg, hf, h1', h2', h3', h4', hci.word hj P.hd P.hs P.disj hd8 hs8 hmem⟩ r hrest

/-- `st8 ea, ld8 eb; rest` copying the byte at offset `j`. -/
theorem cp_bstore (hE : GuestEnv E) (P : CpPre dst src nW) {ea eb : Exp Word}
    {rest : Prog Word} (hS : CpS m0 dst src nW g f jb j s)
    (hea : E.eval s ea = some (.word (off dst j))) (heb : E.eval s eb = some (.word (off src j)))
    (hj : j < nW.toNat)
    (h : ∀ a, CpS m0 dst src nW g f jb (j + 1) a → WPs E a rest Q) :
    WPs E s (.seq (.storeByte ea (.loadByte eb)) rest) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  obtain ⟨fuel, n, hrun⟩ := h1
  rcases storeByte_inv hE.mem hrun with herr | ⟨addr, val, cell, ha', hv', hcell, rfl⟩
  · cases r1 with
    | error l g m f => simp only at hrest; subst hrest; exact Or.inl trivial
    | _ => cases herr
  rw [hea] at ha'
  simp only [Option.some.injEq, PanValue.word.injEq] at ha'
  subst ha'
  obtain ⟨baddr, cell', hb', hcell', hx⟩ := eval_loadByte hE.mem hv'
  rw [heb] at hb'
  simp only [Option.some.injEq, PanValue.word.injEq] at hb' hx
  subst hb' hx
  rw [hE.bytes] at hcell hcell' hrest
  have hbyte : byteAt s.memory (off src j) = some (gb (off src j) cell') := by
    unfold byteAt
    rw [hcell']
  obtain ⟨hg, hf, h1', h2', h3', h4', hci⟩ := hS
  exact h ⟨s.locals, s.globals, setCell s.memory (al8 (off dst j))
      (sb (off dst j) (gb (off src j) cell') cell), s.ffi⟩
    ⟨hg, hf, h1', h2', h3', h4', hci.byte hj P.hd P.hs P.disj hcell hbyte⟩ r hrest

/-- `i = i + k` at the end of a round. -/
theorem cp_assign (hE : GuestEnv E) (k : Word) (hS : CpS m0 dst src nW g f jb j s)
    (hjk : j = jb + k.toNat) :
    WPs E s (.assign .local "i" (.op .add [.var .local "i", .const k]))
      (fun r => ∃ l g' m f', r = .normal l g' m f' ∧ CpS m0 dst src nW g f j j ⟨l, g', m, f'⟩) := by
  obtain ⟨hg, hf, h1, h2, h3, h4, hci⟩ := hS
  have hval : BitVec.ofNat 64 jb + k = BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hjk]
    omega
  refine WPs.assign (old := BitVec.ofNat 64 jb) h4
    (of_eval (w := BitVec.ofNat 64 j) (by rw [← hval]; ev [h4])) ?_
  exact ⟨_, _, _, _, rfl, hg, hf, by lk [h1], by lk [h2], by lk [h3], by lk [], hci⟩

/-- The guard `n >=+ i + k` holds. -/
theorem cond_notLower (hE : GuestEnv E) (P : CpPre dst src nW) (k : Word) (hk : k.toNat ≤ 64)
    (hS : CpS m0 dst src nW g f jb j s) (hjb : jb ≤ nW.toNat)
    (hct : CondTrue E s (.cmp .notLower (.var .local "n")
      (.op .add [.var .local "i", .const k]))) : jb + k.toNat ≤ nW.toNat := by
  obtain ⟨-, -, -, -, h3, h4, -⟩ := hS
  obtain ⟨w, c, hcond, hw⟩ := hct
  have hev := cond_of_eval hcond
  have := eval_cmp_inv hE (of_eval (w := nW) (by lk [h3]))
    (of_eval (w := BitVec.ofNat 64 jb + k) (by ev [h4])) _ hev
  simp only [PanValue.word.injEq] at this
  by_contra hlt
  have hn := P.hn
  have hsum : (BitVec.ofNat 64 jb + k).toNat = jb + k.toNat := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hl : nW < BitVec.ofNat 64 jb + k := by
    rw [BitVec.lt_def, hsum]
    omega
  rw [this] at hw
  simp [evalPanCmp, hl] at hw

/-- A word store at offset `kn` of the round starting at `jb`. -/
theorem cp_wstorek (hE : GuestEnv E) (P : CpPre dst src nW) (k : Word) {kn j' : Nat}
    {rest : Prog Word} (hS : CpS m0 dst src nW g f jb j s) (hk : k.toNat = kn)
    (hjk : j = jb + kn) (hj' : j' = j + 8) (hj : j + 8 ≤ nW.toNat)
    (hd8 : (dst.toNat + j) % 8 = 0) (hs8 : (src.toNat + j) % 8 = 0)
    (h : ∀ a, CpS m0 dst src nW g f jb j' a → WPs E a rest Q) :
    WPs E s (.seq (.store (.op .add [.var .local "dst", .var .local "i", .const k])
      (.load .one (.op .add [.var .local "src", .var .local "i", .const k]))) rest) Q := by
  subst hk hjk hj'
  obtain ⟨-, -, h1, h2, -, h4, -⟩ := id hS
  exact cp_wstore hE P hS (eval_offk hE k h1 h4) (eval_offk hE k h2 h4) hj hd8 hs8 h

theorem cp_wstore0 (hE : GuestEnv E) (P : CpPre dst src nW) {j' : Nat} {rest : Prog Word}
    (hS : CpS m0 dst src nW g f jb jb s) (hj' : j' = jb + 8) (hj : jb + 8 ≤ nW.toNat)
    (hd8 : (dst.toNat + jb) % 8 = 0) (hs8 : (src.toNat + jb) % 8 = 0)
    (h : ∀ a, CpS m0 dst src nW g f jb j' a → WPs E a rest Q) :
    WPs E s (.seq (.store (.op .add [.var .local "dst", .var .local "i"])
      (.load .one (.op .add [.var .local "src", .var .local "i"]))) rest) Q := by
  subst hj'
  obtain ⟨-, -, h1, h2, -, h4, -⟩ := id hS
  exact cp_wstore hE P hS (eval_off0 hE h1 h4) (eval_off0 hE h2 h4) hj hd8 hs8 h

theorem cp_bstorek (hE : GuestEnv E) (P : CpPre dst src nW) (k : Word) {kn j' : Nat}
    {rest : Prog Word} (hS : CpS m0 dst src nW g f jb j s) (hk : k.toNat = kn)
    (hjk : j = jb + kn) (hj' : j' = j + 1) (hj : j < nW.toNat)
    (h : ∀ a, CpS m0 dst src nW g f jb j' a → WPs E a rest Q) :
    WPs E s (.seq (.storeByte (.op .add [.var .local "dst", .var .local "i", .const k])
      (.loadByte (.op .add [.var .local "src", .var .local "i", .const k]))) rest) Q := by
  subst hk hjk hj'
  obtain ⟨-, -, h1, h2, -, h4, -⟩ := id hS
  exact cp_bstore hE P hS (eval_offk hE k h1 h4) (eval_offk hE k h2 h4) hj h

theorem cp_bstore0 (hE : GuestEnv E) (P : CpPre dst src nW) {j' : Nat} {rest : Prog Word}
    (hS : CpS m0 dst src nW g f jb jb s) (hj' : j' = jb + 1) (hj : jb < nW.toNat)
    (h : ∀ a, CpS m0 dst src nW g f jb j' a → WPs E a rest Q) :
    WPs E s (.seq (.storeByte (.op .add [.var .local "dst", .var .local "i"])
      (.loadByte (.op .add [.var .local "src", .var .local "i"]))) rest) Q := by
  subst hj'
  obtain ⟨-, -, h1, h2, -, h4, -⟩ := id hS
  exact cp_bstore hE P hS (eval_off0 hE h1 h4) (eval_off0 hE h2 h4) hj h

local notation "MC_W32G" => ((Exp.cmp Cmp.notLower (Exp.var VarKind.local "n") (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 32))])) : Exp Word)

local notation "MC_W32B" => ((Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i")]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i")]))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))]))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 16))]))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 24))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 24))]))) (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 32))])))))) : Prog Word)

local notation "MC_W8G" => ((Exp.cmp Cmp.notLower (Exp.var VarKind.local "n") (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])) : Exp Word)

local notation "MC_W8B" => ((Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i")]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i")]))) (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))]))) : Prog Word)

local notation "MC_B8G" => ((Exp.cmp Cmp.notLower (Exp.var VarKind.local "n") (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])) : Exp Word)

local notation "MC_B8B" => ((Prog.seq (Prog.storeByte (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i")]) (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i")]))) (Prog.seq (Prog.storeByte (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]) (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))) (Prog.seq (Prog.storeByte (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 2))]) (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 2))]))) (Prog.seq (Prog.storeByte (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 3))]) (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 3))]))) (Prog.seq (Prog.storeByte (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 4))]) (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 4))]))) (Prog.seq (Prog.storeByte (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 5))]) (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 5))]))) (Prog.seq (Prog.storeByte (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 6))]) (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 6))]))) (Prog.seq (Prog.storeByte (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 7))]) (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 7))]))) (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])))))))))) : Prog Word)

local notation "MC_B1G" => ((Exp.cmp Cmp.lower (Exp.var VarKind.local "i") (Exp.var VarKind.local "n")) : Exp Word)

local notation "MC_B1B" => ((Prog.seq (Prog.storeByte (Exp.op BinOp.add [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "i")]) (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "src"), (Exp.var VarKind.local "i")]))) (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))) : Prog Word)

local notation "MC_ITEG" => ((Exp.cmp Cmp.equal (Exp.op BinOp.and [(Exp.op BinOp.or [(Exp.var VarKind.local "dst"), (Exp.var VarKind.local "src")]), (Exp.const (BitVec.ofNat 64 7))]) (Exp.const (BitVec.ofNat 64 0))) : Exp Word)


theorem cp_loop_w32 (hE : GuestEnv E) (P : CpPre dst src nW) (hd8 : dst.toNat % 8 = 0)
    (hs8 : src.toNat % 8 = 0)
    (hI : ∃ j, CpS m0 dst src nW g f j j s ∧ j ≤ nW.toNat ∧ j % 8 = 0) :
    WPs E s (.while MC_W32G MC_W32B) (fun r => ∃ l g' m f', r = .normal l g' m f' ∧
      ∃ j, CpS m0 dst src nW g f j j ⟨l, g', m, f'⟩ ∧ j ≤ nW.toNat ∧ j % 8 = 0) := by
  refine WPs.loop (I := fun a => ∃ j, CpS m0 dst src nW g f j j a ∧ j ≤ nW.toNat ∧ j % 8 = 0)
    hI ?_ (fun a k hI _ => ⟨_, _, _, _, rfl, hI⟩)
  rintro a ⟨j, hS, hj, hj8⟩ hct
  have hle := cond_notLower hE P 32#64 (by decide) hS hj hct
  have h32 : (32#64 : Word).toNat = 32 := by decide
  rw [h32] at hle
  refine cp_wstore0 hE P hS (j' := j + 8) rfl (by omega) (by omega) (by omega) ?_
  intro a1 hS1
  refine cp_wstorek hE P 8#64 hS1 (kn := 8) (by decide) rfl (j' := j + 16) rfl (by omega)
    (by omega) (by omega) ?_
  intro a2 hS2
  refine cp_wstorek hE P 16#64 hS2 (kn := 16) (by decide) rfl (j' := j + 24) rfl (by omega)
    (by omega) (by omega) ?_
  intro a3 hS3
  refine cp_wstorek hE P 24#64 hS3 (kn := 24) (by decide) rfl (j' := j + 32) rfl (by omega)
    (by omega) (by omega) ?_
  intro a4 hS4
  refine (cp_assign hE 32#64 hS4 (by rw [h32])).conseq ?_
  rintro r ⟨l, g', m, f', rfl, hS'⟩
  exact ⟨l, g', m, f', rfl, j + 32, hS', by omega, by omega⟩

theorem cp_loop_w8 (hE : GuestEnv E) (P : CpPre dst src nW) (hd8 : dst.toNat % 8 = 0)
    (hs8 : src.toNat % 8 = 0)
    (hI : ∃ j, CpS m0 dst src nW g f j j s ∧ j ≤ nW.toNat ∧ j % 8 = 0) :
    WPs E s (.while MC_W8G MC_W8B) (fun r => ∃ l g' m f', r = .normal l g' m f' ∧
      ∃ j, CpS m0 dst src nW g f j j ⟨l, g', m, f'⟩ ∧ j ≤ nW.toNat) := by
  refine WPs.loop (I := fun a => ∃ j, CpS m0 dst src nW g f j j a ∧ j ≤ nW.toNat ∧ j % 8 = 0)
    hI ?_ (fun a k ⟨j, h1, h2, _⟩ _ => ⟨_, _, _, _, rfl, j, h1, h2⟩)
  rintro a ⟨j, hS, hj, hj8⟩ hct
  have hle := cond_notLower hE P 8#64 (by decide) hS hj hct
  have h8 : (8#64 : Word).toNat = 8 := by decide
  rw [h8] at hle
  refine cp_wstore0 hE P hS (j' := j + 8) rfl (by omega) (by omega) (by omega) ?_
  intro a1 hS1
  refine (cp_assign hE 8#64 hS1 (by rw [h8])).conseq ?_
  rintro r ⟨l, g', m, f', rfl, hS'⟩
  exact ⟨l, g', m, f', rfl, j + 8, hS', by omega, by omega⟩

theorem cp_loop_b8 (hE : GuestEnv E) (P : CpPre dst src nW)
    (hI : ∃ j, CpS m0 dst src nW g f j j s ∧ j ≤ nW.toNat) :
    WPs E s (.while MC_B8G MC_B8B) (fun r => ∃ l g' m f', r = .normal l g' m f' ∧
      ∃ j, CpS m0 dst src nW g f j j ⟨l, g', m, f'⟩ ∧ j ≤ nW.toNat) := by
  refine WPs.loop (I := fun a => ∃ j, CpS m0 dst src nW g f j j a ∧ j ≤ nW.toNat)
    hI ?_ (fun a k hI _ => ⟨_, _, _, _, rfl, hI⟩)
  rintro a ⟨j, hS, hj⟩ hct
  have hle := cond_notLower hE P 8#64 (by decide) hS hj hct
  have h8 : (8#64 : Word).toNat = 8 := by decide
  rw [h8] at hle
  refine cp_bstore0 hE P hS (j' := j + 1) rfl (by omega) ?_
  intro a1 hS1
  refine cp_bstorek hE P 1#64 hS1 (kn := 1) (by decide) rfl (j' := j + 2) rfl (by omega) ?_
  intro a2 hS2
  refine cp_bstorek hE P 2#64 hS2 (kn := 2) (by decide) rfl (j' := j + 3) rfl (by omega) ?_
  intro a3 hS3
  refine cp_bstorek hE P 3#64 hS3 (kn := 3) (by decide) rfl (j' := j + 4) rfl (by omega) ?_
  intro a4 hS4
  refine cp_bstorek hE P 4#64 hS4 (kn := 4) (by decide) rfl (j' := j + 5) rfl (by omega) ?_
  intro a5 hS5
  refine cp_bstorek hE P 5#64 hS5 (kn := 5) (by decide) rfl (j' := j + 6) rfl (by omega) ?_
  intro a6 hS6
  refine cp_bstorek hE P 6#64 hS6 (kn := 6) (by decide) rfl (j' := j + 7) rfl (by omega) ?_
  intro a7 hS7
  refine cp_bstorek hE P 7#64 hS7 (kn := 7) (by decide) rfl (j' := j + 8) rfl (by omega) ?_
  intro a8 hS8
  refine (cp_assign hE 8#64 hS8 (by rw [h8])).conseq ?_
  rintro r ⟨l, g', m, f', rfl, hS'⟩
  exact ⟨l, g', m, f', rfl, j + 8, hS', by omega⟩

theorem cp_loop_b1 (hE : GuestEnv E) (P : CpPre dst src nW)
    (hI : ∃ j, CpS m0 dst src nW g f j j s ∧ j ≤ nW.toNat) :
    WPs E s (.while MC_B1G MC_B1B) (fun r => ∃ l g' m f', r = .normal l g' m f' ∧
      CpS m0 dst src nW g f nW.toNat nW.toNat ⟨l, g', m, f'⟩) := by
  have hn := P.hn
  have hcmp : ∀ (a : St σ) (j : Nat), CpS m0 dst src nW g f j j a → j ≤ nW.toNat →
      ∀ x, E.eval a MC_B1G = some x →
        x = .word (evalPanCmp .lower (BitVec.ofNat 64 j) nW) := by
    intro a j hS hj
    obtain ⟨-, -, -, -, h3, h4, -⟩ := hS
    exact eval_cmp_inv hE (of_eval (w := BitVec.ofNat 64 j) (by lk [h4]))
      (of_eval (w := nW) (by lk [h3]))
  have hjt : ∀ j : Nat, j ≤ nW.toNat → (BitVec.ofNat 64 j : Word).toNat = j := by
    intro j hj
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine WPs.loop (I := fun a => ∃ j, CpS m0 dst src nW g f j j a ∧ j ≤ nW.toNat) hI ?_ ?_
  · rintro a ⟨j, hS, hj⟩ ⟨w, c, hcond, hw⟩
    have := hcmp a j hS hj _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at this
    have hlt : j < nW.toNat := by
      by_contra hge
      have hnl : ¬ (BitVec.ofNat 64 j : Word) < nW := by
        rw [BitVec.lt_def, hjt j hj]
        exact hge
      rw [this] at hw
      simp [evalPanCmp, hnl] at hw
    have h1 : (1#64 : Word).toNat = 1 := by decide
    refine cp_bstore0 hE P hS (j' := j + 1) rfl hlt ?_
    intro a1 hS1
    refine (cp_assign hE 1#64 hS1 (by rw [h1])).conseq ?_
    rintro r ⟨l, g', m, f', rfl, hS'⟩
    exact ⟨l, g', m, f', rfl, j + 1, hS', by omega⟩
  · rintro a k ⟨j, hS, hj⟩ hcond
    have := hcmp a j hS hj _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at this
    have hnl := lower_zero this.symm
    rw [BitVec.lt_def, hjt j hj] at hnl
    have hjn : j = nW.toNat := by omega
    subst hjn
    exact ⟨_, _, _, _, rfl, hS⟩

theorem or_and7 (a b : Word) (h : (a ||| b) &&& 7#64 = 0#64) :
    a.toNat % 8 = 0 ∧ b.toNat % 8 = 0 := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_or] at this
  have h7 : (7#64 : Word).toNat = 2 ^ 3 - 1 := by decide
  have h0 : (0#64 : Word).toNat = 0 := by decide
  rw [h7, Nat.and_two_pow_sub_one_eq_mod, h0, Nat.or_mod_two_pow] at this
  exact Nat.or_eq_zero_iff.mp this

theorem and7_mod (x : Word) (h : x &&& 7#64 = 0#64) : x.toNat % 8 = 0 := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_and] at this
  have h7 : (7#64 : Word).toNat = 2 ^ 3 - 1 := by decide
  have h0 : (0#64 : Word).toNat = 0 := by decide
  rw [h7, Nat.and_two_pow_sub_one_eq_mod, h0] at this
  exact this

set_option maxHeartbeats 2000000 in
/-- `memcpy(dst, src, n)` on disjoint ranges returns 0 after copying `n` bytes. -/
theorem memcpy_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "memcpy" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (dst src nW : Word) (hdst : s.locals "dst" = some (.word dst))
    (hsrc : s.locals "src" = some (.word src)) (hn : s.locals "n" = some (.word nW))
    (P : CpPre dst src nW) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      CopyInv s.memory dst src nW.toNat m' := by
  have hbody := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    CopyInv s.memory dst src nW.toNat m')) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  have hS0 : CpS s.memory dst src nW s.globals s.ffi 0 0
      ⟨updatePanValueMap s.locals "i" (.word 0#64), s.globals, s.memory, s.ffi⟩ :=
    ⟨rfl, rfl, by lk [hdst], by lk [hsrc], by lk [hn], by lk [], CopyInv.start _ _ _⟩
  refine WPs.seq (fun a => ∃ j, CpS s.memory dst src nW s.globals s.ffi j j a ∧ j ≤ nW.toNat)
    ?_ ?_
  · refine WPs.ite_both ?_
    intro w hw
    split
    · exact WPs.skip ⟨_, _, _, _, rfl, 0, hS0, Nat.zero_le _⟩
    · rename_i hw0
      have hal : dst.toNat % 8 = 0 ∧ src.toNat % 8 = 0 := by
        have hand : ∀ a b : Word, AndOp.and a b = a &&& b := fun _ _ => rfl
        have hor : ∀ a b : Word, OrOp.or a b = a ||| b := fun _ _ => rfl
        have hones : ∀ a : Word, a &&& 18446744073709551615#64 = a := by intro a; bv_decide
        simp [evalF_cmp hE.word, evalF_op hE.word, evalArgs_cons, evalArgs_nil,
          update_lookup, hdst, hsrc, wordOp, hand, hor, hones, evalPanCmp] at hw
        have hz : (dst ||| src) &&& 7#64 = 0#64 := by
          by_contra hne
          rw [if_neg hne] at hw
          exact hw0 hw.symm
        exact or_and7 dst src hz
      refine WPs.seq (fun a => ∃ j, CpS s.memory dst src nW s.globals s.ffi j j a ∧
          j ≤ nW.toNat ∧ j % 8 = 0)
        (cp_loop_w32 hE P hal.1 hal.2 ⟨0, hS0, Nat.zero_le _, rfl⟩) ?_
      intro a hI
      exact cp_loop_w8 hE P hal.1 hal.2 hI
  · intro a hI
    refine WPs.seq (fun a => ∃ j, CpS s.memory dst src nW s.globals s.ffi j j a ∧ j ≤ nW.toNat)
      (cp_loop_b8 hE P hI) ?_
    intro a' hI'
    refine WPs.seq (fun a => CpS s.memory dst src nW s.globals s.ffi nW.toNat nW.toNat a)
      (cp_loop_b1 hE P hI') ?_
    rintro a'' ⟨hg, hf, -, -, -, -, hci⟩
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    exact ⟨_, _, by rw [hg, hf]; rfl, hci⟩

end InitECandidate.Solver.GuestBound
