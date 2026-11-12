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

end InitECandidate.Solver.GuestBound
