import InitECandidate.Solver.GuestBound.MemEqGen

/-!
# Hash tables: `htab_first_diff`

The index of the first bit, most significant bit of each byte first, where two
keys differ; `key_len * 8` when they are equal.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A loop whose body keeps an invariant or leaves with `Q`. -/
theorem WPs.loopG {I : St σ → Prop} {c : Exp Word} {body : Prog Word} (hinit : I s)
    (hbody : ∀ a, I a → CondTrue E a c → WPs E a body (fun r => match r with
      | .normal l g m f => I ⟨l, g, m, f⟩
      | .continued _ _ _ _ | .broke _ _ _ _ => False
      | r => Q r))
    (hexit : ∀ a k, I a → E.cond a c = some (0, k) →
      Q (.normal a.locals a.globals a.memory a.ffi)) :
    WPs E s (.while c body) Q := by
  intro r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  refine while_inv (I := I) (Q := fun r => Stopped r ∨ Q r)
    (fun r hr => Or.inl (Stopped.of_error hr)) (fun a k hI hc => Or.inr (hexit a k hI hc)) ?_
    fuel s r n hinit hrun
  intro fuel' a r' n' hI hct hrun'
  rcases hbody a hI hct r' (Runs.of_run hrun') with hst | hpost
  · cases r' with
    | error l g m f => exact Or.inl trivial
    | raised l g m f ex val => exact Or.inl trivial
    | finalFfi l g m f ev => exact Or.inl trivial
    | _ => exact absurd hst (fun h => h)
  · cases r' with
    | normal l g m f => exact hpost
    | continued l g m f => exact hpost.elim
    | broke l g m f => exact hpost.elim
    | _ => exact Or.inr hpost

/-- A declaration, using what its value evaluated to. -/
theorem WPs.dec_ev {x : VarName} {sh : Shape} {e : Exp Word} {body : Prog Word}
    (h : ∀ v, E.eval s e = some v →
      WPs E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.dec x sh e body) Q := by
  intro r hr
  rw [runs_dec] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some v =>
    rw [hv] at hr
    simp only at hr
    split at hr
    · obtain ⟨rb, hrb, rfl⟩ := hr
      rcases h v hv rb hrb with hs | hq
      · exact Or.inl hs.restore
      · exact Or.inr hq
    · subst hr
      exact Or.inl (Stopped.err s)

/-- Bit `j` of a byte, most significant first. -/
def bitOf (x : Word) (j : Nat) : Bool := x.getLsbD (7 - j)

theorem and_one_ne_zero (x : Word) (k : Nat) :
    ((x >>> k) &&& 1#64 ≠ 0#64) ↔ x.getLsbD k = true := by
  constructor
  · intro h
    by_contra hb
    apply h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
    by_cases hi0 : i = 0
    · subst hi0
      simp only [Nat.add_zero]
      have : x.getLsbD k = false := by simpa using hb
      simp [this]
    · have : (1#64 : Word).getLsbD i = false := by
        simp [BitVec.getLsbD_one, hi0]
      simp [this]
  · intro hb h
    have := congrArg (fun y : Word => y.getLsbD 0) h
    simp [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, hb] at this

/-- A nonzero byte has a set bit. -/
theorem byte_bit (x : Word) (hx : x.toNat < 256) (hne : x ≠ 0#64) : ∃ j, j < 8 ∧ bitOf x j = true := by
  by_contra hall
  apply hne
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_zero]
  by_cases hi8 : i < 8
  · by_contra hb
    exact hall ⟨7 - i, by omega, by
      unfold bitOf
      have : 7 - (7 - i) = i := by omega
      rw [this]
      simpa using hb⟩
  · simp only [BitVec.getLsbD]
    apply Nat.testBit_lt_two_pow
    calc x.toNat < 256 := hx
      _ = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem bitOf_xor (a b : Word) (j : Nat) : bitOf (a ^^^ b) j = (bitOf a j ^^ bitOf b j) := by
  unfold bitOf
  rw [BitVec.getLsbD_xor]

theorem xor_lt (a b : Word) (ha : a.toNat < 256) (hb : b.toNat < 256) : (a ^^^ b).toNat < 256 := by
  rw [BitVec.toNat_xor]
  exact Nat.xor_lt_two_pow (n := 8) ha hb

theorem byteAt_lt {m : Word → Option (PanValue Word)} {p x : Word} (h : byteAt m p = some x) :
    x.toNat < 256 := by
  unfold byteAt at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact gb_lt _ _
  · cases h

local notation "FD_XOR" => ((Exp.op BinOp.xor [(Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "a"), (Exp.var VarKind.local "i")])), (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "b"), (Exp.var VarKind.local "i")]))]) : Exp Word)

local notation "FD_BIT" => ((Exp.cmp Cmp.notEqual (Exp.op BinOp.and [(Exp.shift Shift.lsr (Exp.var VarKind.local "x") (Exp.op BinOp.sub [(Exp.const (BitVec.ofNat 64 7)), (Exp.var VarKind.local "j")])), (Exp.const (BitVec.ofNat 64 1))]) (Exp.const (BitVec.ofNat 64 0))) : Exp Word)

variable {m : Word → Option (PanValue Word)} {A B nW : Word}

/-- The xor of the two key bytes at offset `jb`. -/
theorem fd_xor (hE : GuestEnv E) {jb : Nat} (ha : s.locals "a" = some (.word A))
    (hb : s.locals "b" = some (.word B))
    (hi : s.locals "i" = some (.word (BitVec.ofNat 64 jb))) (hm : s.memory = m)
    {v : PanValue Word} (hv : E.eval s FD_XOR = some v) :
    ∃ xa xb, byteAt m (off A jb) = some xa ∧ byteAt m (off B jb) = some xb ∧
      v = .word (xa ^^^ xb) := by
  obtain ⟨va, vb, w, hva, hvb, hw, rfl⟩ := eval_op2_inv hE.word hv
  obtain ⟨a1, c1, ha1, hc1, hx1⟩ := eval_loadByte hE.mem hva
  obtain ⟨a2, c2, ha2, hc2, hx2⟩ := eval_loadByte hE.mem hvb
  rw [eval_off0 hE ha hi] at ha1
  rw [eval_off0 hE hb hi] at ha2
  simp only [Option.some.injEq, PanValue.word.injEq] at ha1 ha2 hx1 hx2
  subst ha1 ha2 hx1 hx2
  rw [hE.bytes, hm] at hc1 hc2
  rw [hE.bytes] at hw
  refine ⟨_, _, by unfold byteAt; rw [hc1], by unfold byteAt; rw [hc2], ?_⟩
  simp [wordOp] at hw
  rw [← hw]

/-- The test of bit `jj` of `x`. -/
theorem fd_bit (hE : GuestEnv E) {xv : Word} {jj : Nat} (hjj : jj < 8)
    (hx : s.locals "x" = some (.word xv))
    (hj : s.locals "j" = some (.word (BitVec.ofNat 64 jj))) :
    E.eval s FD_BIT = some (.word (if bitOf xv jj then 1#64 else 0#64)) := by
  have hand : ∀ a b : Word, AndOp.and a b = a &&& b := fun _ _ => rfl
  have hones : ∀ a : Word, a &&& 18446744073709551615#64 = a := by intro a; bv_decide
  have key : ∀ k : Nat, (if (xv >>> k) &&& 1#64 = 0#64 then (0#64 : Word) else 1#64) =
      if xv.getLsbD k then 1#64 else 0#64 := by
    intro k
    by_cases hb : xv.getLsbD k = true
    · rw [if_neg ((and_one_ne_zero xv k).mpr hb), if_pos hb]
    · have : (xv >>> k) &&& 1#64 = 0#64 := by
        by_contra hne
        exact hb ((and_one_ne_zero xv k).mp hne)
      rw [if_pos this, if_neg hb]
  unfold bitOf
  interval_cases jj <;>
    simp [evalF_cmp hE.word, evalF_op hE.word, evalF_shift hE.word, evalArgs_cons, evalArgs_nil,
      hx, hj, wordOp, RiscV.panRiscVShift, hand, hones, evalPanCmp, key] <;>
    try (have h0 := key 0; simpa using h0)

/-- The compared keys do not wrap, and neither does the bit count. -/
structure FdPre (A B nW : Word) : Prop where
  hA : A.toNat + nW.toNat < 2 ^ 64
  hB : B.toNat + nW.toNat < 2 ^ 64
  hn : nW.toNat * 8 < 2 ^ 64

/-- `d` is the first differing bit of the `n`-byte keys at `A` and `B`, or
`n * 8` when all bytes are equal. -/
def FdPost (m : Word → Option (PanValue Word)) (A B : Word) (n : Nat) (d : Word) : Prop :=
  (d.toNat = n * 8 ∧ ∀ k, k < n → byteAt m (off A k) = byteAt m (off B k)) ∨
  ∃ i j xa xb, i < n ∧ j < 8 ∧ d.toNat = i * 8 + j ∧
    (∀ k, k < i → byteAt m (off A k) = byteAt m (off B k)) ∧
    byteAt m (off A i) = some xa ∧ byteAt m (off B i) = some xb ∧
    bitOf xa j ≠ bitOf xb j ∧ ∀ j', j' < j → bitOf xa j' = bitOf xb j'

/-- Outer loop state: the first `jb` bytes are equal. -/
def FdS (m : Word → Option (PanValue Word)) (A B nW : Word)
    (g : VarName → Option (PanValue Word)) (f : FfiState σ) (jb : Nat) (a : St σ) : Prop :=
  a.globals = g ∧ a.memory = m ∧ a.ffi = f ∧ a.locals "a" = some (.word A) ∧
    a.locals "b" = some (.word B) ∧ a.locals "key_len" = some (.word nW) ∧
    a.locals "i" = some (.word (BitVec.ofNat 64 jb)) ∧ jb ≤ nW.toNat ∧
    ∀ k, k < jb → byteAt m (off A k) = byteAt m (off B k)

/-- Inner loop state: the first `jj` bits of `xv` are clear. -/
def FdJ (m : Word → Option (PanValue Word)) (g : VarName → Option (PanValue Word))
    (f : FfiState σ) (xv : Word) (jb jj : Nat) (a : St σ) : Prop :=
  a.globals = g ∧ a.memory = m ∧ a.ffi = f ∧
    a.locals "i" = some (.word (BitVec.ofNat 64 jb)) ∧ a.locals "x" = some (.word xv) ∧
    a.locals "j" = some (.word (BitVec.ofNat 64 jj)) ∧ jj ≤ 8 ∧
    ∀ j', j' < jj → bitOf xv j' = false

def FdQ (m : Word → Option (PanValue Word)) (A B nW : Word)
    (g : VarName → Option (PanValue Word)) (f : FfiState σ) (r : Result σ) : Prop :=
  ∃ l d, r = .returned l g m f [.word d] ∧ FdPost m A B nW.toNat d

theorem less8 (jj : Nat) (h : jj ≤ 8) :
    evalPanCmp .less (BitVec.ofNat 64 jj) (8#64 : Word) = if jj < 8 then 1#64 else 0#64 := by
  interval_cases jj <;> rfl

theorem ofNat_succ (j : Nat) : (BitVec.ofNat 64 j : Word) + 1#64 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 4000000 in
/-- `htab_first_diff(a, b, key_len)` returns the first differing bit. -/
theorem htab_first_diff_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_first_diff" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A B nW : Word) (ha : s.locals "a" = some (.word A))
    (hb : s.locals "b" = some (.word B)) (hn : s.locals "key_len" = some (.word nW))
    (P : FdPre A B nW) (h : Runs E s body r) :
    Stopped r ∨ ∃ l d, r = .returned l s.globals s.memory s.ffi [.word d] ∧
      FdPost s.memory A B nW.toNat d := by
  have hbody := (fun_of_index 130 hE.functions (by guest_decl_at 130) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hPA := P.hA
  have hPn := P.hn
  refine (?_ : WPs E s _ (FdQ s.memory A B nW s.globals s.ffi)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := FdQ s.memory A B nW s.globals s.ffi) ?_
    (by rintro r ⟨l, d, rfl, hd⟩; exact ⟨_, d, rfl, hd⟩)
  have hS0 : FdS s.memory A B nW s.globals s.ffi 0
      ⟨updatePanValueMap s.locals "i" (.word 0#64), s.globals, s.memory, s.ffi⟩ :=
    ⟨rfl, rfl, rfl, by lk [ha], by lk [hb], by lk [hn], by lk [], Nat.zero_le _,
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  have hjt : ∀ j : Nat, j ≤ nW.toNat → (BitVec.ofNat 64 j : Word).toNat = j := by
    intro j hj
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine WPs.seqG (fun a => FdS s.memory A B nW s.globals s.ffi nW.toNat a)
    (WPs.loopG (I := fun a => ∃ jb, FdS s.memory A B nW s.globals s.ffi jb a) ⟨0, hS0⟩ ?_ ?_) ?_
  · -- one byte
    rintro a ⟨jb, hg, hm, hf, hA', hB', hK, hI, hjn, hbytes⟩ ⟨w, c, hcond, hw⟩
    have hc := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 jb) (by lk [hI]))
      (of_eval (w := nW) (by lk [hK])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hlt : jb < nW.toNat := by
      by_contra hge
      have hnl : ¬ (BitVec.ofNat 64 jb : Word) < nW := by
        rw [BitVec.lt_def, hjt jb hjn]
        exact hge
      rw [hc] at hw
      simp [evalPanCmp, hnl] at hw
    refine WPs.dec_ev (fun v hv => ?_)
    obtain ⟨xa, xb, hxa, hxb, rfl⟩ := fd_xor hE hA' hB' hI hm hv
    have hxlt : (xa ^^^ xb).toNat < 256 := xor_lt _ _ (byteAt_lt hxa) (byteAt_lt hxb)
    by_cases hx0 : xa ^^^ xb = 0#64
    · have hab : xa = xb := BitVec.xor_eq_zero_iff.mp hx0
      refine WPs.guard0 (fun y hy => by
        rw [eval_cmp_inv hE (of_eval (w := xa ^^^ xb) (by lk [])) (of_eval (eval_const _ _)) y hy]
        simp [evalPanCmp, hx0]) ?_
      refine WPs.assign (old := BitVec.ofNat 64 jb) (by lk [hI])
        (of_eval (w := BitVec.ofNat 64 (jb + 1)) (by ev [hI, ofNat_succ])) ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨jb + 1, hg, hm, hf, ?_, ?_, ?_, ?_, by omega, ?_⟩
      · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hA']
      · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hB']
      · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hK]
      · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      · intro k hk
        by_cases hkj : k = jb
        · subst hkj
          rw [hxa, hxb, hab]
        · exact hbytes k (by omega)
    · refine WPs.seqG (fun _ => False) ?_ (fun _ hF => hF.elim)
      refine WPs.ite (w := 1#64) (fun y hy => by
        rw [eval_cmp_inv hE (of_eval (w := xa ^^^ xb) (by lk [])) (of_eval (eval_const _ _)) y hy]
        simp [evalPanCmp, hx0]) ?_
      split
      · rename_i h10
        exact absurd h10 (by decide)
      refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
      refine WPs.conseq (Q' := FdQ s.memory A B nW s.globals s.ffi) ?_
        (by rintro r ⟨l, d, rfl, hd⟩; exact ⟨_, d, rfl, hd⟩)
      refine WPs.loopG (I := fun a' => ∃ jj, FdJ s.memory s.globals s.ffi (xa ^^^ xb) jb jj a')
        ⟨0, hg, hm, hf, by lk [hI], by lk [], by lk [], by omega,
          fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩ ?_ ?_
      · -- one bit
        rintro a' ⟨jj, hg', hm', hf', hi', hx', hj', hj8, hbits⟩ ⟨w', c', hcond', hw'⟩
        have hc' := eval_cmp_inv hE (op := .less)
          (of_eval (w := BitVec.ofNat 64 jj) (by lk [hj'])) (of_eval (eval_const _ (8#64))) _
          (cond_of_eval hcond')
        simp only [PanValue.word.injEq] at hc'
        rw [less8 jj hj8] at hc'
        have hjj : jj < 8 := by
          by_contra hge
          rw [if_neg hge] at hc'
          rw [hc'] at hw'
          simp at hw'
        by_cases hbit : bitOf (xa ^^^ xb) jj = true
        · refine WPs.seqG (fun _ => False) ?_ (fun _ hF => hF.elim)
          refine WPs.ite (w := 1#64) (of_eval (by rw [fd_bit hE hjj hx' hj', if_pos hbit])) ?_
          split
          · rename_i h10
            exact absurd h10 (by decide)
          refine WPs.ret (of_eval (w := BitVec.ofNat 64 jb * 8#64 + BitVec.ofNat 64 jj)
            (by ev [evalPanOp, hi', hj'])) ?_
          refine ⟨_, _, by rw [hg', hm', hf'], Or.inr ⟨jb, jj, xa, xb, hlt, hjj, ?_, hbytes, hxa,
            hxb, ?_, ?_⟩⟩
          · have h8 : (8#64 : Word).toNat = 8 := by decide
            have hjj64 : (BitVec.ofNat 64 jj : Word).toNat = jj := by
              rw [BitVec.toNat_ofNat]
              exact Nat.mod_eq_of_lt (by omega)
            have hmul : jb * 8 % 2 ^ 64 = jb * 8 := Nat.mod_eq_of_lt (by omega)
            rw [BitVec.toNat_add, BitVec.toNat_mul, hjt jb hjn, hjj64, h8, hmul]
            exact Nat.mod_eq_of_lt (by omega)
          · rw [bitOf_xor] at hbit
            intro heq
            rw [heq] at hbit
            simp at hbit
          · intro j0 hj0
            have := hbits j0 hj0
            rw [bitOf_xor] at this
            simpa using this
        · have hbit' : bitOf (xa ^^^ xb) jj = false := by simpa using hbit
          refine WPs.guard0 (of_eval (by rw [fd_bit hE hjj hx' hj', hbit']; rfl)) ?_
          refine WPs.assign (old := BitVec.ofNat 64 jj) hj'
            (of_eval (w := BitVec.ofNat 64 (jj + 1)) (by ev [hj', ofNat_succ])) ?_
          refine ⟨jj + 1, hg', hm', hf', by lk [hi'], by lk [hx'], by lk [], by omega, ?_⟩
          intro j0 hj0
          by_cases h0 : j0 = jj
          · rw [h0]; exact hbit'
          · exact hbits j0 (by omega)
      · -- all eight bits clear: impossible
        rintro a' k ⟨jj, hg', hm', hf', hi', hx', hj', hj8, hbits⟩ hcond'
        exfalso
        have hc' := eval_cmp_inv hE (op := .less)
          (of_eval (w := BitVec.ofNat 64 jj) (by lk [hj'])) (of_eval (eval_const _ (8#64))) _
          (cond_of_eval hcond')
        simp only [PanValue.word.injEq] at hc'
        rw [less8 jj hj8] at hc'
        have hj8' : jj = 8 := by
          by_contra hne
          rw [if_pos (by omega)] at hc'
          cases hc'
        obtain ⟨j0, hj0, hset⟩ := byte_bit _ hxlt hx0
        rw [hbits j0 (by omega)] at hset
        cases hset
  · -- loop exit: all bytes compared
    rintro a k ⟨jb, hg, hm, hf, hA', hB', hK, hI, hjn, hbytes⟩ hcond
    have hc := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 jb) (by lk [hI]))
      (of_eval (w := nW) (by lk [hK])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hnl := lower_zero hc.symm
    rw [BitVec.lt_def, hjt jb hjn] at hnl
    have hjb : jb = nW.toNat := by omega
    subst hjb
    exact ⟨hg, hm, hf, hA', hB', hK, hI, hjn, hbytes⟩
  · rintro a ⟨hg, hm, hf, hA', hB', hK, hI, hjn, hbytes⟩
    refine WPs.ret (of_eval (w := nW * 8#64) (by ev [evalPanOp, hK])) ?_
    refine ⟨_, _, by rw [hg, hm, hf], Or.inl ⟨?_, hbytes⟩⟩
    have h8 : (8#64 : Word).toNat = 8 := by decide
    rw [BitVec.toNat_mul, h8]
    exact Nat.mod_eq_of_lt hPn

end InitECandidate.Solver.GuestBound
