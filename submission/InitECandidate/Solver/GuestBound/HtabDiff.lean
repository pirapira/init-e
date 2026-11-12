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

end InitECandidate.Solver.GuestBound
