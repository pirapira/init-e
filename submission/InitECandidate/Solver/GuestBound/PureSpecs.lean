import InitECandidate.Solver.GuestBound.SepExtendMem

/-!
# Value specifications of small pure helpers

`add_sat` (exact), `ceil32`. Each changes nothing and returns one word; the
statements say which.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- `add_sat(a, b)`: the sum, or `2^64 - 1` when it does not fit. -/
theorem add_sat_exact (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "add_sat" E.functions = some (parameters, body))
    (c : St σ) (a b : Word) (ha : c.locals "a" = some (.word a))
    (hb : c.locals "b" = some (.word b)) :
    WPr E c body (fun r => ∃ l t, r = .returned l c.globals c.memory c.ffi [.word t] ∧
      ((a.toNat + b.toNat < 2 ^ 64 ∧ t.toNat = a.toNat + b.toNat) ∨
        (2 ^ 64 ≤ a.toNat + b.toNat ∧ t = 18446744073709551615#64))) := by
  have hbody := (fun_of_index 441 hE.functions (by guest_decl_at 441) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.dec_ev (fun v hv => ?_)
  have hs := (of_eval (w := a + b) (by ev [ha, hb])) v hv
  subst hs
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap c.locals "s" (.word (a + b)), c.globals,
      c.memory, c.ffi⟩ ∧ ¬ (a + b) < a) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := a + b) (by lk []))
      (of_eval (w := a) (by lk [ha])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      exact WPr.skip ⟨rfl, lower_zero hcv.symm⟩
    · rename_i h0
      have hlt : a + b < a := by
        by_contra hlt
        exact h0 (by rw [hcv]; simp [evalPanCmp, hlt])
      refine WPr.ret (w := 18446744073709551615#64) (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨_, _, rfl, Or.inr ⟨?_, rfl⟩⟩
      bv_omega
  rintro _ ⟨rfl, hge⟩
  refine WPr.ret (w := a + b) (of_eval (by lk [])) ?_
  simp only [restorePanValueFfiLocal]
  refine ⟨_, _, rfl, Or.inl ?_⟩
  constructor <;> bv_omega

/-- The low five bits, in the form the evaluator produces for `v & 31`. -/
theorem and_31 (v : BitVec 64) :
    (AndOp.and v (AndOp.and 31#64 (~~~(0 : BitVec 64)))).toNat = v.toNat % 32 := by
  have hmask : AndOp.and 31#64 (~~~(0 : BitVec 64)) = 31#64 := by decide
  rw [hmask]
  show (v &&& 31#64).toNat = v.toNat % 32
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod v.toNat 5

/-- `ceil32(v)`: the next multiple of 32, or `2^64 - 1` when that does not fit. -/
theorem ceil32_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "ceil32" E.functions = some (parameters, body))
    (c : St σ) (v : Word) (hv : c.locals "v" = some (.word v)) :
    WPr E c body (fun r => ∃ l t, r = .returned l c.globals c.memory c.ffi [.word t] ∧
      (t = 18446744073709551615#64 ∨
        (t.toNat % 32 = 0 ∧ v.toNat ≤ t.toNat ∧ t.toNat < v.toNat + 32))) := by
  have hbody := (fun_of_index 442 hE.functions (by guest_decl_at 442) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.dec_ev (fun x hx => ?_)
  have hr := (of_eval (w := AndOp.and v (AndOp.and 31#64 (~~~(0 : BitVec 64))))
    (by ev [hv])) x hx
  subst hr
  have h31 := and_31 v
  generalize hrd : AndOp.and v (AndOp.and 31#64 (~~~(0 : BitVec 64))) = rr at h31 ⊢
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap c.locals "r" (.word rr), c.globals,
      c.memory, c.ffi⟩ ∧ rr ≠ 0#64) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .equal) (of_eval (w := rr) (by lk []))
      (of_eval (w := 0#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      refine WPr.skip ⟨rfl, fun hz => ?_⟩
      rw [hz] at hcv
      simp [evalPanCmp] at hcv
    · rename_i h0
      have hz : rr = 0#64 := by
        by_contra hne
        exact h0 (by rw [hcv]; simp [evalPanCmp, hne])
      refine WPr.ret (w := v) (of_eval (by lk [hv])) ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨_, _, rfl, Or.inr ⟨?_, Nat.le_refl _, by omega⟩⟩
      rw [hz] at h31
      simp at h31
      omega
  rintro _ ⟨rfl, hne⟩
  have hr0 : rr.toNat ≠ 0 := fun h => hne (by bv_omega)
  have hsub : (32#64 - rr).toNat = 32 - rr.toNat := by
    have : rr.toNat < 32 := by rw [h31]; exact Nat.mod_lt _ (by norm_num)
    bv_omega
  refine WPr.decCall_spec (fun rb => ∃ l t, rb = .returned l c.globals c.memory c.ffi [.word t] ∧
      ((v.toNat + (32#64 - rr).toNat < 2 ^ 64 ∧ t.toNat = v.toNat + (32#64 - rr).toNat) ∨
        (2 ^ 64 ≤ v.toNat + (32#64 - rr).toNat ∧ t = 18446744073709551615#64))) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 441 hE.functions (by guest_decl_at 441) (by decide +kernel)
      hlk).2
    have hvals : values = [.word v, .word (32#64 - rr)] := by
      have h1 : E.evalArgs ⟨updatePanValueMap c.locals "r" (.word rr), c.globals, c.memory,
          c.ffi⟩ [.var .local "v", .op .sub [.const 32#64, .var .local "r"]] =
          some [.word v, .word (32#64 - rr)] := by ev [hv]
      rw [h1] at hvalues
      exact (Option.some.inj hvalues).symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact add_sat_exact hE parameters cbody hlk ⟨cl, c.globals, c.memory, c.ffi⟩ v (32#64 - rr)
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  · rintro l g m ffi t ⟨l', t', hC, ht⟩
    injection hC with _ hg hm hf hv'
    subst hg hm hf
    simp only [List.cons.injEq, and_true] at hv'
    subst hv'
    refine WPr.ret (w := t') (of_eval (by lk [])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨_, _, rfl, ?_⟩
    rcases ht with ⟨h1, h2⟩ | ⟨-, h2⟩
    · right
      have : rr.toNat < 32 := by rw [h31]; exact Nat.mod_lt _ (by norm_num)
      refine ⟨?_, by omega, by omega⟩
      rw [h2, hsub, h31]
      omega
    · exact Or.inl h2
  · rintro l g m ffi exc v' ⟨l', t', hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', t', hC, -⟩
    cases hC

end InitECandidate.Solver.GuestBound
