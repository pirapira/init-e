import InitECandidate.Solver.GuestBound.Mul64

/-!
# Value specifications for the memory-cost helpers

`sat_word`, `u256_is_zero`, `words_of`, and the one fact needed about
`memory_gas_cost`: a result other than `2^64 - 1` means the size is below `2^37`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem or3_zero (w1 w2 w3 : Word) :
    OrOp.or w1 (OrOp.or w2 (OrOp.or w3 0#64)) = 0#64 ↔ w1 = 0#64 ∧ w2 = 0#64 ∧ w3 = 0#64 := by
  show (w1 ||| (w2 ||| (w3 ||| 0#64))) = 0#64 ↔ _
  constructor
  · intro h
    simpa [BitVec.or_eq_zero_iff] using h
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem or4_zero (w0 w1 w2 w3 : Word) :
    OrOp.or w0 (OrOp.or w1 (OrOp.or w2 (OrOp.or w3 0#64))) = 0#64 ↔
      w0 = 0#64 ∧ w1 = 0#64 ∧ w2 = 0#64 ∧ w3 = 0#64 := by
  show (w0 ||| (w1 ||| (w2 ||| (w3 ||| 0#64)))) = 0#64 ↔ _
  constructor
  · intro h
    simpa [BitVec.or_eq_zero_iff] using h
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

/-- The value of `sat_word` on a four-word value. -/
def satW (w0 w1 w2 w3 : Word) : Word :=
  if w1 = 0#64 ∧ w2 = 0#64 ∧ w3 = 0#64 then w0 else 18446744073709551615#64

/-- `sat_word(v)`: the low word when the others are zero, else `2^64 - 1`. -/
theorem sat_word_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "sat_word" E.functions = some (parameters, body))
    (c : St σ) (w0 w1 w2 w3 : Word)
    (hv : c.locals "v" = some (.rStruct [.word w0, .word w1, .word w2, .word w3])) :
    WPr E c body (fun r => ∃ l, r = .returned l c.globals c.memory c.ffi
      [.word (satW w0 w1 w2 w3)]) := by
  have hbody := (fun_of_index 440 hE.functions (by guest_decl_at 440) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.seq (fun s' => s' = c ∧ (w1 = 0#64 ∧ w2 = 0#64 ∧ w3 = 0#64))
    (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .notEqual)
      (of_eval (w := OrOp.or w1 (OrOp.or w2 (OrOp.or w3 0#64)))
        (by simp (config := { decide := true }) [evalF_op hE.word, evalF_rField, evalArgs_cons,
          evalArgs_nil, wordOp, hv]))
      (of_eval (w := 0#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      refine WPr.skip ⟨rfl, (or3_zero w1 w2 w3).mp ?_⟩
      by_contra hne
      simp [evalPanCmp, hne] at hcv
    · rename_i h0
      have hnz : ¬ (w1 = 0#64 ∧ w2 = 0#64 ∧ w3 = 0#64) := by
        intro hz
        exact h0 (by rw [hcv, (or3_zero w1 w2 w3).mpr hz]; simp [evalPanCmp])
      have e : satW w0 w1 w2 w3 = 18446744073709551615#64 := by simp [satW, hnz]
      refine WPr.ret (w := 18446744073709551615#64) (of_eval (eval_const _ _)) ?_
      exact ⟨_, by rw [e]⟩
  intro a ha
  obtain ⟨ha1, hz⟩ := ha
  rw [ha1]
  clear ha1 a
  have e : satW w0 w1 w2 w3 = w0 := by simp [satW, hz]
  refine WPr.ret (w := w0) (of_eval (by simp [evalF_rField, hv])) ?_
  exact ⟨_, by rw [e]⟩

/-- `u256_is_zero(a)`: nonzero exactly when all four words are zero. -/
theorem u256_is_zero_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_is_zero" E.functions = some (parameters, body))
    (c : St σ) (w0 w1 w2 w3 : Word)
    (hv : c.locals "a" = some (.rStruct [.word w0, .word w1, .word w2, .word w3])) :
    WPr E c body (fun r => ∃ l z, r = .returned l c.globals c.memory c.ffi [.word z] ∧
      (z ≠ 0#64 ↔ (w0 = 0#64 ∧ w1 = 0#64 ∧ w2 = 0#64 ∧ w3 = 0#64))) := by
  have hbody := (fun_of_index 42 hE.functions (by guest_decl_at 42) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.seq (fun s' => s' = c ∧ ¬ (w0 = 0#64 ∧ w1 = 0#64 ∧ w2 = 0#64 ∧ w3 = 0#64))
    (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .equal)
      (of_eval (w := OrOp.or w0 (OrOp.or w1 (OrOp.or w2 (OrOp.or w3 0#64))))
        (by simp (config := { decide := true }) [evalF_op hE.word, evalF_rField, evalArgs_cons,
          evalArgs_nil, wordOp, hv]))
      (of_eval (w := 0#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      refine WPr.skip ⟨rfl, fun hz => ?_⟩
      rw [(or4_zero w0 w1 w2 w3).mpr hz] at hcv
      simp [evalPanCmp] at hcv
    · rename_i h0
      have hz : w0 = 0#64 ∧ w1 = 0#64 ∧ w2 = 0#64 ∧ w3 = 0#64 := by
        refine (or4_zero w0 w1 w2 w3).mp ?_
        by_contra hne
        exact h0 (by rw [hcv]; simp [evalPanCmp, hne])
      refine WPr.ret (w := 1#64) (of_eval (eval_const _ _)) ?_
      exact ⟨_, _, rfl, by simp [hz]⟩
  intro a ha
  obtain ⟨ha1, hnz⟩ := ha
  rw [ha1]
  clear ha1 a
  refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  exact ⟨_, _, rfl, by simp [hnz]⟩

/-- `words_of(n)`: `ceil32(n) / 32`. -/
theorem words_of_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "words_of" E.functions = some (parameters, body))
    (c : St σ) (n : Word) (hn : c.locals "n" = some (.word n)) :
    WPr E c body (fun r => ∃ l w cv, r = .returned l c.globals c.memory c.ffi [.word w] ∧
      (cv = 18446744073709551615#64 ∨
        (cv.toNat % 32 = 0 ∧ n.toNat ≤ cv.toNat ∧ cv.toNat < n.toNat + 32)) ∧
      w.toNat = cv.toNat / 32) := by
  have hbody := (fun_of_index 443 hE.functions (by guest_decl_at 443) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.decCall_spec (fun rb => ∃ l t, rb = .returned l c.globals c.memory c.ffi [.word t] ∧
      (t = 18446744073709551615#64 ∨
        (t.toNat % 32 = 0 ∧ n.toNat ≤ t.toNat ∧ t.toNat < n.toNat + 32))) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 442 hE.functions (by guest_decl_at 442) (by decide +kernel)
      hlk).2
    have hvals : values = [.word n] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local, hn]
        at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact ceil32_runs hE parameters cbody hlk ⟨cl, c.globals, c.memory, c.ffi⟩ n
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  · rintro l g m ffi v ⟨l', t, hC, ht⟩
    injection hC with _ hg hm hf hv'
    subst hg hm hf
    simp only [List.cons.injEq, and_true] at hv'
    subst hv'
    refine WPr.ret (w := t >>> 5) (of_eval (by
      simp (config := { decide := true }) [evalF_shift hE.word, eval_const,
        RiscV.panRiscVShift, update_lookup])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨_, _, t, rfl, ht, ?_⟩
    rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rfl
  · rintro l g m ffi exc v ⟨l', t, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', t, hC, -⟩
    cases hC

end InitECandidate.Solver.GuestBound
