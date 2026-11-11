import InitECandidate.Solver.GuestBound.Limbs

/-!
# Four-limb comparison and subtraction

Specifications of `u256_lt` and `u256_sub` in terms of the represented numbers.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

set_option hygiene false in
/-- One limb of a most-significant-first comparison of four-limb numbers. -/
local macro "lt_level4" x:ident y:ident : tactic => `(tactic| (
  by_cases e : $x = $y
  rotate_left
  · have hne : ($x).toNat ≠ ($y).toNat := fun hh => e (BitVec.eq_of_toNat_eq hh)
    by_cases l : $x < $y
    · simp only [e, l, if_false, not_true_eq_false, exists_eq_left] at h
      rw [h, if_pos (by simp only [limbsVal]; rw [BitVec.lt_def] at l; omega)]
      rfl
    · simp only [e, l, if_false, if_true, not_false_eq_true, exists_eq_left] at h
      rw [h, if_neg (by simp only [limbsVal]; rw [BitVec.lt_def] at l; omega)]
      rfl
  subst e
  simp only [if_true, exists_eq_left, ha, hb, List.getElem?_cons_zero,
    List.getElem?_cons_succ, key, keyl] at h))

set_option maxHeartbeats 4000000 in
/-- `u256_lt` compares the represented numbers. -/
theorem u256_lt_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_lt" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha : s.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hb : s.locals "b" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (h : Runs E s body r) :
    r = .returned (fun _ => none) s.globals s.memory s.ffi
      [.word (if limbsVal [a0, a1, a2, a3] < limbsVal [b0, b1, b2, b3] then 1 else 0)] := by
  have hbody := (fun_of_index 46 hE.functions (by guest_decl_at 46) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp only [runs_seq, runs_ite, runs_return, runs_skip, evalF_cmp hE.word, evalF_rField,
    evalF_local, eval_const, ha, hb, payload_word, if_true, List.getElem?_cons_zero,
    List.getElem?_cons_succ] at h
  have key : ∀ x y : Word, (evalPanCmp Cmp.notEqual x y = 0) = (x = y) := by
    intro x y
    by_cases hxy : x = y <;> simp [evalPanCmp, hxy]
  have keyl : ∀ x y : Word, (evalPanCmp Cmp.lower x y = 0) = (¬ x < y) := by
    intro x y
    by_cases hxy : x < y <;> simp [evalPanCmp, hxy]
  simp only [key, keyl] at h
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  lt_level4 a3 b3
  lt_level4 a2 b2
  lt_level4 a1 b1
  by_cases l : a0 < b0
  · simp only [l, if_false, not_true_eq_false, exists_eq_left] at h
    rw [h, if_pos (by simp only [limbsVal]; rw [BitVec.lt_def] at l; omega)]
    rfl
  · simp only [l, if_true, not_false_eq_true, exists_eq_left] at h
    rw [h, if_neg (by simp only [limbsVal]; rw [BitVec.lt_def] at l; omega)]
    rfl

theorem payload_words4 (structs : StructContext) (d0 d1 d2 d3 : Word) :
    panValuePayloadWithinLimit structs
      (.rStruct [.word d0, .word d1, .word d2, .word d3]) = true := by
  simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
    panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel, panValueFlatValueFuel,
    panValueFlatValueFuel.panValueFlatValueListFuel]

set_option maxHeartbeats 4000000 in
/-- `u256_sub` subtracts the represented numbers when there is no borrow. -/
theorem u256_sub_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_sub" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha : s.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hb : s.locals "b" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hle : limbsVal [b0, b1, b2, b3] ≤ limbsVal [a0, a1, a2, a3])
    (h : Runs E s body r) :
    ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] = limbsVal [a0, a1, a2, a3] - limbsVal [b0, b1, b2, b3] := by
  have hbody := (fun_of_index 57 hE.functions (by guest_decl_at 57) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp (config := { decide := true }) only [runs_seq, runs_dec, runs_primitive', runs_return,
    evalF_rStruct, evalF_rField,
    evalF_local, eval_const, evalF_op hE.word, evalArgs_cons, evalArgs_nil, ha, hb,
    hE.prim.addCarry, Option.map_some, List.getElem?_cons_zero, List.getElem?_cons_succ,
    shape_word, shape_rStruct, shape_matches_self, wordsProj_nil, wordsProj_cons,
    update_lookup, addCarryResult, List.map_cons, List.map_nil, if_true, if_false, wordOp,
    List.foldr, restorePanValueFfiLocal, payload_words4, exists_eq_left] at h
  refine ⟨_, _, _, _, _, h, ?_⟩
  have key := subLimbs_sub [a0.toNat, a1.toNat, a2.toNat, a3.toNat]
    [b0.toNat, b1.toNat, b2.toNat, b3.toNat] rfl
    (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact BitVec.isLt _)
    (by
      intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> exact BitVec.isLt _)
    (by simpa only [limbsVal, nval] using hle)
  simp only [subLimbs, nval] at key
  simp only [limbsVal, BitVec.toNat_ofNat, not_word, carry_in]
  exact key

end InitECandidate.Solver.GuestBound
