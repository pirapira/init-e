import InitECandidate.Solver.GuestBound.Limbs4

/-!
# 256-bit helpers of the guest

`u256_sub` and `u256_add` on four 64-bit limbs, as arithmetic modulo `2^256`
(`u256_lt` and the borrow-free subtraction are in `Limbs4.lean`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem mem4 {P : Nat → Prop} {a b c d : Nat} (ha : P a) (hb : P b) (hc : P c) (hd : P d) :
    ∀ x ∈ [a, b, c, d], P x := by
  intro x hx
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> assumption

set_option maxHeartbeats 4000000 in
/-- `u256_sub` subtracts modulo `2^256`. -/
theorem u256_sub_mod (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_sub" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha : s.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hb : s.locals "b" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (h : Runs E s body r) :
    ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] =
        (limbsVal [a0, a1, a2, a3] + 2 ^ 256 - limbsVal [b0, b1, b2, b3]) % 2 ^ 256 := by
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
  obtain ⟨c', hc', key⟩ := subLimbs_val [a0.toNat, a1.toNat, a2.toNat, a3.toNat]
    [b0.toNat, b1.toNat, b2.toNat, b3.toNat] 1 rfl
    (mem4 (P := fun x => x < 2 ^ 64) a0.isLt a1.isLt a2.isLt a3.isLt)
    (mem4 (P := fun x => x < 2 ^ 64) b0.isLt b1.isLt b2.isLt b3.isLt) (Nat.le_refl 1)
  have hd := nval_lt _ (subLimbs_lt [a0.toNat, a1.toNat, a2.toNat, a3.toNat]
    [b0.toNat, b1.toNat, b2.toNat, b3.toNat] 1)
  have hB := nval_lt [b0.toNat, b1.toNat, b2.toNat, b3.toNat]
    (mem4 (P := fun x => x < 2 ^ 64) b0.isLt b1.isLt b2.isLt b3.isLt)
  have hA := nval_lt [a0.toNat, a1.toNat, a2.toNat, a3.toNat]
    (mem4 (P := fun x => x < 2 ^ 64) a0.isLt a1.isLt a2.isLt a3.isLt)
  simp only [subLimbs, nval, List.length_cons, List.length_nil] at key hd hB hA
  simp only [limbsVal, BitVec.toNat_ofNat, not_word, carry_in]
  norm_num at key hd hB hA ⊢
  rcases Nat.lt_or_ge c' 1 with h0 | h1
  · have : c' = 0 := by omega
    subst this
    omega
  · have : c' = 1 := by omega
    subst this
    omega

set_option maxHeartbeats 4000000 in
/-- `u256_add` adds modulo `2^256`. -/
theorem u256_add_mod (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_add" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha : s.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hb : s.locals "b" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (h : Runs E s body r) :
    ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] =
        (limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3]) % 2 ^ 256 := by
  have hbody := (fun_of_index 56 hE.functions (by guest_decl_at 56) (by decide +kernel)
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
  obtain ⟨c', hc', key⟩ := addLimbs_val [a0.toNat, a1.toNat, a2.toNat, a3.toNat]
    [b0.toNat, b1.toNat, b2.toNat, b3.toNat] 0 rfl
    (mem4 (P := fun x => x < 2 ^ 64) a0.isLt a1.isLt a2.isLt a3.isLt)
    (mem4 (P := fun x => x < 2 ^ 64) b0.isLt b1.isLt b2.isLt b3.isLt) (Nat.zero_le 1)
  have hd := nval_lt _ (addLimbs_lt [a0.toNat, a1.toNat, a2.toNat, a3.toNat]
    [b0.toNat, b1.toNat, b2.toNat, b3.toNat] 0)
  simp only [addLimbs, nval, List.length_cons, List.length_nil] at key hd
  simp only [limbsVal, BitVec.toNat_ofNat, carry_in]
  norm_num at key hd ⊢
  rcases Nat.lt_or_ge c' 1 with h0 | h1
  · have : c' = 0 := by omega
    subst this
    omega
  · have : c' = 1 := by omega
    subst this
    omega

theorem payload_words5 (structs : StructContext) (d0 d1 d2 d3 d4 : Word) :
    panValuePayloadWithinLimit structs
      (.rStruct [.word d0, .word d1, .word d2, .word d3, .word d4]) = true := by
  simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
    panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel, panValueFlatValueFuel,
    panValueFlatValueFuel.panValueFlatValueListFuel]

set_option maxHeartbeats 4000000 in
/-- `u256_add_carry` adds exactly, with the carry as a fifth limb. -/
theorem u256_add_carry_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_add_carry" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha : s.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hb : s.locals "b" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (h : Runs E s body r) :
    ∃ l d0 d1 d2 d3 d4, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3, .word d4]] ∧
      limbsVal [d0, d1, d2, d3, d4] = limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3] := by
  have hbody := (fun_of_index 55 hE.functions (by guest_decl_at 55) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp (config := { decide := true }) only [runs_seq, runs_dec, runs_primitive', runs_return,
    evalF_rStruct, evalF_rField,
    evalF_local, eval_const, evalF_op hE.word, evalArgs_cons, evalArgs_nil, ha, hb,
    hE.prim.addCarry, Option.map_some, List.getElem?_cons_zero, List.getElem?_cons_succ,
    shape_word, shape_rStruct, shape_matches_self, wordsProj_nil, wordsProj_cons,
    update_lookup, addCarryResult, List.map_cons, List.map_nil, if_true, if_false, wordOp,
    List.foldr, restorePanValueFfiLocal, payload_words5, exists_eq_left] at h
  refine ⟨_, _, _, _, _, _, h, ?_⟩
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt
  simp only [limbsVal, BitVec.toNat_ofNat, carry_in]
  split_ifs <;> omega

end InitECandidate.Solver.GuestBound
