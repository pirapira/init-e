import InitECandidate.Solver.GuestBound.Limbs4

/-!
# `u256` helpers on zero operands

Specifications used for the loop of `taylor_exponential`: converting a word,
testing for zero, and dividing by zero (which returns zero before the
division workspace is touched).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem evalF_panOp (s : St σ) (operator : PanOp) (es : List (Exp Word)) :
    E.eval s (.panOp operator es) =
      match E.evalArgs s es with
      | some [.word l, .word r] => (evalPanOp operator [l, r]).map .word
      | _ => none := by
  simp only [Env.eval, Env.evalArgs, evalPanValueExps]
  rw [evalPanValueExp]
  cases evalPanValueExp.evalPanValueExps E.structs s.locals s.globals s.memory E.baseAddress
      E.topAddress E.bytesInWord es E.memoryAccess with
  | none => rfl
  | some values =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    rcases values with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, rest⟩⟩⟩
    · rfl
    · cases v1 <;> rfl
    · cases v1 <;> cases v2 <;> rfl
    · cases v1 <;> cases v2 <;> rfl

/-- The record of four zero words. -/
abbrev zero4 : PanValue Word := .rStruct [.word 0, .word 0, .word 0, .word 0]

theorem payload_words8 (structs : StructContext) (d0 d1 d2 d3 d4 d5 d6 d7 : Word) :
    panValuePayloadWithinLimit structs
      (.rStruct [.word d0, .word d1, .word d2, .word d3, .word d4, .word d5, .word d6,
        .word d7]) = true := by
  simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
    panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel, panValueFlatValueFuel,
    panValueFlatValueFuel.panValueFlatValueListFuel]

/-- `u256_from_word(w)` is `<w, 0, 0, 0>`. -/
theorem u256_from_word_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_from_word" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (w : Word) (hw : s.locals "w" = some (.word w))
    (h : Runs E s body r) :
    r = .returned (fun _ => none) s.globals s.memory s.ffi
      [.rStruct [.word w, .word 0, .word 0, .word 0]] := by
  have hbody := (fun_of_index 39 hE.functions (by guest_decl_at 39) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp only [runs_return, evalF_rStruct, evalF_local, eval_const, evalArgs_cons, evalArgs_nil,
    hw, Option.map_some, payload_words4, if_true] at h
  exact h

/-- `u256_is_zero` returns 1 on zero. -/
theorem u256_is_zero_zero (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_is_zero" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (ha : s.locals "a" = some zero4) (h : Runs E s body r) :
    r = .returned (fun _ => none) s.globals s.memory s.ffi [.word 1] := by
  have hbody := (fun_of_index 42 hE.functions (by guest_decl_at 42) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp (config := { decide := true }) only [runs_seq, runs_ite, runs_return, runs_skip,
    evalF_cmp hE.word, evalF_op hE.word, evalF_rField, evalF_local, eval_const, evalArgs_cons,
    evalArgs_nil, ha, Option.map_some, List.getElem?_cons_zero, List.getElem?_cons_succ,
    wordsProj_nil, wordsProj_cons, wordOp, List.foldr, payload_word, if_true, if_false,
    exists_eq_left] at h
  exact h

/-- `u256_divmod` by zero returns eight zero words. -/
theorem u256_divmod_zero (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_divmod" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (hb : s.locals "b" = some zero4) (h : Runs E s body r) :
    r = .returned (fun _ => none) s.globals s.memory s.ffi
      [.rStruct [.word 0, .word 0, .word 0, .word 0, .word 0, .word 0, .word 0, .word 0]] := by
  have hbody := (fun_of_index 69 hE.functions (by guest_decl_at 69) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp (config := { decide := true }) only [runs_seq, runs_ite, runs_return, runs_skip,
    evalF_rStruct, evalF_cmp hE.word, evalF_op hE.word, evalF_rField, evalF_local, eval_const,
    evalArgs_cons, evalArgs_nil, hb, Option.map_some, List.getElem?_cons_zero,
    List.getElem?_cons_succ, wordsProj_nil, wordsProj_cons, wordOp, List.foldr,
    payload_words8, if_true, if_false, exists_eq_left] at h
  exact h

theorem payload_words2 (structs : StructContext) (d0 d1 : Word) :
    panValuePayloadWithinLimit structs (.rStruct [.word d0, .word d1]) = true := by
  simp [panValuePayloadWithinLimit, panValuePayloadSizeFuel,
    panValuePayloadSizeFuel.panValuePayloadSizeFieldsFuel, panValueFlatValueFuel,
    panValueFlatValueFuel.panValueFlatValueListFuel]

set_option maxHeartbeats 4000000 in
/-- `mul64x64(0, b)` is `<0, 0>`. -/
theorem mul64x64_zero (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "mul64x64" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (b : Word) (ha : s.locals "a" = some (.word 0))
    (hb : s.locals "b" = some (.word b)) (h : Runs E s body r) :
    ∃ l, r = .returned l s.globals s.memory s.ffi [.rStruct [.word 0, .word 0]] := by
  have hbody := (fun_of_index 59 hE.functions (by guest_decl_at 59) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp (config := { decide := true }) only [runs_seq, runs_dec, runs_primitive', runs_return,
    evalF_rStruct, evalF_rField, evalF_local, eval_const, evalF_op hE.word,
    evalF_shift hE.word, evalF_panOp, evalArgs_cons, evalArgs_nil, ha, hb,
    hE.prim.addCarry, Option.map_some, List.getElem?_cons_zero, List.getElem?_cons_succ,
    shape_word, shape_rStruct, shape_matches_self, wordsProj_nil, wordsProj_cons,
    update_lookup, addCarryResult, List.map_cons, List.map_nil, if_true, if_false, wordOp,
    List.foldr, RiscV.panRiscVShift, BitVec.toNat_ofNat, evalPanOp_mul,
    restorePanValueFfiLocal, payload_words2, exists_eq_left] at h
  have hz : ∀ m : BitVec 64, AndOp.and (0 : BitVec 64) (AndOp.and m (~~~0)) = 0 := by
    intro m
    show (0 &&& (m &&& ~~~0)) = 0
    simp
  simp only [hz] at h
  simp at h
  exact ⟨_, h⟩

end InitECandidate.Solver.GuestBound
