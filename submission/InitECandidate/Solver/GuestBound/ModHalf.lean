import InitECandidate.Solver.GuestBound.ModSub

/-!
# `mod_half`: halving, after adding the modulus to an odd operand
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem and1_toNat (w : Word) : (w &&& 1#64).toNat = w.toNat % 2 := by
  have h : (1#64 : Word).toNat = 2 ^ 1 - 1 := by decide
  rw [BitVec.toNat_and, h, Nat.and_two_pow_sub_one_eq_mod]

set_option maxHeartbeats 8000000 in
theorem mod_half_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "mod_half" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (x0 x1 x2 x3 m0 m1 m2 m3 : Word)
    (hx : s.locals "x" = some (.rStruct [.word x0, .word x1, .word x2, .word x3]))
    (hm : s.locals "m" = some (.rStruct [.word m0, .word m1, .word m2, .word m3]))
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] = (if limbsVal [x0, x1, x2, x3] % 2 = 0
        then limbsVal [x0, x1, x2, x3] / 2
        else (limbsVal [x0, x1, x2, x3] + limbsVal [m0, m1, m2, m3]) / 2) := by
  have hbody := (fun_of_index 158 hE.functions (by guest_decl_at 158) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp h
  rw [runs_ite] at h1
  have hpar : limbsVal [x0, x1, x2, x3] % 2 = x0.toNat % 2 := by
    simp only [limbsVal]
    omega
  simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_op hE.word, evalF_rField,
    evalF_local, eval_const, evalArgs_cons, evalArgs_nil, hx, Option.map_some,
    List.getElem?_cons_zero, wordsProj_nil, wordsProj_cons, wordOp, List.foldr] at h1
  have hand : AndOp.and x0 (AndOp.and (1#64) (~~~(0 : Word))) = x0 &&& 1#64 := by
    have : AndOp.and (1#64 : Word) (~~~0) = 1#64 := by decide
    rw [this]
    rfl
  rw [hand] at h1
  have hXb : limbsVal [x0, x1, x2, x3] < 2 ^ 256 := by
    have := x0.isLt; have := x1.isLt; have := x2.isLt; have := x3.isLt
    simp only [limbsVal]
    omega
  have hMb : limbsVal [m0, m1, m2, m3] < 2 ^ 256 := by
    have := m0.isLt; have := m1.isLt; have := m2.isLt; have := m3.isLt
    simp only [limbsVal]
    omega
  by_cases hp : x0 &&& 1#64 = 0#64
  · have hev : x0.toNat % 2 = 0 := by
      have := congrArg BitVec.toNat hp
      rw [and1_toNat] at this
      exact this
    have hc : evalPanCmp .equal (x0 &&& 1#64) 0#64 = 1#64 := by simp [evalPanCmp, hp]
    rw [hc, if_neg (by decide)] at h1
    rw [runs_return] at h1
    simp (config := { decide := true }) only [evalF_rStruct, evalF_rField, evalF_local,
      eval_const, evalF_op hE.word, evalF_shift hE.word, evalArgs_cons, evalArgs_nil, hx,
      Option.map_some, List.getElem?_cons_zero, List.getElem?_cons_succ, wordsProj_nil,
      wordsProj_cons, wordOp, List.foldr, RiscV.panRiscVShift, BitVec.toNat_ofNat, if_true,
      payload_words4] at h1
    subst h1
    simp only at hrest
    subst hrest
    refine Or.inr ⟨_, _, _, _, _, rfl, ?_⟩
    rw [if_pos (by rw [hpar]; exact hev)]
    have key := shrLimbs_val [x0.toNat, x1.toNat, x2.toNat, x3.toNat]
    simp only [shrLimbs, nval] at key
    simp only [limbsVal, show (1 % 2 ^ 64 : Nat) = 1 from by decide,
      show (63 % 2 ^ 64 : Nat) = 63 from by decide, shr_limb, shr_last]
    exact key
  · have hod : x0.toNat % 2 ≠ 0 := by
      intro h0
      apply hp
      apply BitVec.eq_of_toNat_eq
      rw [and1_toNat, h0]
      rfl
    have hc : evalPanCmp .equal (x0 &&& 1#64) 0#64 = 0#64 := by simp [evalPanCmp, hp]
    rw [hc, if_pos (show (0#64 : Word) = 0 from rfl)] at h1
    rw [runs_skip] at h1
    subst h1
    simp only at hrest
    rcases runs_decCall_inv hrest with herr | ⟨ps, cb, vals, cl, rb, hl, hvals, hbind, hcal, hout⟩
    · exact Or.inl (Stopped.of_error herr)
    have hparams := (fun_of_index 55 hE.functions (by guest_decl_at 55) (by decide +kernel) hl).2
    simp only [evalArgs_cons, evalArgs_nil, evalF_local, hx, hm, Option.map_some,
      Option.some.injEq] at hvals
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    obtain ⟨l1, e0, e1, e2, e3, e4, rfl, he⟩ := u256_add_carry_spec hE ps cb hl
      ⟨cl, s.globals, s.memory, s.ffi⟩ rb x0 x1 x2 x3 m0 m1 m2 m3
      (by rw [← hbind]; simp [updatePanValueMap]) (by rw [← hbind]; simp [updatePanValueMap]) hcal
    obtain ⟨r2, -, hrun2, rfl⟩ := hout
    rw [runs_return] at hrun2
    simp (config := { decide := true }) only [evalF_rStruct, evalF_rField, evalF_local,
      update_lookup, eval_const, evalF_op hE.word, evalF_shift hE.word, evalArgs_cons,
      evalArgs_nil, Option.map_some, List.getElem?_cons_zero, List.getElem?_cons_succ,
      wordsProj_nil, wordsProj_cons, wordOp, List.foldr, RiscV.panRiscVShift,
      BitVec.toNat_ofNat, if_true, payload_words4] at hrun2
    subst hrun2
    refine Or.inr ⟨_, _, _, _, _, rfl, ?_⟩
    rw [if_neg (by rw [hpar]; exact hod)]
    have key := shrLimbs_val [e0.toNat, e1.toNat, e2.toNat, e3.toNat, e4.toNat]
    simp only [shrLimbs, nval] at key
    simp only [limbsVal] at he hXb hMb
    simp only [limbsVal, show (1 % 2 ^ 64 : Nat) = 1 from by decide,
      show (63 % 2 ^ 64 : Nat) = 63 from by decide, shr_limb, shr_last]
    have := e0.isLt; have := e1.isLt; have := e2.isLt; have := e3.isLt
    omega

end InitECandidate.Solver.GuestBound
