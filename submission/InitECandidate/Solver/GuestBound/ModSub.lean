import InitECandidate.Solver.GuestBound.FqSub

/-!
# `mod_sub`: subtraction modulo `m` on operands below `m`
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

set_option maxHeartbeats 8000000 in
theorem mod_sub_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "mod_sub" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 b0 b1 b2 b3 m0 m1 m2 m3 : Word)
    (ha : s.locals "x" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hb : s.locals "y" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hm : s.locals "m" = some (.rStruct [.word m0, .word m1, .word m2, .word m3]))
    (hA : limbsVal [a0, a1, a2, a3] < limbsVal [m0, m1, m2, m3])
    (hB : limbsVal [b0, b1, b2, b3] < limbsVal [m0, m1, m2, m3])
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] = (if limbsVal [a0, a1, a2, a3] < limbsVal [b0, b1, b2, b3]
        then limbsVal [a0, a1, a2, a3] + limbsVal [m0, m1, m2, m3] - limbsVal [b0, b1, b2, b3]
        else limbsVal [a0, a1, a2, a3] - limbsVal [b0, b1, b2, b3]) := by
  have hbody := (fun_of_index 159 hE.functions (by guest_decl_at 159) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  -- lt = u256_lt(a, b)
  rcases runs_decCall_inv h with herr | ⟨ps, cb, vals, cl, rb, hl, hvals, hbind, hcal, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 46 hE.functions (by guest_decl_at 46) (by decide +kernel) hl).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ha, hb, Option.map_some,
    Option.some.injEq] at hvals
  subst hvals
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hlt := u256_lt_spec hE ps cb hl ⟨cl, s.globals, s.memory, s.ffi⟩ rb a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp [updatePanValueMap]) (by rw [← hbind]; simp [updatePanValueMap]) hcal
  subst hlt
  obtain ⟨r1, -, hrun1, rfl⟩ := hout
  -- d = u256_sub(a, b)
  rcases runs_decCall_inv hrun1 with herr | ⟨ps2, cb2, vals2, cl2, rb2, hl2, hvals2, hbind2, hcal2,
    hout2⟩
  · exact Or.inl (Stopped.restore (Stopped.of_error herr))
  have hparams2 := (fun_of_index 57 hE.functions (by guest_decl_at 57) (by decide +kernel) hl2).2
  simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local,
    update_lookup, ha, hb, Option.map_some, Option.some.injEq, if_false] at hvals2
  subst hvals2
  rw [hparams2] at hbind2
  simp [bindPanValueParameters] at hbind2
  obtain ⟨l2, d0, d1, d2, d3, rfl, hd⟩ := u256_sub_mod hE ps2 cb2 hl2
    ⟨cl2, s.globals, s.memory, s.ffi⟩ rb2 a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind2]; simp [updatePanValueMap]) (by rw [← hbind2]; simp [updatePanValueMap]) hcal2
  obtain ⟨r2, -, hrun2, rfl⟩ := hout2
  obtain ⟨r3, h3, hrest⟩ := runs_seq.mp hrun2
  have herror : r3.isError = true → Stopped (restorePanValueFfiLocal "lt" (s.locals "lt")
      (restorePanValueFfiLocal "d" ((updatePanValueMap s.locals "lt" (.word
        (if limbsVal [a0, a1, a2, a3] < limbsVal [b0, b1, b2, b3] then 1 else 0))) "d") r2)) := by
    intro herr
    have hr2 : r2.isError = true := by
      cases r3 with
      | error l g m f =>
        simp only at hrest
        subst hrest
        rfl
      | _ => cases herr
    exact Stopped.restore (Stopped.restore (Stopped.of_error hr2))
  have hMb : limbsVal [m0, m1, m2, m3] < 2 ^ 256 := by
    have := m0.isLt; have := m1.isLt; have := m2.isLt; have := m3.isLt
    simp only [limbsVal]
    omega
  rw [runs_ite] at h3
  by_cases hc : limbsVal [a0, a1, a2, a3] < limbsVal [b0, b1, b2, b3]
  · simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      eval_const, hc, if_true, if_false, evalPanCmp] at h3
    rcases runs_call_inv (some (some (.local, "d"))) h3 with herr | ⟨ps3, cb3, vals3, cl3, rb3,
      hl3, hvals3, hbind3, hcal3, hout3⟩
    · exact Or.inl (herror herr)
    have hparams3 := (fun_of_index 56 hE.functions (by guest_decl_at 56) (by decide +kernel)
      hl3).2
    simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, hm, Option.map_some, Option.some.injEq, if_true,
      if_false] at hvals3
    subst hvals3
    rw [hparams3] at hbind3
    simp [bindPanValueParameters] at hbind3
    obtain ⟨l3, e0, e1, e2, e3, rfl, he⟩ := u256_add_mod hE ps3 cb3 hl3
      ⟨cl3, s.globals, s.memory, s.ffi⟩ rb3 d0 d1 d2 d3 m0 m1 m2 m3
      (by rw [← hbind3]; simp [updatePanValueMap]) (by rw [← hbind3]; simp [updatePanValueMap])
      hcal3
    simp only [CallOutcome] at hout3
    rcases hout3 with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl (herror herr)
    simp only [assignPanValueCallResult] at hassign
    split at hassign
    · simp only [Option.some.injEq, Prod.mk.injEq] at hassign
      obtain ⟨rfl, rfl⟩ := hassign
      simp only at hrest
      rw [runs_return] at hrest
      simp (config := { decide := true }) only [evalF_local, update_lookup, payload_words4,
        if_true] at hrest
      subst hrest
      refine Or.inr ⟨_, e0, e1, e2, e3, rfl, ?_⟩
      rw [he, hd, if_pos hc]
      omega
    · cases hassign
  · simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      eval_const, hc, if_true, if_false, evalPanCmp] at h3
    rw [runs_skip] at h3
    subst h3
    simp only at hrest
    rw [runs_return] at hrest
    simp (config := { decide := true }) only [evalF_local, update_lookup, payload_words4,
      if_true] at hrest
    subst hrest
    refine Or.inr ⟨_, d0, d1, d2, d3, rfl, ?_⟩
    rw [hd, if_neg hc]
    omega

end InitECandidate.Solver.GuestBound
