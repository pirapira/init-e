import InitECandidate.Solver.GuestBound.FqSub

/-!
# The bn254 base field: addition

`fq_add` on canonical operands returns the canonical sum modulo `p`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

set_option maxHeartbeats 8000000 in
theorem fq_add_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq_add" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha : s.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hb : s.locals "b" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) (hB : limbsVal [b0, b1, b2, b3] < bnP)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] = (limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3]) % bnP := by
  have hbody := (fun_of_index 649 hE.functions (by guest_decl_at 649) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  -- r = u256_add(a, b)
  rcases runs_decCall_inv h with herr | ⟨ps, cb, vals, cl, rb, hl, hvals, hbind, hcal, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 56 hE.functions (by guest_decl_at 56) (by decide +kernel) hl).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ha, hb, Option.map_some,
    Option.some.injEq] at hvals
  subst hvals
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  obtain ⟨l1, c0, c1, c2, c3, rfl, hc⟩ := u256_add_mod hE ps cb hl
    ⟨cl, s.globals, s.memory, s.ffi⟩ rb a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp [updatePanValueMap]) (by rw [← hbind]; simp [updatePanValueMap]) hcal
  obtain ⟨r1, -, hrun1, rfl⟩ := hout
  -- lt = u256_lt(r, p)
  rcases runs_decCall_inv hrun1 with herr | ⟨ps2, cb2, vals2, cl2, rb2, hl2, hvals2, hbind2, hcal2,
    hout2⟩
  · exact Or.inl (Stopped.restore (Stopped.of_error herr))
  have hparams2 := (fun_of_index 46 hE.functions (by guest_decl_at 46) (by decide +kernel) hl2).2
  simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local,
    update_lookup, evalF_rStruct, eval_const, Option.map_some, Option.some.injEq, if_true,
    if_false] at hvals2
  subst hvals2
  rw [hparams2] at hbind2
  simp [bindPanValueParameters] at hbind2
  have hlt := u256_lt_spec hE ps2 cb2 hl2 ⟨cl2, s.globals, s.memory, s.ffi⟩ rb2 c0 c1 c2 c3
    4332616871279656263#64 10917124144477883021#64 13281191951274694749#64
    3486998266802970665#64
    (by rw [← hbind2]; simp [updatePanValueMap]) (by rw [← hbind2]; simp [updatePanValueMap]) hcal2
  subst hlt
  obtain ⟨r2, -, hrun2, rfl⟩ := hout2
  obtain ⟨r3, h3, hrest⟩ := runs_seq.mp hrun2
  rw [bnP_limbs] at h3
  simp only [bnP] at hA hB h3 ⊢
  rw [runs_ite] at h3
  by_cases hlt : limbsVal [c0, c1, c2, c3] <
      21888242871839275222246405745257275088696311157297823662689037894645226208583
  · simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      eval_const, hlt, if_true, if_false, evalPanCmp] at h3
    rw [runs_skip] at h3
    subst h3
    simp only at hrest
    rw [runs_return] at hrest
    simp (config := { decide := true }) only [evalF_local, update_lookup, payload_words4,
      if_true] at hrest
    subst hrest
    refine Or.inr ⟨_, c0, c1, c2, c3, rfl, ?_⟩
    rw [hc] at hlt ⊢
    omega
  · simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      eval_const, hlt, if_true, if_false, evalPanCmp] at h3
    rcases runs_call_inv none h3 with herr | ⟨ps3, cb3, vals3, cl3, rb3, hl3, hvals3, hbind3,
      hcal3, hout3⟩
    · have hr2 : r2.isError = true := by
        cases r3 with
        | error l g m f =>
          simp only at hrest
          subst hrest
          rfl
        | _ => cases herr
      exact Or.inl (Stopped.restore (Stopped.restore (Stopped.of_error hr2)))
    have hparams3 := (fun_of_index 57 hE.functions (by guest_decl_at 57) (by decide +kernel)
      hl3).2
    simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, evalF_rStruct, eval_const, Option.map_some, Option.some.injEq, if_true,
      if_false] at hvals3
    subst hvals3
    rw [hparams3] at hbind3
    simp [bindPanValueParameters] at hbind3
    obtain ⟨l3, e0, e1, e2, e3, rfl, he⟩ := u256_sub_mod hE ps3 cb3 hl3
      ⟨cl3, s.globals, s.memory, s.ffi⟩ rb3 c0 c1 c2 c3 4332616871279656263#64
      10917124144477883021#64 13281191951274694749#64 3486998266802970665#64
      (by rw [← hbind3]; simp [updatePanValueMap]) (by rw [← hbind3]; simp [updatePanValueMap])
      hcal3
    simp only [CallOutcome] at hout3
    rcases hout3 with herr | ⟨l', rfl⟩
    · have hr2 : r2.isError = true := by
        cases r3 with
        | error l g m f =>
          simp only at hrest
          subst hrest
          rfl
        | _ => cases herr
      exact Or.inl (Stopped.restore (Stopped.restore (Stopped.of_error hr2)))
    simp only at hrest
    subst hrest
    refine Or.inr ⟨_, e0, e1, e2, e3, rfl, ?_⟩
    rw [he, bnP_limbs, hc]
    rw [hc] at hlt
    simp only [bnP]
    omega

end InitECandidate.Solver.GuestBound
