import InitECandidate.Solver.GuestBound.SepMemOp

/-!
# Memory handlers under the frame invariant with the memory buffer

`op_mload`: pop the offset, pay for and perform the memory growth, read 32
bytes, push, advance the program counter.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

set_option maxHeartbeats 2000000 in
theorem op_mload_frameM (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_mload" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt) (Y0 : MemSt)
    (hok : FrameOk M K fv X0) (hY : MBufOk Y0 fv) (hgl : X0.gl.toNat < 2 ^ 64 - 1)
    (h : (FrameOp M K e fv X0 ⋆ MemExtra e Y0 ⋆ R).holds s) :
    WPr E s body (HandlerQM M K e R s.ffi X0) := by
  have hbody := (fun_of_index 510 hE.functions (by guest_decl_at 510) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine op_pop_sh hE hok hp h (AcceptsM.refl.toH hY).abort
    (fun v g m hsh_start hok hp h => ?_)
  obtain ⟨a0, a1, a2, a3, rfl⟩ := struct4_of_shape hsh_start
  refine op_charge_mem hE (base := 3#64) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := 32#64) (b1 := 0#64) (b2 := 0#64) (b3 := 0#64)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_const, eval_local,
      evalF_rStruct, update_lookup]) hok hY hp hgl h AcceptsM.refl.restore
    (fun fv' x total cap' g m hok hY hp _ h => ?_)
  refine op_quiet (keepFn_sound (quietKeeper E) hE.functions 6 "sat_word"
      (show keepFn quietLeaf Guest.Software.guestAst 6 "sat_word" = true by decide +kernel))
    (raiseFn_sound _ hE.functions 6 "sat_word"
      (show raiseFn (fun _ => false) Guest.Software.guestAst 6 "sat_word" = true by
        decide +kernel))
    h (AcceptsM.refl.restore.toH hY).abort (fun _ hsh_s h => ?_)
  refine op_quiet (keepFn_sound (quietKeeper E) hE.functions 6 "u256_from_be"
      (show keepFn quietLeaf Guest.Software.guestAst 6 "u256_from_be" = true by decide +kernel))
    (raiseFn_sound _ hE.functions 6 "u256_from_be"
      (show raiseFn (fun _ => false) Guest.Software.guestAst 6 "u256_from_be" = true by
        decide +kernel))
    h (AcceptsM.refl.restore.restore.toH hY).abort (fun _ hsh_v h => ?_)
  refine op_push hok hp h (AcceptsM.refl.restore.restore.restore.toH hY).abort
    (stack_push_any_hc hE (arg4_shape (by simp (config := { decide := true }) [update_lookup])
      hsh_v) e _ _ _ _ _ hok.ok)
    (fun _ g m hok hp h => ?_)
  refine op_pc_add hE (d := 1#64)
    (by simp [evalArgs_cons, evalArgs_nil, eval_const]) hok hp h
    (AcceptsM.refl.restore.restore.restore.toH hY).abort (fun g m hok hp h => ?_)
  exact op_return hok hp (by decide) h (AcceptsM.refl.restore.restore.restore.toH hY)

end InitECandidate.Solver.GuestBound
