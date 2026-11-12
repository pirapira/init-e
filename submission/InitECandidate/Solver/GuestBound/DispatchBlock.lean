import InitECandidate.Solver.GuestBound.DispatchOps
import InitECandidate.Solver.GuestBound.SepFrameExc
import InitECandidate.Solver.GuestBound.RunFramesLoop

/-!
# The dispatch block of the interpreter loop

`rfDispatch` is `op_dispatch(…)` with the handler `EvmErr err => frame_exception(err)`.
From the current frame's assertion (`FrameOp` and the cells `frame_exception`
touches) it traps, or ends normally with the assertion intact and either

* gas left strictly lower and the exception flag unchanged (the opcode returned), or
* gas left plus spilled not higher and the exception flag set (the opcode
  raised `EvmErr` and the handler ran).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The frame fields that only `frame_exception` touches. -/
structure ExSt where
  sgl : Word
  sp : Word
  msg : Word
  r0 : Word
  code : Word
  rd : Word
  rl : Word
  cc : Word
  fl : Word
  ee : Word

/-- The cells of `ExSt`. -/
def ExcExtra (e : Word) (Y : ExSt) : Assn :=
  .mem (e + 72#64) ↦ .word Y.sgl ⋆ .mem (e + 192#64) ↦ .word Y.sp ⋆
    .mem (e + 112#64) ↦ .word Y.msg ⋆ .mem (Y.msg + 48#64) ↦ .word Y.r0 ⋆
    .mem (e + 160#64) ↦ .word Y.code ⋆ .mem (e + 120#64) ↦ .word Y.rd ⋆
    .mem (e + 128#64) ↦ .word Y.rl ⋆ .glob "cur_cont" ↦ .word Y.cc ⋆
    .mem (Y.cc + 32#64) ↦ .word Y.fl ⋆ .glob "evm_empty" ↦ .word Y.ee

/-- The current frame, seen as what `frame_exception` owns and the rest. -/
theorem FrameX_exc (M : Word) (K : Word → Prop) (e fv : Word) (X : OpSt) (Y : ExSt) :
    (FrameOp M K e fv X ⋆ ExcExtra e Y) =
      (ExcW e X.gl Y.sgl Y.sp Y.msg Y.r0 X.used Y.code Y.rd Y.rl Y.cc Y.fl Y.ee ⋆
        (OpNoGas e X.sp X.cap X.base X.pv fv X.pc ⋆ JunkW M K X.pv X.base X.cap)) := by
  unfold FrameOp ExcW ExcExtra
  rw [OpW_gas]
  unfold GasCells
  ac_rfl

set_option maxHeartbeats 1000000 in
/-- One dispatch from the current frame's assertion. -/
theorem rfDispatch_step (hE : GuestEnv E) (hrest : ∀ f, f ∈ restOps → HandlerSpec E f)
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X : OpSt) (Y : ExSt)
    (hok : FrameOk M K fv X) (hno : X.gl.toNat + Y.sp.toNat < 2 ^ 64)
    (h : (FrameOp M K e fv X ⋆ ExcExtra e Y ⋆ R).holds s) :
    WPr E s rfDispatch (fun r => Trap r ∨ ∃ l g m X' Y', r = .normal l g m s.ffi ∧
      FrameOk M K fv X' ∧ (FrameOp M K e fv X' ⋆ ExcExtra e Y' ⋆ R).holds ⟨l, g, m, s.ffi⟩ ∧
      (∀ x, x ≠ "err" → l x = s.locals x) ∧
      ((X'.gl.toNat + Y'.sp.toNat < X.gl.toNat + Y.sp.toNat ∧ Y'.fl = Y.fl) ∨
        (X'.gl.toNat + Y'.sp.toNat ≤ X.gl.toNat + Y.sp.toNat ∧ Y'.fl = 1#64))) := by
  unfold rfDispatch
  refine WPr.callH (fun rb hrb => ?_)
  obtain ⟨parameters, body, values, cl, hlk, -, -, hrun⟩ := hrb
  have hd := op_dispatch_frame hE hrest parameters body hlk ⟨cl, s.globals, s.memory, s.ffi⟩
    M K e fv (ExcExtra e Y ⋆ R) X hok (Assn.holds_congr rfl rfl h) rb hrun
  cases rb with
  | returned l g m ffi vs =>
    rcases hd with he | hq
    · cases he
    rcases hq with (ht | ⟨_, _, _, _, _, _, _, _, _, hC⟩) | ⟨X1, n, hok1, hp1, hn, hh, _, _, _, hC⟩
    · exact ht.elim
    · cases hC
    injection hC with _ _ _ hf _
    subst hf
    intro l' g' hassign
    obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
    have : l' = s.locals := funext (fun x => hl x (by simp))
    subst this
    refine Or.inr ⟨_, _, _, X1, Y, rfl, hok1, Assn.holds_congr rfl rfl hh, fun _ _ => rfl,
      Or.inl ⟨?_, rfl⟩⟩
    have := hp1.1
    omega
  | raised l g m ffi e' v =>
    rcases hd with he | hq
    · cases he
    rcases hq with (ht | ⟨X1, n, hok1, hp1, hh, _, _, _, _, hC⟩) | ⟨_, _, _, _, _, _, _, _, _, hC⟩
    · have ht' : e' = "TrapErr" := ht
      subst ht'
      exact ⟨fun _ => Or.inl rfl, fun h0 => absurd h0 (by decide)⟩
    rotate_left
    · cases hC
    injection hC with _ _ _ hf hx hv
    subst hf hx hv
    refine ⟨fun h0 => absurd rfl h0, fun _ => ?_⟩
    have hE1 := Assn.holds_focus (FrameX_exc M K e fv X1 Y) (Assn.holds_assoc_l
      (P := FrameOp M K e fv X1) (Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "err" v,
        g, m, s.ffi⟩ : St σ)) rfl rfl hh))
    refine WPr.call_framed hE1 (Qc := fun r => Assn.ex fun err : Word =>
        ⌜v = .word err ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        ExcW e (if err = 1#64 then X1.gl + Y.sp else 0#64) Y.r0 0#64 Y.msg Y.r0
          (if err = 1#64 then X1.used else X1.used + (X1.gl + Y.sp)) err
          (if err = 1#64 then Y.rd else Y.ee) (if err = 1#64 then Y.rl else 0#64) Y.cc 1#64
          Y.ee) ?_ ?_ ?_ ?_
    · intro parameters2 cbody values2 cl2 hlk2 hvalues2 hbind2
      have hparams := (fun_of_index 579 hE.functions (by guest_decl_at 579) (by decide +kernel)
        hlk2).2
      have hvals : values2 = [v] := by
        simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
          update_lookup] at hvalues2
        exact hvalues2.symm
      subst hvals
      rw [hparams] at hbind2
      simp [bindPanValueParameters] at hbind2
      exact frame_exception_framed hE parameters2 cbody hlk2 ⟨cl2, g, m, s.ffi⟩ e X1.gl Y.sgl
        Y.sp Y.msg Y.r0 X1.used Y.code Y.rd Y.rl Y.cc Y.fl Y.ee v
        (by rw [← hbind2]; simp (config := { decide := true }) [updatePanValueMap])
    · intro l2 g2 m2 ffi2 vs2 hpost
      obtain ⟨err, hpost⟩ := Assn.holdsV_ex.mp hpost
      obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hpost
      injection hC with _ _ _ hf _
      subst hf
      have hle := hp1.1
      refine Or.inr ⟨_, _, _,
        { X1 with gl := if err = 1#64 then X1.gl + Y.sp else 0#64,
                  used := if err = 1#64 then X1.used else X1.used + (X1.gl + Y.sp) },
        { Y with sgl := Y.r0, sp := 0#64, code := err,
                 rd := if err = 1#64 then Y.rd else Y.ee,
                 rl := if err = 1#64 then Y.rl else 0#64, fl := 1#64 },
        rfl, ⟨hok1.ok, hok1.pb, hok1.bM, hok1.Kpv, hok1.Kst⟩, ?_, ?_, Or.inr ⟨?_, rfl⟩⟩
      · exact Assn.holds_assoc_r (Assn.holds_unfocus (FrameX_exc M K e fv
          { X1 with gl := if err = 1#64 then X1.gl + Y.sp else 0#64,
                    used := if err = 1#64 then X1.used else X1.used + (X1.gl + Y.sp) }
          { Y with sgl := Y.r0, sp := 0#64, code := err,
                   rd := if err = 1#64 then Y.rd else Y.ee,
                   rl := if err = 1#64 then Y.rl else 0#64, fl := 1#64 }) hk)
      · intro x hx
        simp [update_lookup, hx]
      · show (if err = 1#64 then X1.gl + Y.sp else 0#64).toNat + (0#64 : Word).toNat ≤
          X.gl.toNat + Y.sp.toNat
        split
        · have : (X1.gl + Y.sp).toNat = X1.gl.toNat + Y.sp.toNat := by bv_omega
          simp
          omega
        · simp
    · intro l2 g2 m2 ffi2 exc v2 hpost
      obtain ⟨err, hpost⟩ := Assn.holdsV_ex.mp hpost
      obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hpost
      cases hC
    · intro l2 g2 m2 ffi2 ev hpost
      obtain ⟨err, hpost⟩ := Assn.holdsV_ex.mp hpost
      obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hpost
      cases hC
  | finalFfi l g m ffi ev => exact Or.inl trivial
  | _ => trivial

end InitECandidate.Solver.GuestBound
