import InitECandidate.Solver.GuestBound.DispatchM
import InitECandidate.Solver.GuestBound.RfInstance

/-!
# The loop interface at the memory level

`rfDispatch_stepM`, `rfInvM`, `rfSpecM`, `run_frames_bound_frameM`: as in
`DispatchBlock.lean` / `RfInstance.lean`, with the frame's memory buffer in the
invariant, so that handlers proved at the memory level count.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

set_option maxHeartbeats 2000000 in
/-- One dispatch from the current frame's assertion with its memory buffer. -/
theorem rfDispatch_stepM (hE : GuestEnv E) (hrest : ∀ f, f ∈ restOpsM → HandlerSpecM E f)
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X : OpSt) (Y : MemSt)
    (Z : ExSt) (hok : FrameOk M K fv X) (hY : MBufOk Y fv)
    (hno : X.gl.toNat + Z.sp.toNat < 2 ^ 64 - 1)
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtra e Z ⋆ R).holds s) :
    WPr E s rfDispatch (fun r => Trap r ∨ ∃ l g m fv' X' Y' Z', r = .normal l g m s.ffi ∧
      FrameOk M K fv' X' ∧ MBufOk Y' fv' ∧
      (FrameOp M K e fv' X' ⋆ MemExtra e Y' ⋆ ExcExtra e Z' ⋆ R).holds ⟨l, g, m, s.ffi⟩ ∧
      (∀ x, x ≠ "err" → l x = s.locals x) ∧
      ((X'.gl.toNat + Z'.sp.toNat < X.gl.toNat + Z.sp.toNat ∧ Z'.fl = Z.fl) ∨
        (X'.gl.toNat + Z'.sp.toNat ≤ X.gl.toNat + Z.sp.toNat ∧ Z'.fl = 1#64))) := by
  unfold rfDispatch
  refine WPr.callH (fun rb hrb => ?_)
  obtain ⟨parameters, body, values, cl, hlk, -, -, hrun⟩ := hrb
  have hd := op_dispatch_frameM hE hrest parameters body hlk ⟨cl, s.globals, s.memory, s.ffi⟩
    M K e fv (ExcExtra e Z ⋆ R) X Y hok hY (by omega) (Assn.holds_congr rfl rfl h) rb hrun
  cases rb with
  | returned l g m ffi vs =>
    rcases hd with he | hq
    · cases he
    rcases hq with (ht | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩) |
      ⟨fv1, X1, Y1, n, hok1, hY1, hp1, hn, hh, _, _, _, hC⟩
    · exact ht.elim
    · cases hC
    injection hC with _ _ _ hf _
    subst hf
    intro l' g' hassign
    obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
    have : l' = s.locals := funext (fun x => hl x (by simp))
    subst this
    refine Or.inr ⟨_, _, _, fv1, X1, Y1, Z, rfl, hok1, hY1, Assn.holds_congr rfl rfl hh,
      fun _ _ => rfl, Or.inl ⟨?_, rfl⟩⟩
    have := hp1.1
    omega
  | raised l g m ffi e' v =>
    rcases hd with he | hq
    · cases he
    rcases hq with (ht | ⟨fv1, X1, Y1, n, hok1, hY1, hp1, hh, _, _, _, _, hC⟩) |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩
    · have ht' : e' = "TrapErr" := ht
      subst ht'
      exact ⟨fun _ => Or.inl rfl, fun h0 => absurd h0 (by decide)⟩
    rotate_left
    · cases hC
    injection hC with _ _ _ hf hx hv
    subst hf hx hv
    refine ⟨fun h0 => absurd rfl h0, fun _ => ?_⟩
    have hE0 : ((FrameOp M K e fv1 X1 ⋆ ExcExtra e Z) ⋆ MemExtra e Y1 ⋆ R).holds
        (⟨updatePanValueMap s.locals "err" v, g, m, s.ffi⟩ : St σ) :=
      Assn.holds_perm (Assn.holds_congr rfl rfl hh) (by ac_rfl)
    have hE1 := Assn.holds_focus (FrameX_exc M K e fv1 X1 Z) hE0
    refine WPr.call_framed hE1 (Qc := fun r => Assn.ex fun err : Word =>
        ⌜v = .word err ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        ExcW e (if err = 1#64 then X1.gl + Z.sp else 0#64) Z.r0 0#64 Z.msg Z.r0
          (if err = 1#64 then X1.used else X1.used + (X1.gl + Z.sp)) err
          (if err = 1#64 then Z.rd else Z.ee) (if err = 1#64 then Z.rl else 0#64) Z.cc 1#64
          Z.ee) ?_ ?_ ?_ ?_
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
      exact frame_exception_framed hE parameters2 cbody hlk2 ⟨cl2, g, m, s.ffi⟩ e X1.gl Z.sgl
        Z.sp Z.msg Z.r0 X1.used Z.code Z.rd Z.rl Z.cc Z.fl Z.ee v
        (by rw [← hbind2]; simp (config := { decide := true }) [updatePanValueMap])
    · intro l2 g2 m2 ffi2 vs2 hpost
      obtain ⟨err, hpost⟩ := Assn.holdsV_ex.mp hpost
      obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hpost
      injection hC with _ _ _ hf _
      subst hf
      have hle := hp1.1
      refine Or.inr ⟨_, _, _, fv1,
        { X1 with gl := if err = 1#64 then X1.gl + Z.sp else 0#64,
                  used := if err = 1#64 then X1.used else X1.used + (X1.gl + Z.sp) }, Y1,
        { Z with sgl := Z.r0, sp := 0#64, code := err,
                 rd := if err = 1#64 then Z.rd else Z.ee,
                 rl := if err = 1#64 then Z.rl else 0#64, fl := 1#64 },
        rfl, ⟨hok1.ok, hok1.pb, hok1.bM, hok1.Kpv, hok1.Kst⟩, hY1, ?_, ?_, Or.inr ⟨?_, rfl⟩⟩
      · have hb := Assn.holds_unfocus (FrameX_exc M K e fv1
          { X1 with gl := if err = 1#64 then X1.gl + Z.sp else 0#64,
                    used := if err = 1#64 then X1.used else X1.used + (X1.gl + Z.sp) }
          { Z with sgl := Z.r0, sp := 0#64, code := err,
                   rd := if err = 1#64 then Z.rd else Z.ee,
                   rl := if err = 1#64 then Z.rl else 0#64, fl := 1#64 }) hk
        exact Assn.holds_perm hb (by ac_rfl)
      · intro x hx
        simp [update_lookup, hx]
      · show (if err = 1#64 then X1.gl + Z.sp else 0#64).toNat + (0#64 : Word).toNat ≤
          X.gl.toNat + Z.sp.toNat
        split
        · have : (X1.gl + Z.sp).toNat = X1.gl.toNat + Z.sp.toNat := by bv_omega
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

/-- The invariant of the current frame, with its memory buffer. -/
def rfInvM (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) : Prop :=
  ∃ (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X : OpSt) (Y : MemSt) (Z : ExSt),
    FrameOk M K fv X ∧ MBufOk Y fv ∧ X.gl.toNat + Z.sp.toNat < 2 ^ 64 - 1 ∧
      (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtra e Z ⋆ R).holds (⟨fun _ => none, g, m, f⟩ : St σ)

theorem holdsM_to {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt} {Y : MemSt}
    {Z : ExSt} {s : St σ} (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtra e Z ⋆ R).holds s) :
    (FrameOp M K e fv X ⋆ ExcExtra e Z ⋆ MemExtra e Y ⋆ R).holds s :=
  Assn.holds_perm h (by ac_rfl)

/-- The loop interface for the current frame with its memory buffer. -/
def rfSpecM (hE : GuestEnv E) (hrest : ∀ f, f ∈ restOpsM → HandlerSpecM E f) (BD BF : Nat)
    (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (finish : ∀ a : St σ, rfInvM a.globals a.memory a.ffi →
      WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
        (l "go" = some (.word 0#64) ∨
          (l "go" = a.locals "go" ∧ rfInvM g m f ∧ rfMu g m < rfMu a.globals a.memory)))) :
    RfSpec E where
  Inv := rfInvM
  μ := rfMu
  DispatchPre := fun a => ∃ l, E.eval ⟨l, a.globals, a.memory, a.ffi⟩ rfC1 = some (.word 0#64)
  BD := BD
  BF := BF
  costD := costD
  costF := costF
  pre := fun a _ h1 _ _ _ => ⟨_, h1⟩
  finish := finish
  dispatch := by
    rintro a ⟨M, K, e, fv, R, X, Y, Z, hok, hY, hno, hh⟩ ⟨l0, hpre⟩
    have hha := Assn.holds_congr (s' := a) rfl rfl hh
    have hfl : Z.fl = 0#64 := rfC1_flag hE (holdsM_to
      (Assn.holds_congr (s' := (⟨l0, a.globals, a.memory, a.ffi⟩ : St σ)) rfl rfl hh)) hpre
    refine WPr.wps (rfDispatch_stepM hE hrest a M K e fv R X Y Z hok hY hno hha) (fun r hr => ?_)
    rcases hr with ht | ⟨l, g, m, fv', X', Y', Z', rfl, hok', hY', hh', hl, hcase⟩
    · exact Or.inl ht.stopped
    · refine Or.inr ⟨l, g, m, a.ffi, rfl, ⟨M, K, e, fv', R, X', Y', Z', hok', hY', ?_,
        Assn.holds_congr rfl rfl hh'⟩, ?_, hl "go" (by decide), hl "done" (by decide)⟩
      · rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
      · have e1 := rfMu_eq (holdsM_to hh')
        have e2 := rfMu_eq (holdsM_to hha)
        dsimp only at e1
        rw [e1, e2]
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h2]
          omega
        · rw [h2, hfl]
          simp
          omega

/-- `run_frames` from a state satisfying the current-frame invariant with its
memory buffer. -/
theorem run_frames_bound_frameM (hE : GuestEnv E)
    (hrest : ∀ f, f ∈ restOpsM → HandlerSpecM E f) (BD BF : Nat)
    (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (finish : ∀ a : St σ, rfInvM a.globals a.memory a.ffi →
      WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
        (l "go" = some (.word 0#64) ∨
          (l "go" = a.locals "go" ∧ rfInvM g m f ∧ rfMu g m < rfMu a.globals a.memory))))
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "run_frames" E.functions = some (parameters, body))
    (s : St σ) (hI : rfInvM s.globals s.memory s.ffi) (fuel : Nat) (r : Result σ) (n : Nat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ (rfMu s.globals s.memory + 1 + 1) * (expCost rfCond + (BD + BF + 200) + 1) + 10 :=
  run_frames_bound hE (rfSpecM hE hrest BD BF costD costF finish) parameters body hlookup s hI
    fuel r n hrun hne

end InitECandidate.Solver.GuestBound
