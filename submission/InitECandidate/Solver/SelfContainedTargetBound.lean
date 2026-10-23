import InitECandidate.Solver.YukonBaselineCompat
import InitECandidate.Solver.YukonCleanVerifierCheck
import InitECandidate.Solver.FastBaselineEnv
import InitECandidate.Proofs.BootstrapProgram
import InitECandidate.Proofs.OracleBaselineCorrectness
import Flapjack.Compiler.Backend.LabToTarget.EvaluateIgnoreClocks

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace



set_option autoImplicit false

/-!
# `InitECandidate.Solver.SelfContainedTargetBound`

Clocked non-`timeOut` halt agreement, re-proved inside `Solver/` without importing
`Proofs/BoundedTarget`, `Proofs/BootstrapSteps`, `Proofs/OracleBaselineCertificate`
(nor `Proofs/BoundedStackToLab` / `Proofs/BoundedPanToWord`, which import them).
Every `Proofs/` module imported here exists in upstream baseline `a267157e2`.

The source-to-target clocked halt witness (`∃ k, evaluateTargetHOL … k ms = .halt …`)
is an explicit hypothesis: upstream it is produced by the compiler-correctness chain
(`oracle_*_clocked_halt` in `Proofs/BoundedPanToWord`). The lemmas below are the
clock-agreement step: witness + `¬ timeOut` at any budget `K` ⇒ exact halt + I/O at `K`.
-/

namespace InitECandidate.Solver.SelfContainedTargetBound

open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend

/-- Local copy of `InitE.evaluateTarget_halt_of_not_timeOut_and_halt`. -/
theorem evaluateTarget_halt_of_not_timeOut_and_halt {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (k0 K : Nat) (outcome : HolOutcome) (ms0 : S) (ffi0 : HolFfiState σ)
    (hhalt0 : evaluateTargetHOL mc ffi k0 ms = (.halt outcome, ms0, ffi0))
    (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    ∃ ms1, evaluateTargetHOL mc ffi K ms = (.halt outcome, ms1, ffi0) := by
  rcases hrun1 : evaluateTargetHOL mc ffi K ms with ⟨r1, ms1, ffi1⟩
  rw [hrun1] at hnt
  have heq := evaluateTargetIgnoreClocks mc ffi K k0 ms r1 (.halt outcome) ms1 ms0
    ffi1 ffi0 ⟨hrun1, hnt, hhalt0, by simp⟩
  have hr1 : r1 = .halt outcome := congrArg Prod.fst heq
  have hffi1 : ffi1 = ffi0 := congrArg (fun p => p.2.2) heq
  subst hr1 hffi1
  exact ⟨ms1, rfl⟩

/-- Generic backend form: a clocked halt witness with source I/O `events`, plus
non-timeout at `K`, gives halt with the same outcome and I/O at `K`. -/
theorem pan_to_target_backend_halt_agree_of_not_timeOut {width : Nat} [NeZero width]
    {S Q σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hclocked : ∃ k_target ms2 ffi2,
      evaluateTargetHOL mc ffi k_target ms = (.halt outcome, ms2, ffi2) ∧ ffi2.ioEvents = events)
    (K : Nat) (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi K ms).1 = .halt outcome ∧
      (evaluateTargetHOL mc ffi K ms).2.2.ioEvents = events := by
  obtain ⟨k_target, ms2, ffi2, htarget, hio⟩ := hclocked
  obtain ⟨ms1, hK⟩ :=
    evaluateTarget_halt_of_not_timeOut_and_halt mc ffi ms k_target K outcome ms2 ffi2 htarget hnt
  rw [hK]; exact ⟨rfl, hio⟩

/-- Post-bootstrap endpoint form on the baseline machine. -/
theorem oracle_baseline_endpoint_halt_agree_of_not_timeOut (input : Guest.InputBlob)
    (ms : RiscV.L3.riscv_state) (outcome : HolOutcome) (events : List HolIoEvent)
    (hclocked : ∃ k_target ms2 ffi2,
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) k_target ms =
        (.halt outcome, ms2, ffi2) ∧ ffi2.ioEvents = events)
    (K : Nat)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K ms).1 ≠ .timeOut) :
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K ms).1 = .halt outcome ∧
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K ms).2.2.ioEvents = events :=
  pan_to_target_backend_halt_agree_of_not_timeOut _ _ _ outcome events hclocked K hnt

/-- Full baseline form, including the bootstrap prefix (`bootstrapSteps + ·`). -/
theorem oracle_full_baseline_halt_agree_of_not_timeOut (input : Guest.InputBlob)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hclocked : ∃ k_target ms2 ffi2,
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) (bootstrapSteps + k_target)
        (baselineInitialState input) = (.halt outcome, ms2, ffi2) ∧ ffi2.ioEvents = events)
    (K_post : Nat)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input) (bootstrapSteps + K_post)
      (baselineInitialState input)).1 ≠ .timeOut) :
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input) (bootstrapSteps + K_post)
      (baselineInitialState input)).1 = .halt outcome ∧
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input) (bootstrapSteps + K_post)
      (baselineInitialState input)).2.2.ioEvents = events := by
  obtain ⟨k, ms2, ffi2, h, hio⟩ := hclocked
  exact pan_to_target_backend_halt_agree_of_not_timeOut _ _ _ outcome events
    ⟨bootstrapSteps + k, ms2, ffi2, h, hio⟩ _ hnt

end InitECandidate.Solver.SelfContainedTargetBound
