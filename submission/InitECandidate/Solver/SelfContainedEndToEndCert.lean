import InitECandidate.Solver.SelfContainedPipelineBridge
import InitECandidate.Solver.SelfContainedMasterK

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
Final Solver-local assembly. The stage non-timeout premises remain explicit:
this file does not claim their derivation from the Guest interpreter.
GuestMainLoopGasInvariant imports YukonPipelineBridge and hence forbidden
Proofs/Bounded* modules. Its amortized arithmetic interface is reproduced below
without that import. The coarse 219-ticks/gas invariant alone cannot establish
the refined 459,564,194 source clock; that refinement remains a semantic premise.
-/
namespace InitECandidate.Solver.SelfContainedEndToEndCert

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.YukonCleanVerifierCheck (baselineHeapLen baseline_pan_installed oracle_baseline_installation)
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanToTarget (semanticsDecls_mainFirstHOL)
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.LoopToWordStateRelImpSemanticsSupport


open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedPipelineBridge

theorem end_to_end_refined_finite_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (k_pan k_word k_stack k_lab : Guest.InputBlob → Nat)
    (pan_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
          decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
            { sourceInitialState input with structs := stCtxt }
            (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
            sourceDeclarations = some s_decls →
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            { s_decls with clock := k_pan input }
            (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut)
    (word_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (WordSemStateFiniteExact.evaluate
            (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
            { pipelinePanToWordInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
                InitECandidate.bitmaps p 0 with clock := k_word input }).1 ≠ some .timeOut)
    (stack_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (StackSemEvaluate.evaluate
            ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64),
              { pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0 with
                  clock := k_stack input })).1 ≠ some .timeOut)
    (lab_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).1 ≠ .timeOut)
    (target_not_timeOut_of_lab_halt : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).1 = .halt outcome →
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).2.ffi.ioEvents = events →
          (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
            refinedCandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK refinedCandidateK)
      (.finite refinedCandidateK) := by
  exact finite_certificate_of_source_to_target_clock_chain
    oracles c depth refinedPostK hlab compiled depthBound
    k_pan k_word k_stack k_lab pan_not_timeOut word_not_timeOut
    stack_not_timeOut lab_not_timeOut target_not_timeOut_of_lab_halt

/-- Baseline submission used by Solution.lean, with the unchanged infinity claim. -/
def submission : InitE.Submission := InitECandidate.Solver.FastEnv.baselineSubmission

/-- Changing the score field preserves every concrete matching execution. -/
theorem matchingExecutionAt_with_score (s : InitE.Submission) (K : InitE.NatE)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent) (steps : Nat) :
    matchingExecutionAt { s with K := K } input outcome events steps ↔
      matchingExecutionAt s input outcome events steps := by
  cases s
  rfl

/-- A finite certificate also certifies the original baseline at infinity. -/
theorem baseline_certificate_of_refined
    (finite : InitE.Certificate (baselineWithFiniteK refinedCandidateK) (.finite refinedCandidateK)) :
    InitE.Certificate submission .infinity := by
  refine ⟨rfl, InitECandidate.Solver.FastEnv.baselineSubmission_admitted, ?_⟩
  intro input gas outcome events source covered
  obtain ⟨steps, _, execution⟩ := finite.correct input gas outcome events source covered
  exact ⟨steps, trivial,
    (matchingExecutionAt_with_score InitECandidate.Solver.FastEnv.baselineSubmission (.finite refinedCandidateK)
      input outcome events steps).mp execution⟩

/-- Exact assembly of the finite claim and its Solution-compatible baseline claim. -/
theorem finite_and_baseline_compatible
    (finite : InitE.Certificate (baselineWithFiniteK refinedCandidateK) (.finite refinedCandidateK)) :
    InitE.Certificate (baselineWithFiniteK refinedCandidateK) (.finite refinedCandidateK) ∧
      InitE.Certificate submission .infinity :=
  ⟨finite, baseline_certificate_of_refined finite⟩

theorem refined_bound_exact : refinedCandidateK = 36765558597 := refinedCandidateK_eq

theorem refined_bound_below_ceiling : refinedCandidateK < 900719925474 :=
  refinedCandidateK_lt_ceiling

theorem refined_score_exactly_representable (minutes : Nat) :
    yukonScore refinedCandidateK minutes < 2 ^ 53 - 1 := yukonScore_refined_lt minutes

theorem refined_source_exact : refinedSourceClock = 459564194 := refinedSourceClock_eq.1

theorem refined_post_exact : refinedPostK = 36765535520 := by decide

theorem refined_front_threshold (factor : Nat) :
    bootstrapSteps + bMax * (factor * (refinedSourceClock + pipeOffset)) < 400000000000 ↔
      factor ≤ 108 := front_factor_threshold factor

/-- Exact local arithmetic interface of GuestMainLoopGasInvariant.loop_and_epi_le. -/
theorem guest_amortized_sum (ticks keys gas : List Nat) (epiPerKey : Nat)
    (h : ticks.sum + epiPerKey * keys.sum ≤ 219 * gas.sum) (pro epi : Nat) :
    pro + ticks.sum + (epi + epiPerKey * keys.sum) ≤ pro + epi + 219 * gas.sum := by
  omega

/-- The coarse Guest invariant yields 43,934,217,712, not the refined source bound. -/
theorem guest_coarse_budget_exact :
    Guest.maxInputBytes + 219 * gasCap = 44873741808 ∧
      refinedSourceClock < Guest.maxInputBytes + 219 * gasCap := by decide

/-- Concrete nonempty saturated witness for the amortized Guest arithmetic. -/
theorem guest_amortized_saturated_witness :
    (43800000000 : Nat) + 0 * 0 ≤ 219 * gasCap ∧
      Guest.maxInputBytes + 43800000000 = 44873741808 := by decide

/-- A further tick exceeds the saturated coarse budget. -/
theorem guest_coarse_one_tick_tight :
    ¬ Guest.maxInputBytes + 219 * gasCap + 1 ≤ 44873741808 := by decide


end InitECandidate.Solver.SelfContainedEndToEndCert
