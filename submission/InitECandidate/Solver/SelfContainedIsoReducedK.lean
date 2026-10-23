import InitECandidate.Solver.LoopWordStackExactClockIso
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


namespace InitECandidate.Solver.SelfContainedIsoReducedK

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

/-- Factor after the two isometric passes; entry offsets remain separate. -/
def isoFrontFactor : Nat := 1 * 3 * 1 * 1 * 2

def isoReducedPostK : Nat := 8 * isoFrontFactor * (refinedSourceClock + pipeOffset)

def isoReducedCandidateK : Nat := 23_077 + 8 * 6 * (459_564_194 + 5_000)

theorem iso_front_factor_eq : isoFrontFactor = 6 := by decide

/-- Instantiation of the affine composition theorem at C_pc=1, C_cl=3, C_sl=2.
The existential WordToStack offset is retained as d_ws, not assumed bounded. -/
theorem iso_front_clock_composition (d_pc d_cl d_sl d_ws k : Nat) :
    LoopWordStackExactClockIso.affine 2 d_sl
      (LoopWordStackExactClockIso.affine 1 d_ws
        (LoopWordStackExactClockIso.affine 1 0
          (LoopWordStackExactClockIso.affine 3 d_cl
            (LoopWordStackExactClockIso.affine 1 d_pc k)))) =
    LoopWordStackExactClockIso.affine isoFrontFactor
      (2 * (3 * d_pc + d_cl + d_ws) + d_sl) k := by
  exact LoopWordStackExactClockIso.front_factor_after_iso 1 d_pc 3 d_cl 2 d_sl d_ws k

theorem isoReducedCandidateK_eq : isoReducedCandidateK = 22_059_344_389 := by decide

theorem isoReducedPostK_eq : isoReducedPostK = 22_059_321_312 := by decide

theorem iso_budget_decomposition :
    isoReducedCandidateK = bootstrapSteps + isoReducedPostK := by
  rw [InitE.bootstrapSteps_eq]
  decide

theorem isoReducedCandidateK_lt_refined : isoReducedCandidateK < refinedCandidateK := by
  rw [isoReducedCandidateK_eq, refinedCandidateK_eq]
  decide

theorem isoReducedCandidateK_lt_ceiling : isoReducedCandidateK < 900_719_925_474 := by decide

theorem iso_saving_exact : refinedCandidateK - isoReducedCandidateK = 14_706_214_208 := by
  rw [refinedCandidateK_eq, isoReducedCandidateK_eq]

theorem iso_score_representable (minutes : Nat) :
    yukonScore isoReducedCandidateK minutes < 2 ^ 53 - 1 :=
  yukonScore_lt_two_pow_53_sub_one (by decide)

/-- Exact cost threshold for an arbitrary front factor at the reduced budget. -/
theorem iso_front_factor_threshold (factor : Nat) :
    bootstrapSteps + bMax * (factor * (refinedSourceClock + pipeOffset)) ≤
      isoReducedCandidateK ↔ factor ≤ 6 := by
  rw [InitE.bootstrapSteps_eq, refinedSourceClock_eq.1, isoReducedCandidateK_eq]
  change 23077 + 8 * (factor * (459564194 + 5000)) ≤ 22059344389 ↔ factor ≤ 6
  omega

/-- Budget one tick below the advertised cost rejects the saturated factor-six witness. -/
theorem iso_budget_one_tick_tight :
    ¬ bootstrapSteps + bMax * (6 * (refinedSourceClock + pipeOffset)) ≤
      isoReducedCandidateK - 1 := by
  rw [InitE.bootstrapSteps_eq]
  decide

theorem end_to_end_iso_reduced_finite_certificate
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
            isoReducedCandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK isoReducedCandidateK)
      (.finite isoReducedCandidateK) := by
  rw [iso_budget_decomposition] at target_not_timeOut_of_lab_halt ⊢
  exact finite_certificate_of_source_to_target_clock_chain
    oracles c depth isoReducedPostK hlab compiled depthBound
    k_pan k_word k_stack k_lab pan_not_timeOut word_not_timeOut
    stack_not_timeOut lab_not_timeOut target_not_timeOut_of_lab_halt


end InitECandidate.Solver.SelfContainedIsoReducedK
