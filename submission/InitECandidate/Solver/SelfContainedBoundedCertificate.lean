import InitECandidate.Solver.SelfContainedCertificateModel
import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Solver.YukonBaselineCompat
import InitECandidate.Solver.YukonCleanVerifierCheck
import InitECandidate.Proofs.CompilerOracles

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.SelfContainedBoundedCertificate

open Classical
open InitE
open YukonCleanVerifierCheck (baselineHeapLen baselineAdj2 baselineAdj4)
open InitECandidate.Proofs
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanToTarget (semanticsDecls_mainFirstHOL)
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock

/-- A terminating machine behaviour fixes every non-timeout evaluator result. -/
private theorem halt_agree_of_terminates {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (outcome : HolOutcome) (events : List HolIoEvent) (K : Nat)
    (terminates : machineSemHOL mc ffi ms (.terminate outcome events))
    (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi K ms).1 = .halt outcome ∧
      (evaluateTargetHOL mc ffi K ms).2.2.ioEvents = events := by
  obtain ⟨k0, ms0, ffi0, run0, io0⟩ := terminates
  rcases run : evaluateTargetHOL mc ffi K ms with ⟨res, post, finalFfi⟩
  rw [run] at hnt
  have equal := evaluateTargetIgnoreClocks mc ffi K k0 ms res (.halt outcome)
    post ms0 finalFfi ffi0 ⟨run, hnt, run0, by simp⟩
  exact ⟨congrArg Prod.fst equal,
    (congrArg (fun r => r.2.2.ioEvents) equal).trans io0⟩

/-- Oracle correctness and the transported Solver installation yield native termination. -/
private theorem endpoint_terminates
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat) (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events) :
    machineSemHOL baselineMachineConfig (sourceFfi input) ms (.terminate outcome events) := by
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  have correct := oracle_baseline_behaviour_eq oracles input baselineMachineConfig ms
    InitECandidate.nativeCode InitECandidate.bitmaps c depth baselineHeapLen
    baselineAdj2 baselineAdj4 3788 0 compiled depthBound
    (YukonCleanVerifierCheck.oracle_baseline_installation_transport input c ms related installed)
    nonfail
  exact target_termination_of_behaviour_eq baselineMachineConfig (sourceFfi input) ms
    outcome events (fun b hb => (correct b hb).trans source)

/-- 1. Zero-clock timeout characterization and positive step budget of non-`timeOut` target runs. -/
theorem evaluateTarget_zero_timeOut_and_pos_of_not_timeOut {width : Nat} [NeZero width]
    {S Q σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (K_post : Nat) (ms : S) :
    evaluateTargetHOL mc ffi 0 ms = (.timeOut, ms, ffi) ∧
      ((evaluateTargetHOL mc ffi K_post ms).1 ≠ .timeOut → 1 ≤ K_post) := by
  refine ⟨rfl, ?_⟩
  intro hnt
  cases K_post with
  | zero => exact False.elim (hnt rfl)
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)

/-- 2. Direct full-baseline non-`timeOut` target halt agreement from `sourceBehaviour = .terminate`
(including the 23,132-step zero-RAM bootstrap) together with `1 ≤ K_post`. -/
theorem oracle_full_baseline_terminate_halt_agree_of_not_timeOut
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (K_post : Nat)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + K_post) (baselineInitialState input)).1 ≠ .timeOut) :
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + K_post) (baselineInitialState input)).1 = .halt outcome ∧
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + K_post) (baselineInitialState input)).2.2.ioEvents = events ∧
    1 ≤ bootstrapSteps + K_post := by
  obtain ⟨post, shift, related⟩ := YukonBaselineCompat.full_evaluator_exact
    (sourceFfi input) (baselineInitialState input) (baselineInitialState_related input)
  have termination := endpoint_terminates oracles input c depth post related
    compiled depthBound installed outcome events source
  obtain ⟨k, ms', ffi', run, io⟩ := termination
  have fullTermination : machineSemHOL baselineMachineConfig (sourceFfi input)
      (baselineInitialState input) (.terminate outcome events) :=
    ⟨bootstrapSteps + k, ms', ffi', (shift k).trans run, io⟩
  have agreement := halt_agree_of_terminates baselineMachineConfig (sourceFfi input)
    (baselineInitialState input) outcome events (bootstrapSteps + K_post) fullTermination hnt
  exact ⟨agreement.1, agreement.2,
    (evaluateTarget_zero_timeOut_and_pos_of_not_timeOut baselineMachineConfig
      (sourceFfi input) (bootstrapSteps + K_post) (baselineInitialState input)).2 hnt⟩

/-- 3. Direct post-bootstrap non-`timeOut` target halt agreement on any `ms` related to `installedAsm`
from `sourceBehaviour = .terminate` together with `1 ≤ K_post`. -/
theorem oracle_baseline_endpoint_terminate_halt_agree_of_not_timeOut
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (K_post : Nat)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K_post ms).1 ≠ .timeOut) :
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K_post ms).1 = .halt outcome ∧
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K_post ms).2.2.ioEvents = events ∧
    1 ≤ K_post := by
  have agreement := halt_agree_of_terminates baselineMachineConfig (sourceFfi input)
    ms outcome events K_post
    (endpoint_terminates oracles input c depth ms related compiled depthBound installed
      outcome events source) hnt
  exact ⟨agreement.1, agreement.2,
    (evaluateTarget_zero_timeOut_and_pos_of_not_timeOut baselineMachineConfig
      (sourceFfi input) K_post ms).2 hnt⟩

/-- 4a. Structural clock neutrality and zero-clock preservation for `StackRemove.storeListCode`. -/
theorem stack_remove_store_list_clock_neutral {width : Nat} [NeZero width] {C F : Type}
    (values : List (Sum (BitVec width) Nat)) (address temporary : Nat)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (clock : Nat)
    (run : StackSemEvaluate.evaluate (storeListCode address temporary values, source) = (result, post)) :
    clockNeutralHOL (storeListCode address temporary values) ∧
      StackSemEvaluate.evaluate (storeListCode address temporary values, { source with clock := clock }) =
        (result, { post with clock := clock }) :=
  ⟨clockNeutralStoreListCode values address temporary,
    EvaluateNeutral.evaluateClockNeutral _ source post result clock
      ⟨run, clockNeutralStoreListCode values address temporary⟩⟩

/-- 4b. Zero-clock expansion for `StackRemove.initCode`: `initCode` is structurally clock-neutral
and consumes `0` clock ticks (`{source with clock := clock} -> {post with clock := clock}`). -/
theorem stack_remove_init_code_clock_preserve {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maximumHeap pointer : Nat)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (clock : Nat)
    (run : StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, source) = (result, post)) :
    clockNeutralHOL (initCode (width := width) generateGc maximumHeap pointer) ∧
      StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, { source with clock := clock }) =
        (result, { post with clock := clock }) :=
  ⟨initCodeClockNeutral generateGc maximumHeap pointer,
    evaluateInitCodeClock generateGc maximumHeap pointer source post result clock run⟩

private theorem evalCrepSemHOLExpWithDecider_clock_irrel {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (k : Nat)
    (memDec : (address : BitVec width) → Decidable (s.memaddrs address)) :
    ∀ e : CrepExpHOL width,
      evalCrepSemHOLExpWithDecider { s with clock := k } memDec e =
        evalCrepSemHOLExpWithDecider s memDec e
  | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by
      simp only [evalCrepSemHOLExpWithDecider]
  | .load address => by
      simp only [evalCrepSemHOLExpWithDecider,
        evalCrepSemHOLExpWithDecider_clock_irrel s k memDec address]
  | .load32 address | .loadByte address => by
      simp only [evalCrepSemHOLExpWithDecider,
        evalCrepSemHOLExpWithDecider_clock_irrel s k memDec address]
  | .op operator args | .crepOp operator args => by
      simp only [evalCrepSemHOLExpWithDecider]
      rw [optMmapCongHOL args args _ _ rfl
        (fun x hx => evalCrepSemHOLExpWithDecider_clock_irrel s k memDec x)]
  | .cmp operator left right | .shift operator left right => by
      simp only [evalCrepSemHOLExpWithDecider,
        evalCrepSemHOLExpWithDecider_clock_irrel s k memDec left,
        evalCrepSemHOLExpWithDecider_clock_irrel s k memDec right]
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals decreasing_trivial

/-- 5. `CrepSem` expression evaluation is completely independent of `s.clock`. -/
theorem crep_eval_exp_clock_irrel {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (k : Nat) (e : CrepExpHOL width) :
    evalCrepSemHOLExp { s with clock := k } e = evalCrepSemHOLExp s e := by
  let memDec := fun a => Classical.propDecidable (s.memaddrs a)
  rw [← evalCrepSemHOLExpWithDecider_eq { s with clock := k } memDec e,
      ← evalCrepSemHOLExpWithDecider_eq s memDec e]
  exact evalCrepSemHOLExpWithDecider_clock_irrel s k memDec e

/-- 6a. `baselineSubmission` equipped with a finite step budget `.finite K`. -/
def baselineWithFiniteK (K : Nat) : InitE.Submission :=
  { InitECandidate.Solver.FastEnv.baselineSubmission with K := .finite K }

private theorem baselineWithFiniteK_machineConfig (K : Nat) :
    (baselineWithFiniteK K).machineConfig = baselineMachineConfig := rfl

private theorem baselineWithFiniteK_initialMemory (K : Nat) (input : Guest.InputBlob) :
    (baselineWithFiniteK K).initialMemory input =
      (fun a =>
        if machineSharedDomain a then byteToBits ((Guest.guestHostMemory input a).getD 0)
        else initialMemory a) := by
  have h := submission_record_memory InitECandidate.code (.finite K)
    nativePc baselineNames 2 baselineMmio input
  have hpure : romMemory InitECandidate.code = initialMemory := rfl
  rw [hpure] at h
  have hd : submissionSharedDomain = machineSharedDomain := rfl
  unfold hostOverlay at h
  rw [hd] at h
  exact h

private theorem baselineWithFiniteK_initialState (K : Nat) :
    (baselineWithFiniteK K).initialState = baselineInitialState := by
  funext input
  unfold Submission.initialState
  rw [baselineWithFiniteK_initialMemory K input]
  rfl

/-- 6b. Admission theorem for `baselineWithFiniteK K`. -/
theorem baselineWithFiniteK_admitted (K : Nat) :
    (baselineWithFiniteK K).Admitted := by
  have h := InitECandidate.Solver.FastEnv.baselineSubmission_admitted
  exact ⟨h.code_nonempty, h.code_limit, h.anchor_lower, h.anchor_upper,
    h.anchor_aligned, h.name_boundary, h.metadata_length, h.ordinary_slots_loaded,
    h.mmio_valid, h.entry_distinct, h.entry_loaded, h.entry_aligned,
    h.entry_dispatch_separate, h.mmio_program, h.exit_loaded, h.layout_bound⟩

/-- 7. Final Yukon finite-`K` certificate reducer: a uniform non-`timeOut` bound at
`bootstrapSteps + K_post` on `baselineInitialState input` directly yields
`InitE.Certificate (baselineWithFiniteK (bootstrapSteps + K_post)) (.finite (bootstrapSteps + K_post))`! -/
theorem finite_certificate_of_uniform_post_bootstrap_not_timeOut
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth K_post : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          (bootstrapSteps + K_post) (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK (bootstrapSteps + K_post))
      (.finite (bootstrapSteps + K_post)) := by
  refine ⟨rfl, baselineWithFiniteK_admitted (bootstrapSteps + K_post), ?_⟩
  intro input hgas outcome events source covered
  have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [hlab]
    exact YukonCleanVerifierCheck.baseline_pan_installed input
  have hinst := YukonCleanVerifierCheck.oracle_baseline_installation input c hmem
  have hnt := not_timeOut input hgas outcome events source covered
  obtain ⟨hhalt, hio, _⟩ :=
    oracle_full_baseline_terminate_halt_agree_of_not_timeOut
      oracles input c depth compiled depthBound hinst
      outcome events source K_post hnt
  rcases hrun : evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + K_post) (baselineInitialState input) with ⟨res, post, finalFfi⟩
  rw [hrun] at hhalt hio
  dsimp only at hhalt hio
  subst hhalt
  refine ⟨bootstrapSteps + K_post, Nat.le_refl _, outcome, post, finalFfi, ?_, ?_⟩
  · rw [baselineWithFiniteK_machineConfig, baselineWithFiniteK_initialState]
    exact hrun
  · rw [hio]
    exact matchingResult_refl input outcome events covered


end InitECandidate.Solver.SelfContainedBoundedCertificate
