import InitECandidate.Proofs.CompilerComputation
import InitECandidate.Proofs.OracleBaselineCorrectness
import InitECandidate.Solver.FastBaselineEnv
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitSemantics
import Flapjack.Compiler.Backend.StackNames.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace



open scoped InitECandidate.Proofs.CompilerComputation

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

/-!
# `InitECandidate.Solver.YukonCleanVerifierCheck` — Clean `Solver/` Initialization & Clock-Agreement Bridge

This module encapsulates the initialization and clock-agreement lemmas inside
`InitECandidate.Solver.YukonCleanVerifierCheck` using only upstream/baseline modules:
1. `stack_remove_clocked_agree`: same-clock non-`.timeOut` run agreement across `StackRemove`
   together with `+1` entry shift across `StackRemove.initCode`.
2. `stack_names_clocked_agree`: exact `0`-tick same-clock run agreement across `StackNames`.
3. `PanInstallation` and `BaselineInstallationFacts` invariants (`baselineHeapLen`,
   `baselineAdj2`, `baselineAdj4`, `baseline_mmio_projection`,
   `baseline_pan_installed_metadata`, `baseline_pan_installed`,
   `oracle_baseline_installation`, `oracle_baseline_installed`, and
   `oracle_baseline_installation_transport`).
-/

namespace InitECandidate.Solver.YukonCleanVerifierCheck

open Classical
open InitE
open InitECandidate.Proofs
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock
open Flapjack.Pancake.Proofs.PanToTarget

/-! ## 1. `StackRemove` & `StackNames` Clocked Agreement (`stack_remove_clocked_agree`, `stack_names_clocked_agree`) -/

/-- Clock-preserving `StackRemove` simulation and non-`.timeOut` same-clock run agreement:
if a `StackSem` entry call on `source` at `clock` does not error (`sourceResult ≠ some .error`)
and the `StackRemove`-compiled state `target` does not time out at `clock`
(`targetResult ≠ some .timeOut`), then `targetResult = sourceResult` and
`postTarget.ffi = postSource.ffi` at the exact same `clock`. -/
theorem stack_remove_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock : Nat)
    (source target postSource postTarget : StackSemStateFiniteExact width C F)
    (sourceResult targetResult : Option (StackSemResult width))
    (relation : StackRemove.stateRelHOL jump bounds pointer source target)
    (sourceRun : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { source with clock := clock }) =
      (sourceResult, postSource))
    (nonError : sourceResult ≠ some .error)
    (targetRun : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { target with clock := clock }) =
      (targetResult, postTarget))
    (nonTimeout : targetResult ≠ some .timeOut) :
    targetResult = sourceResult ∧ postTarget.ffi = postSource.ffi := by
  obtain ⟨extra, compiledPost, compiledRun, ffi⟩ :=
    StackRemove.CompileSemantics.entrySimulation jump bounds pointer start clock
      source target postSource sourceResult relation sourceRun nonError
  have boostedRun := StackProps.evaluateAddClock extra (.call none (.inl start) none)
    { target with clock := clock } targetResult postTarget ⟨targetRun, nonTimeout⟩
  have same : (targetResult, { postTarget with clock := postTarget.clock + extra }) =
      (sourceResult, compiledPost) := by
    rw [← boostedRun]
    simpa only [Nat.add_comm] using compiledRun
  rcases Prod.mk.inj same with ⟨resultEqual, postEqual⟩
  exact ⟨resultEqual, (congrArg StackSemStateFiniteExact.ffi postEqual).trans ffi⟩

/-- Clock-preserving `StackRemove.initCode` `+1` entry shift and `clockNeutralHOL` witness:
if `StackRemove.initCode` finishes normally (`(none, t)`) from `s2`, then `initCode` is
`clockNeutralHOL`, preserves any clock `k` (`(none, { t with clock := k })`), and calling
procedure `0` on `s2` at clock `k + 1` produces the exact same result and FFI state as
calling `start` on `t` at clock `k`. -/
theorem stack_remove_init_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer start : Nat)
    (s2 t : StackSemStateFiniteExact width C F) (k : Nat)
    (hentry : sptLookup 0 s2.code =
      some (.seq (StackRemove.initCode generateGc maxHeap pointer)
        (.call none (.inl start) none)))
    (hrun : StackSemEvaluate.evaluate (StackRemove.initCode generateGc maxHeap pointer, s2) =
      (none, t)) :
    clockNeutralHOL (StackRemove.initCode (width := width) generateGc maxHeap pointer) ∧
    StackSemEvaluate.evaluate
      (StackRemove.initCode generateGc maxHeap pointer, { s2 with clock := k }) =
      (none, { t with clock := k }) ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { s2 with clock := k + 1 })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k })).1 ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { s2 with clock := k + 1 })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k })).2.ffi := by
  have hneutral := initCodeClockNeutral (width := width) generateGc maxHeap pointer
  have clockRun := evaluateInitCodeClock generateGc maxHeap pointer s2 t none k hrun
  have body : StackSemEvaluate.evaluate
      (.seq (StackRemove.initCode generateGc maxHeap pointer) (.call none (.inl start) none),
        { s2 with clock := k }) =
      StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k }) := by
    rw [StackSemEvaluate.evaluate_seq, clockRun]
    simp [StackSemControl.fixClock]
  have notBad := StackRemove.Proofs.InitSemantics.callNotBad start { t with clock := k }
  refine ⟨hneutral, clockRun, ?_⟩
  rw [StackSemEvaluate.evaluate_call]
  simp only [StackSemControl.findCode, hentry, Nat.add_one_ne_zero, if_false,
    StackSemStateOps.decClock, Nat.add_sub_cancel]
  rw [show ({ ({ s2 with clock := k + 1 } : StackSemStateFiniteExact width C F) with
      clock := k } : StackSemStateFiniteExact width C F) = { s2 with clock := k } from rfl, body]
  simp only [StackSemControl.fixClock, notBad]
  exact ⟨rfl, rfl⟩

/-- Clock-preserving `StackNames` simulation (`extra = 0`): at any clock `k`, calling `start`
on `StackNames.renameState c f s` produces the exact same result and FFI state as calling
`start` on `s` at the same clock `k`. -/
theorem stack_names_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F}
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f))
    (start k : Nat) :
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { StackNames.renameState c f s with clock := k })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k })).1 ∧
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { StackNames.renameState c f s with clock := k })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k })).2.ffi := by
  have h := StackNames.CompileSemantics.evaluate_entry_renameState
    (c := c) (f := f) (s := s) hf ha hs hk hc start k
  rw [h]
  exact ⟨rfl, rfl⟩

/-! ## 2. `PanInstallation` & `BaselineInstallationFacts` Invariants -/

/-- Heap-shaped domain size, including the globals reserved at its upper end. -/
def baselineHeapLen : Nat := (stackStart - sourceBase) / 8

/-- Adjusted lower stack-check bound (`sourceBase + 8 * maxStackAlloc`). -/
def baselineAdj2 : BitVec 64 := BitVec.ofNat 64 sourceBase +
  (8 : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc

/-- Adjusted upper stack-check bound (`ramEnd - 8 * maxStackAlloc`). -/
def baselineAdj4 : BitVec 64 := BitVec.ofNat 64 ramEnd -
  (8 : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc

set_option maxRecDepth 10000 in
/-- `baselineLabConfig.shmemExtra` and `baselineConfigLiteral.labConf.shmemExtra` both equal `baselineMmio`. -/
theorem baseline_mmio_projection :
    baselineLabConfig.shmemExtra = baselineMmio ∧
    baselineConfigLiteral.labConf.shmemExtra = baselineMmio := by
  refine ⟨by decide_cbv, by decide_cbv⟩

set_option maxRecDepth 10000 in
/-- Metadata-level `panInstalled` certificate on `baselineInstalledState` and `sourceMemory`. -/
theorem baseline_pan_installed_metadata :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      baselineLabConfig.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineLabConfig.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ sourceMemory) ordinaryDomain sharedDomain := by
  have hregs : heapRegs pancakeRiscVBackendConfig.stackConf.regNames = (11, 13) := by
    unfold pancakeRiscVBackendConfig
    rw [riscvBackendConfig_eq_executable]
    decide_cbv
  exact panInstalled_metadata_congr _ _ _ _ _ (some baselineNames) _ (11, 13)
    _ _ baselineMmio _ _ (wlabWlocExact ∘ sourceMemory) _ ordinaryDomain _ sharedDomain
    baseline_installation_metadata.1 hregs baseline_mmio_projection.1 rfl rfl rfl
    baseline_pan_installed_core

/-- Every compiler installation premise is certified after the bootstrap for any `input : Guest.InputBlob`. -/
theorem baseline_pan_installed (input : Guest.InputBlob) :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      baselineLabConfig.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineLabConfig.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
  exact panInstalled_metadata_congr _ _ _ _ _ baselineLabConfig.ffiNames
    _ (heapRegs pancakeRiscVBackendConfig.stackConf.regNames) _ _ baselineLabConfig.shmemExtra
    _ _ (wlabWlocExact ∘ sourceMemory) _ ordinaryDomain _ sharedDomain
    rfl rfl rfl rfl (source_memory_domain input) rfl baseline_pan_installed_metadata

set_option maxRecDepth 100000 in
/-- Remaining numeric and register premises for `OracleBaselineInstallation`,
decoupled from the 46,000-file artifact stage tree. -/
theorem oracle_baseline_installation (input : Guest.InputBlob)
    (c : Backend.Config)
    (memory : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs) :
    OracleBaselineInstallation input baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode InitECandidate.bitmaps c baselineHeapLen
      baselineAdj2 baselineAdj4 3788 0 := by
  refine ⟨baseline_machine_isRiscv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, memory, ?_⟩
  · change (0 : BitVec 64) < BitVec.ofNat 64 sourceBase
    decide_cbv
  · change BitVec.ofNat 64 sourceBase < BitVec.ofNat 64 stackStart
    decide_cbv
  · rfl
  · change baselineHeapLen = (BitVec.ofNat 64 stackStart +
      -1 * BitVec.ofNat 64 sourceBase).toNat / (64 / 8)
    decide_cbv
  · change BitVec.ofNat 64 heapEnd = BitVec.ofNat 64 sourceBase +
      (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 baselineHeapLen -
        BitVec.ofNat 64 (globalsWords * 64 / 8)
    decide_cbv
  · decide_cbv
  · rfl
  · change holAligned (wordShiftAmount 64 + 1)
      (BitVec.ofNat 64 stackStart + -1 * BitVec.ofNat 64 sourceBase) = true
    decide_cbv
  · rfl
  · rfl
  · change baselineAdj2 ≤ BitVec.ofNat 64 stackStart
    decide_cbv
  · change BitVec.ofNat 64 stackStart ≤ baselineAdj4
    decide_cbv
  · change (BitVec.ofNat 64 stackStart + -1 * BitVec.ofNat 64 sourceBase).toNat ≤
      (wordSemBytesInWord : BitVec 64).toNat *
        (2 * DataToWord.maxHeapLimit 64 pancakeRiscVBackendConfig.dataConf - 1)
    decide_cbv
  · rfl
  · have names :
        (StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 2,
         StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 3,
         StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 4) =
          (11, 12, 13) := by decide_cbv
    have n2 := congrArg Prod.fst names
    have n3 := congrArg (fun p => p.2.1) names
    have n4 := congrArg (fun p => p.2.2) names
    dsimp only at n2 n3 n4
    simp only [readLimits, n2, n3, n4]
    rfl

/-- Concrete pre-transport oracle installation witness for `baselineConfigLiteral`. -/
theorem oracle_baseline_installed (input : Guest.InputBlob) :
    OracleBaselineInstallation input baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode InitECandidate.bitmaps baselineConfigLiteral
      baselineHeapLen baselineAdj2 baselineAdj4 3788 0 :=
  oracle_baseline_installation input baselineConfigLiteral (baseline_pan_installed input)

set_option maxRecDepth 100000 in
/-- Oracle installations are stable under the machine projection agreement
established by the bootstrap. -/
theorem oracle_baseline_installation_transport (input : Guest.InputBlob)
    (c : Backend.Config)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0) :
    OracleBaselineInstallation input baselineMachineConfig ms
      InitECandidate.nativeCode InitECandidate.bitmaps c baselineHeapLen
      baselineAdj2 baselineAdj4 3788 0 := by
  have agreement := baseline_endpoint_agreement ms related
  have r11 := agreement.regs 11 (by decide)
  have r12 := agreement.regs 12 (by decide)
  have r13 := agreement.regs 13 (by decide)
  have names :
      (StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 2,
       StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 3,
       StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 4) =
         (11, 12, 13) := by decide_cbv
  have n2 := congrArg Prod.fst names
  have n3 := congrArg (fun p => p.2.1) names
  have n4 := congrArg (fun p => p.2.2) names
  dsimp only at n2 n3 n4
  have limits : readLimits baselineMachineConfig.target.config pancakeRiscVBackendConfig
      baselineMachineConfig ms = readLimits baselineMachineConfig.target.config
        pancakeRiscVBackendConfig baselineMachineConfig baselineInstalledState := by
    simp only [readLimits, n2, n3, n4, r11, r12, r13]
  have rlen : baselineMachineConfig.target.getReg ms baselineMachineConfig.lenReg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.lenReg := r11
  have rptr : baselineMachineConfig.target.getReg ms baselineMachineConfig.ptr2Reg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.ptr2Reg := r12
  have rlen2 : baselineMachineConfig.target.getReg ms baselineMachineConfig.len2Reg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.len2Reg := r13
  rcases installed with ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals,
    hdomain, haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hmemory, hlimits⟩
  have memory := panInstalled_transport agreement hmemory
  unfold OracleBaselineInstallation
  simp only [rlen, rptr, rlen2, limits]
  exact ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax, hendian, memory, hlimits⟩


end InitECandidate.Solver.YukonCleanVerifierCheck
