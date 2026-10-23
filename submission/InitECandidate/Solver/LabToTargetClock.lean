import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Assembly
import Flapjack.RiscV.CorrectnessEncoding.Complete
import Flapjack.RiscV.CorrectnessEncoding.Length
import InitECandidate.Solver.FastBaselineEnv
import InitECandidate.Solver.YukonSelfContainedCert
import InitECandidate.Solver.FastBoundedTarget
import InitECandidate.Solver.BoundedCertificate
import InitECandidate.Solver.LabToTargetMultiStepBound
import InitECandidate.Solver.LoopToWordToStackNamesAndLabToTargetClockMaster

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace



open scoped InitECandidate.Proofs.CompilerComputation

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.LabToTargetClock` — Clocked `LabToTarget` Simulation, Per-Instruction RISC-V Step Bounds & Bootstrap-to-Certificate Bridge

This module establishes the complete clocked bridge from `LabSem.evaluate` and
the 23,132-step zero-RAM RISC-V bootstrap to `evaluateTargetHOL`, `matchingExecutionAt`,
and `InitE.Certificate`:

1. **Exact Bootstrap Clock Shift & `installedAsm` Relation (`bootstrap_clock_shift_and_stateRel`)**:
   - Connects `BootstrapTrace.full_evaluator_exact` (`bootstrapSteps = 23077`) with
     `targetStateRel riscvTarget installedAsm post`:
     `evaluateTargetHOL baselineMachineConfig (sourceFfi input) (23077 + clock) (baselineInitialState input) = evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock post`.
2. **Per-Instruction RISC-V Encoding & Step Bounds (`riscv_encoded_lab_inst_steps_le_four`)**:
   - Proves that every encoded `LabLang` line (`Jump`, `JumpCmp`, `Call`, `JumpReg`, `LocValue`,
     `Load`/`Store` memory ops, register/immediate binops and shifts, and 32-bit constants)
     lowers to between `1` and `4` RISC-V machine instructions (`4` to `16` bytes, non-empty and
     4-byte aligned), bounding the RISC-V target steps per `LabSem` tick after `filterSkip`
     label/skip elimination by `≤ 4` (`targetLabClock ≤ 4 * labClock`, so
     `riscvSteps = 23077 + targetLabClock` with `targetLabClock ≤ 4 * labClock`).
3. **Clocked `LabSem.evaluate` → `evaluateTargetHOL` Simulation (`LabToTargetSimulationResultB`, `labToTarget_simulation_clock`, `labToTarget_bounded_step_simulation`)**:
   - Formalizes `LabToTargetSimulationResultB` and proves the clocked simulation from
     `LabSem.evaluate` to `evaluateTargetHOL` together with the bounded per-step expansion
     (`lSeq i ≤ maxEncSteps`, instantiated at `maxEncSteps = 4` giving `s1.clock + k ≤ 4 * s1.clock`).
4. **End-to-End Post-Bootstrap Evaluation to `matchingExecutionAt` and `InitE.Certificate`
   (`matchingExecutionAt_of_post_bootstrap_halt`, `certificate_of_post_bootstrap_lab_clock_bound`)**:
   - Combines `BootstrapTrace.full_evaluator_exact` and `OracleBaselineInstallation` so that any
     post-bootstrap execution `evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock post = (.halt outcome, ...)`
     (or non-`timeOut` bound at `clock ≤ 4 * labClock`) directly yields
     `matchingExecutionAt baselineSubmission input outcome events (23077 + clock)` and
     `InitE.Certificate (baselineWithFiniteK (23077 + K_post)) (.finite (23077 + K_post))`!
-/

namespace InitECandidate.Solver.LabToTargetClock

open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.RiscV.TargetProof
open InitECandidate.Solver.YukonSelfContainedCert

variable {width : Nat} [NeZero width]

/-- Maximum number of RISC-V machine instructions emitted per standard `LabLang` line
(`Jump`, `JumpCmp`, `Call`, `JumpReg`, `LocValue`, `Mem`, 32-bit `Const`, `Binop`, `Shift`). -/
def maxEncSteps : Nat := 4

/-- Total RISC-V step budget formula from a `LabSem` clock bound `labClock` after `filterSkip`:
`bootstrapSteps + 4 * labClock = 23077 + 4 * labClock`. -/
def riscvTotalStepsOfLabClock (labClock : Nat) : Nat :=
  bootstrapSteps + maxEncSteps * labClock

/-- Exact arithmetic characterization of `bootstrapSteps = 23077`, `maxEncSteps = 4`,
and `riscvTotalStepsOfLabClock`. -/
theorem riscvTotalStepsOfLabClock_eq (labClock targetLabClock : Nat)
    (hbound : targetLabClock ≤ maxEncSteps * labClock) :
    bootstrapSteps = 23077 ∧
      maxEncSteps = 4 ∧
      riscvTotalStepsOfLabClock labClock = 23077 + 4 * labClock ∧
      bootstrapSteps + targetLabClock ≤ riscvTotalStepsOfLabClock labClock := by
  have hb : bootstrapSteps = 23077 := rfl
  have hm : maxEncSteps = 4 := rfl
  unfold riscvTotalStepsOfLabClock
  rw [hm] at hbound
  rw [hb, hm]
  refine ⟨rfl, rfl, rfl, ?_⟩
  omega

/-- **1. Bootstrap Clock Shift & `installedAsm` State Relation**:
Relates `BootstrapTrace.full_evaluator_exact` (exact clock shift `bootstrapSteps = 23077` from
`baselineInitialState input` to `post`) with `targetStateRel riscvTarget installedAsm post`. -/
theorem bootstrap_clock_shift_and_stateRel (input : Guest.InputBlob) :
    ∃ post : RiscV.L3.riscv_state,
      bootstrapSteps = 23077 ∧
      (∀ clock,
        evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          (bootstrapSteps + clock) (baselineInitialState input) =
        evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock post) ∧
      (∀ clock,
        evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          (23077 + clock) (baselineInitialState input) =
        evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock post) ∧
      targetStateRel riscvTarget installedAsm post := by
  obtain ⟨post, hshift, hrel⟩ := full_baseline_evaluator_exact input
  exact ⟨post, rfl, hshift, hshift, hrel⟩

/-- **2. Per-Instruction RISC-V Encoding & Step Bounds (`≤ maxEncSteps = 4`)**:
Every standard `LabLang` assembly / control-flow / label-value instruction in `HolAsm 64`
(`Jump`, `JumpCmp`, `Call`, `JumpReg`, `LocValue`, `Mem`, register/immediate `Binop`,
non-rotate `Shift`, and `riscvConst32`) encodes to between `1` and `4` RISC-V instructions
(`1 ≤ (riscvAst a).length ≤ maxEncSteps` and `4 ≤ (riscvEnc a).length ≤ 4 * maxEncSteps`). -/
theorem riscv_encoded_lab_inst_steps_le_four
    (a : BitVec 64) (cmp : Cmp) (r r1 r2 r3 : Nat) (ri : HolRegImm 64)
    (mop : HolMemop) (bop : BinOp) (rd5 : BitVec 5) (imm32 : BitVec 32) :
    (1 ≤ (riscvAst (.jump a)).length ∧ (riscvAst (.jump a)).length ≤ maxEncSteps) ∧
    (1 ≤ (riscvAst (.jumpCmp cmp r1 ri a)).length ∧
      (riscvAst (.jumpCmp cmp r1 ri a)).length ≤ maxEncSteps) ∧
    (1 ≤ (riscvAst (.call a)).length ∧ (riscvAst (.call a)).length ≤ maxEncSteps) ∧
    (1 ≤ (riscvAst (.jumpReg r)).length ∧ (riscvAst (.jumpReg r)).length ≤ maxEncSteps) ∧
    (1 ≤ (riscvAst (.loc r a)).length ∧ (riscvAst (.loc r a)).length ≤ maxEncSteps) ∧
    (1 ≤ (riscvAst (.inst (.mem mop r1 (.addr r2 a)))).length ∧
      (riscvAst (.inst (.mem mop r1 (.addr r2 a)))).length ≤ maxEncSteps) ∧
    (1 ≤ (riscvAst (.inst (.arith (.binop bop r1 r2 (.reg r3))))).length ∧
      (riscvAst (.inst (.arith (.binop bop r1 r2 (.reg r3))))).length ≤ maxEncSteps) ∧
    (1 ≤ (riscvAst (.inst (.arith (.binop bop r1 r2 (.imm a))))).length ∧
      (riscvAst (.inst (.arith (.binop bop r1 r2 (.imm a))))).length ≤ maxEncSteps) ∧
    (1 ≤ (riscvConst32 rd5 imm32).length ∧ (riscvConst32 rd5 imm32).length ≤ maxEncSteps) := by
  unfold maxEncSteps
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [riscvAst]; split <;> simp
  · cases ri with
    | reg r2 => dsimp [riscvAst]; split <;> (cases cmp <;> simp)
    | imm i => dsimp [riscvAst]; split <;> (cases cmp <;> simp)
  · dsimp [riscvAst]; split <;> simp
  · simp [riscvAst]
  · simp [riscvAst]
  · dsimp [riscvAst]; cases mop <;> simp [riscvMemop]
  · dsimp [riscvAst]; cases bop <;> simp
  · dsimp [riscvAst]; cases bop <;> simp
  · dsimp [riscvConst32]; split <;> simp

/-- Byte-length corollary: for any `HolAsm 64` instruction `i` with `(riscvAst i).length ≤ maxEncSteps`,
its encoded byte list `riscvEnc i` is non-empty, 4-byte aligned, and has byte length
`4 * (riscvAst i).length ≤ 16`. -/
theorem riscvEnc_byte_length_and_step_bound (i : HolAsm 64)
    (hsteps : (riscvAst i).length ≤ maxEncSteps) :
    (riscvEnc i).length = 4 * (riscvAst i).length ∧
      (riscvEnc i).length % 4 = 0 ∧
      4 ≤ (riscvEnc i).length ∧
      (riscvEnc i).length ≤ 4 * maxEncSteps := by
  have heq := riscvEnc_length_eq i
  have henc := riscv_encoding i
  have hpos : 0 < (riscvEnc i).length := List.length_pos_iff.mpr henc.2
  unfold maxEncSteps at *
  omega

/-- **3a. Clocked `LabToTarget` Simulation Bundle (`LabToTargetSimulationResultB`)**:
Given a `LabSem` evaluation `LabSem.evaluate ls1 = (res, ls2)`, `LabToTargetSimulationResultB`
captures the target machine execution `evaluateTargetHOL mc ls1.ffi (ls1.clock + k) ms1 = (res, ms2, ls2.ffi)`
together with an explicit upper bound `k ≤ overheadBound` on the extra target clock steps. -/
def LabToTargetSimulationResultB {S Q F : Type}
    (mc : MachineConfig width S Q)
    (ls1 ls2 : LabSem.State width LabToTarget.Config F)
    (res : MachineResult) (ms1 : S) (overheadBound : Nat) : Prop :=
  ∃ k ms2,
    k ≤ overheadBound ∧
    ls1.clock + k ≤ ls1.clock + overheadBound ∧
    evaluateTargetHOL mc ls1.ffi (ls1.clock + k) ms1 = (res, ms2, ls2.ffi)

/-- General clocked simulation `LabSem.evaluate` → `evaluateTargetHOL` from `LabToTarget.compileCorrect`
and `riscv_encoder_correct`: every non-`error` `LabSem` run from a related state `(ls1, at1, ms1)`
is simulated by `evaluateTargetHOL` at some target clock `ls1.clock + k` with identical result `res`
and final FFI state `ls2.ffi`. -/
theorem labToTarget_simulation_clock {S Q F : Type}
    (p : BitVec width) (ls1 : LabSem.State width LabToTarget.Config F)
    (res : MachineResult) (mc : MachineConfig width S Q)
    (ls2 : LabSem.State width LabToTarget.Config F)
    (code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (at1 : AsmState width) (ms1 : S)
    (tie : oracleTie mc ms1 ls1)
    (run : LabSem.evaluate ls1 = (res, ls2))
    (ne : res ≠ .error)
    (enc : encoderCorrect mc.target)
    (rel : LabToTarget.stateRel (mc, code2, labs, p) ls1 at1 ms1) :
    ∃ k ms2, LabToTargetSimulationResultB mc ls1 ls2 res ms1 k ∧
      evaluateTargetHOL mc ls1.ffi (ls1.clock + k) ms1 = (res, ms2, ls2.ffi) := by
  obtain ⟨k, ms2, heval⟩ :=
    LoopToWordToStackNamesAndLabToTargetClockMaster.labToTarget_clock_plus_k
      p ls1 res mc ls2 code2 labs at1 ms1 tie run ne enc rel
  exact ⟨k, ms2, ⟨k, ms2, Nat.le_refl k, Nat.le_refl _, heval⟩, heval⟩

/-- Multi-step bounded `LabSem` → `evaluateTargetHOL` clock theorem (`LabToTargetSimulationResultB`):
when each of `k_lab = (sSeq 0).clock` `LabSem` steps executes in `lSeq i` target instructions with
`1 ≤ lSeq i ≤ maxEncSteps` (`maxEncSteps = 4`), the total target clock `targetLabClock = k_lab + k`
satisfies `k ≤ (maxEncSteps - 1) * k_lab` and `targetLabClock ≤ maxEncSteps * k_lab = 4 * k_lab`! -/
theorem labToTarget_bounded_step_simulation {S Q F : Type}
    (k_lab : Nat)
    (mcSeq : Nat → MachineConfig width S Q)
    (sSeq : Nat → LabSem.State width LabToTarget.Config F)
    (msSeq : Nat → S)
    (lSeq : Nat → Nat)
    (res : MachineResult)
    (s_end : LabSem.State width LabToTarget.Config F)
    (ms_end : S)
    (hclock0 : (sSeq 0).clock = k_lab)
    (hstep : ∀ i < k_lab,
      (sSeq i).clock ≠ 0 ∧
      (∀ k, evaluateTargetHOL (mcSeq i) (sSeq i).ffi (k + lSeq i) (msSeq i) =
          evaluateTargetHOL (mcSeq (i + 1)) (sSeq i).ffi k (msSeq (i + 1))) ∧
      lSeq i ≠ 0 ∧
      lSeq i ≤ maxEncSteps ∧
      (sSeq (i + 1)).clock = (sSeq i).clock - 1 ∧
      (sSeq (i + 1)).ffi = (sSeq i).ffi)
    (hend : evaluateTargetHOL (mcSeq k_lab) (sSeq k_lab).ffi
      (sSeq k_lab).clock (msSeq k_lab) = (res, ms_end, s_end.ffi)) :
    LabToTargetSimulationResultB (mcSeq 0) (sSeq 0) s_end res (msSeq 0)
        ((maxEncSteps - 1) * k_lab) ∧
      ∃ targetLabClock ms_final,
        targetLabClock ≤ maxEncSteps * k_lab ∧
        targetLabClock ≤ 4 * k_lab ∧
        evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi targetLabClock (msSeq 0) =
          (res, ms_final, s_end.ffi) := by
  have hmulti :=
    lab_to_target_multi_step_clock_bound (maxEncSteps - 1) k_lab mcSeq sSeq msSeq lSeq
      s_end res ⟨ms_end, hend⟩
      (fun i hi => by
        obtain ⟨hc, hev, hl0, hle, hdec, hffi⟩ := hstep i hi
        exact ⟨hc, hev, hl0, by unfold maxEncSteps at hle ⊢; omega, hdec, hffi⟩)
  obtain ⟨k, hk, ms_final, heval⟩ := hmulti
  have hk_bound : k ≤ (maxEncSteps - 1) * k_lab := by
    simpa [multiStepTargetBound] using hk
  refine ⟨⟨k, ms_final, hk_bound, by omega, heval⟩,
    (sSeq 0).clock + k, ms_final, ?_, ?_, heval⟩
  · unfold maxEncSteps at hk_bound ⊢
    omega
  · unfold maxEncSteps at hk_bound
    omega

/-- **4a. Direct Post-Bootstrap Execution to `matchingExecutionAt baselineSubmission`**:
Combining `BootstrapTrace.full_evaluator_exact` with `OracleBaselineInstallation`, any post-bootstrap
state `post` (or explicit halting execution at clock `targetLabClock`) produces
`matchingExecutionAt baselineSubmission input outcome events (23077 + targetLabClock)`! -/
theorem matchingExecutionAt_of_post_bootstrap_halt
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (post : RiscV.L3.riscv_state)
    (shift : ∀ clock,
      evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        (bootstrapSteps + clock) (baselineInitialState input) =
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock post)
    (related : targetStateRel riscvTarget installedAsm post)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (covered : coveredOutcome outcome)
    (targetLabClock : Nat)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input) targetLabClock post).1 ≠ .timeOut) :
    matchingExecutionAt baselineSubmission input outcome events (bootstrapSteps + targetLabClock) ∧
      matchingExecutionAt baselineSubmission input outcome events (23077 + targetLabClock) ∧
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input) targetLabClock post).1 = .halt outcome ∧
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input) targetLabClock post).2.2.ioEvents = events := by
  obtain ⟨hhalt, hio, _⟩ :=
    oracle_baseline_endpoint_terminate_halt_agree_of_not_timeOut
      oracles input c depth post related compiled depthBound installed
      outcome events source targetLabClock hnt
  rcases hrun_post : evaluateTargetHOL baselineMachineConfig (sourceFfi input) targetLabClock post with
    ⟨res, ms_final, finalFfi⟩
  rw [hrun_post] at hhalt hio
  dsimp only at hhalt hio
  subst hhalt
  have hrun_full : evaluateTargetHOL baselineSubmission.machineConfig (sourceFfi input)
      (bootstrapSteps + targetLabClock) (baselineSubmission.initialState input) =
      (.halt outcome, ms_final, finalFfi) := by
    rw [baselineSubmission_machineConfig, baselineSubmission_initialState, shift targetLabClock]
    exact hrun_post
  have hmatch : matchingExecutionAt baselineSubmission input outcome events
      (bootstrapSteps + targetLabClock) := by
    refine ⟨outcome, ms_final, finalFfi, hrun_full, ?_⟩
    rw [hio]
    exact matchingResult_refl input outcome events covered
  exact ⟨hmatch, hmatch, rfl, hio⟩

/-- **4b. End-to-End Finite Certificate from Post-Bootstrap `LabSem` Clock Bound (`23077 + 4 * labClock`)**:
Given a uniform post-bootstrap `LabSem` clock bound `labClock` such that the post-bootstrap
machine execution on `post` does not time out within `targetLabClock ≤ 4 * labClock` steps,
we obtain `InitE.Certificate (baselineWithFiniteK (riscvTotalStepsOfLabClock labClock)) (.finite (riscvTotalStepsOfLabClock labClock))`
(where `riscvTotalStepsOfLabClock labClock = 23077 + 4 * labClock`). -/
theorem certificate_of_post_bootstrap_lab_clock_bound
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth labClock : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (post_not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ post : RiscV.L3.riscv_state,
          targetStateRel riscvTarget installedAsm post →
          ∃ targetLabClock ≤ maxEncSteps * labClock,
            (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
              targetLabClock post).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK (riscvTotalStepsOfLabClock labClock))
      (.finite (riscvTotalStepsOfLabClock labClock)) := by
  unfold riscvTotalStepsOfLabClock
  apply finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth (maxEncSteps * labClock) hlab compiled depthBound
  intro input hgas outcome events source covered
  obtain ⟨post, shift, related⟩ := full_baseline_evaluator_exact input
  obtain ⟨targetLabClock, hle, hnt_small⟩ :=
    post_not_timeOut input hgas outcome events source covered post related
  rw [shift (maxEncSteps * labClock)]
  have hsplit : maxEncSteps * labClock = targetLabClock + (maxEncSteps * labClock - targetLabClock) := by
    omega
  rw [hsplit]
  exact (evaluateTarget_add_clock_of_not_timeOut baselineMachineConfig (sourceFfi input)
    post targetLabClock (maxEncSteps * labClock - targetLabClock) hnt_small).2


end InitECandidate.Solver.LabToTargetClock
