import InitECandidate.Solver.SelfContainedBoundedCertificate
import InitECandidate.Solver.VerifySpeedBound

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# Self-contained master finite `K` (no `Proofs/Bounded*` in the transitive closure)

The EVM opcode model of `EvmOpcodeTightBound` is restated arithmetically here, because
`EvmOpcodeTightBound` and `SourceWitnessClockBound` import `GuestGasAndHtabBound`, whose
closure contains `Proofs/BoundedPanToWord`, `Proofs/BoundedStackToLab`, `Proofs/BoundedTarget`.

Worst case source clock: the `keccak256` family (`200,000,000 / 30 * 60 = 399,999,960` loop
ticks), not `arithStack`, plus the `59,564,234` prologue ticks.
-/

namespace InitECandidate.Solver.SelfContainedMasterK

open Classical
open InitE
open InitECandidate.Proofs
open Flapjack
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate

/-- Block gas limit. -/
def gasCap : Nat := 200000000
/-- Prologue ticks (`tightArithPrologueTicks`). -/
def prologueTicks : Nat := 59564234
/-- Worst family: min gas per opcode and source ticks per opcode (keccak256: 30 gas, 60 ticks). -/
def worstMinGas : Nat := 30
def worstTicks : Nat := 60
/-- Arithmetic-stack family (3 gas, 2 ticks), the case used by `maxTightSourceClock`. -/
def arithMinGas : Nat := 3
def arithTicks : Nat := 2

def loopTicks (minGas ticks : Nat) : Nat := gasCap / minGas * ticks

/-- Refined source clock, worst over the two families. -/
def refinedSourceClock : Nat :=
  prologueTicks + max (loopTicks worstMinGas worstTicks) (loopTicks arithMinGas arithTicks)

/-- Front-end (PanSem → LabSem) multiplier and additive pipeline offset. -/
def frontFactor : Nat := 10
def pipeOffset : Nat := 5000
/-- Realistic LabToTarget basic-block factor: RISC-V instructions per LabSem tick. -/
def bMax : Nat := 8

def refinedPostK : Nat := bMax * (frontFactor * (refinedSourceClock + pipeOffset))
def refinedCandidateK : Nat := bootstrapSteps + refinedPostK

theorem loopTicks_values :
    loopTicks worstMinGas worstTicks = 399999960 ∧ loopTicks arithMinGas arithTicks = 133333332 := by
  decide

/-- The worst family is keccak256, so `refinedSourceClock` exceeds the arithStack-only clock. -/
theorem refinedSourceClock_eq :
    refinedSourceClock = 459564194 ∧ prologueTicks + loopTicks arithMinGas arithTicks < refinedSourceClock := by
  decide

theorem refinedCandidateK_eq : refinedCandidateK = 36765558597 := by
  unfold refinedCandidateK refinedPostK
  rw [InitE.bootstrapSteps_eq]; decide

theorem refinedCandidateK_lt_400B : refinedCandidateK < 400000000000 := by
  rw [refinedCandidateK_eq]; decide

theorem refinedCandidateK_lt_ceiling : refinedCandidateK < 900719925474 := by
  rw [refinedCandidateK_eq]; decide

theorem yukonScore_refined_lt (minutes : Nat) :
    yukonScore refinedCandidateK minutes < 2 ^ 53 - 1 :=
  yukonScore_lt_two_pow_53_sub_one (by rw [refinedCandidateK_eq]; decide)

/-- Tightness of the 400B target in the front factor at `B_max = 8`: the budget stays below
`400,000,000,000` iff the front multiplier is at most `108`. -/
theorem front_factor_threshold (M : Nat) :
    bootstrapSteps + bMax * (M * (refinedSourceClock + pipeOffset)) < 400000000000 ↔ M ≤ 108 := by
  rw [InitE.bootstrapSteps_eq, (refinedSourceClock_eq).1]
  unfold bMax pipeOffset
  omega

/-- Master certificate: no `Proofs/Bounded*` module in the closure. Remaining obligation:
uniform non-`timeOut` of the target at `refinedCandidateK`. -/
theorem self_contained_master_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
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
          refinedCandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK refinedCandidateK) (.finite refinedCandidateK) ∧
      refinedCandidateK < 400000000000 ∧
      ∀ minutes, yukonScore refinedCandidateK minutes < 2 ^ 53 - 1 :=
  ⟨finite_certificate_of_uniform_post_bootstrap_not_timeOut
      oracles c depth refinedPostK hlab compiled depthBound not_timeOut,
    refinedCandidateK_lt_400B, yukonScore_refined_lt⟩


end InitECandidate.Solver.SelfContainedMasterK
