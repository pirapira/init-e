import InitECandidate.Solver.CrepToStackNamesAndLabToTargetEndToEndClockMaster

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# Flapjack eleven-pass simulation and clock: grand summary (Axis A)

Status per pass (no `sorryAx`, no `Proofs/Bounded*`):

| pass         | simulation                         | clock                                  |
|--------------|------------------------------------|----------------------------------------|
| PanToCrep    | none in Flapjack                   | —                                      |
| CrepToLoop   | `crepToLoop_ncompile_correct`      | `+ ck`, ∃ ck                           |
| LoopToWord   | `compileCorrect`                   | exact (1:1)                            |
| WordToWord   | `compile_single_correct`           | same state (not glued)                 |
| WordToStack  | `compCorrect`                      | `+ extraClock`, ∃                      |
| StackRawCall | `compCorrectB` (this campaign)     | `extra ≤ source.clock`                 |
| StackAlloc   | identity on sections ≠ 6           | 0                                      |
| StackRemove  | `compCorrectZ`                     | `+0`, `+1` on final `halt`             |
| StackNames   | `compCorrect`                      | exact (1:1)                            |
| StackToLab   | `flattenCorrect`                   | **no** linear bound (proved)           |
| LabToTarget  | `compileCorrect`                   | `+ k`, ∃ k                             |

Long statements are re-exposed with `type_of%` so they stay definitionally the proved ones.
-/

namespace InitECandidate.Solver.FlapjackElevenPassSimulationAndClockGrandMaster

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang

variable {width : Nat} [NeZero width]

/-- StackNames flags derived from `StackRemove.stateRelHOL`. -/
theorem grand_stackNames_flags_from_stackRemove {C F : Type} {jump : Bool}
    {bounds : BitVec width × BitVec width} {pointer : Nat}
    {source target : StackSemStateFiniteExact width C F}
    (h : StackRemove.stateRelHOL jump bounds pointer source target) :
    ¬target.useAlloc ∧ ¬target.useStore ∧ ¬target.useStack ∧ target.clock = source.clock :=
  let f := StackRemoveToStackNamesStateRelAndClockBridge.stateRelHOL_target_flags h
  ⟨f.1, f.2.1, f.2.2.1,
    (StackRemoveToStackNamesStateRelAndClockBridge.stateRelHOL_compile_and_clock h).2⟩

/-- StackRawCall → StackAlloc → StackRemove → StackNames, final clock `≤ 2 * source.clock + 1`. -/
theorem grand_stackRawCall_to_stackNames_linear :
    type_of% @PanToStackNamesEndToEndLinearClockMaster.pancake_to_stackNames_end_to_end_linear_clock :=
  @PanToStackNamesEndToEndLinearClockMaster.pancake_to_stackNames_end_to_end_linear_clock

/-- Same chain outside `halt`: final clock `mid.clock + extra`, `extra ≤ source.clock`. -/
theorem grand_stackRawCall_to_stackNames_noHalt :
    type_of% @PanToStackNamesEndToEndLinearClockMaster.pancake_to_stackNames_noHalt_linear_clock :=
  @PanToStackNamesEndToEndLinearClockMaster.pancake_to_stackNames_noHalt_linear_clock

/-- CrepSem → LoopSem → WordSem → StackSem → … → StackNames. -/
theorem grand_crep_to_stackNames :
    type_of% @CrepToStackNamesAndLabToTargetEndToEndClockMaster.crep_to_stackNames_clock :=
  @CrepToStackNamesAndLabToTargetEndToEndClockMaster.crep_to_stackNames_clock

/-- LoopToWord is 1:1 in clock. -/
theorem grand_loopToWord_exact :
    type_of% @PanToWordToStackNamesSimulationAndClockMaster.loopToWord_exact_clock :=
  @PanToWordToStackNamesSimulationAndClockMaster.loopToWord_exact_clock

/-- StackToLab: no bound linear in StackSem ticks. -/
theorem grand_stackToLab_no_linear_bound {C F : Type}
    (s : StackSemStateFiniteExact width C F) (t : LabSem.State width C F)
    (h0 : s.clock = 0) (slope : Nat) :
    StackSemEvaluate.evaluate ((.skip : HolProg width), s) = (none, s) ∧
    (LabSem.evaluate {t with clock := slope * s.clock}).1 = .timeOut :=
  let e := StackRawCallToStackNamesAndStackToLabLinearBridge.stackToLab_no_linear_clock_bound s t h0 slope
  ⟨e.1, e.2.2⟩

/-- LabToTarget: target machine at `s1.clock + k`, ∃ k. -/
theorem grand_labToTarget :
    type_of% @LoopToWordToStackNamesAndLabToTargetClockMaster.labToTarget_clock_plus_k :=
  @LoopToWordToStackNamesAndLabToTargetClockMaster.labToTarget_clock_plus_k

end InitECandidate.Solver.FlapjackElevenPassSimulationAndClockGrandMaster
