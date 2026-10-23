import InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateDef
import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Compiler.Backend.StackRemove.Proofs.AllocationArithmetic
import Flapjack.Compiler.Backend.StackRemove.Proofs.BytearrayReads
import Flapjack.Compiler.Backend.StackRemove.Proofs.ExpressionSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.InstructionSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.LabelPreservation
import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryReads
import Flapjack.Compiler.Backend.StackRemove.Proofs.ProgCompEta
import Flapjack.Compiler.Backend.StackRemove.Proofs.RelationLaws
import Flapjack.Compiler.Backend.StackRemove.Proofs.ShiftSimulation
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeapWrites
import Flapjack.Compiler.Backend.StackRemove.Proofs.StackPointer
import Flapjack.Compiler.Backend.StackRemove.Proofs.StateUpdates
import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreHeapWrites
import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreNames
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordAddressArithmetic
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListExists
import Flapjack.Compiler.Backend.StackRemove.Proofs.WordStoreLaws
import Flapjack.Compiler.Backend.StackRemove.Proofs.WriteBytearrayFrame
import Flapjack.Compiler.Backend.StackRemove.StackAlloc
import Flapjack.Compiler.Backend.StackRemove.StackFree
import Flapjack.FiniteMap.MapKeys
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-! Zero-clock StackRemove simulations: `StackAlloc` / `StackFree` (guest `jump = false`)
and every non-recursive `StackRemove.CompCorrect` case except `storeConsts`. Each theorem
is the Flapjack case with its conclusion `∃ clock postTarget, evaluate (comp …,
{target with clock := clock + target.clock}) = …` strengthened to `∃ postTarget,
evaluate (comp …, target) = …`: the compiled code needs **no** extra clock. -/

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.StackAllocSimulation
open Flapjack.Compiler.Backend.StackRemove
open Flapjack
/-- Flapjack factoring of original single_stack_alloc successful post-relation
proof. No separately named HOL declaration corresponds to this helper. The
original available-space condition is discharged in the full theorem below;
all26 relation conjuncts are established rather than assumed. -/
theorem stateRelAllocStepZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (safe : count ≤ source.stackSpace) :
    stateRelHOL jump bounds pointer {source with stackSpace := source.stackSpace - count}
      (StackSemStateOps.setVar pointer
        (.word ((match target.regs.lookup pointer with | some (.word value) => value | _ => 0) - wordOffset count)) target) := by
  obtain ⟨base, baseLookup, lower, upper, pointerLookup, heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
  have arithmetic : (base + bytesInWord width * BitVec.ofNat width source.stackSpace) - wordOffset count =
      base + bytesInWord width * BitVec.ofNat width (source.stackSpace - count) := by
    have parts : BitVec.ofNat width source.stackSpace =
        BitVec.ofNat width (source.stackSpace - count) + BitVec.ofNat width count := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel safe]
    have offset : bytesInWord width * BitVec.ofNat width count = wordOffset count := by
      simp [bytesInWord, wordOffset, BitVec.ofNat_mul]
    rw [parts, BitVec.mul_add, offset, ← BitVec.add_assoc]
    exact BitVec.add_sub_cancel _ _
  have baseNe : pointer + 1 ≠ pointer := by omega
  have heapNe : pointer + 2 ≠ pointer := by omega
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have low : ∀ query, query < pointer →
      (target.regs.updateEq (pointer, .word (base + bytesInWord width * BitVec.ofNat width (source.stackSpace - count)))).lookup query = source.regs.lookup query := by
    intro query below
    have ne : query ≠ pointer := by omega
    simpa only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne, ite_false] using h18 query below
  simp only [stateRelHOL, StackSemStateOps.setVar, pointerLookup, arithmetic,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, baseNe, heapNe, ite_false, ite_true, baseLookup]
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,low,h19,h20,h21,h22,h23,Nat.le_trans (Nat.sub_le _ _) h24,
    h25.1,lower,upper,True.intro,heap⟩
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete original single_stack_alloc simulation, including both native
jump and conditional overflow modes and the original FFI/full-relation split.
Every original conjunct is retained and no target evaluation is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateSingleStackAllocZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      (result, postSource) = (if source.stackSpace < count then
        (some (.halt (.word 2)), StackSemStateOps.emptyEnv source)
        else (none, {source with stackSpace := source.stackSpace - count})) ∧
      count ≠ 0 ∧ count ≤ maxStackAlloc) :
    ∃ clock postTarget, clock ≤ (if source.stackSpace < count then 1 else 0) ∧
      StackSemEvaluate.evaluate (singleStackAlloc jump pointer count,
        {target with clock := target.clock + clock}) = (result, postTarget) ∧
      (if source.stackSpace < count then postTarget.ffi = postSource.ffi
       else stateRelHOL jump bounds pointer postSource postTarget) := by
  classical
  rcases hypothesis with ⟨relation, output, _nonzero, countBound⟩
  obtain ⟨base, baseLookup, lower, upper, pointerLookup, _heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
  have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spaceBound : source.stackSpace ≤ source.stack.length := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have comparison := AllocationArithmetic.allocationGuard base source.stackSpace source.stack.length count good lower upper spaceBound countBound
  have guard : Compiler.Encoders.Asm.wordCmpHOL .lower
      (base + bytesInWord width * BitVec.ofNat width source.stackSpace - wordOffset count) base =
      decide (source.stackSpace < count) := by
    simp only [Compiler.Encoders.Asm.wordCmpHOL, comparison]
  have codeLookup : sptLookup stackErrLab target.code = some (haltInst (BitVec.ofNat width 2)) := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have baseNe : pointer + 1 ≠ pointer := by omega
  by_cases overflow : source.stackSpace < count
  · rw [if_pos overflow] at output
    rcases Prod.mk.inj output with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    simp only [overflow, decide_true] at guard
    cases jump with
    | false =>
      refine ⟨1, StackSemStateOps.emptyEnv {target with clock := target.clock + 1}, by simp [overflow], ?_, ?_⟩
      · simp [singleStackAlloc,  StackSemStateOps.emptyEnv, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
          StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup,
          wordOpHOL, wordOp, StackSemControl.fixClock,
          StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          StackSemEvaluate.evaluate_ite,
          StackSemStateOps.getVar, StackSemStateOps.getVarImm, Compiler.Encoders.Asm.HolRegImm.toWordRegImm,
          wordSemWordCmp, baseLookup, guard,
            haltInst,
          StackSemEvaluate.evaluate_halt]
      · simpa [overflow, StackSemStateOps.emptyEnv] using relation.2.2.2.2.2.2.2.2.2.1
    | true =>
      refine ⟨1, StackSemStateOps.emptyEnv target, by simp [overflow], ?_, ?_⟩
      · simp [singleStackAlloc,  StackSemStateOps.emptyEnv, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
          StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup,
          wordOpHOL, wordOp, StackSemControl.fixClock,
          StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
           StackSemEvaluate.evaluate_jumpLower,
          StackSemStateOps.getVar,
           baseLookup, guard,
          StackSemControl.findCode, codeLookup, haltInst,
          StackSemEvaluate.evaluate_halt, StackSemStateOps.decClock, StackSemControl.badFunReturn]
      · simpa [overflow, StackSemStateOps.emptyEnv] using relation.2.2.2.2.2.2.2.2.2.1
  · rw [if_neg overflow] at output
    rcases Prod.mk.inj output with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, StackSemStateOps.setVar pointer
      (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace - wordOffset count)) target, by simp, ?_, ?_⟩
    · cases jump <;> simp [singleStackAlloc,  StackSemEvaluate.evaluate_seq,
        StackSemEvaluate.evaluate_inst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
        StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup, wordOpHOL, wordOp,
        StackSemControl.fixClock, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        StackSemEvaluate.evaluate_ite, StackSemEvaluate.evaluate_jumpLower, StackSemEvaluate.evaluate_skip,
        StackSemStateOps.getVar, StackSemStateOps.getVarImm, Compiler.Encoders.Asm.HolRegImm.toWordRegImm, wordSemWordCmp, baseLookup, guard, overflow]
    · rw [if_neg overflow]
      simpa only [pointerLookup] using stateRelAllocStepZ jump bounds pointer count source target relation (Nat.le_of_not_gt overflow)
/-- Source-local execution factoring for a successful native allocation chunk at any clock.
No standalone HOL declaration; guard facts are derived from the full relation. -/
theorem runSingleAvailableZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count clock : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (available : count ≤ source.stackSpace) (countBound : count ≤ maxStackAlloc) :
    StackSemEvaluate.evaluate (singleStackAlloc jump pointer count, {target with clock := clock}) =
      (none, StackSemStateOps.setVar pointer
        (.word ((match target.regs.lookup pointer with | some (.word word) => word | _ => 0) - wordOffset count))
        {target with clock := clock}) := by
  obtain ⟨base, baseLookup, lower, upper, pointerLookup, _heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
  have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spaceBound : source.stackSpace ≤ source.stack.length := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have comparison := AllocationArithmetic.allocationGuard base source.stackSpace source.stack.length count good lower upper spaceBound countBound
  have guard : Compiler.Encoders.Asm.wordCmpHOL .lower
      (base + bytesInWord width * BitVec.ofNat width source.stackSpace - wordOffset count) base =
      decide (source.stackSpace < count) := by
    simp only [Compiler.Encoders.Asm.wordCmpHOL, comparison]
  have overflow : ¬ source.stackSpace < count := Nat.not_lt.mpr available
  cases jump <;> simp [singleStackAlloc, StackSemEvaluate.evaluate_seq,
    StackSemEvaluate.evaluate_inst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
    StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup, wordOpHOL, wordOp,
    StackSemControl.fixClock, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    StackSemEvaluate.evaluate_ite, StackSemEvaluate.evaluate_jumpLower, StackSemEvaluate.evaluate_skip,
    StackSemStateOps.getVar, StackSemStateOps.getVarImm, Compiler.Encoders.Asm.HolRegImm.toWordRegImm,
    wordSemWordCmp, baseLookup, guard, overflow]
set_option maxRecDepth 2048 in
/-- Source-local strong-induction execution contract for the native recursive builder.
No standalone HOL declaration; this factors the original allocation proof. -/
theorem runAllocZ {width : Nat} [NeZero width] {C F : Type}
    (count : Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    ∃ clock postTarget, clock ≤ (if source.stackSpace < count then 1 else 0) ∧
      StackSemEvaluate.evaluate (StackRemove.stackAlloc jump pointer count, {target with clock := clock + target.clock}) =
        ((if source.stackSpace < count then some (.halt (.word 2)) else none), postTarget) ∧
      (if source.stackSpace < count then postTarget.ffi = source.ffi
       else stateRelHOL jump bounds pointer {source with stackSpace := source.stackSpace - count} postTarget) := by
  classical
  induction count using Nat.strongRecOn generalizing source target with
  | ind count ih =>
    by_cases zero : count = 0
    · subst count
      exact ⟨0, target, by simp, by simp [StackRemove.stackAlloc, StackSemEvaluate.evaluate_skip], by simpa using relation⟩
    by_cases small : count ≤ maxStackAlloc
    · let expectedSource := if source.stackSpace < count then StackSemStateOps.emptyEnv source
        else {source with stackSpace := source.stackSpace - count}
      obtain ⟨clock, postTarget, hc, run, post⟩ := evaluateSingleStackAllocZ jump bounds pointer count
        source target expectedSource (if source.stackSpace < count then some (.halt (.word 2)) else none)
        ⟨relation, by dsimp [expectedSource]; split <;> rfl, zero, small⟩
      refine ⟨clock, postTarget, hc, ?_, ?_⟩
      · rw [StackRemove.stackAlloc, if_neg zero, if_pos small]
        simpa only [Nat.add_comm] using run
      · by_cases overflow : source.stackSpace < count
        · simpa [overflow, expectedSource, StackSemStateOps.emptyEnv] using post
        · simpa [overflow, expectedSource] using post
    by_cases firstOverflow : source.stackSpace < maxStackAlloc
    · have overflow : source.stackSpace < count := by omega
      obtain ⟨clock, postTarget, hc, run, post⟩ := evaluateSingleStackAllocZ jump bounds pointer maxStackAlloc
        source target (StackSemStateOps.emptyEnv source) (some (.halt (.word 2)))
        ⟨relation, by rw [if_pos firstOverflow], by decide, Nat.le_refl _⟩
      have firstRun : StackSemEvaluate.evaluate (singleStackAlloc jump pointer maxStackAlloc,
          {target with clock := clock + target.clock}) = (some (.halt (.word 2)),postTarget) := by
        simpa only [Nat.add_comm] using run
      refine ⟨clock, (StackSemControl.fixClock {target with clock := clock + target.clock}
        ((some (.halt (.word 2)) : Option (StackSemResult width)), postTarget)).2,
        by simp only [firstOverflow, overflow, if_true] at hc ⊢; exact hc, ?_, ?_⟩
      · rw [StackRemove.stackAlloc, if_neg zero, if_neg small, StackSemEvaluate.evaluate_seq, firstRun]
        simp [StackSemControl.fixClock, overflow]
      · simpa [overflow, firstOverflow, StackSemControl.fixClock, StackSemStateOps.emptyEnv] using post
    · have available : maxStackAlloc ≤ source.stackSpace := Nat.le_of_not_gt firstOverflow
      let nextSource := {source with stackSpace := source.stackSpace - maxStackAlloc}
      let nextTarget := StackSemStateOps.setVar pointer
        (.word ((match target.regs.lookup pointer with | some (.word word) => word | _ => 0) - wordOffset maxStackAlloc)) target
      have nextRelation : stateRelHOL jump bounds pointer nextSource nextTarget :=
        stateRelAllocStepZ jump bounds pointer maxStackAlloc source target relation available
      obtain ⟨clock, postTarget, hc, run, post⟩ := ih (count - maxStackAlloc)
        (by simp only [maxStackAlloc] at *; omega) nextSource nextTarget nextRelation
      have overflowEq : nextSource.stackSpace < count - maxStackAlloc ↔ source.stackSpace < count := by
        dsimp [nextSource]; omega
      have subtractionEq : (source.stackSpace - maxStackAlloc) - (count - maxStackAlloc) = source.stackSpace - count := by omega
      refine ⟨clock, postTarget, by simpa only [overflowEq] using hc, ?_, ?_⟩
      · rw [StackRemove.stackAlloc, if_neg zero, if_neg small, StackSemEvaluate.evaluate_seq]
        have firstRun := runSingleAvailableZ jump bounds pointer maxStackAlloc (clock + target.clock)
          source target relation available (Nat.le_refl _)
        have presented : StackSemEvaluate.evaluate (singleStackAlloc jump pointer maxStackAlloc,
          {target with clock := clock + target.clock}) = (none, {nextTarget with clock := clock + nextTarget.clock}) := by
          simpa only [nextTarget, StackSemStateOps.setVar] using firstRun
        rw [presented]
        have clamp : StackSemControl.fixClock {target with clock := clock + target.clock}
            ((none : Option (StackSemResult width)), {nextTarget with clock := clock + nextTarget.clock}) =
            (none, {nextTarget with clock := clock + nextTarget.clock}) := by
          simp [StackSemControl.fixClock, nextTarget, StackSemStateOps.setVar]
        rw [clamp]
        simpa only [overflowEq] using run
      · simpa only [overflowEq, nextSource, subtractionEq] using post
attribute [local instance] Classical.propDecidable
/-- Full original arbitrary-count stack allocation simulation, including both
native overflow modes and the original universally quantified non-Halt branch. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackAllocZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target) :
    ∃ clock postTarget, clock ≤ 1 ∧ (result = none → clock = 0) ∧
      StackSemEvaluate.evaluate (StackRemove.stackAlloc jump pointer count,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (if ∀ word, result ≠ some (.halt word) then
        stateRelHOL jump bounds pointer postSource postTarget else postTarget.ffi = postSource.ffi) := by
  classical
  rcases hypothesis with ⟨sourceRun, _notError, relation⟩
  rw [StackSemEvaluate.evaluate_stackAlloc] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  obtain ⟨clock, postTarget, hc, targetRun, post⟩ := runAllocZ count jump bounds pointer source target relation
  by_cases overflow : source.stackSpace < count
  · rw [if_pos overflow] at sourceRun targetRun post
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨clock, postTarget, by simpa [overflow] using hc, by simp, targetRun, ?_⟩
    simpa [StackSemStateOps.emptyEnv] using post
  · rw [if_neg overflow] at sourceRun targetRun post
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    exact ⟨clock, postTarget, by simp [overflow] at hc; omega, fun _ => by simpa [overflow] using hc, targetRun, by simpa [relation.1] using post⟩
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.StackFreeSimulation
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation
open Flapjack.Compiler.Backend.StackRemove
open Flapjack
/-- Flapjack factoring of the full state relation transition in original
single-stack-free proof. It has no separately named HOL original: the original
proof unfolds the relation directly. The stack safety premise is discharged
from the original theorem; target evaluation is proved separately below. -/
theorem stateRelFreeStepZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (safe : source.stackSpace + count ≤ source.stack.length) :
    stateRelHOL jump bounds pointer {source with stackSpace := source.stackSpace + count}
      (StackSemStateOps.setVar pointer
        (.word ((match target.regs.lookup pointer with | some (.word value) => value | _ => 0) + wordOffset count)) target) := by
  obtain ⟨base, baseLookup, lower, upper, pointerLookup, heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
  have arithmetic : (base + bytesInWord width * BitVec.ofNat width source.stackSpace) + wordOffset count =
      base + bytesInWord width * BitVec.ofNat width (source.stackSpace + count) := by
    simp [wordOffset, bytesInWord, BitVec.ofNat_mul, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
  have baseNe : pointer + 1 ≠ pointer := by omega
  have heapNe : pointer + 2 ≠ pointer := by omega
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have low : ∀ query, query < pointer →
      (target.regs.updateEq (pointer, .word (base + bytesInWord width * BitVec.ofNat width (source.stackSpace + count)))).lookup query = source.regs.lookup query := by
    intro query below
    have ne : query ≠ pointer := by omega
    simpa only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne, ite_false] using h18 query below
  simp only [stateRelHOL, StackSemStateOps.setVar, pointerLookup, arithmetic,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, baseNe, heapNe, ite_false, ite_true, baseLookup]
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,low,h19,h20,h21,h22,h23,safe,
    h25.1,lower,upper,True.intro,heap⟩
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original single_stack_free simulation with exactly its original
relation, output-state, stack-safety, nonzero and chunk-bound conjuncts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateSingleStackFreeZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      (result, postSource) = (none, {source with stackSpace := source.stackSpace + count}) ∧
      ¬ source.stack.length < source.stackSpace + count ∧ count ≠ 0 ∧ count ≤ maxStackAlloc) :
    ∃ postTarget,
      StackSemEvaluate.evaluate (singleStackFree pointer count,
        target) = (result, postTarget) ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨relation, output, safe, _nonzero, _small⟩
  rcases Prod.mk.inj output with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  obtain ⟨base, _baseLookup, _lower, _upper, pointerLookup, _heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  have lookup : target.regs.lookup pointer =
      some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) := pointerLookup
  refine ⟨StackSemStateOps.setVar pointer
    (.word ((base + bytesInWord width * BitVec.ofNat width source.stackSpace) + wordOffset count)) target, ?_, ?_⟩
  · simp [singleStackFree, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, lookup,
      wordOpHOL, wordOp]
  · simpa only [lookup] using stateRelFreeStepZ jump bounds pointer count source target
      relation (Nat.le_of_not_gt safe)
/-- Flapjack-specific native execution/update factoring for the original
recursive StackFree proof; no independently named HOL declaration is claimed. -/
theorem setVarExistingZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register : Nat) (value : WordLocW width)
    (lookup : state.regs.lookup register = some value) :
    StackSemStateOps.setVar register value state = state := by
  have maps : state.regs.updateEq (register,value) = state.regs := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases same : query = register
    · subst query; simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, lookup]
    · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same]
  simp [StackSemStateOps.setVar, maps]
/-- Flapjack-specific native execution/update factoring for the original
recursive StackFree proof; no independently named HOL declaration is claimed. -/
theorem setVarTwiceZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register : Nat) (first second : WordLocW width) :
    StackSemStateOps.setVar register second (StackSemStateOps.setVar register first state) =
      StackSemStateOps.setVar register second state := by
  have maps : (state.regs.updateEq (register, first)).updateEq (register, second) =
      state.regs.updateEq (register, second) := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases same : query = register <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same]
  simp [StackSemStateOps.setVar, maps]
/-- Flapjack-specific native execution/update factoring for the original
recursive StackFree proof; no independently named HOL declaration is claimed. -/
theorem runSingleZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register count : Nat) (value : BitVec width)
    (lookup : state.regs.lookup register = some (.word value)) :
    StackSemEvaluate.evaluate (singleStackFree register count, state) =
      (none, StackSemStateOps.setVar register (.word (value + wordOffset count)) state) := by
  simp [singleStackFree, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, lookup, wordOpHOL, wordOp]
/-- Flapjack-specific native execution/update factoring for the original
recursive StackFree proof; no independently named HOL declaration is claimed. -/
theorem runFreeZ {width : Nat} [NeZero width] {C F : Type}
    (count register : Nat) (state : StackSemStateFiniteExact width C F) (value : BitVec width)
    (lookup : state.regs.lookup register = some (.word value)) :
    StackSemEvaluate.evaluate (stackFree register count, state) =
      (none, StackSemStateOps.setVar register (.word (value + wordOffset count)) state) := by
  induction count using Nat.strongRecOn generalizing state value with
  | ind count ih =>
    rw [stackFree]
    split
    · rename_i zero
      subst count
      simp [StackSemEvaluate.evaluate_skip, wordOffset, setVarExistingZ state register (.word value) lookup]
    · split
      · exact runSingleZ state register count value lookup
      · rw [StackSemEvaluate.evaluate_seq, runSingleZ state register maxStackAlloc value lookup]
        simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        have nextLookup : (StackSemStateOps.setVar register (.word (value + wordOffset maxStackAlloc)) state).regs.lookup register =
            some (.word (value + wordOffset maxStackAlloc)) := by
          simp [StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        change StackSemEvaluate.evaluate (stackFree register (count - maxStackAlloc),
          StackSemStateOps.setVar register (.word (value + wordOffset maxStackAlloc)) state) =
          (none, StackSemStateOps.setVar register (.word (value + wordOffset count)) state)
        rw [ih (count - maxStackAlloc) (by simp only [maxStackAlloc] at *; omega) _ _ nextLookup]
        rw [setVarTwiceZ]
        have offsets : (wordOffset maxStackAlloc : BitVec width) + wordOffset (count - maxStackAlloc) = wordOffset count := by
          rw [wordOffset, wordOffset, wordOffset, ← BitVec.ofNat_add]
          have countEq : maxStackAlloc + (count - maxStackAlloc) = count := by omega
          rw [← Nat.mul_add, countEq]
        rw [BitVec.add_assoc, offsets]
/-- Full original arbitrary-count recursive stack_free simulation. Source
non-error establishes stack safety; all generated chunks are executed and the
complete post-state relation is derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackFreeZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target) :
    ∃ postTarget,
      StackSemEvaluate.evaluate (stackFree pointer count,
        target) = (result, postTarget) ∧
      stateRelHOL jump bounds pointer postSource postTarget := by
  rcases hypothesis with ⟨sourceRun, notError, relation⟩
  rw [StackSemEvaluate.evaluate_stackFree] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases safe : source.stack.length < source.stackSpace + count
  · rw [if_pos safe] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · rw [if_neg safe] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨base, _baseLookup, _lower, _upper, pointerLookup, _heap⟩ :=
      StackPointer.stateRelGetVarK jump bounds pointer source target relation
    have lookup : target.regs.lookup pointer =
        some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) := pointerLookup
    refine ⟨StackSemStateOps.setVar pointer
      (.word ((base + bytesInWord width * BitVec.ofNat width source.stackSpace) + wordOffset count)) target, ?_, ?_⟩
    · simpa only [Nat.zero_add] using runFreeZ count pointer target _ lookup
    · simpa only [lookup, relation.1] using stateRelFreeStepZ jump bounds pointer count source target relation (Nat.le_of_not_gt safe)
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Atoms
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Skip case with its unchanged existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSkipZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.skip : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .skip,
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  rw [StackSemEvaluate.evaluate_skip] at sourceRun
  rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  refine ⟨target, ?_, relation⟩
  simp [comp, StackSemEvaluate.evaluate_skip]

/-- Full original Halt case with its unchanged existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectHaltZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.halt register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.halt register) : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.halt register),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have registerBound : register < pointer := bound
  have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, registerBound⟩
  rw [StackSemEvaluate.evaluate_halt] at sourceRun
  cases sourceLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [sourceLookup] at sourceRun
    have resultEq := (Prod.mk.inj sourceRun).1
    exact (notError resultEq.symm).elim
  | some value =>
    rw [sourceLookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have targetLookup : StackSemStateOps.getVar register target = some value :=
      lookupEq.symm.trans sourceLookup
    refine ⟨StackSemStateOps.emptyEnv target, ?_, ?_⟩
    · simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_halt register target).trans
          (by rw [targetLookup])
    · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1

/-- Full original Alloc case with its unchanged existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectAllocZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.alloc register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.alloc register) : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.alloc register),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  have noAlloc := relation
  simp only [stateRelHOL] at noAlloc
  have flag := noAlloc.2.2.2.2.2.1
  rw [StackSemEvaluate.evaluate_alloc] at sourceRun
  simp only [flag, Bool.not_false, ite_true] at sourceRun
  have resultEq := (Prod.mk.inj sourceRun).1
  exact (notError resultEq.symm).elim
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Atoms

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Control
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.Control
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Tick case, with no added successful-run or clock premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectTickZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.tick, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.tick : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .tick,
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [StackSemEvaluate.evaluate_tick] at sourceRun
  by_cases zero : source.clock = 0
  · simp only [zero, ite_true] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨StackSemStateOps.emptyEnv target, ?_, ?_⟩
    · simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_tick target).trans (by simp [clocks, zero])
    · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
  · simp only [zero, ite_false] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨StackSemStateOps.decClock target, ?_, ?_⟩
    · simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_tick target).trans (by simp [clocks, zero])
    · exact RelationLaws.stateRelDecClock jump bounds pointer source target relation

/-- Full original Return case, with no added successful-run or clock premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectReturnZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.ret register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.ret register) : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.ret register),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have registerBound : register < pointer := bound
  have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, registerBound⟩
  rw [StackSemEvaluate.evaluate_ret] at sourceRun
  cases sourceLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [sourceLookup] at sourceRun
    have resultEq := (Prod.mk.inj sourceRun).1
    exact (notError resultEq.symm).elim
  | some value =>
    cases value with
    | word value =>
      rw [sourceLookup] at sourceRun
      have resultEq := (Prod.mk.inj sourceRun).1
      exact (notError resultEq.symm).elim
    | loc block offset =>
      rw [sourceLookup] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      have targetLookup : StackSemStateOps.getVar register target = some (.loc block offset) :=
        lookupEq.symm.trans sourceLookup
      refine ⟨target, ?_, relation⟩
      simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_ret register target).trans (by rw [targetLookup])

/-- Full original Raise case, with no added successful-run or clock premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectRaiseZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.raise register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.raise register) : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.raise register),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have registerBound : register < pointer := bound
  have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, registerBound⟩
  rw [StackSemEvaluate.evaluate_raise] at sourceRun
  cases sourceLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [sourceLookup] at sourceRun
    have resultEq := (Prod.mk.inj sourceRun).1
    exact (notError resultEq.symm).elim
  | some value =>
    cases value with
    | word value =>
      rw [sourceLookup] at sourceRun
      have resultEq := (Prod.mk.inj sourceRun).1
      exact (notError resultEq.symm).elim
    | loc block offset =>
      rw [sourceLookup] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      have targetLookup : StackSemStateOps.getVar register target = some (.loc block offset) :=
        lookupEq.symm.trans sourceLookup
      refine ⟨target, ?_, relation⟩
      simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_raise register target).trans (by rw [targetLookup])

/-- Full original Break case, with no added successful-run or clock premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectBreakZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (label : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.break label), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.break label) : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.break label),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  rw [StackSemEvaluate.evaluate_break] at sourceRun
  rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  refine ⟨target, ?_, relation⟩
  simp [comp, StackSemEvaluate.evaluate_break]

/-- Full original Continue case, with no added successful-run or clock premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectContinueZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (label : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.continue label), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.continue label) : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.continue label),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  rw [StackSemEvaluate.evaluate_continue] at sourceRun
  rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  refine ⟨target, ?_, relation⟩
  simp [comp, StackSemEvaluate.evaluate_continue]
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Control

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Locations
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.Locations
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine complete LocValue case: non-error source evaluation establishes
its location check; the full code relation transports it, and bounded register
assignment preserves every original post-state conjunct. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectLocValueZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (register first second : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate ((.locValue register first second), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.locValue register first second) : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.locValue register first second),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  classical
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  rw [StackSemEvaluate.evaluate_locValue] at sourceRun
  by_cases checked : StackSem.locCheckExact source.code (first, second)
  · rw [if_pos checked] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have codeRelation : codeRelHOL jump bounds pointer source.code target.code :=
      relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have targetChecked := LabelPreservation.codeRelLocCheck jump bounds pointer
      source.code target.code first second ⟨codeRelation, checked⟩
    have registerBound : register < pointer := bound
    refine ⟨StackSemStateOps.setVar register (.loc first second) target, ?_, ?_⟩
    · simp [comp, StackSemEvaluate.evaluate_locValue, targetChecked]
    · exact StateUpdates.stateRelSetVar jump bounds pointer register (.loc first second)
        source target ⟨relation, registerBound⟩
  · rw [if_neg checked] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Locations

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Instructions
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.Instructions
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Canonical imported-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full genuine Inst case of comp_correct: the original non-error premise
excludes native instruction failure. Full instruction simulation derives the
target execution with zero extra clock and the complete post-state relation.
Native evaluator closure retains inherited reals_as_rational_cuts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectInstZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (instruction : HolInst width)
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.inst instruction) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.inst instruction),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  rw [StackSemEvaluate.evaluate_inst] at sourceRun
  cases instRun : StackSemInst.instHOL instruction source with
  | none =>
    rw [instRun] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some state =>
    rw [instRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have instructionBound : StackProps.regBoundInst instruction pointer := bound
    obtain ⟨postTarget, targetRun, postRelation⟩ :=
      InstructionSimulation.stateRelInst jump bounds pointer instruction source target state
        ⟨relation, instructionBound, instRun⟩
    refine ⟨postTarget, ?_, postRelation⟩
    simpa only [comp, Nat.zero_add] using
      (StackSemEvaluate.evaluate_inst instruction target).trans (by rw [targetRun])
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Instructions

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.HeapOperation
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.HeapOperation
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Canonical imported-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine full OpCurrHeap case: both native operands and target execution
are derived from the original full state relation and register bound. The full
evaluator closure retains inherited reals_as_rational_cuts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectOpCurrHeapZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (operator : BinOp) (destination input : Nat)
    (hypothesis : StackSemEvaluate.evaluate (.opCurrHeap operator destination input, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.opCurrHeap operator destination input : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.opCurrHeap operator destination input),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  have regEq : target.regs.lookup input = source.regs.lookup input :=
    relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 input bound.2
  have heapEq : target.regs.lookup (pointer + 2) = source.store.lookup .currHeap :=
    relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have expressionEq : StackSemExpressions.wordExp target (.op operator [.var input, .var (pointer + 2)]) =
      StackSemExpressions.wordExp source (.op operator [.var input, .lookup .currHeap]) := by
    simp [StackSemExpressions.wordExp, regEq, heapEq]
  rw [StackSemEvaluate.evaluate_opCurrHeap] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases valueRun : StackSemExpressions.wordExp source (.op operator [.var input, .lookup .currHeap]) with
  | none =>
    rw [valueRun] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [valueRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨StackSemStateOps.setVar destination (.word value) target, ?_, ?_⟩
    · have different : pointer + 2 ≠ input := by have := bound.2; omega
      simp only [comp, Nat.zero_add, StackSemEvaluate.evaluate_inst,
        StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, Option.join_some]
      simp [different, StackSemExpressions.assign, expressionEq, valueRun]
    · exact StateUpdates.stateRelSetVar jump bounds pointer destination (.word value) source target
        ⟨relation, bound.1⟩
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.HeapOperation

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StoreTransfers
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreTransfers
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm

/-- Canonical imported-state codec witness, Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Flapjack proof factoring of the original Set CurrHeap case. Its only
relation premise is the full original state relation, with no added bound,
frame, successful-evaluation or post-state relation assumption. -/
theorem stateRelSetCurrHeapZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (value : WordLocW width) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer (StackSemStateOps.setStore .currHeap value source)
      (StackSemStateOps.setVar (pointer + 2) value target) := by
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  have lookupPreserved : ∀ query, query < pointer →
      (target.regs.updateEq (pointer + 2, value)).lookup query = source.regs.lookup query := by
    intro query below
    have different : query ≠ pointer + 2 := by omega
    simpa only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different, ite_false] using h18 query below
  have pointerNe : pointer ≠ pointer + 2 := by omega
  have baseNe : pointer + 1 ≠ pointer + 2 := by omega
  have bitmapNe : (WordStore.bitmapBase : WordStoreHOL) ≠ WordStore.currHeap := by
    intro equal
    cases equal
  simp only [stateRelHOL, StackSemStateOps.setStore, StackSemStateOps.setVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, pointerNe, baseNe, bitmapNe, ite_false,
    ite_true]
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    lookupPreserved, h19, h20, True.intro, h22, ?_, h24, ?_⟩
  · exact h23
  · simpa only [WordStoreLaws.wordStoreCurrHeap] using h25

/-- Flapjack proof factoring of the original non-CurrHeap Set branch.
The name exclusions and base lookup are discharged by the original bound and
full state relation in the genuine constructor theorem. -/
theorem stateRelSetStoreZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (name : StoreName) (value : WordLocW width) (base : BitVec width)
    (source target : StackSemStateFiniteExact width C F)
    (notCurrHeap : name ≠ .currHeap) (notBitmapBase : name ≠ .bitmapBase)
    (baseLookup : target.regs.lookup (pointer + 1) = some (.word base))
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer
      (StackSemStateOps.setStore (StackSemRegisterTransfers.storeOfSyntax name) value source)
      {target with memory := fun key => if key = base + storeOffset name then value else target.memory key} := by
  have currNe : WordStore.currHeap ≠ StackSemRegisterTransfers.storeOfSyntax name := by
    intro equal
    have names := congrArg StackSemRegisterTransfers.storeToSyntax equal
    simp only [StackSemRegisterTransfers.storeToSyntax_storeOfSyntax] at names
    exact notCurrHeap names.symm
  have bitmapNe : WordStore.bitmapBase ≠ StackSemRegisterTransfers.storeOfSyntax name := by
    intro equal
    have names := congrArg StackSemRegisterTransfers.storeToSyntax equal
    simp only [StackSemRegisterTransfers.storeToSyntax_storeOfSyntax] at names
    exact notBitmapBase names.symm
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  simp only [stateRelHOL, StackSemStateOps.setStore,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, currNe, bitmapNe, ite_false]
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17,
    h18, h19, h20, h21, h22, h23, h24, ?_⟩
  simp only [baseLookup] at h25 ⊢
  refine ⟨h25.1, h25.2.1, h25.2.2.1, h25.2.2.2.1, ?_⟩
  have written := StoreHeapWrites.storeWriteLemma name source target.memory
    (fun address => target.mdomain address = true) value base
    ⟨StoreNames.nameCases name notCurrHeap, by
      simpa only [List.length_append, Nat.add_comm] using h25.2.2.2.2⟩
  simpa only [List.length_append, Nat.add_comm] using written


/-- Full genuine Get case: original non-error excludes absent source store
lookup, and the complete state relation derives reserved-register or full-heap
load execution before establishing the full post-state relation. The total
evaluator retains inherited reals_as_rational_cuts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectGetZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat) (name : StoreName)
    (hypothesis : StackSemEvaluate.evaluate (.get register name, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.get register name : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.get register name),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  rw [StackSemEvaluate.evaluate_get] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases lookup : source.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) with
  | none =>
    rw [lookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [lookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨StackSemStateOps.setVar register value target, ?_, ?_⟩
    · by_cases current : name = .currHeap
      · subst name
        have heapLookup := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        simp only [StackSemRegisterTransfers.storeOfSyntax] at lookup
        rw [lookup] at heapLookup
        simp [comp, moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
          StackSemIntegerInstructions.instInteger, heapLookup]
      · have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        dsimp only at heaps
        cases baseLookup : target.regs.lookup (pointer + 1) with
        | none => simp only [baseLookup] at heaps; exact heaps.2.elim
        | some baseValue =>
          cases baseValue with
          | loc block offset => simp only [baseLookup] at heaps; exact heaps.2.elim
          | word base =>
            simp only [baseLookup] at heaps
            have load := StoreHeapReads.memLoadLemma name source target value base
              ⟨StoreNames.nameCases name current, lookup, by
                simpa only [List.length_append, Nat.add_comm] using heaps.2.2.2.2⟩
            have expression : StackSemExpressions.wordExp target
                (.op .add [.var (pointer + 1), .const (storeOffset name)]) =
                some (base + storeOffset name) := by
              simp [StackSemExpressions.wordExp, baseLookup, wordOpHOL, wordOp]
            simp [comp, current, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
              StackSemIntegerInstructions.instInteger, expression, load]
    · exact StateUpdates.stateRelSetVar jump bounds pointer register value source target
        ⟨relation, bound⟩

/-- Full genuine Set case: the original bound excludes BitmapBase. CurrHeap
updates the reserved target register; every other name uses the full native
store heap write law. Target execution and all post-state relation conjuncts
are derived. The total evaluator retains inherited reals_as_rational_cuts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSetZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat) (name : StoreName)
    (hypothesis : StackSemEvaluate.evaluate (.set name register, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.set name register : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.set name register),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  rw [StackSemEvaluate.evaluate_set] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases lookup : StackSemStateOps.getVar register source with
  | none =>
    rw [lookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [lookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have getVarEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
      ⟨relation, bound.1⟩
    have targetLookup : target.regs.lookup register = some value := by
      simpa only [StackSemStateOps.getVar] using getVarEq.symm.trans lookup
    by_cases current : name = .currHeap
    · subst name
      refine ⟨StackSemStateOps.setVar (pointer + 2) value target, ?_, ?_⟩
      · simp [comp, moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
          StackSemIntegerInstructions.instInteger, targetLookup]
      · exact stateRelSetCurrHeapZ jump bounds pointer value source target relation
    · have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      dsimp only at heaps
      cases baseLookup : target.regs.lookup (pointer + 1) with
      | none => simp only [baseLookup] at heaps; exact heaps.2.elim
      | some baseValue =>
        cases baseValue with
        | loc block offset => simp only [baseLookup] at heaps; exact heaps.2.elim
        | word base =>
          simp only [baseLookup] at heaps
          have domain := StoreHeapReads.memLoadLemma2 name source target base
            ⟨StoreNames.nameCases name current, by
              simpa only [List.length_append, Nat.add_comm] using heaps.2.2.2.2⟩
          have expression : StackSemExpressions.wordExp target
              (.op .add [.var (pointer + 1), .const (storeOffset name)]) =
              some (base + storeOffset name) := by
            simp [StackSemExpressions.wordExp, baseLookup, wordOpHOL, wordOp]
          refine ⟨{target with memory := fun key =>
            if key = base + storeOffset name then value else target.memory key}, ?_, ?_⟩
          · simp [comp, current, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
              StackSemIntegerInstructions.instInteger, expression, StackSemStateOps.getVar,
              targetLookup, StackSemStateOps.memStore, domain]
          · exact stateRelSetStoreZ jump bounds pointer name value base source target
              current bound.2 baseLookup relation
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StoreTransfers

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemory
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemory
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Flapjack primitive-load execution factoring; the full constructor below
 derives both lookup and memory-read premises from the source relation.
No standalone HOL declaration is claimed. -/
theorem runLoadZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (destination baseReg : Nat)
    (base offset : BitVec width) (value : WordLocW width)
    (lookup : state.regs.lookup baseReg = some (.word base))
    (read : StackSemStateOps.memLoad (base + offset) state = some value) :
    StackSemEvaluate.evaluate (.inst (.mem .load destination (.addr baseReg offset)), state) =
      (none, StackSemStateOps.setVar destination value state) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.wordExp,
    lookup, wordOpHOL, wordOp, read]
/-- Genuine full original StackLoad compiler constructor: direct and large-offset
paths derive native execution and the complete postrelation from the original
four premises. There is no successful target-load or target-state premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackLoadZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackLoad register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackLoad register count : HolProg width) pointer) :
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoad register count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackLoad] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases bound : source.stackSpace + count < source.stack.length
  · rw [dif_pos bound] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
    change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
    have addressEq : base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count =
        base + wordOffset (source.stackSpace + count) := by
      simp [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
    have read : StackSemStateOps.memLoad
        (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count) target =
        some source.stack[source.stackSpace + count] := by
      rw [addressEq]
      exact reads (source.stackSpace + count) bound
    refine ⟨StackSemStateOps.setVar register source.stack[source.stackSpace + count] target, ?_, ?_⟩
    · try simp only [Nat.zero_add]
      rw [comp]
      split
      · exact runLoadZ target register pointer _ _ _ pointerLookup read
      · have moveRun : StackSemEvaluate.evaluate (moveInst register pointer, target) =
            (none, StackSemStateOps.setVar register
              (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) target) := by
          simp [moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
            StackSemIntegerInstructions.instInteger, pointerLookup]
        rw [StackSemEvaluate.evaluate_seq, moveRun]
        simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        let initial := StackSemStateOps.setVar register
          (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) target
        have initialLookup : initial.regs.lookup register =
            some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) := by
          simp [initial, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        change StackSemEvaluate.evaluate (stackLoad register count, initial) = _
        rw [stackLoad, StackSemEvaluate.evaluate_seq,
          ShiftSimulation.evaluateUpshift count register initial _ initialLookup]
        simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
        let shifted := StackSemStateOps.setVar register
          (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count)) initial
        have shiftedLookup : shifted.regs.lookup register =
            some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count)) := by
          simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        change StackSemEvaluate.evaluate (.inst (.mem .load register (.addr register 0)), shifted) = _
        have shiftedRead : StackSemStateOps.memLoad
            (base + bytesInWord width * BitVec.ofNat width source.stackSpace + wordOffset count + 0) shifted =
            some source.stack[source.stackSpace + count] := by
          simpa [shifted, initial, StackSemStateOps.memLoad, StackSemStateOps.setVar] using read
        rw [runLoadZ shifted register register _ 0 _ shiftedLookup shiftedRead]
        simp only [shifted, initial, setVarTwiceZ]
        rfl
    · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
        source.stack[source.stackSpace + count] source target ⟨relation, lower⟩
  · rw [dif_neg bound] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
/-- Flapjack primitive-store execution factoring. The full constructor derives
the original register value, pointer lookup and memory-domain facts rather
than taking them as compiler-correctness premises. No standalone HOL declaration. -/
theorem runStoreZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register baseReg : Nat)
    (base offset : BitVec width) (value : WordLocW width)
    (baseLookup : state.regs.lookup baseReg = some (.word base))
    (valueLookup : state.regs.lookup register = some value)
    (domain : state.mdomain (base + offset) = true) :
    StackSemEvaluate.evaluate (.inst (.mem .store register (.addr baseReg offset)), state) =
      (none, {state with memory := fun key => if key = base + offset then value else state.memory key}) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.wordExp,
    StackSemStateOps.getVar, baseLookup, valueLookup, wordOpHOL, wordOp,
    StackSemStateOps.memStore, domain]
/-- Genuine full original StackStore constructor, including direct store and
upshift/store/downshift fallback. The actual target memory update and exact
pointer restoration establish the full post-state relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackStoreZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register count pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackStore register count, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackStore register count : HolProg width) pointer) :
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStore register count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackStore] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  by_cases outsideBounds : source.stack.length ≤ source.stackSpace + count
  · rw [if_pos outsideBounds] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · rw [if_neg outsideBounds] at sourceRun
    cases sourceLookup : StackSemStateOps.getVar register source with
    | none =>
      rw [sourceLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some value =>
      rw [sourceLookup] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      have safe : source.stackSpace + count < source.stack.length := Nat.lt_of_not_ge outsideBounds
      have different : register ≠ pointer := by omega
      have valueLookup : target.regs.lookup register = some value := by
        change StackSemStateOps.getVar register target = some value
        rw [← RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower⟩]
        exact sourceLookup
      obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
      let pointerWord := base + bytesInWord width * BitVec.ofNat width source.stackSpace
      change target.regs.lookup pointer = some (.word pointerWord) at pointerLookup
      have addressEq : pointerWord + wordOffset count = base + wordOffset (source.stackSpace + count) := by
        dsimp [pointerWord]
        simp [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
      have read : StackSemStateOps.memLoad (pointerWord + wordOffset count) target =
          some source.stack[source.stackSpace + count] := by
        rw [addressEq]
        exact reads _ safe
      have domain : target.mdomain (pointerWord + wordOffset count) = true := by
        by_contra outside
        simp [StackSemStateOps.memLoad, outside] at read
      let updated := {target with memory := fun key => if key = pointerWord + wordOffset count then value else target.memory key}
      refine ⟨updated, ?_, ?_⟩
      · try simp only [Nat.zero_add]
        rw [comp]
        split
        · exact runStoreZ target register pointer _ _ value pointerLookup valueLookup domain
        · rw [stackStore, StackSemEvaluate.evaluate_seq,
            ShiftSimulation.evaluateUpshift count pointer target pointerWord pointerLookup]
          simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
          let shifted := StackSemStateOps.setVar pointer (.word (pointerWord + wordOffset count)) target
          have shiftedPointer : shifted.regs.lookup pointer = some (.word (pointerWord + wordOffset count)) := by
            simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          have shiftedValue : shifted.regs.lookup register = some value := by
            simpa [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using valueLookup
          have shiftedDomain : shifted.mdomain (pointerWord + wordOffset count + 0) = true := by
            simpa [shifted, StackSemStateOps.setVar] using domain
          change StackSemEvaluate.evaluate (.seq (.inst (.mem .store register (.addr pointer 0)))
            (downshift pointer count), shifted) = _
          rw [StackSemEvaluate.evaluate_seq,
            runStoreZ shifted register pointer _ 0 value shiftedPointer shiftedValue shiftedDomain]
          simp only [StackSemControl.fixClock, Nat.min_self]
          let written := {shifted with memory := fun key => if key = pointerWord + wordOffset count + 0 then value else shifted.memory key}
          have writtenPointer : written.regs.lookup pointer = some (.word (pointerWord + wordOffset count)) := shiftedPointer
          change StackSemEvaluate.evaluate (downshift pointer count, written) = _
          rw [ShiftSimulation.evaluateDownshift count pointer written _ writtenPointer]
          simp only [BitVec.add_sub_cancel]
          have restore : StackSemStateOps.setVar pointer (.word pointerWord) shifted = target := by
            dsimp [shifted]
            rw [setVarTwiceZ, setVarExistingZ target pointer (.word pointerWord) pointerLookup]
          let newMemory : BitVec width → WordLocW width :=
            fun key => if key = (pointerWord + wordOffset count + 0) then value else target.memory key
          change (none, {(StackSemStateOps.setVar pointer (.word pointerWord) shifted) with memory := newMemory}) = _
          rw [restore]
          simp [updated, newMemory]
      · simpa only [updated, relation.1, Nat.add_comm] using
          StackHeapWrites.stateRelStackStore jump bounds pointer count source target source.stack pointerWord
            (pointerWord + wordOffset count) value
            ⟨relation, rfl, pointerLookup, safe, by rw [WordAddressArithmetic.wordOffsetEq]⟩
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemory

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemoryAny
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackMemoryAny
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-local alignment factoring: the original successful Any-case guard
and good word dimension supply the exact byte offset. No standalone HOL
original is claimed. -/
theorem alignedOffsetZ {width : Nat} [NeZero width] (word : BitVec width)
    (good : goodDimindex width)
    (aligned : (word >>> wordShiftAmount width) <<< wordShiftAmount width = word) :
    wordOffset (word >>> wordShiftAmount width).toNat = word := by
  rw [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.mul_comm]
  rw [← WordAddressArithmetic.lslWordShift (word >>> wordShiftAmount width) good]
  exact aligned
/-- Flapjack native execution factoring for the original Any constructors;
all lookup facts are derived inside the full cases below. No standalone HOL
declaration is claimed. -/
theorem runMoveAddZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (word pointerWord : BitVec width)
    (indexLookup : state.regs.lookup index = some (.word word))
    (pointerLookup : state.regs.lookup pointer = some (.word pointerWord))
    (different : pointer ≠ register) :
    StackSemEvaluate.evaluate (.seq (moveInst register index) (addInst register pointer), state) =
      (none, StackSemStateOps.setVar register (.word (word + pointerWord)) state) := by
  have moveRun : StackSemEvaluate.evaluate (moveInst register index, state) =
      (none, StackSemStateOps.setVar register (.word word) state) := by
    simp [moveInst, moveHOL, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, indexLookup]
  let copied := StackSemStateOps.setVar register (.word word) state
  have addRun : StackSemEvaluate.evaluate (addInst register pointer, copied) =
      (none, StackSemStateOps.setVar register (.word (word + pointerWord)) copied) := by
    simp [addInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign, StackSemExpressions.wordExp,
      copied, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
      different, pointerLookup, wordOpHOL, wordOp]
  rw [StackSemEvaluate.evaluate_seq, moveRun]
  simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
  change StackSemEvaluate.evaluate (addInst register pointer, copied) = _
  rw [addRun, setVarTwiceZ]
  rfl
/-- Genuine full original StackLoadAny compiler constructor. The source
alignment/index guard derives actual native heap access and the complete
postrelation; no target-access, postheap or pointer-restoration premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackLoadAnyZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackLoadAny register index, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackLoadAny register index : HolProg width) pointer) :
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackLoadAny register index),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer ∧ index < pointer at lower
  rw [StackSemEvaluate.evaluate_stackLoadAny] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  cases indexLookup : StackSemStateOps.getVar index source with
  | none =>
    rw [indexLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    cases value with
    | loc block offset =>
      rw [indexLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | word word =>
      rw [indexLookup] at sourceRun
      dsimp only at sourceRun
      by_cases valid : source.stackSpace + (word >>> wordShiftAmount width).toNat < source.stack.length ∧
          (word >>> wordShiftAmount width) <<< wordShiftAmount width = word
      · rw [dif_pos valid] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
        subst result
        subst postSource
        have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have offsetEq := alignedOffsetZ word good valid.2
        have targetIndex : target.regs.lookup index = some (.word word) := by
          change StackSemStateOps.getVar index target = some (.word word)
          rw [← RelationLaws.stateRelGetVar jump bounds pointer index source target ⟨relation, lower.2⟩]
          exact indexLookup
        obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
        let pointerWord := base + bytesInWord width * BitVec.ofNat width source.stackSpace
        change target.regs.lookup pointer = some (.word pointerWord) at pointerLookup
        have addressEq : word + pointerWord = base + wordOffset (source.stackSpace + (word >>> wordShiftAmount width).toNat) := by
          calc
            word + pointerWord = wordOffset (word >>> wordShiftAmount width).toNat + pointerWord := by
              rw [offsetEq]
            _ = _ := by
              dsimp [pointerWord]
              simp only [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add]
              rw [BitVec.add_comm (bytesInWord width * BitVec.ofNat width (word >>> wordShiftAmount width).toNat),
                BitVec.add_assoc]
        let entry := source.stack[source.stackSpace + (word >>> wordShiftAmount width).toNat]
        have read : StackSemStateOps.memLoad (word + pointerWord) target = some entry := by
          rw [addressEq]
          exact reads _ valid.1
        refine ⟨StackSemStateOps.setVar register entry target, ?_, ?_⟩
        · try simp only [Nat.zero_add]
          rw [comp, StackSemEvaluate.evaluate_seq,
            runMoveAddZ target register index pointer word pointerWord targetIndex pointerLookup (by omega)]
          simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
          let addressed := StackSemStateOps.setVar register (.word (word + pointerWord)) target
          have addressedLookup : addressed.regs.lookup register = some (.word (word + pointerWord)) := by
            simp [addressed, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          have addressedRead : StackSemStateOps.memLoad (word + pointerWord + 0) addressed = some entry := by
            simpa [addressed, StackSemStateOps.memLoad, StackSemStateOps.setVar] using read
          change StackSemEvaluate.evaluate (.inst (.mem .load register (.addr register 0)), addressed) = _
          rw [StackMemory.runLoad addressed register register _ 0 entry addressedLookup addressedRead]
          simp only [addressed, setVarTwiceZ]
          rfl
        · simpa only [entry, relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
            entry source target ⟨relation, lower.1⟩
      · rw [dif_neg valid] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
/-- Flapjack native execution factoring for the original Any constructors;
all lookup facts are derived inside the full cases below. No standalone HOL
declaration is claimed. -/
theorem runAddZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (destination left right : Nat)
    (first second : BitVec width)
    (leftLookup : state.regs.lookup left = some (.word first))
    (rightLookup : state.regs.lookup right = some (.word second)) :
    StackSemEvaluate.evaluate (.inst (.arith (.binop .add destination left (.reg right))), state) =
      (none, StackSemStateOps.setVar destination (.word (first + second)) state) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign, StackSemExpressions.wordExp,
    leftLookup, rightLookup, wordOpHOL, wordOp]
/-- Flapjack native execution factoring for the original Any constructors;
all lookup facts are derived inside the full cases below. No standalone HOL
declaration is claimed. -/
theorem runSubZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (destination left right : Nat)
    (first second : BitVec width)
    (leftLookup : state.regs.lookup left = some (.word first))
    (rightLookup : state.regs.lookup right = some (.word second)) :
    StackSemEvaluate.evaluate (.inst (.arith (.binop .sub destination left (.reg right))), state) =
      (none, StackSemStateOps.setVar destination (.word (first - second)) state) := by
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign, StackSemExpressions.wordExp,
    leftLookup, rightLookup, wordOpHOL, wordOp]
/-- Genuine full original StackStoreAny compiler constructor. The source
alignment/index guard derives actual native heap access and the complete
postrelation; no target-access, postheap or pointer-restoration premise is added. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackStoreAnyZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackStoreAny register index, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackStoreAny register index : HolProg width) pointer) :
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackStoreAny register index),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer ∧ index < pointer at lower
  rw [StackSemEvaluate.evaluate_stackStoreAny] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  cases valueLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [valueLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [valueLookup] at sourceRun
    cases indexLookup : StackSemStateOps.getVar index source with
    | none =>
      rw [indexLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some indexValue =>
      cases indexValue with
      | loc block offset =>
        rw [indexLookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | word word =>
        rw [indexLookup] at sourceRun
        dsimp only at sourceRun
        by_cases valid : source.stackSpace + (word >>> wordShiftAmount width).toNat < source.stack.length ∧
            (word >>> wordShiftAmount width) <<< wordShiftAmount width = word
        · rw [if_pos valid] at sourceRun
          rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
          subst result
          subst postSource
          have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have offsetEq := alignedOffsetZ word good valid.2
          have pointerNeRegister : register ≠ pointer := by omega
          have pointerNeIndex : index ≠ pointer := by omega
          have targetValue : target.regs.lookup register = some value := by
            change StackSemStateOps.getVar register target = some value
            rw [← RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower.1⟩]
            exact valueLookup
          have targetIndex : target.regs.lookup index = some (.word word) := by
            change StackSemStateOps.getVar index target = some (.word word)
            rw [← RelationLaws.stateRelGetVar jump bounds pointer index source target ⟨relation, lower.2⟩]
            exact indexLookup
          obtain ⟨base, pointerLookup, reads⟩ := StackHeap.stateRelStackReads jump bounds pointer source target relation
          let pointerWord := base + bytesInWord width * BitVec.ofNat width source.stackSpace
          change target.regs.lookup pointer = some (.word pointerWord) at pointerLookup
          have addressEq : pointerWord + word = base + wordOffset (source.stackSpace + (word >>> wordShiftAmount width).toNat) := by
            calc
              pointerWord + word = pointerWord + wordOffset (word >>> wordShiftAmount width).toNat := by rw [offsetEq]
              _ = _ := by
                dsimp [pointerWord]
                simp [WordAddressArithmetic.wordOffsetEq, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
          have read : StackSemStateOps.memLoad (pointerWord + word) target =
              some source.stack[source.stackSpace + (word >>> wordShiftAmount width).toNat] := by
            rw [addressEq]
            exact reads _ valid.1
          have domain : target.mdomain (pointerWord + word) = true := by
            by_contra outside
            simp [StackSemStateOps.memLoad, outside] at read
          let updated := {target with memory := fun key => if key = pointerWord + word then value else target.memory key}
          refine ⟨updated, ?_, ?_⟩
          · try simp only [Nat.zero_add]
            rw [comp, StackSemEvaluate.evaluate_seq,
              runAddZ target pointer pointer index pointerWord word pointerLookup targetIndex]
            simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
            let shifted := StackSemStateOps.setVar pointer (.word (pointerWord + word)) target
            have shiftedPointer : shifted.regs.lookup pointer = some (.word (pointerWord + word)) := by
              simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
            have shiftedValue : shifted.regs.lookup register = some value := by
              simpa [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, pointerNeRegister] using targetValue
            have shiftedDomain : shifted.mdomain (pointerWord + word + 0) = true := by
              simpa [shifted, StackSemStateOps.setVar] using domain
            change StackSemEvaluate.evaluate (.seq (.inst (.mem .store register (.addr pointer 0)))
              (.inst (.arith (.binop .sub pointer pointer (.reg index)))), shifted) = _
            rw [StackSemEvaluate.evaluate_seq,
              StackMemory.runStore shifted register pointer _ 0 value shiftedPointer shiftedValue shiftedDomain]
            simp only [StackSemControl.fixClock, Nat.min_self]
            let written := {shifted with memory := fun key => if key = pointerWord + word + 0 then value else shifted.memory key}
            have writtenPointer : written.regs.lookup pointer = some (.word (pointerWord + word)) := shiftedPointer
            have writtenIndex : written.regs.lookup index = some (.word word) := by
              simpa [written, shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, pointerNeIndex] using targetIndex
            change StackSemEvaluate.evaluate (.inst (.arith (.binop .sub pointer pointer (.reg index))), written) = _
            rw [runSubZ written pointer pointer index _ word writtenPointer writtenIndex]
            simp only [BitVec.add_sub_cancel]
            have restore : StackSemStateOps.setVar pointer (.word pointerWord) shifted = target := by
              dsimp [shifted]
              rw [setVarTwiceZ, setVarExistingZ target pointer (.word pointerWord) pointerLookup]
            let newMemory : BitVec width → WordLocW width :=
              fun key => if key = (pointerWord + word + 0) then value else target.memory key
            change (none, {(StackSemStateOps.setVar pointer (.word pointerWord) shifted) with memory := newMemory}) = _
            rw [restore]
            simp [updated, newMemory]
          · simpa only [updated, relation.1, Nat.add_comm, offsetEq] using
              StackHeapWrites.stateRelStackStore jump bounds pointer (word >>> wordShiftAmount width).toNat
                source target source.stack pointerWord (pointerWord + word) value
                ⟨relation, rfl, pointerLookup, valid.1, by rw [← WordAddressArithmetic.wordOffsetEq, offsetEq]⟩
        · rw [if_neg valid] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemoryAny

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSize
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackSize
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-local arithmetic for the genuine size constructor. The original
full relation supplies the inverse-shift no-wrap bound; no target premise. -/
theorem sizeInverseZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    ∃ base : BitVec width,
      StackSemStateOps.getVar pointer target = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) ∧
      StackSemStateOps.getVar (pointer + 1) target = some (.word base) ∧
      ((base + bytesInWord width * BitVec.ofNat width source.stackSpace) - base) >>> wordShiftAmount width = BitVec.ofNat width source.stackSpace := by
  obtain ⟨base, baseLookup, reserve, upper, pointerLookup, heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spaceBound : source.stackSpace ≤ source.stack.length := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have modBound : (BitVec.ofNat width source.stackSpace).toNat ≤ source.stackSpace := by
    simp only [BitVec.toNat_ofNat]
    exact Nat.mod_le _ _
  have noWrap : (bytesInWord width).toNat * (BitVec.ofNat width source.stackSpace).toNat < 2 ^ width := by
    have product := Nat.mul_le_mul_left (bytesInWord width).toNat (Nat.le_trans modBound spaceBound)
    omega
  refine ⟨base, pointerLookup, baseLookup, ?_⟩
  rw [BitVec.add_comm base, BitVec.add_sub_cancel]
  exact WordAddressArithmetic.bytesInWordWordShift _ ⟨good, noWrap⟩

/-- Native get-size arithmetic execution, factored separately from the full
source simulation; all lookup premises are discharged by sizeInverseZ. -/
theorem runGetSizeZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register pointer : Nat)
    (pointerWord base : BitVec width)
    (pointerLookup : state.regs.lookup pointer = some (.word pointerWord))
    (baseLookup : state.regs.lookup (pointer + 1) = some (.word base))
    (different : pointer + 1 ≠ register)
    (good : goodDimindex width) :
    StackSemEvaluate.evaluate (comp false (0,0) pointer (.stackGetSize register), state) =
      (none, StackSemStateOps.setVar register
        (.word ((pointerWord - base) >>> wordShiftAmount width)) state) := by
  have shiftBound : wordShiftAmount width < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have shiftWidth : wordShiftAmount width < width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have maps (first second : WordLocW width) :
      (state.regs.updateEq (register, first)).updateEq (register, second) = state.regs.updateEq (register, second) := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases same : query = register <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same]
  simp [comp, StackSemEvaluate.evaluate_seq, moveInst, moveHOL, subInst,
    rightShiftInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, pointerLookup, baseLookup,
    StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    different, wordOpHOL, wordOp, wordShiftHOL,
    StackSemControl.fixClock, BitVec.toNat_ofNat, Nat.mod_eq_of_lt shiftBound, Nat.not_le_of_gt shiftWidth, maps]

/-- Full original StackGetSize case, with precisely the original four premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackGetSizeZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackGetSize register, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackGetSize register : HolProg width) pointer) :
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackGetSize register),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackGetSize] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  have resultEq := (Prod.mk.inj sourceRun).1.symm
  have sourceEq := (Prod.mk.inj sourceRun).2.symm
  subst result
  subst postSource
  obtain ⟨base, pointerLookup, baseLookup, inverse⟩ := sizeInverseZ jump bounds pointer source target relation
  have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨StackSemStateOps.setVar register (.word (BitVec.ofNat width source.stackSpace)) target, ?_, ?_⟩
  · try simp only [Nat.zero_add]
    have execution := runGetSizeZ target register pointer _ base pointerLookup baseLookup (by omega) good
    simpa only [comp, inverse] using execution
  · exact StateUpdates.stateRelSetVar jump bounds pointer register _ source target ⟨relation, lower⟩

/-- Full relation reconstructed after setting the stack position. This is
source-local constructor factoring, with no standalone HOL declaration. -/
theorem stateRelSizeStepZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target)
    (safe : count ≤ source.stack.length) :
    ∃ base : BitVec width,
      StackSemStateOps.getVar (pointer + 1) target = some (.word base) ∧
      stateRelHOL jump bounds pointer {source with stackSpace := count}
        (StackSemStateOps.setVar pointer (.word (base + bytesInWord width * BitVec.ofNat width count)) target) := by
  obtain ⟨base, baseLookup, reserve, upper, pointerLookup, heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  refine ⟨base, baseLookup, ?_⟩
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  have baseNe : pointer + 1 ≠ pointer := by omega
  have heapNe : pointer + 2 ≠ pointer := by omega
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have low : ∀ query, query < pointer →
      (target.regs.updateEq (pointer, .word (base + bytesInWord width * BitVec.ofNat width count))).lookup query = source.regs.lookup query := by
    intro query below
    have ne : query ≠ pointer := by omega
    simpa only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne, ite_false] using h18 query below
  simp only [stateRelHOL, StackSemStateOps.setVar,
    HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, baseNe, heapNe, ite_false, ite_true, baseLookup]
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,low,h19,h20,h21,h22,h23,safe,
    h25.1,reserve,upper,True.intro,heap⟩

/-- Native SetSize executes the original shift and pointer reconstruction.
Lookup premises are supplied from the full source relation in the case below. -/
theorem runSetSizeZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register pointer : Nat)
    (word base : BitVec width)
    (wordLookup : state.regs.lookup register = some (.word word))
    (baseLookup : state.regs.lookup (pointer + 1) = some (.word base))
    (lower : register < pointer)
    (good : goodDimindex width) :
    StackSemEvaluate.evaluate (comp false (0,0) pointer (.stackSetSize register), state) =
      (none, StackSemStateOps.setVar pointer (.word (base + (word <<< wordShiftAmount width)))
        (StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) state)) := by
  have shiftBound : wordShiftAmount width < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have shiftWidth : wordShiftAmount width < width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have shiftRun : StackSemEvaluate.evaluate (leftShiftInst register (wordShiftAmount width), state) =
      (none, StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) state) := by
    simp [leftShiftInst, StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
      StackSemExpressions.wordExp, wordLookup, wordShiftHOL,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt shiftBound, Nat.not_le_of_gt shiftWidth]
  let shifted := StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) state
  have shiftedWord : shifted.regs.lookup register = some (.word (word <<< wordShiftAmount width)) := by
    simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  have shiftedBase : shifted.regs.lookup (pointer + 1) = some (.word base) := by
    have different : pointer + 1 ≠ register := by omega
    simp [shifted, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different, baseLookup]
  rw [comp, StackSemEvaluate.evaluate_seq, shiftRun]
  simp only [StackSemControl.fixClock, StackSemStateOps.setVar, Nat.min_self]
  change StackSemEvaluate.evaluate (.seq (moveInst pointer (pointer + 1)) (addInst pointer register), shifted) = _
  exact CompCorrect.StackMemoryAny.runMoveAdd shifted pointer (pointer + 1) register base (word <<< wordShiftAmount width) shiftedBase shiftedWord (by omega)
/-- Canonical updates to distinct registers commute. Flapjack infrastructure,
not a standalone HOL port. -/
theorem setVarCommuteZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (first second : Nat)
    (a b : WordLocW width) (different : first ≠ second) :
    StackSemStateOps.setVar first a (StackSemStateOps.setVar second b state) =
      StackSemStateOps.setVar second b (StackSemStateOps.setVar first a state) := by
  have maps : (state.regs.updateEq (second,b)).updateEq (first,a) =
      (state.regs.updateEq (first,a)).updateEq (second,b) := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases eqFirst : query = first
    · subst query; simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different]
    · by_cases eqSecond : query = second <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eqFirst, eqSecond, Ne.symm different]
  simp [StackSemStateOps.setVar, maps]
/-- Full original StackSetSize case, with precisely the original four premises. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackSetSizeZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.stackSetSize register, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.stackSetSize register : HolProg width) pointer) :
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackSetSize register),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer at lower
  rw [StackSemEvaluate.evaluate_stackSetSize] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun

  cases lookup : StackSemStateOps.getVar register source with
  | none =>
    rw [lookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    cases value with
    | loc first second =>
      rw [lookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | word word =>
      rw [lookup] at sourceRun
      simp only [] at sourceRun
      by_cases outsideBounds : source.stack.length ≤ word.toNat
      · rw [if_pos outsideBounds] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      · rw [if_neg outsideBounds] at sourceRun
        have resultEq := (Prod.mk.inj sourceRun).1.symm
        have sourceEq := (Prod.mk.inj sourceRun).2.symm
        subst result
        subst postSource
        obtain ⟨base, baseLookup, postRelation⟩ := stateRelSizeStepZ jump bounds pointer word.toNat source target
          relation (by omega)
        have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        have targetLookup : target.regs.lookup register = some (.word word) := by
          change StackSemStateOps.getVar register target = some (.word word)
          rw [← RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower⟩]
          exact lookup
        have shiftEq : word <<< wordShiftAmount width = bytesInWord width * BitVec.ofNat width word.toNat := by
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, WordAddressArithmetic.lslWordShift word good, BitVec.mul_comm]
        let pointerTarget := StackSemStateOps.setVar pointer (.word (base + bytesInWord width * BitVec.ofNat width word.toNat)) target
        refine ⟨StackSemStateOps.setVar register (.word (word <<< wordShiftAmount width)) pointerTarget, ?_, ?_⟩
        · try simp only [Nat.zero_add]
          have execution := runSetSizeZ target register pointer word base targetLookup baseLookup lower good
          rw [setVarCommuteZ target pointer register _ _ (by omega), shiftEq] at execution
          simpa only [comp, pointerTarget, shiftEq] using execution
        · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register (.word (word <<< wordShiftAmount width)) {source with stackSpace := word.toNat}
            pointerTarget ⟨postRelation, lower⟩
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSize

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.StackSpace
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine full StackFree constructor of the original compiler theorem.
The original three-premise recursive simulation supplies the existential target
execution and full postrelation; the fourth constructor bound is retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackFreeZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate ((.stackFree count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackFree count) : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackFree count),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  obtain ⟨postTarget, targetRun, postRelation⟩ :=
    evaluateStackFreeZ jump bounds pointer count source target postSource result
      ⟨sourceRun, notError, relation⟩
  refine ⟨postTarget, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · cases result with
    | none => exact postRelation
    | some result =>
      cases result <;> first | exact postRelation | exact postRelation.2.2.2.2.2.2.2.2.2.1
/-- Genuine full StackAlloc constructor of the original compiler theorem.
The original three-premise recursive simulation supplies the existential target
execution and full postrelation; the fourth constructor bound is retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackAllocZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound ((.stackAlloc count) : HolProg width) pointer) :
    ∃ (clock : Nat) (postTarget : StackSemStateFiniteExact width C F), clock ≤ 1 ∧ (result = none → clock = 0) ∧
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  classical
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  obtain ⟨clock, postTarget, hc1, hc0, targetRun, postRelation⟩ :=
    evaluateStackAllocZ jump bounds pointer count source target postSource result
      ⟨sourceRun, notError, relation⟩
  refine ⟨clock, postTarget, hc1, hc0, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · cases result with
    | none => simpa using postRelation
    | some result =>
      cases result <;> simp at postRelation <;>
        first | exact postRelation | exact postRelation.2.2.2.2.2.2.2.2.2.1
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Bitmap
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.Bitmap
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-local extraction of bounded bitmap reads from the original full
separated heap. No target load or domain fact is supplied as a premise. -/
theorem bitmapReadsZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    ∃ bitmapWord : BitVec width,
      source.store.lookup .bitmapBase = some (.word bitmapWord) ∧
      ∀ (index : Nat) (bound : index < source.bitmaps.length),
        StackSemStateOps.memLoad ((bitmapWord <<< wordShiftAmount width) + bytesInWord width * BitVec.ofNat width index) target =
          some (.word source.bitmaps[index]) := by
  have validWord := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨base, baseLookup, reserve, upper, pointerLookup, heaps⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  cases lookup : source.store.lookup .bitmapBase with
  | none => simp [lookup, isSomeWord] at validWord
  | some value =>
    cases value with
    | loc first second => simp [lookup, isSomeWord, wordLocWToGeneric] at validWord
    | word bitmapWord =>
      refine ⟨bitmapWord, rfl, ?_⟩
      intro index bound
      rcases heaps with ⟨heap4, heapStack, part4, assertion4, stack⟩
      rcases assertion4 with ⟨heap3, heapStore, part3, assertion3, store⟩
      rcases assertion3 with ⟨heap2, heapBuffer, part2, assertion2, buffer⟩
      rcases assertion2 with ⟨heapMemory, heapBitmap, part1, memory, bitmap⟩
      simp only [lookup, Option.map_some, wordLocWToGeneric, theSomeWord] at bitmap
      have combinedBound : index < ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word).length := by
        simp only [List.length_map, List.length_append]
        omega
      have member := StackHeap.wordListNth (bitmapWord <<< wordShiftAmount width)
        ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word) heapBitmap index combinedBound bitmap
      have entry : ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word)[index] = .word source.bitmaps[index] := by
        simp only [List.getElem_map, List.getElem_append_left bound]
      rw [entry] at member
      have targetMember : SetSep.fun2Set (target.memory, fun address => target.mdomain address = true)
          ((bitmapWord <<< wordShiftAmount width) + bytesInWord width * BitVec.ofNat width index, .word source.bitmaps[index]) := by
        rw [← part4.1, ← part3.1, ← part2.1, ← part1.1]
        exact Or.inl (Or.inl (Or.inl (Or.inr member)))
      have facts := (SetSep.fun2SetThm target.memory (fun address => target.mdomain address = true)
        _ (.word source.bitmaps[index])).mp targetMember
      simp only [StackSemStateOps.memLoad, facts.1, facts.2, ite_true]

/-- Factoring of the original native BitmapLoad instruction sequence;
the full constructor derives all target lookup/read premises. -/
theorem runBitmapZ {width : Nat} [NeZero width] {C F : Type}
    (state : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (base bitmapWord word entry : BitVec width)
    (baseLookup : state.regs.lookup (pointer + 1) = some (.word base))
    (indexLookup : state.regs.lookup index = some (.word word))
    (different : index ≠ register)
    (firstRead : StackSemStateOps.memLoad (base + storeOffset .bitmapBase) state = some (.word bitmapWord))
    (finalRead : StackSemStateOps.memLoad ((bitmapWord + word) <<< wordShiftAmount width) state = some (.word entry))
    (good : goodDimindex width) :
    StackSemEvaluate.evaluate (comp false (0,0) pointer (.bitmapLoad register index), state) =
      (none, StackSemStateOps.setVar register (.word entry) state) := by
  have shiftBound : wordShiftAmount width < 2 ^ width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have shiftWidth : wordShiftAmount width < width := by
    rcases good with h | h <;> subst width <;> norm_num [wordShiftAmount]
  have maps (first second : WordLocW width) :
      (state.regs.updateEq (register, first)).updateEq (register, second) = state.regs.updateEq (register, second) := by
    apply HolFiniteMapExact.ext_lookup
    intro query
    by_cases same : query = register <;> simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same]
  have firstFacts : state.mdomain (base + storeOffset .bitmapBase) = true ∧
      state.memory (base + storeOffset .bitmapBase) = .word bitmapWord := by
    by_cases domain : state.mdomain (base + storeOffset .bitmapBase) = true
    · exact ⟨domain, Option.some.inj (by simpa [StackSemStateOps.memLoad, domain] using firstRead)⟩
    · simp [StackSemStateOps.memLoad, domain] at firstRead
  have finalReadNormalized : StackSemStateOps.memLoad
      ((bitmapWord <<< wordShiftAmount width) + (word <<< wordShiftAmount width)) state = some (.word entry) := by
    simpa using finalRead
  have finalFacts : state.mdomain ((bitmapWord <<< wordShiftAmount width) + (word <<< wordShiftAmount width)) = true ∧
      state.memory ((bitmapWord <<< wordShiftAmount width) + (word <<< wordShiftAmount width)) = .word entry := by
    by_cases domain : state.mdomain ((bitmapWord <<< wordShiftAmount width) + (word <<< wordShiftAmount width)) = true
    · exact ⟨domain, Option.some.inj (by simpa [StackSemStateOps.memLoad, domain] using finalReadNormalized)⟩
    · simp [StackSemStateOps.memLoad, domain] at finalReadNormalized
  simp [comp, listSeqHOL, StackSemEvaluate.evaluate_seq, addInst, leftShiftInst,
    StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.assign,
    StackSemExpressions.wordExp, baseLookup, indexLookup,
    StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
    different, wordOpHOL, wordOp, wordShiftHOL,
    StackSemControl.fixClock, BitVec.toNat_ofNat, Nat.mod_eq_of_lt shiftBound,
    Nat.not_le_of_gt shiftWidth, maps, StackSemStateOps.memLoad, firstFacts.1, firstFacts.2, finalFacts.1, finalFacts.2]

/-- Full original BitmapLoad constructor, retaining all original guards and
four premises. Target reads are derived from the full separated source heap. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectBitmapLoadZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F) (register index pointer : Nat)
    (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.bitmapLoad register index, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.bitmapLoad register index : HolProg width) pointer) :
    ∃ postTarget,
      StackSemEvaluate.evaluate (comp jump bounds pointer (.bitmapLoad register index),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change register < pointer ∧ index < pointer at lower
  rw [StackSemEvaluate.evaluate_bitmapLoad] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_or] at sourceRun
  by_cases same : register = index
  · simp only [same, beq_self_eq_true, if_true] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  · simp only [beq_eq_false_iff_ne.mpr same, Bool.false_eq_true, if_false] at sourceRun
    cases lookup : StackSemStateOps.getVar index source with
    | none =>
      rw [lookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some value =>
      cases value with
      | loc first second =>
        rw [lookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | word word =>
        rw [lookup] at sourceRun
        simp only [] at sourceRun
        by_cases outsideBounds : source.bitmaps.length ≤ word.toNat
        · rw [dif_pos outsideBounds] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
        · rw [dif_neg outsideBounds] at sourceRun
          have resultEq := (Prod.mk.inj sourceRun).1.symm
          have sourceEq := (Prod.mk.inj sourceRun).2.symm
          subst result
          subst postSource
          have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          obtain ⟨bitmapWord, bitmapLookup, reads⟩ := bitmapReadsZ jump bounds pointer source target relation
          obtain ⟨base, baseLookup, reserve, upper, pointerLookup, heap⟩ :=
            StackPointer.stateRelGetVarK jump bounds pointer source target relation
          have firstRead := StoreHeapReads.memLoadLemma .bitmapBase source target (.word bitmapWord) base
            ⟨by simp [storeList], by simpa only [StackSemRegisterTransfers.storeOfSyntax] using bitmapLookup,
              by simpa only [List.length_append, Nat.add_comm] using heap⟩
          have targetIndex : target.regs.lookup index = some (.word word) := by
            change StackSemStateOps.getVar index target = some (.word word)
            rw [← RelationLaws.stateRelGetVar jump bounds pointer index source target ⟨relation, lower.2⟩]
            exact lookup
          have addressEq : (bitmapWord + word) <<< wordShiftAmount width =
              (bitmapWord <<< wordShiftAmount width) + bytesInWord width * BitVec.ofNat width word.toNat := by
            simp only [BitVec.shiftLeft_add_distrib, BitVec.ofNat_toNat, BitVec.setWidth_eq]
            rw [WordAddressArithmetic.lslWordShift word good, BitVec.mul_comm word]
          have bound : word.toNat < source.bitmaps.length := by omega
          have read := reads word.toNat bound
          rw [← addressEq] at read
          refine ⟨StackSemStateOps.setVar register (.word source.bitmaps[word.toNat]) target, ?_, ?_⟩
          · try simp only [Nat.zero_add]
            have execution := runBitmapZ target register index pointer base bitmapWord word source.bitmaps[word.toNat]
              baseLookup targetIndex (Ne.symm same) firstRead read good
            simpa only [comp] using execution
          · simpa only [relation.1] using StateUpdates.stateRelSetVar jump bounds pointer register
              (.word source.bitmaps[word.toNat]) source target ⟨relation, lower.1⟩
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Bitmap

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.CodeBufferWrite
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.CodeBufferWrite
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness


/-- Flapjack infrastructure: replacing both equal code buffers preserves the
original full relation; no independent HOL declaration is claimed. -/
theorem stateRelCodeBufferZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (buffer : WordSemBuffer width 8)
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer {source with codeBuffer := buffer}
      {target with codeBuffer := buffer} := by
  simp only [stateRelHOL] at relation ⊢
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,True.intro,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩

/-- Genuine original CodeBufferWrite case, retaining the original four
premises and full existential native target run/post-state relation. Operand
lookups and buffer success on the target are proved from the source relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCodeBufferWriteZ {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.codeBufferWrite first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.codeBufferWrite first second : HolProg width) pointer) :
    ∃ postTarget,
      evaluate (comp jump bounds pointer (.codeBufferWrite first second),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change first < pointer ∧ second < pointer at bound
  have readFirst := RelationLaws.stateRelGetVar jump bounds pointer first source target ⟨relation, bound.1⟩
  have readSecond := RelationLaws.stateRelGetVar jump bounds pointer second source target ⟨relation, bound.2⟩
  change source.regs.lookup first = target.regs.lookup first at readFirst
  change source.regs.lookup second = target.regs.lookup second at readSecond
  have buffers : target.codeBuffer = source.codeBuffer := relation.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [evaluate_codeBufferWrite] at sourceRun
  cases hFirst : getVar first source with
  | none =>
    simp only [hFirst] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some left =>
    cases left with
    | loc name offset =>
      simp only [hFirst] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word left =>
      cases hSecond : getVar second source with
      | none =>
        simp only [hFirst, hSecond] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some right =>
        cases right with
        | loc name offset =>
          simp only [hFirst, hSecond] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word right =>
          simp only [hFirst, hSecond] at sourceRun
          cases write : wordSemBufferWrite source.codeBuffer left (right.setWidth 8) with
          | none =>
            simp only [write] at sourceRun
            exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          | some buffer =>
            simp only [write] at sourceRun
            rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
            subst result
            subst postSource
            have targetFirst : target.regs.lookup first = some (.word left) := readFirst.symm.trans hFirst
            have targetSecond : target.regs.lookup second = some (.word right) := readSecond.symm.trans hSecond
            refine ⟨{target with codeBuffer := buffer}, ?_, ?_⟩
            · simpa only [comp, Nat.zero_add] using
                (evaluate_codeBufferWrite first second target).trans (by
                  simp only [getVar, targetFirst, targetSecond, buffers, write])
            · exact stateRelCodeBufferZ jump bounds pointer source target buffer relation
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.CodeBufferWrite

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.DataBufferWrite
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.DataBufferWrite
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

/-- Flapjack infrastructure for the original DataBufferWrite case: a nonempty
remaining buffer segment exposes the next target-memory cell. This is derived
from the full separated state relation, without a target-domain premise. The
case proof must derive nonempty space from the successful source buffer write. -/
theorem nextBufferCellZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (count : Nat)
    (relation : stateRelHOL jump bounds pointer source target)
    (space : source.dataBuffer.spaceLeft = count + 1) :
    let bitmapBase := theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric)
      <<< wordShiftAmount width
    let address := bitmapBase + bytesInWord width *
      BitVec.ofNat width (source.bitmaps ++ source.dataBuffer.buffer).length
    target.mdomain address = true := by
  let next := (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric)
    <<< wordShiftAmount width) + bytesInWord width *
    BitVec.ofNat width (source.bitmaps ++ source.dataBuffer.buffer).length
  have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  dsimp only at heaps ⊢
  cases baseLookup : target.regs.lookup (pointer + 1) with
  | none => simp only [baseLookup] at heaps; exact heaps.2.elim
  | some value =>
    cases value with
    | loc block offset => simp only [baseLookup] at heaps; exact heaps.2.elim
    | word base =>
      simp only [baseLookup] at heaps
      rcases heaps.2.2.2.2 with ⟨heap4, heapStack, split4, assertion4, _⟩
      rcases assertion4 with ⟨heap3, heapStore, split3, assertion3, _⟩
      rcases assertion3 with ⟨heap2, heapSpace, split2, _, spaceHeap⟩
      rw [space, (WordListExists.wordListExistsThm _ count).2] at spaceHeap
      rcases spaceHeap with ⟨oldValue, head, tail, splitHead, singleton, _⟩
      have memberHead : head (next, oldValue) := by rw [singleton]
      have memberSpace : heapSpace (next, oldValue) := by
        rw [← splitHead.1]; exact Or.inl memberHead
      have member3 : heap3 (next, oldValue) := by
        rw [← split2.1]; exact Or.inr memberSpace
      have member4 : heap4 (next, oldValue) := by
        rw [← split3.1]; exact Or.inl member3
      have memberTarget : SetSep.fun2Set (target.memory, fun a => target.mdomain a = true)
          (next, oldValue) := by
        rw [← split4.1]; exact Or.inl member4
      exact ((SetSep.fun2SetThm _ _ _ _).mp memberTarget).2

/-- Flapjack case infrastructure: the actual successful native buffer write
supplies both the address and available-space facts needed for target membership.
No target-domain or separately supplied successful guard is assumed. -/
theorem bufferWriteTargetDomainZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (address value : BitVec width) (updated : WordSemBuffer width width)
    (relation : stateRelHOL jump bounds pointer source target)
    (written : wordSemBufferWrite source.dataBuffer address value = some updated) :
    target.mdomain address = true := by
  unfold wordSemBufferWrite at written
  split at written
  next guard =>
    have positive := guard.2
    have space : source.dataBuffer.spaceLeft = (source.dataBuffer.spaceLeft - 1) + 1 := by omega
    have member := nextBufferCellZ jump bounds pointer source target
      (source.dataBuffer.spaceLeft - 1) relation space
    have heaps := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    dsimp only at heaps member
    rw [← guard.1, heaps.1]
    simpa only [List.length_append, BitVec.ofNat_add, BitVec.mul_add,
      BitVec.add_assoc, bytesInWord] using member
  next => simp at written

/-- Native target store execution derived from source operands and actual
buffer-write success. This supports the full case; it assumes no target run. -/
theorem bufferWriteTargetExecutionZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer first second : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (address value : BitVec width) (updated : WordSemBuffer width width)
    (relation : stateRelHOL jump bounds pointer source target)
    (firstBound : first < pointer) (secondBound : second < pointer)
    (firstValue : source.regs.lookup first = some (.word address))
    (secondValue : source.regs.lookup second = some (.word value))
    (written : wordSemBufferWrite source.dataBuffer address value = some updated) :
    StackSemEvaluate.evaluate (.inst (.mem .store second (.addr first 0)), target) =
      (none, {target with memory := fun key =>
        if key = address then .word value else target.memory key}) := by
  have registers := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have firstTarget := (registers first firstBound).trans firstValue
  have secondTarget := (registers second secondBound).trans secondValue
  have domain := bufferWriteTargetDomainZ jump bounds pointer source target
    address value updated relation written
  simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
    StackSemIntegerInstructions.instInteger, StackSemExpressions.wordExp,
    StackSemStateOps.getVar, StackSemStateOps.memStore, firstTarget, secondTarget,
    domain, wordOpHOL, wordOp]

/-- Flapjack factoring of the three original surrounding separation frames.
This changes only association/order of STAR, retaining complete predicate heaps. -/
private theorem exposeBufferCell {α : Type} (preceding suffix outer : (α → Prop) → Prop)
    (entry : α) :
    SetSep.star (SetSep.star preceding (SetSep.star (SetSep.one entry) suffix)) outer =
      SetSep.star (SetSep.one entry) (SetSep.star (SetSep.star preceding suffix) outer) := by
  rw [SetSep.starAssoc preceding (SetSep.one entry) suffix,
    SetSep.starComm preceding (SetSep.one entry),
    ← SetSep.starAssoc (SetSep.one entry) preceding suffix,
    ← SetSep.starAssoc]

/-- Derived buffer-cell update with every surrounding separated heap preserved.
The original graph and singleton partition derive unique-address frame safety;
no post-heap, frame-preservation or target-domain fact is supplied. -/
theorem writeBufferCellZ {width : Nat} [NeZero width]
    (preceding suffix outer : ((BitVec width × WordLocW width) → Prop) → Prop)
    (address : BitVec width) (oldValue newValue : WordLocW width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (heap : SetSep.star
      (SetSep.star preceding (SetSep.star (SetSep.one (address, oldValue)) suffix)) outer
      (SetSep.fun2Set (memory, domain))) :
    SetSep.star
      (SetSep.star preceding (SetSep.star (SetSep.one (address, newValue)) suffix)) outer
      (SetSep.fun2Set ((fun key => if key = address then newValue else memory key), domain)) := by
  rw [exposeBufferCell] at heap ⊢
  have changed := SetSep.writeFun2Set newValue address oldValue
    (SetSep.star (SetSep.star preceding suffix) outer) memory domain heap
  rw [SetSep.starComm] at changed
  convert changed using 1
  congr 2
  funext key
  by_cases same : key = address <;> simp [same]

/-- Exact append/remaining-slot reassociation for the native buffer segment.
Flapjack infrastructure; addresses use modular word arithmetic throughout. -/
theorem bufferListSlotZ {width : Nat} [NeZero width]
    (base : BitVec width) (values : List (WordLocW width))
    (value : WordLocW width) (count : Nat) :
    SetSep.star (Misc.wordList base (values ++ [value]))
      (Misc.wordListExists
        (base + bytesInWord width * BitVec.ofNat width (values.length + 1)) count) =
    SetSep.star (Misc.wordList base values)
      (SetSep.star (SetSep.one
        (base + bytesInWord width * BitVec.ofNat width values.length, value))
        (Misc.wordListExists
          (base + bytesInWord width * BitVec.ofNat width values.length + bytesInWord width) count)) := by
  rw [StackHeap.wordListAppend values [value] base]
  simp only [Misc.wordList]
  rw [SetSep.starComm (SetSep.one _) SetSep.emp, StackHeap.starEmptyLeft,
    ← SetSep.starAssoc]
  congr 2
  congr 1
  simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]

/-- Native buffer append consumes exactly one existential remaining cell while
preserving its full outer frame. Neither the new heap nor memory-domain success
is a premise: the old separated functional graph supplies them. -/
theorem appendBufferCellZ {width : Nat} [NeZero width]
    (base : BitVec width) (values : List (WordLocW width))
    (value : WordLocW width) (count : Nat)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Prop)
    (heap : SetSep.star
      (SetSep.star (Misc.wordList base values)
        (Misc.wordListExists (base + bytesInWord width * BitVec.ofNat width values.length) (count + 1)))
      frame (SetSep.fun2Set (memory, domain))) :
    SetSep.star
      (SetSep.star (Misc.wordList base (values ++ [value]))
        (Misc.wordListExists (base + bytesInWord width * BitVec.ofNat width (values.length + 1)) count))
      frame (SetSep.fun2Set
        ((fun key => if key = base + bytesInWord width * BitVec.ofNat width values.length
          then value else memory key), domain)) := by
  rw [bufferListSlotZ]
  rw [(WordListExists.wordListExistsThm _ count).2] at heap
  rcases heap with ⟨front, back, partition, listHeap, frameHeap⟩
  rcases listHeap with ⟨stored, remaining, splitList, storedHeap, old, oldHeap⟩
  exact writeBufferCellZ _ _ frame _ old value memory domain
    ⟨front, back, partition, ⟨stored, remaining, splitList, storedHeap, oldHeap⟩, frameHeap⟩

/-- Reassociate the original memory, store and stack frames around the buffer
segment. This is separation-algebra infrastructure, with no HOL port claim. -/
private theorem bufferFrames {α : Type}
    (memory buffer remaining store stack : (α → Prop) → Prop) :
    SetSep.star (SetSep.star (SetSep.star (SetSep.star memory buffer) remaining) store) stack =
      SetSep.star (SetSep.star buffer remaining)
        (SetSep.star memory (SetSep.star store stack)) := by
  rw [← SetSep.starAssoc (SetSep.star (SetSep.star memory buffer) remaining) store stack,
    ← SetSep.starAssoc memory buffer remaining,
    SetSep.starComm memory (SetSep.star buffer remaining),
    ← SetSep.starAssoc]

/-- Successful native buffer writes preserve the full source/target relation.
The old separated heap supplies the target update and every frame. -/
theorem bufferWriteStateRelZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (address value : BitVec width) (updated : WordSemBuffer width width)
    (relation : stateRelHOL jump bounds pointer source target)
    (written : wordSemBufferWrite source.dataBuffer address value = some updated) :
    stateRelHOL jump bounds pointer {source with dataBuffer := updated}
      {target with memory := fun key => if key = address then .word value else target.memory key} := by
  unfold wordSemBufferWrite at written
  split at written
  next guard =>
    have updatedEq := Option.some.inj written
    subst updated
    unfold stateRelHOL at relation ⊢
    rcases relation with ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, heaps⟩
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, ?_⟩
    dsimp only at heaps ⊢
    refine ⟨heaps.1, ?_⟩
    cases lookup : target.regs.lookup (pointer + 1) with
    | none => simp only [lookup] at heaps; exact heaps.2.elim
    | some entry =>
      cases entry with
      | loc block offset => simp only [lookup] at heaps; exact heaps.2.elim
      | word base =>
        simp only [lookup] at heaps ⊢
        refine ⟨heaps.2.1, heaps.2.2.1, heaps.2.2.2.1, ?_⟩
        have heap := heaps.2.2.2.2
        rw [bufferFrames] at heap ⊢
        have space : source.dataBuffer.spaceLeft = (source.dataBuffer.spaceLeft - 1) + 1 := by
          have positive := guard.2
          omega
        rw [space] at heap
        have changed := appendBufferCellZ
          (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric) <<< wordShiftAmount width)
          ((source.bitmaps ++ source.dataBuffer.buffer).map WordLocW.word) (.word value) (source.dataBuffer.spaceLeft - 1)
          _ target.memory (fun key => target.mdomain key = true) (by simpa only [List.length_map] using heap)
        have addressEq : address =
            (theSomeWord ((source.store.lookup .bitmapBase).map wordLocWToGeneric)
              <<< wordShiftAmount width) + bytesInWord width *
                BitVec.ofNat width (source.bitmaps ++ source.dataBuffer.buffer).length := by
          rw [← guard.1, heaps.1]
          simp [List.length_append, BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc, bytesInWord]
        rw [addressEq]
        simpa only [List.append_assoc, List.map_append, List.map_cons, List.map_nil,
          List.length_append, List.length_cons, List.length_nil, List.length_map,
          Nat.add_assoc, Nat.add_zero] using changed
  next => simp at written

/-- Canonical imported-state codec witness; Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full native DataBufferWrite case of the original simulation statement.
Only original evaluation, non-error, full state relation and register bounds
are premises; the target store and complete postrelation are derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectDataBufferWriteZ {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (first second : Nat)
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.dataBufferWrite first second : HolProg width) pointer) :
    ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.dataBufferWrite first second),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStack := relation.1
  rw [StackSemEvaluate.evaluate_dataBufferWrite] at sourceRun
  simp only [useStack, not_true_eq_false, ite_false] at sourceRun
  cases firstLookup : StackSemStateOps.getVar first source with
  | none =>
    simp only [firstLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some firstValue =>
    cases firstValue with
    | loc block offset =>
      simp only [firstLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | word address =>
      cases secondLookup : StackSemStateOps.getVar second source with
      | none =>
        simp only [firstLookup, secondLookup] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | some secondValue =>
        cases secondValue with
        | loc block offset =>
          simp only [firstLookup, secondLookup] at sourceRun
          exact (notError (Prod.mk.inj sourceRun).1.symm).elim
        | word value =>
          simp only [firstLookup, secondLookup] at sourceRun
          cases written : wordSemBufferWrite source.dataBuffer address value with
          | none =>
            rw [written] at sourceRun
            exact (notError (Prod.mk.inj sourceRun).1.symm).elim
          | some updated =>
            rw [written] at sourceRun
            rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
            subst result
            subst postSource
            refine ⟨{target with memory := fun key => if key = address then .word value else target.memory key}, ?_, ?_⟩
            · simpa only [comp, Nat.zero_add] using
                bufferWriteTargetExecutionZ jump bounds pointer first second source target address value updated
                  relation bound.1 bound.2 firstLookup secondLookup written
            · simpa only [useStack] using bufferWriteStateRelZ jump bounds pointer source target address value updated relation written
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.DataBufferWrite

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.ShMemOp
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.ShMemOp
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps StackSemShMem

/-- Flapjack infrastructure for the shared-memory case: replacing the common
FFI state preserves every conjunct of the original relation. There is no
standalone HOL declaration for this field-update factoring. -/
theorem stateRelFfiZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (ffi : HolFfiState F)
    (relation : stateRelHOL jump bounds pointer source target) :
    stateRelHOL jump bounds pointer {source with ffi := ffi} {target with ffi := ffi} := by
  simp only [stateRelHOL] at relation ⊢
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,True.intro,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩

/-- Flapjack factoring of the eight original shared-memory cases. Source
execution determines the target execution; it is not a target-run premise. -/
private def simulationPost {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (result : Option (StackSemResult width))
    (source target : StackSemStateFiniteExact width C F) : Prop :=
  match result with
  | some (.halt _) | some .timeOut | some (.finalFFI _) => target.ffi = source.ffi
  | _ => stateRelHOL jump bounds pointer source target

theorem shMemOpSimulationZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register : Nat)
    (op : WordMemOp) (address : BitVec width)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (relation : stateRelHOL jump bounds pointer source target)
    (below : register < pointer)
    (sourceRun : shMemOp op register address source = (result, postSource))
    (notError : result ≠ some .error) :
    ∃ postTarget, shMemOp op register address target = (result, postTarget) ∧
      simulationPost jump bounds pointer result postSource postTarget := by
  have readEq := (RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, below⟩).symm
  have domainEq : target.shMdomain = source.shMdomain :=
    (RelationLaws.stateRelConst jump bounds pointer source target relation).2.1
  have ffiEq : target.ffi = source.ffi :=
    (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
  cases op <;> simp only [shMemOp, shMemLoad, shMemStore, shMemLoadByte,
    shMemStoreByte, shMemLoad16, shMemStore16, shMemLoad32, shMemStore32] at sourceRun ⊢
  all_goals simp only [readEq, domainEq, ffiEq]
  all_goals repeat' split at sourceRun
  all_goals simp only [Prod.mk.injEq] at sourceRun
  all_goals rcases sourceRun with ⟨rfl, rfl⟩
  all_goals try contradiction
  all_goals simp_all only [simulationPost]
  all_goals refine ⟨_, rfl, ?_⟩
  all_goals first
    | exact ffiEq
    | simpa only [domainEq] using stateRelFfiZ jump bounds pointer source target _ relation
    | simpa only [domainEq, setVar] using
        stateRelFfiZ jump bounds pointer (setVar register _ source)
          (setVar register _ target) _
          (StateUpdates.stateRelSetVar jump bounds pointer register _ source target ⟨relation, below⟩)

/-- Canonical state codec, re-exported locally for the representation qualifier.
This is Flapjack infrastructure, with no standalone HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original ShMemOp case (1998–2022). All eight operations use the
actual native evaluator and FFI transition. The target address and run follow
from the original four premises; zero clock addition suffices, including the
original timeout and terminal FFI cases. No target execution is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectShMemOpZ {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (register base : Nat) (offset : BitVec width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.shMemOp op register (.addr base offset), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.shMemOp op register (.addr base offset) : HolProg width) pointer) :
    ∃ postTarget,
      evaluate (comp jump bounds pointer (.shMemOp op register (.addr base offset)),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change register < pointer ∧ base < pointer at bound
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_shMemOp] at sourceRun
  cases addressRun : StackSemExpressions.wordExp source (.op .add [.var base, .const offset]) with
  | none =>
    simp only [addressRun] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some address =>
    have targetAddress := ExpressionSimulation.stateRelWordExp jump bounds pointer source target
      (.op .add [.var base, .const offset]) address
      ⟨relation, by simpa [StackProps.regBoundExp] using bound.2, addressRun⟩
    simp only [addressRun] at sourceRun
    by_cases zero : source.clock = 0
    · simp only [zero, ite_true] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
      subst result
      subst postSource
      refine ⟨emptyEnv target, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluate_shMemOp op register base offset target).trans
            (by simp only [targetAddress, clocks, zero, ite_true])
      · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
    · simp only [zero, ite_false] at sourceRun
      obtain ⟨postTarget, targetRun, postRelation⟩ := shMemOpSimulationZ jump bounds pointer register
        op address (decClock source) (decClock target) postSource result
        (RelationLaws.stateRelDecClock jump bounds pointer source target relation)
        bound.1 sourceRun notError
      refine ⟨postTarget, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluate_shMemOp op register base offset target).trans
            (by simp only [targetAddress, clocks, zero, ite_false]; exact targetRun)
      · cases result with
        | none => exact postRelation
        | some outcome => cases outcome <;> exact postRelation
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.ShMemOp

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.FFI
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.FFI
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

/-- Flapjack-specific factoring of the returning FFI case; no independent HOL
declaration is claimed. The original relation supplies every saved reserved
register and the separated memory frame. Only the actual successful read
needed by the original bytearray frame theorem is required. -/
theorem stateRelFfiWritebackZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (address : BitVec width) (bytes readBytes : List (BitVec 8)) (ffi : HolFfiState F)
    (relation : stateRelHOL jump bounds pointer source target)
    (read : readBytearrayWordHOL address bytes.length
      (memLoadByteAuxExact source.memory source.mdomain source.be) = some readBytes) :
    stateRelHOL jump bounds pointer
      {source with
        memory := writeBytearrayExact address bytes source.memory source.mdomain source.be
        regs := restrictIn source.regs source.ffiSaveRegs
        fpRegs := HolFiniteMapExact.empty
        ffi := ffi}
      {target with
        memory := writeBytearrayExact address bytes target.memory target.mdomain target.be
        regs := restrictIn target.regs target.ffiSaveRegs
        fpRegs := HolFiniteMapExact.empty
        ffi := ffi} := by
  simp only [stateRelHOL] at relation
  rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
  have registers : ∀ register, register < pointer →
      (restrictIn target.regs target.ffiSaveRegs).lookup register =
      (restrictIn source.regs source.ffiSaveRegs).lookup register := by
    intro register below
    simp only [restrictIn_lookup, h10, h18 register below]
  have heapSave := h22 (pointer + 2) (Or.inr (Or.inr rfl))
  have baseSave := h22 (pointer + 1) (Or.inr (Or.inl rfl))
  have pointerSave := h22 pointer (Or.inl rfl)
  simp only [stateRelHOL, restrictIn_lookup, heapSave, baseSave, pointerSave, ite_true]
  refine ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,True.intro,h10,True.intro,h12,h13,h14,h15,h16,h17,registers,h19,h20,h21,h22,h23,h24,?_⟩
  cases baseRead : target.regs.lookup (pointer + 1) with
  | none => simp [baseRead] at h25
  | some value =>
    cases value with
    | loc block offset => simp [baseRead] at h25
    | word base =>
      simp only [baseRead] at h25 ⊢
      refine ⟨h25.1,h25.2.1,h25.2.2.1,h25.2.2.2.1,?_⟩
      simp only [← SetSep.starAssoc] at h25 ⊢
      have updated := writeBytearrayFrame bytes address source.memory source.mdomain source.be readBytes
        _ target.memory target.mdomain ⟨h25.2.2.2.2, read⟩
      simpa only [h6] using updated

/-- Canonical owning-state roundtrip for the representation qualifier;
Flapjack infrastructure with no independent HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original FFI case (2081–2098), with the original four premises,
actual mlstring identifier, native evaluator and FFI result. Byte reads and
framed writeback on the target are proved from the original relation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectFFIZ {width : Nat} [NeZero width] {C F : Type}
    (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.ffi name ptr len ptr2 len2 ret, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.ffi name ptr len ptr2 len2 ret : HolProg width) pointer) :
    ∃ postTarget,
      evaluate (comp jump bounds pointer (.ffi name ptr len ptr2 len2 ret),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change ptr < pointer ∧ len < pointer ∧ ptr2 < pointer ∧ len2 < pointer ∧ ret < pointer at bound
  have ptrEq := RelationLaws.stateRelGetVar jump bounds pointer ptr source target ⟨relation,bound.1⟩
  have lenEq := RelationLaws.stateRelGetVar jump bounds pointer len source target ⟨relation,bound.2.1⟩
  have ptr2Eq := RelationLaws.stateRelGetVar jump bounds pointer ptr2 source target ⟨relation,bound.2.2.1⟩
  have len2Eq := RelationLaws.stateRelGetVar jump bounds pointer len2 source target ⟨relation,bound.2.2.2.1⟩
  have ffiEq : target.ffi = source.ffi :=
    (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
  rw [evaluate_ffi] at sourceRun
  cases readLen : getVar len source with
  | none =>
    simp only [readLen] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some value =>
    cases value with
    | loc block offset =>
      simp only [readLen] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word length1 =>
      cases readPtr : getVar ptr source with
      | none =>
        simp only [readLen, readPtr] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some value =>
        cases value with
        | loc block offset =>
          simp only [readLen, readPtr] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word address1 =>
          cases readLen2 : getVar len2 source with
          | none =>
            simp only [readLen, readPtr, readLen2] at sourceRun
            exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          | some value =>
            cases value with
            | loc block offset =>
              simp only [readLen, readPtr, readLen2] at sourceRun
              exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
            | word length2 =>
              cases readPtr2 : getVar ptr2 source with
              | none =>
                simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
              | some value =>
                cases value with
                | loc block offset =>
                  simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                  exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                | word address2 =>
                  simp only [readLen, readPtr, readLen2, readPtr2] at sourceRun
                  cases read1 : readBytearrayWordHOL address1 length1.toNat (memLoadByteAuxExact source.memory source.mdomain source.be) with
                  | none =>
                    simp only [read1] at sourceRun
                    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                  | some config =>
                    cases read2 : readBytearrayWordHOL address2 length2.toNat (memLoadByteAuxExact source.memory source.mdomain source.be) with
                    | none =>
                      simp only [read1,read2] at sourceRun
                      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                    | some bytes =>
                      have targetRead1 := BytearrayReads.readBytearrayImp jump bounds pointer length1.toNat address1 source target config ⟨relation,read1⟩
                      have targetRead2 := BytearrayReads.readBytearrayImp jump bounds pointer length2.toNat address2 source target bytes ⟨relation,read2⟩
                      simp only [read1,read2] at sourceRun
                      cases call : callFFIHOL source.ffi (.extCall name) config bytes with
                      | final outcome =>
                        simp only [call] at sourceRun
                        rcases Prod.mk.inj sourceRun with ⟨resultEq,postEq⟩
                        subst result
                        subst postSource
                        refine ⟨target,?_,ffiEq⟩
                        simpa only [comp,Nat.zero_add] using
                          (evaluate_ffi name ptr len ptr2 len2 ret target).trans (by
                            simp only [← lenEq,← ptrEq,← len2Eq,← ptr2Eq,readLen,readPtr,readLen2,readPtr2,targetRead1,targetRead2,ffiEq,call])
                      | ret newFfi newBytes =>
                        simp only [call] at sourceRun
                        rcases Prod.mk.inj sourceRun with ⟨resultEq,postEq⟩
                        subst result
                        subst postSource
                        have returnedLength := callFFILengthHOL source.ffi (.extCall name) config bytes newBytes newFfi call
                        have readLength := readBytearrayWordHOL_length address2 length2.toNat
                          (memLoadByteAuxExact source.memory source.mdomain source.be) bytes read2
                        have writeRead : readBytearrayWordHOL address2 newBytes.length
                            (memLoadByteAuxExact source.memory source.mdomain source.be) = some bytes := by
                          rw [returnedLength,readLength]
                          exact read2
                        refine ⟨{target with
                          memory := writeBytearrayExact address2 newBytes target.memory target.mdomain target.be
                          regs := restrictIn target.regs target.ffiSaveRegs
                          fpRegs := HolFiniteMapExact.empty
                          ffi := newFfi},?_,?_⟩
                        · simpa only [comp,Nat.zero_add] using
                            (evaluate_ffi name ptr len ptr2 len2 ret target).trans (by
                              simp only [← lenEq,← ptrEq,← len2Eq,← ptr2Eq,readLen,readPtr,readLen2,readPtr2,targetRead1,targetRead2,ffiEq,call])
                        · exact stateRelFfiWritebackZ jump bounds pointer source target address2 newBytes bytes newFfi relation writeRead
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.FFI

namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Install
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.Install
open InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackAllocSimulation InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackFreeSimulation
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps
/-- Flapjack-only first-match lookup transport for Install; no independent HOL declaration. -/
theorem compiledEntriesLookupZ {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer name : Nat)
    (entries : List (Nat × HolProg width)) :
    sptAListLookup name (entries.map (progComp jump bounds pointer)) =
      (sptAListLookup name entries).map (comp jump bounds pointer) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨other, program⟩
    by_cases same : name = other <;>
      simp [sptAListLookup, progComp, same, ih]

/-- Flapjack-only domain transport for Install, including duplicate names; no independent HOL declaration. -/
theorem compiledEntriesDomainZ {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (entries : List (Nat × HolProg width)) :
    sptDomain (sptFromAList (entries.map (progComp jump bounds pointer))) =
      sptDomain (sptFromAList entries) := by
  funext name
  simp only [sptDomain, sptLookup_sptFromAList, compiledEntriesLookupZ, Option.isSome_map]

/-- Original Install code-relation transition, derived from actual oracle
entry bounds. New code retains first-match lookup and cannot shadow stubs.
Flapjack-only transition factoring; no independent HOL declaration. -/
theorem codeRelInstallZ {width : Nat} [NeZero width]
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : Spt (HolProg width)) (entries : List (Nat × HolProg width))
    (relation : codeRelHOL jump bounds pointer source target)
    (entryBounds : ∀ name program, (name, program) ∈ entries →
      StackProps.regBound program pointer ∧ stackNumStubs ≤ name + 1) :
    codeRelHOL jump bounds pointer
      (sptUnion source (sptFromAList entries))
      (sptUnion target (sptFromAList (entries.map (progComp jump bounds pointer)))) := by
  rcases relation with ⟨lookupRel, domainRel⟩
  constructor
  · intro name program lookup
    rw [sptLookup_sptUnion] at lookup
    cases old : sptLookup name source with
    | some oldProgram =>
      simp only [old] at lookup
      cases Option.some.inj lookup
      obtain ⟨bound, compiled⟩ := lookupRel name program old
      exact ⟨bound, by rw [sptLookup_sptUnion, compiled]⟩
    | none =>
      simp only [old, sptLookup_sptFromAList] at lookup
      obtain ⟨bound, fresh⟩ := entryBounds name program
        (sptAListLookup_mem name entries program lookup)
      have targetOld : sptLookup name target = none := by
        cases found : sptLookup name target with
        | none => rfl
        | some value =>
          have member : sptDomain target name := by simp [sptDomain, found]
          rw [domainRel] at member
          simp only [sptDomain, old, Option.isSome_none, Bool.false_eq_true, false_or] at member
          simp only [stackNumStubs] at fresh
          omega
      refine ⟨bound, ?_⟩
      rw [sptLookup_sptUnion, targetOld, sptLookup_sptFromAList,
        compiledEntriesLookupZ, lookup]
      rfl
  · rw [sptDomain_sptUnion, sptDomain_sptUnion, compiledEntriesDomainZ, domainRel]
    funext name
    apply propext
    tauto
/-- Flapjack-only factoring of the successful Install record update; no independent HOL declaration. -/
def installedState {width : Nat} [NeZero width] {C F : Type}
    (register entry : Nat) (programs : List (Nat × HolProg width))
    (bitmaps : List (BitVec width)) (codeBuffer : WordSemBuffer width 8)
    (dataBuffer : WordSemBuffer width width)
    (state : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  {state with bitmaps := state.bitmaps ++ bitmaps, codeBuffer := codeBuffer, dataBuffer := dataBuffer, code := sptUnion state.code (sptFromAList programs), regs := (StackSemStateOps.restrictIn state.regs state.ffiSaveRegs).updateEq (register, .loc entry 0), fpRegs := HolFiniteMapExact.empty, compileOracle := holShiftSeq 1 state.compileOracle}

/-- Original Install post-relation, derived from the actual successful data
flush and oracle entry bounds. This local transition is infrastructure for
assembling the full constructor case, not an additional HOL declaration. -/
theorem stateRelInstallZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer register entry : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (programs : List (Nat × HolProg width)) (bitmaps : List (BitVec width))
    (codeBuffer : WordSemBuffer width 8) (dataBuffer : WordSemBuffer width width)
    (dataStart dataEnd : BitVec width)
    (relation : stateRelHOL jump bounds pointer source target)
    (registerBound : register < pointer)
    (programsEq : programs = (source.compileOracle 0).2.1)
    (flush : wordSemBufferFlush source.dataBuffer dataStart dataEnd = some (bitmaps, dataBuffer)) :
    stateRelHOL jump bounds pointer
      (installedState register entry programs bitmaps codeBuffer dataBuffer source)
      (installedState register entry (programs.map (progComp jump bounds pointer))
        bitmaps codeBuffer target.dataBuffer target) := by
  have entryBounds : ∀ name program, (name, program) ∈ programs →
      StackProps.regBound program pointer ∧ stackNumStubs ≤ name + 1 := by
    intro name program member
    exact relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 0 name program
      (by simpa [programsEq] using member)
  have codeRelation := codeRelInstallZ jump bounds pointer source.code target.code programs
    relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 entryBounds
  unfold wordSemBufferFlush at flush
  split at flush
  next condition =>
    cases Option.some.inj flush
    simp only [stateRelHOL, installedState] at relation ⊢
    rcases relation with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25⟩
    refine ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,True.intro,True.intro,h13,h14,?_,?_,h17,?_,codeRelation,?_,?_,h22,h23,h24,?_⟩
    · funext index
      simpa only [holShiftSeq] using congrFun h15 (index + 1)
    · intro index name program member
      exact h16 (index + 1) name program member
    · intro query queryBound
      simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        StackSemStateOps.restrictIn_lookup, h10]
      by_cases same : query = register
      · simp [same]
      · simp only [same, if_false]
        rw [h18 query queryBound]
    · rw [sptLookup_sptUnion, h20]
    · have different : pointer + 2 ≠ register := by omega
      simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different, if_false,
        StackSemStateOps.restrictIn_lookup, h22 (pointer + 2) (by simp), if_true, h21]
    · have position : dataEnd = source.dataBuffer.position +
          bytesInWord width * BitVec.ofNat width source.dataBuffer.buffer.length := by
        simpa only [bytesInWord] using condition.2.symm
      simp only [List.append_nil, List.length_append]
      rw [position]
      rcases h25 with ⟨oldPosition, heap⟩
      refine ⟨?_, ?_⟩
      · rw [oldPosition]
        simp [BitVec.ofNat_add, BitVec.mul_add, BitVec.add_assoc]
      · simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          StackSemStateOps.restrictIn_lookup]
        have different : pointer + 1 ≠ register := by omega
        have saved := h22 (pointer + 1) (by simp)
        simp only [different, if_false, saved, if_true]
        have pointerDifferent : pointer ≠ register := by omega
        have pointerSaved := h22 pointer (by simp)
        simpa only [pointerDifferent, if_false, pointerSaved, if_true, List.length_append] using heap
  next => cases flush

/-- Canonical codec of the actual imported evaluator state. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Install constructor case (1932–1997). Retains all five
constructor registers and the original four premises. The native target
execution, compiler/oracle transport, code-union/stub facts, register
restriction and entire post-relation are derived. No target execution,
successful compilation, code relation or desired post-state is assumed.
The evaluator closure inherits the reviewed reals_as_rational_cuts FP
carrier (SOUNDNESS item 8); this constructor executes no FP instruction. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectInstallZ {width : Nat} [NeZero width] {C F : Type}
    (first second third fourth fifth : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.install first second third fourth fifth, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.install first second third fourth fifth : HolProg width) pointer) :
    ∃ postTarget,
      evaluate (comp jump bounds pointer (.install first second third fourth fifth),
        target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change first < pointer ∧ second < pointer ∧ third < pointer ∧ fourth < pointer ∧ fifth < pointer at bound
  have firstRead := (RelationLaws.stateRelGetVar jump bounds pointer first source target ⟨relation, bound.1⟩).symm
  have secondRead := (RelationLaws.stateRelGetVar jump bounds pointer second source target ⟨relation, bound.2.1⟩).symm
  have thirdRead := (RelationLaws.stateRelGetVar jump bounds pointer third source target ⟨relation, bound.2.2.1⟩).symm
  have fourthRead := (RelationLaws.stateRelGetVar jump bounds pointer fourth source target ⟨relation, bound.2.2.2.1⟩).symm
  rw [evaluate_install] at sourceRun
  split at sourceRun
  next _ _ _ _ w1 w2 w3 w4 lookup1 lookup2 lookup3 lookup4 =>
    rcases oracle : source.compileOracle 0 with ⟨cfg, programs, bitmaps⟩
    simp only [oracle, if_pos relation.1] at sourceRun
    split at sourceRun
    next _ _ bytes codeBuffer data dataBuffer codeFlush dataFlush =>
      split at sourceRun
      next _ _ _ compiledBytes nextConfig entry program rest compileRun =>
        split at sourceRun
        next condition =>
          have dataEq : data = bitmaps := by simpa only [oracle] using condition.2.1
          rw [dataEq] at dataFlush
          have programsEq : (entry, program) :: rest = (source.compileOracle 0).2.1 := by
            rw [oracle]
          have compileTransport := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have oracleTransport := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          have targetCompile : target.compile cfg
              (((entry, program) :: rest).map (progComp jump bounds pointer)) =
              some (compiledBytes, nextConfig) :=
            (congrFun (congrFun compileTransport cfg) ((entry, program) :: rest)).symm.trans compileRun
          have targetCompileCons := targetCompile
          simp only [List.map_cons, progComp] at targetCompileCons
          have targetOracle : target.compileOracle 0 =
              (cfg, (((entry, program) :: rest).map (progComp jump bounds pointer)), bitmaps) := by
            rw [oracleTransport]
            simp only [oracle]
          have nextConfigEq : (holShiftSeq 1 target.compileOracle 0).1 = nextConfig := by
            simpa only [holShiftSeq, oracleTransport] using condition.2.2
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          refine ⟨installedState first entry
            (((entry, program) :: rest).map (progComp jump bounds pointer)) bitmaps
            codeBuffer target.dataBuffer target, ?_, ?_⟩
          · simpa only [comp, Nat.zero_add] using
              (evaluate_install first second third fourth fifth target).trans (by
                simp only [firstRead, secondRead, thirdRead, fourthRead,
                  lookup1, lookup2, lookup3, lookup4, targetOracle,
                  relation.2.2.1, Bool.false_eq_true, if_false,
                  relation.2.2.2.2.2.2.2.2.2.2.2.2.1, codeFlush,
                  targetCompileCons, List.map_cons, progComp, condition.1, nextConfigEq,
                  and_self, if_true, installedState])
          · exact stateRelInstallZ jump bounds pointer first entry source target
              ((entry, program) :: rest) bitmaps codeBuffer dataBuffer w3 w4
              relation bound.1 programsEq dataFlush
        next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Install


namespace InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock
export StackAllocSimulation (evaluateStackAllocZ)
export StackFreeSimulation (evaluateStackFreeZ)
export Atoms (compCorrectSkipZ)
export Control (compCorrectTickZ)
export Instructions (compCorrectInstZ)
export StackMemory (compCorrectStackLoadZ compCorrectStackStoreZ)
end InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock
