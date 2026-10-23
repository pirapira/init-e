import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Nat.Basic
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompLn
import InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

set_option hygiene false in
macro "clockB" : tactic => `(tactic| (
  (try have := Flapjack.Compiler.Backend.StackRawCall.LoopCase.stateRel_clock _ _ _ relation);
  (try have := Flapjack.Compiler.Backend.StackRawCall.LoopCase.stateRel_clock _ _ _ postRelation);
  (try have := Flapjack.Compiler.Backend.StackRawCall.LoopCase.stateRel_clock _ _ _ middleRelation);
  (try have := Flapjack.Compiler.Backend.StackRawCall.LoopCase.stateRel_clock _ _ _ bodyRelation);
  (try have := Flapjack.Compiler.Backend.StackRawCall.LoopCase.stateRel_clock _ _ _ entryRelation);
  (try have := Flapjack.Compiler.Backend.StackRawCall.LoopCase.stateRel_clock _ _ _ shiftedRelation);
  (try have := Flapjack.Compiler.Backend.StackRawCall.LoopCase.stateRel_clock _ _ _ originalRelation);
  (try have := Flapjack.Compiler.Backend.StackRawCall.LoopCase.stateRel_clock _ _ _ recursiveRelation);
  (try simp only [Flapjack.StackSemStateOps.decClock, Flapjack.StackSemStateOps.emptyEnv,
     Flapjack.StackSemStateOps.setVar] at *);
  first | omega | (split <;> omega) | (simp_all; done) | (simp_all; omega)))

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.IfCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.IfCase
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Canonical codec for the imported full evaluator state, without a duplicate
carrier or assumed representation relation. Flapjack infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-! Guard transport infrastructure for the genuine recursive If case of
rawcall comp_correct. No source/target evaluation is assumed by these laws. -/

theorem getVar_targetClockB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (register clock : Nat) :
    StackSemStateOps.getVar register { target with clock := clock } =
      StackSemStateOps.getVar register source := by
  obtain ⟨code, _, equality, _⟩ := relation
  subst target
  rfl

theorem getVarImm_targetClockB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target)
    (operand : Compiler.Encoders.Asm.HolRegImm width) (clock : Nat) :
    StackSemStateOps.getVarImm (Compiler.Encoders.Asm.HolRegImm.toWordRegImm operand)
      { target with clock := clock } =
    StackSemStateOps.getVarImm (Compiler.Encoders.Asm.HolRegImm.toWordRegImm operand)
      source := by
  obtain ⟨code, _, equality, _⟩ := relation
  subst target
  cases operand <;> rfl

/-- The actual compiled If dispatch reads exactly the source operands at
every target clock. Both recursive evaluations remain explicit. -/
theorem evaluateCompiledIfB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (comparison : Cmp) (register : Nat)
    (operand : Compiler.Encoders.Asm.HolRegImm width) (first second : HolProg width)
    (clock : Nat) :
    StackSemEvaluate.evaluate
      (comp info (.ite comparison register operand first second), { target with clock := clock }) =
    match StackSemStateOps.getVar register source,
      StackSemStateOps.getVarImm (Compiler.Encoders.Asm.HolRegImm.toWordRegImm operand) source with
    | some left, some right =>
      match wordSemWordCmp comparison left right with
      | some true => StackSemEvaluate.evaluate (comp info first, { target with clock := clock })
      | some false => StackSemEvaluate.evaluate (comp info second, { target with clock := clock })
      | none => (some .error, { target with clock := clock })
    | _, _ => (some .error, { target with clock := clock }) := by
  simp only [comp, StackSemEvaluate.evaluate_ite,
    getVar_targetClockB info source target relation,
    getVarImm_targetClockB info source target relation]
  rfl

/-! The following abbreviations spell out the original existential conclusion
and its comp component induction hypothesis. They are Flapjack infrastructure,
not alternative evaluators or supplied target results. -/
abbrev SimulationResultB {width : Nat} [NeZero width] {C F : Type}
    (compiled : HolProg width) (info : Spt Nat)
    (target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) : Prop :=
  ∃ clock targetState stackSpace,
    clock + targetState.clock ≤ target.clock ∧
    stateRel info resultState targetState ∧
    StackSemEvaluate.evaluate (compiled, { target with clock := target.clock + clock }) =
      (result, { targetState with stackSpace := stackSpace }) ∧
    (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
      stackSpace = targetState.stackSpace)

abbrev ProgramIHB {width : Nat} [NeZero width] (C F : Type) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (info : Spt Nat) (target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)),
    StackSemEvaluate.evaluate (program, source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target →
    SimulationResultB (comp info program) info target resultState result

/-- The original evaluate_ind branch IH: its source is fixed, and the operand
reads and selected comparison result guard the recursive motive. This is
Flapjack notation for that IH, not a separately named HOL declaration. -/
abbrev BranchIHB {width : Nat} [NeZero width] (C F : Type)
    (comparison : Cmp) (register : Nat) (operand : Compiler.Encoders.Asm.HolRegImm width)
    (truth : Bool) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (left right : WordLocW width),
    StackSemStateOps.getVar register source = some left →
    StackSemStateOps.getVarImm (Compiler.Encoders.Asm.HolRegImm.toWordRegImm operand)
      source = some right →
    wordSemWordCmp comparison left right = some truth →
    ProgramIHB C F program source

/-- Genuine recursive If case: the original fixed-source, selected-branch
evaluate_ind hypotheses augment the three original premises. Both existential conclusions
are retained. The full evaluator inherits its documented real-carrier
assurance limit; this comparison/branch proof introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectIfB {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : Compiler.Encoders.Asm.HolRegImm width)
    (first second : HolProg width)
    (info : Spt Nat) (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : BranchIHB C F comparison register operand true first source)
    (secondIH : BranchIHB C F comparison register operand false second source)
    (hypothesis : StackSemEvaluate.evaluate (.ite comparison register operand first second, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.ite comparison register operand first second))
      info target resultState result ∧
    SimulationResultB (comp info (.ite comparison register operand first second))
      info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  have same : compTop info (.ite comparison register operand first second) =
      comp info (.ite comparison register operand first second) := rfl
  rw [same]
  suffices simulation : SimulationResultB
      (comp info (.ite comparison register operand first second)) info target resultState result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_ite] at execution
  split at execution
  · rename_i left right leftRead rightRead
    split at execution
    · rename_i compared
      obtain ⟨clock, targetState, stackSpace, hb_clock, postRelation, targetExecution, guard⟩ :=
        firstIH left right leftRead rightRead compared
          info target resultState result ⟨execution, nonerror, relation⟩
      refine ⟨clock, targetState, stackSpace, (by first | exact hbz | clockB), postRelation, ?_, guard⟩
      rw [evaluateCompiledIfB info source target relation]
      simp_all
    · rename_i compared
      obtain ⟨clock, targetState, stackSpace, hb_clock, postRelation, targetExecution, guard⟩ :=
        secondIH left right leftRead rightRead compared
          info target resultState result ⟨execution, nonerror, relation⟩
      refine ⟨clock, targetState, stackSpace, (by first | exact hbz | clockB), postRelation, ?_, guard⟩
      rw [evaluateCompiledIfB info source target relation]
      simp_all
    · simp_all
  · simp_all
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.IfCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.BasicLeaves
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.BasicLeaves
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemExpressions

/-- Canonical codec for the actual imported full-state owner; representation
infrastructure without a separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-! Flapjack infrastructure identifying six genuine nonrecursive cases of
the original rawcall comp_correct proof. No simplified evaluator is used. -/
inductive BasicLeaf {width : Nat} [NeZero width] : HolProg width → Prop where
  | skip : BasicLeaf .skip
  | halt (register : Nat) : BasicLeaf (.halt register)
  | get (register : Nat) (name : StoreName) : BasicLeaf (.get register name)
  | set (name : StoreName) (register : Nat) : BasicLeaf (.set name register)
  | opCurrHeap (operator : Compiler.Encoders.Asm.HolBinop) (destination source : Nat) :
      BasicLeaf (.opCurrHeap operator destination source)
  | tick : BasicLeaf .tick

/-- Actual evaluator transport, including source failures and timeouts.
Flapjack support only: the constructor premise is discharged by each final
HOL case theorem, not exposed as an extra pass-correctness premise. -/
theorem evaluate_codeUpdateB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : BasicLeaf program)
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemEvaluate.evaluate (program, { source with code := code }) =
      let outcome := StackSemEvaluate.evaluate (program, source)
      (outcome.1, { outcome.2 with code := code }) := by
  cases leaf <;>
    simp only [StackSemEvaluate.evaluate_skip, StackSemEvaluate.evaluate_halt,
      StackSemEvaluate.evaluate_get, StackSemEvaluate.evaluate_set,
      StackSemEvaluate.evaluate_opCurrHeap, StackSemEvaluate.evaluate_tick,
      wordExp_codeUpdate, getVar, setVar, setStore, emptyEnv, decClock]
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- Derived preservation of the actual code tree, including error outcomes. -/
theorem evaluate_code_eqB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : BasicLeaf program)
    (source : StackSemStateFiniteExact width C F) :
    (StackSemEvaluate.evaluate (program, source)).2.code = source.code := by
  have transport := evaluate_codeUpdateB program leaf source source.code
  have unchanged : { source with code := source.code } = source := by
    cases source
    rfl
  rw [unchanged] at transport
  have projected := congrArg (fun outcome : Option (StackSemResult width) ×
    StackSemStateFiniteExact width C F => outcome.2.code) transport
  exact projected

/-- Full postrelation and target evaluation derived from actual leaf execution.
The leaf predicate is infrastructure; each final source case discharges it. -/
theorem evaluate_stateRelB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : BasicLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (program, source) = (result, resultState))
    (relation : stateRel info source target) :
    ∃ targetState, stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (program, target) = (result, targetState) := by
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  have codeEq := evaluate_code_eqB program leaf source
  rw [execution] at codeEq
  change resultState.code = source.code at codeEq
  refine ⟨{ resultState with code := code }, ?_, ?_⟩
  · refine ⟨code, ?_, rfl, ?_, ?_⟩
    · simpa only [codeEq] using domain
    · simpa only [codeEq] using frames
    · simpa only [codeEq] using entries
  · rw [evaluate_codeUpdateB program leaf, execution]

/-- Flapjack support assembling the original paired existential conclusion.
The constructor predicate is discharged by each of the six final HOL cases. -/
theorem compCorrectBasicB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : BasicLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  obtain ⟨execution, _, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  obtain ⟨targetState, postRelation, targetExecution⟩ :=
    evaluate_stateRelB program leaf info source target resultState result execution relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  have compSelf : comp info program = program := by
    cases leaf <;> rfl
  have compTopSelf : compTop info program = program := by
    cases leaf <;> rfl
  constructor <;>
    refine ⟨0, targetState, targetState.stackSpace, (by first | exact hbz | clockB), postRelation, ?_, fun _ => rfl⟩
  · rw [clockSelf, stackSelf, compTopSelf]
    exact targetExecution
  · rw [clockSelf, stackSelf, compSelf]
    exact targetExecution

/-- Genuine original Skip case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSkipB {width : Nat} [NeZero width] {C F : Type}
     (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.skip : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.skip : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.skip : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasicB (.skip : HolProg width) .skip info source target resultState result hypothesis

/-- Genuine original Halt case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectHaltB {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.halt register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.halt register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.halt register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasicB (.halt register : HolProg width) (.halt register) info source target resultState result hypothesis

/-- Genuine original Get case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectGetB {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (name : StoreName) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.get register name : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.get register name : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.get register name : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasicB (.get register name : HolProg width) (.get register name) info source target resultState result hypothesis

/-- Genuine original Set case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSetB {width : Nat} [NeZero width] {C F : Type}
    (name : StoreName) (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.set name register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.set name register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.set name register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasicB (.set name register : HolProg width) (.set name register) info source target resultState result hypothesis

/-- Genuine original OpCurrHeap case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectOpCurrHeapB {width : Nat} [NeZero width] {C F : Type}
    (operator : Compiler.Encoders.Asm.HolBinop) (destination input : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.opCurrHeap operator destination input : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.opCurrHeap operator destination input : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.opCurrHeap operator destination input : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasicB (.opCurrHeap operator destination input : HolProg width) (.opCurrHeap operator destination input) info source target resultState result hypothesis

/-- Genuine original Tick case with the original three premises and both
existential conclusions. Native evaluator retains its inherited real-carrier
assurance limit; this case proof introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectTickB {width : Nat} [NeZero width] {C F : Type}
     (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.tick : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.tick : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.tick : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectBasicB (.tick : HolProg width) .tick info source target resultState result hypothesis
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.BasicLeaves

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.ControlLeaves
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.ControlLeaves
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemExpressions

/-- Canonical codec for the actual imported full-state owner; representation
infrastructure without a separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-! Flapjack infrastructure identifying four genuine nonrecursive cases of
the original rawcall comp_correct proof. No simplified evaluator is used. -/
inductive ControlLeaf {width : Nat} [NeZero width] : HolProg width → Prop where
  | ret (register : Nat) : ControlLeaf (.ret register)
  | raise (register : Nat) : ControlLeaf (.raise register)
  | break (label : Nat) : ControlLeaf (.break label)
  | continue (label : Nat) : ControlLeaf (.continue label)

/-- Actual evaluator transport, including source failures and timeouts.
Flapjack support only: the constructor premise is discharged by each final
HOL case theorem, not exposed as an extra pass-correctness premise. -/
theorem evaluate_codeUpdateB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : ControlLeaf program)
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemEvaluate.evaluate (program, { source with code := code }) =
      let outcome := StackSemEvaluate.evaluate (program, source)
      (outcome.1, { outcome.2 with code := code }) := by
  cases leaf <;>
    simp only [StackSemEvaluate.evaluate_ret, StackSemEvaluate.evaluate_raise,
      StackSemEvaluate.evaluate_break, StackSemEvaluate.evaluate_continue, getVar]
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- Derived preservation of the actual code tree, including error outcomes. -/
theorem evaluate_code_eqB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : ControlLeaf program)
    (source : StackSemStateFiniteExact width C F) :
    (StackSemEvaluate.evaluate (program, source)).2.code = source.code := by
  have transport := evaluate_codeUpdateB program leaf source source.code
  have unchanged : { source with code := source.code } = source := by
    cases source
    rfl
  rw [unchanged] at transport
  have projected := congrArg (fun outcome : Option (StackSemResult width) ×
    StackSemStateFiniteExact width C F => outcome.2.code) transport
  exact projected

/-- Full postrelation and target evaluation derived from actual leaf execution.
The leaf predicate is infrastructure; each final source case discharges it. -/
theorem evaluate_stateRelB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : ControlLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (program, source) = (result, resultState))
    (relation : stateRel info source target) :
    ∃ targetState, stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (program, target) = (result, targetState) := by
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  have codeEq := evaluate_code_eqB program leaf source
  rw [execution] at codeEq
  change resultState.code = source.code at codeEq
  refine ⟨{ resultState with code := code }, ?_, ?_⟩
  · refine ⟨code, ?_, rfl, ?_, ?_⟩
    · simpa only [codeEq] using domain
    · simpa only [codeEq] using frames
    · simpa only [codeEq] using entries
  · rw [evaluate_codeUpdateB program leaf, execution]

/-- Flapjack support assembling the original paired existential conclusion.
The constructor predicate is discharged by each of the four final HOL cases. -/
theorem compCorrectControlB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : ControlLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  obtain ⟨execution, _, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  obtain ⟨targetState, postRelation, targetExecution⟩ :=
    evaluate_stateRelB program leaf info source target resultState result execution relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  have compSelf : comp info program = program := by
    cases leaf <;> rfl
  have compTopSelf : compTop info program = program := by
    cases leaf <;> rfl
  constructor <;>
    refine ⟨0, targetState, targetState.stackSpace, (by first | exact hbz | clockB), postRelation, ?_, fun _ => rfl⟩
  · rw [clockSelf, stackSelf, compTopSelf]
    exact targetExecution
  · rw [clockSelf, stackSelf, compSelf]
    exact targetExecution

/-- Genuine original Return case with the original three premises and both
existential conclusions. The native evaluator inherits its documented real-carrier
assurance limit; this case introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectReturnB {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.ret register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.ret register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.ret register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectControlB (.ret register : HolProg width) (.ret register) info source target resultState result hypothesis

/-- Genuine original Raise case with the original three premises and both
existential conclusions. The native evaluator inherits its documented real-carrier
assurance limit; this case introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectRaiseB {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.raise register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.raise register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.raise register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectControlB (.raise register : HolProg width) (.raise register) info source target resultState result hypothesis

/-- Genuine original Break case with the original three premises and both
existential conclusions. The native evaluator inherits its documented real-carrier
assurance limit; this case introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectBreakB {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.break register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.break register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.break register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectControlB (.break register : HolProg width) (.break register) info source target resultState result hypothesis

/-- Genuine original Continue case with the original three premises and both
existential conclusions. The native evaluator inherits its documented real-carrier
assurance limit; this case introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectContinueB {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.continue register : HolProg width), source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info (.continue register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info (.continue register : HolProg width), { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  exact compCorrectControlB (.continue register : HolProg width) (.continue register) info source target resultState result hypothesis
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.ControlLeaves

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.LoopCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.LoopCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl

/-- Genuine canonical codec for the actual imported full evaluator state.
Flapjack representation infrastructure with no separate HOL original. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-! Flapjack infrastructure for the genuine recursive rawcall Loop case.
These laws derive whole-state transport from the literal source relation;
they do not assume a target evaluation or postrelation. -/

theorem stateRel_clockB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) : target.clock = source.clock := by
  obtain ⟨code, _, equality, _⟩ := relation
  subst target
  rfl

theorem stateRel_setClockB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (clock : Nat) :
    stateRel info { source with clock := clock } { target with clock := clock } := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  subst target
  exact ⟨code, domain, rfl, frames, entries⟩

theorem stateRel_decClockB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) :
    stateRel info (decClock source) (decClock target) := by
  have clockEq := stateRel_clockB info source target relation
  simpa only [decClock, clockEq] using
    stateRel_setClockB info source target relation (source.clock - 1)

theorem stateRel_emptyEnvB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) :
    stateRel info (emptyEnv source) (emptyEnv target) := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  subst target
  exact ⟨code, domain, rfl, frames, entries⟩

/-- The actual Loop dispatch after the already proved unconditional clock
clamp identity. No body or recursive target execution is assumed. -/
theorem evaluateLoopUnclampedB {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.loop body, source) =
      match StackSemEvaluate.evaluate (body, source) with
      | (result, post) =>
        if contLoop result then
          if post.clock = 0 then (some .timeOut, emptyEnv post)
          else StackSemEvaluate.evaluate (.loop body, decClock post)
        else (StackSemControl.exitLoop result, post) := by
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate]

/-- Non-error Loop execution forces the actual body result to be non-error.
This is a derived induction-hypothesis side condition, not a new case premise. -/
theorem loopBodyNonErrorB {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.loop body, source) = (result, resultState))
    (nonerror : result ≠ some .error) :
    (StackSemEvaluate.evaluate (body, source)).1 ≠ some .error := by
  rw [evaluateLoopUnclampedB] at execution
  rcases bodyExecution : StackSemEvaluate.evaluate (body, source) with ⟨bodyResult, bodyPost⟩
  rw [bodyExecution] at execution
  intro error
  change bodyResult = some .error at error
  subst bodyResult
  simp only [contLoop, StackSemControl.exitLoop, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
  exact nonerror execution.1.symm

/-- Actual recursive source state has a strictly smaller clock. -/
theorem loopReentryClockLessB {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (body, source) = (result, post))
    (nonzero : post.clock ≠ 0) : (decClock post).clock < source.clock := by
  have bound := StackSemEvaluateClock.evaluateClock body source result post execution
  simp only [decClock]
  omega

/-- Exit dispatch preserves the exceptional results mentioned by the original
stack-space guard. Flapjack infrastructure for this case, not a HOL port. -/
theorem exitLoopGuardB {width : Nat} [NeZero width]
    (result : Option (StackSemResult width))
    (guard : StackSemControl.exitLoop result ≠ some .timeOut ∧
      StackSemControl.exitLoop result ≠ some (.halt (.word (BitVec.ofNat width 2)))) :
    result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) := by
  constructor
  · intro h
    subst result
    exact guard.1 rfl
  · intro h
    subst result
    exact guard.2 rfl

/-- Infrastructure for the exiting branch of the genuine Loop case. The
non-continuation condition is discharged by the final case split; it is not
an additional premise of a tagged comp_correct case. -/
theorem compCorrectLoopExitB {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : IfCase.ProgramIHB C F body source)
    (execution : StackSemEvaluate.evaluate (body, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target)
    (exit : contLoop result = false) :
    IfCase.SimulationResultB (comp info (.loop body)) info target post
      (StackSemControl.exitLoop result) := by
  obtain ⟨clock, targetState, stackSpace, hb_clock, postRelation, targetExecution, guard⟩ :=
    bodyIH info target post result ⟨execution, nonerror, relation⟩
  refine ⟨clock, targetState, stackSpace, (by first | exact hbz | clockB), postRelation, ?_, ?_⟩
  · rw [comp, evaluateLoopUnclampedB, targetExecution]
    simp only [exit, Bool.false_eq_true, if_false]
  · intro exitGuard
    exact guard (exitLoopGuardB result exitGuard)

/-- Loop continuation excludes both exceptional stack-space guard results. -/
theorem contLoopGuardB {width : Nat} [NeZero width]
    (result : Option (StackSemResult width)) (continuing : contLoop result = true) :
    result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) := by
  rcases Compiler.Backend.StackProps.contLoopImp result continuing with h | h <;>
    simp [h]

/-- The zero-clock continuation branch, with target timeout and relation
both derived from the actual body induction hypothesis. Untagged case support. -/
theorem compCorrectLoopTimeoutB {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : IfCase.ProgramIHB C F body source)
    (execution : StackSemEvaluate.evaluate (body, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target)
    (continuing : contLoop result = true) (zero : post.clock = 0) :
    IfCase.SimulationResultB (comp info (.loop body)) info target (emptyEnv post)
      (some .timeOut) := by
  obtain ⟨clock, targetState, stackSpace, hb_clock, postRelation, targetExecution, guard⟩ :=
    bodyIH info target post result ⟨execution, nonerror, relation⟩
  have spaceEq := guard (contLoopGuardB result continuing)
  subst stackSpace
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  rw [stackSelf] at targetExecution
  have targetZero : targetState.clock = 0 :=
    (stateRel_clockB info post targetState postRelation).trans zero
  refine ⟨clock, emptyEnv targetState, (emptyEnv targetState).stackSpace, (by first | exact hbz | clockB),
    stateRel_emptyEnvB info post targetState postRelation, ?_, ?_⟩
  · rw [comp, evaluateLoopUnclampedB, targetExecution]
    simp only [continuing, if_true]
    rw [if_pos targetZero]
  · intro impossible
    exact False.elim (impossible.1 rfl)

/-- The original evaluate_ind Loop reentry IH at the actual body's post-state.
The source body evaluation, continuation and nonzero post-clock guard the
motive at decClock bodyPost; no arbitrary smaller-clock state is quantified. -/
abbrev LoopReentryIHB {width : Nat} [NeZero width] (C F : Type)
    (body : HolProg width) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (bodyResult : Option (StackSemResult width))
    (bodyPost : StackSemStateFiniteExact width C F),
    StackSemEvaluate.evaluate (body, source) = (bodyResult, bodyPost) →
    contLoop bodyResult = true → bodyPost.clock ≠ 0 →
    IfCase.ProgramIHB C F (.loop body) (decClock bodyPost)

/-- Nonzero continuation: extend the actual target body clock by the clock
needed for the smaller recursive Loop execution. All target results are derived
from the two genuine IHs. Untagged case-split infrastructure. -/
theorem compCorrectLoopReentryB {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target bodyPost post : StackSemStateFiniteExact width C F)
    (bodyResult result : Option (StackSemResult width))
    (bodyIH : IfCase.ProgramIHB C F body source)
    (reentryIH : LoopReentryIHB C F body source)
    (bodyExecution : StackSemEvaluate.evaluate (body, source) = (bodyResult, bodyPost))
    (bodyNonerror : bodyResult ≠ some .error) (relation : stateRel info source target)
    (continuing : contLoop bodyResult = true) (nonzero : bodyPost.clock ≠ 0)
    (execution : StackSemEvaluate.evaluate (.loop body, decClock bodyPost) = (result, post))
    (nonerror : result ≠ some .error) :
    IfCase.SimulationResultB (comp info (.loop body)) info target post result := by
  obtain ⟨clock, targetBody, stackSpace, hb_clock, bodyRelation, targetBodyExecution, bodyGuard⟩ :=
    bodyIH info target bodyPost bodyResult ⟨bodyExecution, bodyNonerror, relation⟩
  have continuationGuard := contLoopGuardB bodyResult continuing
  have spaceEq := bodyGuard continuationGuard
  subst stackSpace
  have stackSelf : { targetBody with stackSpace := targetBody.stackSpace } = targetBody := by
    cases targetBody
    rfl
  rw [stackSelf] at targetBodyExecution
  have recursiveRelation := stateRel_decClockB info bodyPost targetBody bodyRelation
  obtain ⟨recursiveClock, targetPost, finalSpace, hb_recursiveClock, postRelation, targetExecution, guard⟩ :=
    reentryIH bodyResult bodyPost bodyExecution continuing nonzero
      info (decClock targetBody) post result
      ⟨execution, nonerror, recursiveRelation⟩
  have targetClockEq := stateRel_clockB info bodyPost targetBody bodyRelation
  have targetNonzero : targetBody.clock ≠ 0 := by
    simpa only [targetClockEq] using nonzero
  have extendedBody := Compiler.Backend.StackProps.evaluateAddClock recursiveClock
    (comp info body) { target with clock := target.clock + clock }
    bodyResult targetBody ⟨targetBodyExecution, continuationGuard.1⟩
  have inputEq : { { target with clock := target.clock + clock } with
      clock := ({ target with clock := target.clock + clock }).clock + recursiveClock } =
      { target with clock := target.clock + (clock + recursiveClock) } := by
    simp only [Nat.add_assoc]
  rw [inputEq] at extendedBody
  have reentryEq : decClock { targetBody with clock := targetBody.clock + recursiveClock } =
      { decClock targetBody with clock := (decClock targetBody).clock + recursiveClock } := by
    simp only [decClock]
    congr 1
    omega
  refine ⟨clock + recursiveClock, targetPost, finalSpace, (by first | exact hbz | clockB), postRelation, ?_, guard⟩
  rw [comp, evaluateLoopUnclampedB, extendedBody]
  simp only [continuing, if_true]
  rw [if_neg (show targetBody.clock + recursiveClock ≠ 0 by omega), reentryEq]
  exact targetExecution

/-- Genuine recursive Loop case. The original three premises are retained;
only the body IH at the fixed source and actual guarded body-post reentry IH
are added. Both original compTop/comp existential conclusions remain intact.
The full native evaluator inherits its documented real-carrier assurance limit;
this proof introduces no real rendering. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectLoopB {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (bodyIH : IfCase.ProgramIHB C F body source)
    (reentryIH : LoopReentryIHB C F body source)
    (hypothesis : StackSemEvaluate.evaluate (.loop body, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    IfCase.SimulationResultB (compTop info (.loop body)) info target post result ∧
    IfCase.SimulationResultB (comp info (.loop body)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  have bodyNonerror := loopBodyNonErrorB body source post result execution nonerror
  have same : compTop info (.loop body) = comp info (.loop body) := rfl
  rw [same]
  suffices simulation : IfCase.SimulationResultB (comp info (.loop body)) info target post result by
    exact ⟨simulation, simulation⟩
  rw [evaluateLoopUnclampedB] at execution
  rcases bodyExecution : StackSemEvaluate.evaluate (body, source) with ⟨bodyResult, bodyPost⟩
  rw [bodyExecution] at execution bodyNonerror
  change bodyResult ≠ some .error at bodyNonerror
  by_cases continuing : contLoop bodyResult = true
  · simp only [continuing, if_true] at execution
    by_cases zero : bodyPost.clock = 0
    · rw [if_pos zero] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      exact compCorrectLoopTimeoutB body info source target bodyPost bodyResult bodyIH
        bodyExecution bodyNonerror relation continuing zero
    · rw [if_neg zero] at execution
      exact compCorrectLoopReentryB body info source target bodyPost post bodyResult result
        bodyIH reentryIH bodyExecution bodyNonerror relation continuing zero execution nonerror
  · have exit : contLoop bodyResult = false := by
      cases h : contLoop bodyResult <;> simp_all
    simp only [exit, Bool.false_eq_true, if_false] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    exact compCorrectLoopExitB body info source target bodyPost bodyResult bodyIH
      bodyExecution bodyNonerror relation exit
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.LoopCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.RawCallCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.RawCallCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open IfCase

/-- Frame preservation derived from actual evaluation. Flapjack infrastructure. -/
theorem stateOk_afterEvaluateB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (program : HolProg width)
    (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (frames : stateOk info source.code)
    (execution : StackSemEvaluate.evaluate (program, source) = (result, post)) :
    stateOk info post.code := by
  have mono := (StackProps.EvaluateMono.evaluateMono program source post result execution).2
  intro key size entry
  obtain ⟨body, lookup⟩ := frames key size entry
  exact ⟨body, (sptSubsptLookup source.code post.code).mp mono key _ lookup⟩

/-- Outer frame information affects only its explicit stateOk obligation.
Flapjack infrastructure retaining the per-entry compilation witnesses. -/
theorem stateRel_changeInfoB {width : Nat} [NeZero width] {C F : Type}
    (oldInfo newInfo : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel oldInfo source target) (frames : stateOk newInfo source.code) :
    stateRel newInfo source target := by
  obtain ⟨code, domain, equality, _, entries⟩ := relation
  exact ⟨code, domain, equality, frames, entries⟩

/-- Actual compiled callee lookup derived from the literal relation.
Flapjack infrastructure with no target evaluation premise. -/
theorem rawCallEntryB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (dest : Nat) (first body : HolProg width)
    (lookup : sptLookup dest source.code = some (.seq first body)) :
    ∃ entryInfo : Spt Nat,
      stateRel entryInfo source target ∧
      sptLookup dest target.code = some (.seq (comp entryInfo first) (comp entryInfo body)) := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  obtain ⟨entryInfo, entryFrames, compiled⟩ := entries dest _ lookup
  refine ⟨entryInfo, ⟨code, domain, equality, entryFrames, entries⟩, ?_⟩
  subst target
  simpa only [compTop] using compiled

/-- Actual evaluate_ind callee hypothesis at the fixed recursive source.
Only the comp component of the paired original motive is used. -/
abbrev CalleeIHB {width : Nat} [NeZero width] (C F : Type) (dest : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ first body, sptLookup dest source.code = some (.seq first body) →
    source.clock ≠ 0 → ProgramIHB C F body (decClock source)

/-- Canonical roundtrip of the actual imported evaluator state; representation
infrastructure, without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine RawCall simulation with the original three premises and actual
callee induction hypothesis. Both original existential conclusions remain.
The unused compTop component of the paired callee motive is omitted. Native
compTop preserves the leading Seq, so target dispatch selects the compiled
callee body directly. Frame preservation is derived from evaluateMono.
The full evaluator inherits SOUNDNESS item 8 reals_as_rational_cuts; this
case introduces no real rendering or cross-language equivalence claim. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectRawCallB {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : CalleeIHB C F dest source)
    (hypothesis : StackSemEvaluate.evaluate (.rawCall dest, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.rawCall dest)) info target resultState result ∧
    SimulationResultB (comp info (.rawCall dest)) info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  change SimulationResultB (.rawCall dest) info target resultState result ∧
    SimulationResultB (.rawCall dest) info target resultState result
  suffices simulation : SimulationResultB (.rawCall dest) info target resultState result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_rawCall] at execution
  cases lookup : sptLookup dest source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
    rw [lookup] at execution
    cases program <;> simp only [destSeq] at execution
    all_goals try (exact False.elim (nonerror (Prod.mk.inj execution).1.symm))
    rename_i first body
    obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
      rawCallEntryB info source target relation dest first body lookup
    have clockEq := LoopCase.stateRel_clockB info source target relation
    by_cases zero : source.clock = 0
    · simp only [zero, if_true, Prod.mk.injEq] at execution
      obtain ⟨rfl, rfl⟩ := execution
      refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace, (by first | exact hbz | clockB),
        LoopCase.stateRel_emptyEnvB info source target relation, ?_, ?_⟩
      · simp only [Nat.add_zero, StackSemEvaluate.evaluate_rawCall, targetLookup,
          destSeq]
        have tz : target.clock = 0 := clockEq.trans zero
        simp only [tz, if_true]
        have update : { target with clock := 0 } = target := by
          rw [← tz]
        rw [update]
      · simp
    · simp only [zero, if_false] at execution
      rcases bodyExecution : StackSemEvaluate.evaluate (body, decClock source) with
        ⟨bodyResult, bodyPost⟩
      rw [bodyExecution] at execution
      by_cases bad : badFunReturn bodyResult = true
      · simp only [bad, if_true, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨clock, targetState, stackSpace, hb_clock, postRelation, targetExecution, guard⟩ :=
          calleeIH first body lookup zero entryInfo (decClock target) bodyPost bodyResult
            ⟨bodyExecution, nonerror,
              LoopCase.stateRel_decClockB entryInfo source target entryRelation⟩
        have frames : stateOk info source.code := by
          obtain ⟨_, _, _, frames, _⟩ := relation
          exact frames
        have postFrames := stateOk_afterEvaluateB info body (decClock source) bodyPost
          bodyResult frames bodyExecution
        refine ⟨clock, targetState, stackSpace, (by first | exact hbz | clockB),
          stateRel_changeInfoB entryInfo info bodyPost targetState postRelation postFrames,
          ?_, guard⟩
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + clock ≠ 0 := by omega
        simp only [StackSemEvaluate.evaluate_rawCall, targetLookup, destSeq,
          addedNonzero, if_false,
          StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
          targetExecution, bad, Bool.false_eq_true, if_false]
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.RawCallCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.StackAccessCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.StackAccessCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps
open IfCase

/-! Full original562-581 cases. The native full evaluator inherits the reviewed
reals_as_rational_cuts assurance limit (SOUNDNESS item 8); these stack and label
proofs introduce no real rendering, production-policy change or equivalence
claim. All stack/map/clock/configuration/FFI fields remain native and intact. -/

/-- Canonical roundtrip of the actual imported evaluator state; representation
infrastructure, without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Nine native stack-access cases. Flapjack constructor classification. -/
inductive StackLeaf {width : Nat} [NeZero width] : HolProg width → Prop where
  | stackAlloc (n : Nat) : StackLeaf (.stackAlloc n)
  | stackFree (n : Nat) : StackLeaf (.stackFree n)
  | stackLoad (r n : Nat) : StackLeaf (.stackLoad r n)
  | stackLoadAny (r rn : Nat) : StackLeaf (.stackLoadAny r rn)
  | stackStore (r n : Nat) : StackLeaf (.stackStore r n)
  | stackStoreAny (r rn : Nat) : StackLeaf (.stackStoreAny r rn)
  | stackGetSize (r : Nat) : StackLeaf (.stackGetSize r)
  | stackSetSize (r : Nat) : StackLeaf (.stackSetSize r)
  | bitmapLoad (r v : Nat) : StackLeaf (.bitmapLoad r v)

/-- Unconditional code-update transport derived from actual stack clauses,
including source errors and halt outcomes. Flapjack infrastructure. -/
theorem evaluate_codeUpdateB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : StackLeaf program)
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemEvaluate.evaluate (program, { source with code := code }) =
      let outcome := StackSemEvaluate.evaluate (program, source)
      (outcome.1, { outcome.2 with code := code }) := by
  cases leaf <;>
    simp only [StackSemEvaluate.evaluate_stackAlloc, StackSemEvaluate.evaluate_stackFree,
      StackSemEvaluate.evaluate_stackLoad, StackSemEvaluate.evaluate_stackLoadAny,
      StackSemEvaluate.evaluate_stackStore, StackSemEvaluate.evaluate_stackStoreAny,
      StackSemEvaluate.evaluate_stackGetSize, StackSemEvaluate.evaluate_stackSetSize,
      StackSemEvaluate.evaluate_bitmapLoad, getVar, setVar, emptyEnv]
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- Actual code relation preserves location observations, including the
zero-offset domain branch and all labels inside compiled code entries. -/
theorem locCheck_stateRelB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (label : Nat × Nat) :
    StackSem.locCheckExact target.code label ↔ StackSem.locCheckExact source.code label := by
  obtain ⟨code, domain, equality, _, entries⟩ := relation
  subst target
  have member (key : Nat) : sptMem key code ↔ sptMem key source.code := by
    change sptDomain code key ↔ sptDomain source.code key
    rw [domain]
  constructor
  · rintro (⟨zero, mem⟩ | ⟨key, compiled, lookup, labels⟩)
    · exact Or.inl ⟨zero, (member _).mp mem⟩
    · have mem : sptMem key code := (sptMem_iff_lookup key code).mpr ⟨compiled, lookup⟩
      obtain ⟨body, original⟩ := (sptMem_iff_lookup key source.code).mp ((member key).mp mem)
      obtain ⟨entryInfo, _, compiledLookup⟩ := entries key body original
      have same : compiled = compTop entryInfo body := by
        exact Option.some.inj (lookup.symm.trans compiledLookup)
      subst compiled
      exact Or.inr ⟨key, body, original, by
        simpa only [(getLabelsComp entryInfo body).2] using labels⟩
  · rintro (⟨zero, mem⟩ | ⟨key, body, lookup, labels⟩)
    · exact Or.inl ⟨zero, (member _).mpr mem⟩
    · obtain ⟨entryInfo, _, compiledLookup⟩ := entries key body lookup
      exact Or.inr ⟨key, compTop entryInfo body, compiledLookup, by
        simpa only [(getLabelsComp entryInfo body).2] using labels⟩

/-- Derived preservation of the actual code tree, including error outcomes. -/
theorem evaluate_code_eqB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : StackLeaf program)
    (source : StackSemStateFiniteExact width C F) :
    (StackSemEvaluate.evaluate (program, source)).2.code = source.code := by
  have transport := evaluate_codeUpdateB program leaf source source.code
  have unchanged : { source with code := source.code } = source := by
    cases source
    rfl
  rw [unchanged] at transport
  have projected := congrArg (fun outcome : Option (StackSemResult width) ×
    StackSemStateFiniteExact width C F => outcome.2.code) transport
  exact projected

/-- Full postrelation and target evaluation derived from actual leaf execution.
The leaf predicate is infrastructure; each final source case discharges it. -/
theorem evaluate_stateRelB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : StackLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (program, source) = (result, resultState))
    (relation : stateRel info source target) :
    ∃ targetState, stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (program, target) = (result, targetState) := by
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  have codeEq := evaluate_code_eqB program leaf source
  rw [execution] at codeEq
  change resultState.code = source.code at codeEq
  refine ⟨{ resultState with code := code }, ?_, ?_⟩
  · refine ⟨code, ?_, rfl, ?_, ?_⟩
    · simpa only [codeEq] using domain
    · simpa only [codeEq] using frames
    · simpa only [codeEq] using entries
  · rw [evaluate_codeUpdateB program leaf, execution]

/-- Flapjack support assembling the original paired existential conclusion.
The constructor predicate is discharged by each of the nine final HOL cases. -/
theorem compCorrectStackB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : StackLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  obtain ⟨execution, _, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  obtain ⟨targetState, postRelation, targetExecution⟩ :=
    evaluate_stateRelB program leaf info source target resultState result execution relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  have compSelf : comp info program = program := by
    cases leaf <;> rfl
  have compTopSelf : compTop info program = program := by
    cases leaf <;> rfl
  constructor <;>
    refine ⟨0, targetState, targetState.stackSpace, (by first | exact hbz | clockB), postRelation, ?_, fun _ => rfl⟩
  · rw [clockSelf, stackSelf, compTopSelf]
    exact targetExecution
  · rw [clockSelf, stackSelf, compSelf]
    exact targetExecution


/-- Literal LocValue case: successful target label checking is derived from
stateRel and getLabelsComp, rather than supplied as a simulation premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectLocValueB {width : Nat} [NeZero width] {C F : Type}
    (register first second : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.locValue register first second, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.locValue register first second)) info target resultState result ∧
    SimulationResultB (comp info (.locValue register first second)) info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  have labels := locCheck_stateRelB info source target relation (first, second)
  rw [StackSemEvaluate.evaluate_locValue] at execution
  split at execution
  · rename_i location
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    obtain ⟨code, domain, equality, frames, entries⟩ := relation
    subst target
    have postRelation : stateRel info (setVar register (.loc first second) source)
        { setVar register (.loc first second) source with code := code } := by
      exact ⟨code, domain, rfl, frames, entries⟩
    have targetLocation : StackSem.locCheckExact code (first, second) := labels.mpr location
    constructor <;>
      refine ⟨0, { setVar register (.loc first second) source with code := code },
        (setVar register (.loc first second) source).stackSpace, (by first | exact hbz | clockB), postRelation, ?_, ?_⟩
    all_goals try (intro _; rfl)
    all_goals simp only [compTop, comp, Nat.add_zero, StackSemEvaluate.evaluate_locValue,
      targetLocation, if_true, setVar]
  · exact False.elim (nonerror (Prod.mk.inj execution).1.symm)

/-- Genuine original stackAlloc case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackAllocB {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackAlloc n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.stackAlloc n)) info target resultState result ∧
    SimulationResultB (comp info (.stackAlloc n)) info target resultState result :=
  compCorrectStackB (.stackAlloc n) (.stackAlloc n)
    info source target resultState result hypothesis

/-- Genuine original stackFree case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackFreeB {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackFree n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.stackFree n)) info target resultState result ∧
    SimulationResultB (comp info (.stackFree n)) info target resultState result :=
  compCorrectStackB (.stackFree n) (.stackFree n)
    info source target resultState result hypothesis

/-- Genuine original stackLoad case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackLoadB {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackLoad r n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.stackLoad r n)) info target resultState result ∧
    SimulationResultB (comp info (.stackLoad r n)) info target resultState result :=
  compCorrectStackB (.stackLoad r n) (.stackLoad r n)
    info source target resultState result hypothesis

/-- Genuine original stackLoadAny case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackLoadAnyB {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackLoadAny r rn, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.stackLoadAny r rn)) info target resultState result ∧
    SimulationResultB (comp info (.stackLoadAny r rn)) info target resultState result :=
  compCorrectStackB (.stackLoadAny r rn) (.stackLoadAny r rn)
    info source target resultState result hypothesis

/-- Genuine original stackStore case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackStoreB {width : Nat} [NeZero width] {C F : Type}
    (r n : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackStore r n, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.stackStore r n)) info target resultState result ∧
    SimulationResultB (comp info (.stackStore r n)) info target resultState result :=
  compCorrectStackB (.stackStore r n) (.stackStore r n)
    info source target resultState result hypothesis

/-- Genuine original stackStoreAny case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackStoreAnyB {width : Nat} [NeZero width] {C F : Type}
    (r rn : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackStoreAny r rn, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.stackStoreAny r rn)) info target resultState result ∧
    SimulationResultB (comp info (.stackStoreAny r rn)) info target resultState result :=
  compCorrectStackB (.stackStoreAny r rn) (.stackStoreAny r rn)
    info source target resultState result hypothesis

/-- Genuine original stackGetSize case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackGetSizeB {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackGetSize r, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.stackGetSize r)) info target resultState result ∧
    SimulationResultB (comp info (.stackGetSize r)) info target resultState result :=
  compCorrectStackB (.stackGetSize r) (.stackGetSize r)
    info source target resultState result hypothesis

/-- Genuine original stackSetSize case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStackSetSizeB {width : Nat} [NeZero width] {C F : Type}
    (r : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.stackSetSize r, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.stackSetSize r)) info target resultState result ∧
    SimulationResultB (comp info (.stackSetSize r)) info target resultState result :=
  compCorrectStackB (.stackSetSize r) (.stackSetSize r)
    info source target resultState result hypothesis

/-- Genuine original bitmapLoad case: all three source premises and both
existential conclusions, with no supplied target evaluation or postrelation. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectBitmapLoadB {width : Nat} [NeZero width] {C F : Type}
    (r v : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.bitmapLoad r v, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.bitmapLoad r v)) info target resultState result ∧
    SimulationResultB (comp info (.bitmapLoad r v)) info target resultState result :=
  compCorrectStackB (.bitmapLoad r v) (.bitmapLoad r v)
    info source target resultState result hypothesis
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.StackAccessCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.MemoryFfiCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.MemoryFfiCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps
open IfCase

/-- Four source constructor cases; Flapjack classification infrastructure. -/
inductive MemoryLeaf {width : Nat} [NeZero width] : HolProg width → Prop where
  | shMemOp (op : Compiler.Encoders.Asm.HolMemop) (r a : Nat) (w : BitVec width) :
      MemoryLeaf (.shMemOp op r (.addr a w))
  | codeBufferWrite (r1 r2 : Nat) : MemoryLeaf (.codeBufferWrite r1 r2)
  | dataBufferWrite (r1 r2 : Nat) : MemoryLeaf (.dataBufferWrite r1 r2)
  | ffi (function : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) :
      MemoryLeaf (.ffi function ptr len ptr2 len2 ret)

/-- Unconditional native code-update transport, including errors, timeout and
FFI final outcomes. Flapjack infrastructure, not an extra simulation premise. -/
theorem evaluate_codeUpdateB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : MemoryLeaf program)
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemEvaluate.evaluate (program, { source with code := code }) =
      let outcome := StackSemEvaluate.evaluate (program, source)
      (outcome.1, { outcome.2 with code := code }) := by
  cases leaf
  case shMemOp op r a w =>
    cases op <;>
      simp [StackSemEvaluate.evaluate_shMemOp, StackSemExpressions.wordExp,
        StackSemShMem.shMemOp, StackSemShMem.shMemLoad, StackSemShMem.shMemStore,
        StackSemShMem.shMemLoadByte, StackSemShMem.shMemStoreByte,
        StackSemShMem.shMemLoad16, StackSemShMem.shMemStore16,
        StackSemShMem.shMemLoad32, StackSemShMem.shMemStore32,
        getVar, emptyEnv, decClock]
    all_goals split_ifs <;> try simp_all
    all_goals repeat' (first | rfl | (split <;> try simp_all))
    all_goals split_ifs <;> try simp_all
    all_goals repeat' (first | rfl | (split <;> try simp_all))
  all_goals
    simp only [StackSemEvaluate.evaluate_codeBufferWrite,
      StackSemEvaluate.evaluate_dataBufferWrite, StackSemEvaluate.evaluate_ffi, getVar]
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- Derived preservation of the actual code tree, including error outcomes. -/
theorem evaluate_code_eqB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : MemoryLeaf program)
    (source : StackSemStateFiniteExact width C F) :
    (StackSemEvaluate.evaluate (program, source)).2.code = source.code := by
  have transport := evaluate_codeUpdateB program leaf source source.code
  have unchanged : { source with code := source.code } = source := by
    cases source
    rfl
  rw [unchanged] at transport
  have projected := congrArg (fun outcome : Option (StackSemResult width) ×
    StackSemStateFiniteExact width C F => outcome.2.code) transport
  exact projected

/-- Full postrelation and target evaluation derived from actual leaf execution.
The leaf predicate is infrastructure; each final source case discharges it. -/
theorem evaluate_stateRelB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : MemoryLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (program, source) = (result, resultState))
    (relation : stateRel info source target) :
    ∃ targetState, stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (program, target) = (result, targetState) := by
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  have codeEq := evaluate_code_eqB program leaf source
  rw [execution] at codeEq
  change resultState.code = source.code at codeEq
  refine ⟨{ resultState with code := code }, ?_, ?_⟩
  · refine ⟨code, ?_, rfl, ?_, ?_⟩
    · simpa only [codeEq] using domain
    · simpa only [codeEq] using frames
    · simpa only [codeEq] using entries
  · rw [evaluate_codeUpdateB program leaf, execution]

/-- Flapjack support assembling the original paired existential conclusion.
The constructor predicate is discharged by each of the four final HOL cases. -/
theorem compCorrectMemoryB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (leaf : MemoryLeaf program) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, resultState) ∧
      result ≠ some .error ∧ stateRel info source target) :
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (compTop info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) ∧
    (∃ clock targetState stackSpace,
      clock + targetState.clock ≤ target.clock ∧
      stateRel info resultState targetState ∧
      StackSemEvaluate.evaluate (comp info program, { target with clock := target.clock + clock }) =
        (result, { targetState with stackSpace := stackSpace }) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetState.stackSpace)) := by
  obtain ⟨execution, _, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  obtain ⟨targetState, postRelation, targetExecution⟩ :=
    evaluate_stateRelB program leaf info source target resultState result execution relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
    cases targetState
    rfl
  have compSelf : comp info program = program := by
    cases leaf <;> rfl
  have compTopSelf : compTop info program = program := by
    cases leaf <;> rfl
  constructor <;>
    refine ⟨0, targetState, targetState.stackSpace, (by first | exact hbz | clockB), postRelation, ?_, fun _ => rfl⟩
  · rw [clockSelf, stackSelf, compTopSelf]
    exact targetExecution
  · rw [clockSelf, stackSelf, compSelf]
    exact targetExecution


/-- Canonical roundtrip of the actual imported evaluator state; representation
infrastructure, without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness


/-- Full original ShMemOp case, retaining the three source premises and both
existential simulation conclusions. The evaluator inherits the reviewed
reals_as_rational_cuts assurance limit in SOUNDNESS item 8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectShMemOpB {width : Nat} [NeZero width] {C F : Type}
    (op : Compiler.Encoders.Asm.HolMemop) (r a : Nat) (w : BitVec width) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.shMemOp op r (.addr a w), source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.shMemOp op r (.addr a w))) info target resultState result ∧
    SimulationResultB (comp info (.shMemOp op r (.addr a w))) info target resultState result :=
  compCorrectMemoryB (.shMemOp op r (.addr a w)) (.shMemOp op r a w)
    info source target resultState result hypothesis

/-- Full original CodeBufferWrite case, retaining the three source premises and both
existential simulation conclusions. The evaluator inherits the reviewed
reals_as_rational_cuts assurance limit in SOUNDNESS item 8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCodeBufferWriteB {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.codeBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.codeBufferWrite r1 r2)) info target resultState result ∧
    SimulationResultB (comp info (.codeBufferWrite r1 r2)) info target resultState result :=
  compCorrectMemoryB (.codeBufferWrite r1 r2) (.codeBufferWrite r1 r2)
    info source target resultState result hypothesis

/-- Full original DataBufferWrite case, retaining the three source premises and both
existential simulation conclusions. The evaluator inherits the reviewed
reals_as_rational_cuts assurance limit in SOUNDNESS item 8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectDataBufferWriteB {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.dataBufferWrite r1 r2, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.dataBufferWrite r1 r2)) info target resultState result ∧
    SimulationResultB (comp info (.dataBufferWrite r1 r2)) info target resultState result :=
  compCorrectMemoryB (.dataBufferWrite r1 r2) (.dataBufferWrite r1 r2)
    info source target resultState result hypothesis

/-- Full original Ffi case, retaining the three source premises and both
existential simulation conclusions. The evaluator inherits the reviewed
reals_as_rational_cuts assurance limit in SOUNDNESS item 8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectFfiB {width : Nat} [NeZero width] {C F : Type}
    (function : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.ffi function ptr len ptr2 len2 ret, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.ffi function ptr len ptr2 len2 ret)) info target resultState result ∧
    SimulationResultB (comp info (.ffi function ptr len ptr2 len2 ret)) info target resultState result :=
  compCorrectMemoryB (.ffi function ptr len ptr2 len2 ret) (.ffi function ptr len ptr2 len2 ret)
    info source target resultState result hypothesis
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.MemoryFfiCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.AllocationStoreCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.AllocationStoreCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps
open IfCase

/-- Flapjack infrastructure: actual GC cannot observe the code field. All
collector inputs and outcomes are retained, including failed decoding. -/
theorem gc_codeUpdateB {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (code : Spt (HolProg width)) :
    StackSemAllocation.gc { source with code := code } =
      (StackSemAllocation.gc source).map (fun post => { post with code := code }) := by
  simp only [StackSemAllocation.gc]
  split_ifs <;> simp_all
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- A successful original optional stub check yields the target stub through
stateRel's actual per-entry compilation witness. It is not invariant under an
arbitrary code replacement. Flapjack constructor infrastructure. -/
theorem checkStoreConstsOpt_targetB {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target)
    (checked : StackSemStoreConstsGuard.checkStoreConstsOpt first second stub source.code = true) :
    StackSemStoreConstsGuard.checkStoreConstsOpt first second stub target.code = true := by
  obtain ⟨code, _, targetEq, _, entries⟩ := relation
  subst target
  cases stub with
  | none => rfl
  | some label =>
      have lookup := (StackSemStoreConstsGuard.checkStoreConstsOpt_some_iff first second label source.code).mp checked
      obtain ⟨entryInfo, _, compiledLookup⟩ := entries label _ lookup
      apply (StackSemStoreConstsGuard.checkStoreConstsOpt_some_iff first second label code).mpr
      simpa [compTop, comp] using compiledLookup


/-- Actual allocation code transport, including GC failure, post-GC errors and
Halt Word1 after environment clearing. Flapjack infrastructure. -/
theorem alloc_codeUpdateB {width : Nat} [NeZero width] {C F : Type}
    (amount : BitVec width) (source : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) :
    StackSemAllocation.alloc amount { source with code := code } =
      let outcome := StackSemAllocation.alloc amount source
      (outcome.1, { outcome.2 with code := code }) := by
  simp only [StackSemAllocation.alloc, setStore]
  have transport := gc_codeUpdateB (setStore .allocSize (.word amount) source) code
  dsimp only [setStore] at transport
  rw [transport]
  cases h : StackSemAllocation.gc (setStore .allocSize (.word amount) source) <;>
    simp only [setStore] at h
  all_goals simp only [h, Option.map_none, Option.map_some]
  all_goals repeat' (first | rfl | (split <;> try simp_all [emptyEnv]))

/-- Unconditional actual Alloc evaluator transport. -/
theorem evaluateAlloc_codeUpdateB {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (source : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) :
    StackSemEvaluate.evaluate (.alloc register, { source with code := code }) =
      let outcome := StackSemEvaluate.evaluate (.alloc register, source)
      (outcome.1, { outcome.2 with code := code }) := by
  simp only [StackSemEvaluate.evaluate_alloc, getVar]
  split <;> try rfl
  split <;> try rfl
  exact alloc_codeUpdateB _ source code

/-- Actual store-constant execution transport independent of the optional
code guard; preserves copy failure and unset-register behavior. -/
theorem storeConstSem_codeUpdateB {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (source : StackSemStateFiniteExact width C F)
    (code : Spt (HolProg width)) :
    StackSemStoreConsts.storeConstSem (resultWidth := width) first second { source with code := code } =
      let outcome := StackSemStoreConsts.storeConstSem (resultWidth := width) first second source
      (outcome.1, { outcome.2 with code := code }) := by
  simp only [StackSemStoreConsts.storeConstSem, getVar, setVar]
  all_goals repeat' (first | rfl | (split <;> try simp_all))

/-- Real code equality and postrelation derived from unconditional operation
transport. Flapjack infrastructure; final case theorems derive transport from
native clauses rather than assume a target execution. -/
theorem postRelationOfTransportB {width : Nat} [NeZero width] {C F : Type}
    (operation : StackSemStateFiniteExact width C F →
      Option (StackSemResult width) × StackSemStateFiniteExact width C F)
    (source target post : StackSemStateFiniteExact width C F) (info : Spt Nat)
    (result : Option (StackSemResult width))
    (transport : ∀ code, operation { source with code := code } =
      let outcome := operation source
      (outcome.1, { outcome.2 with code := code }))
    (execution : operation source = (result, post))
    (relation : stateRel info source target) :
    ∃ targetPost, stateRel info post targetPost ∧ operation target = (result, targetPost) := by
  have self := transport source.code
  have unchanged : { source with code := source.code } = source := by cases source; rfl
  rw [unchanged, execution] at self
  have codeEq : post.code = source.code := congrArg (fun outcome => outcome.2.code) self
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  refine ⟨{ post with code := code }, ⟨code, ?_, rfl, ?_, ?_⟩, ?_⟩
  · simpa only [codeEq] using domain
  · simpa only [codeEq] using frames
  · simpa only [codeEq] using entries
  · rw [transport code, execution]

/-- Actual successful source StoreConsts dispatch supplies all guards. The
compiled optional stub guard is independently derived from stateRel. -/
theorem evaluateStoreConsts_stateRelB {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post))
    (nonerror : result ≠ some .error) (relation : stateRel info source target) :
    ∃ targetPost, stateRel info post targetPost ∧
      StackSemEvaluate.evaluate (.storeConsts first second stub, target) = (result, targetPost) := by
  have useStore : ¬ (¬ source.useStore) := by
    intro h
    rw [StackSemEvaluate.evaluate_storeConsts, if_pos h] at execution
    exact nonerror (Prod.mk.inj execution).1.symm
  have useAlloc : ¬ (¬ source.useAlloc ∧ stub.isSome) := by
    intro h
    rw [StackSemEvaluate.evaluate_storeConsts, if_neg useStore, if_pos h] at execution
    exact nonerror (Prod.mk.inj execution).1.symm
  have checked : StackSemStoreConstsGuard.checkStoreConstsOpt first second stub source.code = true := by
    by_contra h
    rw [StackSemEvaluate.evaluate_storeConsts, if_neg useStore, if_neg useAlloc, if_pos h] at execution
    exact nonerror (Prod.mk.inj execution).1.symm
  have targetChecked := checkStoreConstsOpt_targetB first second stub info source target relation checked
  have sourceBody : StackSemStoreConsts.storeConstSem (resultWidth := width) first second source = (result, post) := by
    simpa only [StackSemEvaluate.evaluate_storeConsts, if_neg useStore, if_neg useAlloc,
      checked, Bool.true_eq, not_true_eq_false, if_false] using execution
  obtain ⟨targetPost, postRelation, targetBody⟩ := postRelationOfTransportB
    (StackSemStoreConsts.storeConstSem (resultWidth := width) first second)
    source target post info result (storeConstSem_codeUpdateB first second source) sourceBody relation
  refine ⟨targetPost, postRelation, ?_⟩
  obtain ⟨code, _, targetEq, _, _⟩ := relation
  subst target
  simpa only [StackSemEvaluate.evaluate_storeConsts, if_neg useStore, if_neg useAlloc,
    targetChecked, Bool.true_eq, not_true_eq_false, if_false] using targetBody

/-- Canonical roundtrip of the actual imported evaluator state; representation
infrastructure, without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness



/-- Full original Alloc case153-163: original three source premises and both
existential simulations. Native GC/store-copy outcomes and the target optional
stub guard are derived. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectAllocB {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.alloc register, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.alloc register)) info target post result ∧
    SimulationResultB (comp info (.alloc register)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  obtain ⟨targetPost, postRelation, targetExecution⟩ := postRelationOfTransportB (fun state => StackSemEvaluate.evaluate (.alloc register, state))
      source target post info result (evaluateAlloc_codeUpdateB register source) execution relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetPost with stackSpace := targetPost.stackSpace } = targetPost := by
    cases targetPost
    rfl
  constructor <;>
    refine ⟨0, targetPost, targetPost.stackSpace, (by first | exact hbz | clockB), postRelation, ?_, fun _ => rfl⟩ <;>
    simpa only [clockSelf, stackSelf, compTop, comp] using targetExecution

/-- Full original StoreConsts case153-163: original three source premises and both
existential simulations. Native GC/store-copy outcomes and the target optional
stub guard are derived. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectStoreConstsB {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat) (stub : Option Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.storeConsts first second stub, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.storeConsts first second stub)) info target post result ∧
    SimulationResultB (comp info (.storeConsts first second stub)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  obtain ⟨targetPost, postRelation, targetExecution⟩ := evaluateStoreConsts_stateRelB first second stub info source target post result
      execution nonerror relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetPost with stackSpace := targetPost.stackSpace } = targetPost := by
    cases targetPost
    rfl
  constructor <;>
    refine ⟨0, targetPost, targetPost.stackSpace, (by first | exact hbz | clockB), postRelation, ?_, fun _ => rfl⟩ <;>
    simpa only [clockSelf, stackSelf, compTop, comp] using targetExecution
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.AllocationStoreCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.InstallCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.InstallCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps
open IfCase

/-- Flapjack infrastructure: Install's old-code-left-biased union preserves
every frame allocation already witnessed in the original code. -/
theorem stateOk_unionB {width : Nat} [NeZero width] (info : Spt Nat)
    (old added : Spt (HolProg width)) (frames : stateOk info old) :
    stateOk info (sptUnion old added) := by
  intro n v entry
  obtain ⟨body, lookup⟩ := frames n v entry
  refine ⟨body, ?_⟩
  simp only [sptLookup_sptUnion, lookup]

/-- Flapjack infrastructure for the actual Install update. Old entries retain
their original frame witness; newly visible entries use empty information.
Equal old domains ensure that a new source entry is also new on the target.
The result is a relation on the full updated state, not an evaluation premise. -/
theorem stateRel_unionB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target updated : StackSemStateFiniteExact width C F)
    (added : Spt (HolProg width)) (relation : stateRel info source target)
    (codeEq : updated.code = sptUnion source.code added) :
    stateRel info updated { updated with code := sptUnion target.code added } := by
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  refine ⟨sptUnion code added, ?_, rfl, ?_, ?_⟩
  · simp only [codeEq, sptDomain_sptUnion, domain]
  · rw [codeEq]
    exact stateOk_unionB info source.code added frames
  · intro n body entry
    rw [codeEq, sptLookup_sptUnion] at entry
    cases old : sptLookup n source.code with
    | some oldBody =>
        simp only [old, Option.some.injEq] at entry
        subst oldBody
        obtain ⟨entryInfo, entryFrames, targetEntry⟩ := entries n body old
        refine ⟨entryInfo, ?_, ?_⟩
        · rw [codeEq]
          exact stateOk_unionB entryInfo source.code added entryFrames
        · simp only [sptLookup_sptUnion, targetEntry]
    | none =>
        have targetNone : sptLookup n code = none := by
          have sameDomain := congrFun domain n
          simp only [sptDomain, old, Option.isSome_none, Bool.false_eq_true] at sameDomain
          cases found : sptLookup n code <;> simp_all
        refine ⟨.ln, stateOk_empty updated.code, ?_⟩
        simpa only [sptLookup_sptUnion, targetNone, old, (compLn info body).1] using entry

/-- Flapjack infrastructure deriving Install's actual target execution and
full postrelation from the source execution. Every buffer, oracle, compiler,
register and error branch is retained; no target outcome is assumed. -/
theorem evaluateInstall_stateRelB {width : Nat} [NeZero width] {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post)) (nonerror : result ≠ some .error)
    (relation : stateRel info source target) :
    ∃ targetPost, stateRel info post targetPost ∧
      StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, target) =
        (result, targetPost) := by
  classical
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  have originalRelation : stateRel info source {source with code := code} :=
    ⟨code, domain, rfl, frames, entries⟩
  simp only [StackSemEvaluate.evaluate_install, getVar] at execution ⊢
  split at execution <;> try simp_all
  split at execution <;> try simp_all
  split at execution <;> try simp_all
  split at execution <;> try simp_all
  obtain ⟨rfl, rfl⟩ := execution
  exact stateRel_unionB info source _ _ _ originalRelation rfl

/-- Canonical roundtrip of the imported evaluator state. Representation
infrastructure; no separate HOL declaration or duplicate state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Install case520-539: the original three premises imply both
existential simulations, including actual native oracle/compiler/buffer updates.
Old entries win the union; newly visible entries use empty frame information.
Configuration equality is internal classical decidability, not an extra source
premise. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectInstallB {width : Nat} [NeZero width] {C F : Type}
    (ptr len dptr dlen ret : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.install ptr len dptr dlen ret, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.install ptr len dptr dlen ret)) info target post result ∧
    SimulationResultB (comp info (.install ptr len dptr dlen ret)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  obtain ⟨targetPost, postRelation, targetExecution⟩ :=
    evaluateInstall_stateRelB ptr len dptr dlen ret info source target post result
      execution nonerror relation
  have clockSelf : { target with clock := target.clock + 0 } = target := by
    cases target
    simp
  have stackSelf : { targetPost with stackSpace := targetPost.stackSpace } = targetPost := by
    cases targetPost
    rfl
  constructor <;>
    refine ⟨0, targetPost, targetPost.stackSpace, (by first | exact hbz | clockB), postRelation, ?_, fun _ => rfl⟩ <;>
    simpa only [clockSelf, stackSelf, compTop, comp] using targetExecution
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.InstallCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.JumpLowerCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.JumpLowerCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open IfCase RawCallCase

/-- Actual arbitrary callee lookup and its independent frame information,
derived from stateRel. Flapjack infrastructure, not a supplied target run. -/
theorem calleeEntryB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (dest : Nat) (program : HolProg width)
    (lookup : sptLookup dest source.code = some program) :
    ∃ entryInfo : Spt Nat, stateRel entryInfo source target ∧
      sptLookup dest target.code = some (compTop entryInfo program) := by
  obtain ⟨code, domain, equality, _, entries⟩ := relation
  obtain ⟨entryInfo, frames, compiled⟩ := entries dest program lookup
  refine ⟨entryInfo, ⟨code, domain, equality, frames, entries⟩, ?_⟩
  subst target
  exact compiled

/-- The compTop component of the original paired recursive motive.
Flapjack notation; the unused comp component is omitted for this case. -/
abbrev TopProgramIHB {width : Nat} [NeZero width] (C F : Type) (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)),
    StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target →
    SimulationResultB (compTop info program) info target post result

/-- Actual selected-callee evaluate_ind hypothesis at the fixed decClock
source. Operand reads, the unsigned comparison, code lookup and nonzero clock
are precisely the guards of the original recursive call. -/
abbrev JumpIHB {width : Nat} [NeZero width] (C F : Type) (r1 r2 dest : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (left right : BitVec width) (program : HolProg width),
    StackSemStateOps.getVar r1 source = some (.word left) →
    StackSemStateOps.getVar r2 source = some (.word right) →
    Compiler.Encoders.Asm.wordCmpHOL .lower left right = true →
    sptLookup dest source.code = some program →
    source.clock ≠ 0 → TopProgramIHB C F program (decClock source)

/-- Canonical roundtrip of the actual imported evaluator state; representation
infrastructure, without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine original JumpLower case, preserving both original existential
conclusions and the actual selected-callee induction hypothesis. The unused
comp component of the paired callee motive is omitted; actual target code
entries contain compTop. Source nonError derives callee nonError and valid
return dispatch. Full evaluateMono derives the outer frame-info postcondition.
The full native evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8);
this case introduces no real rendering or HOL-to-Lean equivalence claim. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectJumpLowerB {width : Nat} [NeZero width] {C F : Type}
    (r1 r2 dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : JumpIHB C F r1 r2 dest source)
    (hypothesis : StackSemEvaluate.evaluate (.jumpLower r1 r2 dest, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.jumpLower r1 r2 dest)) info target post result ∧
    SimulationResultB (comp info (.jumpLower r1 r2 dest)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  change SimulationResultB (.jumpLower r1 r2 dest) info target post result ∧
    SimulationResultB (.jumpLower r1 r2 dest) info target post result
  suffices simulation : SimulationResultB (.jumpLower r1 r2 dest) info target post result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_jumpLower] at execution
  split at execution
  · rename_i left right firstRead secondRead
    split at execution
    · rename_i lower
      simp only [findCode] at execution
      cases lookup : sptLookup dest source.code with
      | none =>
        simp only [lookup, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      | some program =>
        rw [lookup] at execution
        obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
          calleeEntryB info source target relation dest program lookup
        have clockEq := LoopCase.stateRel_clockB info source target relation
        by_cases zero : source.clock = 0
        · simp only [zero, if_true, Prod.mk.injEq] at execution
          obtain ⟨rfl, rfl⟩ := execution
          refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace, (by first | exact hbz | clockB),
            LoopCase.stateRel_emptyEnvB info source target relation, ?_, ?_⟩
          · simp only [Nat.add_zero, StackSemEvaluate.evaluate_jumpLower,
              getVar_targetClockB info source target relation, firstRead, secondRead,
              lower, if_true, findCode, targetLookup]
            have tz : target.clock = 0 := clockEq.trans zero
            simp only [tz, if_true]
            have update : { target with clock := 0 } = target := by rw [← tz]
            rw [update]
          · simp
        · simp only [zero, if_false] at execution
          rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
            ⟨bodyResult, bodyPost⟩
          rw [bodyExecution] at execution
          by_cases bad : badFunReturn bodyResult = true
          · simp only [bad, if_true, Prod.mk.injEq] at execution
            exact False.elim (nonerror execution.1.symm)
          · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
            obtain ⟨rfl, rfl⟩ := execution
            obtain ⟨clock, targetState, stackSpace, hb_clock, postRelation, targetExecution, guard⟩ :=
              calleeIH left right program firstRead secondRead lower lookup zero
                entryInfo (decClock target) bodyPost bodyResult
                ⟨bodyExecution, nonerror,
                  LoopCase.stateRel_decClockB entryInfo source target entryRelation⟩
            have frames : stateOk info source.code := by
              obtain ⟨_, _, _, frames, _⟩ := relation
              exact frames
            have postFrames := stateOk_afterEvaluateB info program (decClock source) bodyPost
              bodyResult frames bodyExecution
            refine ⟨clock, targetState, stackSpace, (by first | exact hbz | clockB),
              stateRel_changeInfoB entryInfo info bodyPost targetState postRelation postFrames,
              ?_, guard⟩
            have targetNonzero : target.clock ≠ 0 := by omega
            have addedNonzero : target.clock + clock ≠ 0 := by omega
            simp only [StackSemEvaluate.evaluate_jumpLower,
              getVar_targetClockB info source target relation, firstRead, secondRead,
              lower, if_true, findCode, targetLookup, addedNonzero, if_false,
              StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
              targetExecution, bad, Bool.false_eq_true, if_false]
    · rename_i notLower
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      refine ⟨0, target, target.stackSpace, (by first | exact hbz | clockB), relation, ?_, fun _ => rfl⟩
      simp only [StackSemEvaluate.evaluate_jumpLower,
        getVar_targetClockB info source target relation, firstRead, secondRead,
        notLower, Bool.false_eq_true, if_false]
      have update : { target with clock := target.clock + 0 } = target := by
        cases target
        simp
      rw [update]
  · exact False.elim (nonerror (Prod.mk.inj execution).1.symm)
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.JumpLowerCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.CallCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.CallCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open IfCase RawCallCase

/-- Actual direct or indirect callee lookup through the literal code relation.
Flapjack infrastructure: no target evaluation is a premise. -/
theorem callEntryB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (dest : Sum Nat Nat)
    (program : HolProg width)
    (lookup : findCode dest source.regs source.code = some program) :
    ∃ entryInfo : Spt Nat, stateRel entryInfo source target ∧
      findCode dest target.regs target.code = some (compTop entryInfo program) := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  subst target
  have entry : ∀ label, sptLookup label source.code = some program →
      ∃ entryInfo : Spt Nat,
        stateRel entryInfo source {source with code := code} ∧
        sptLookup label code = some (compTop entryInfo program) := by
    intro label found
    obtain ⟨entryInfo, entryFrames, compiled⟩ := entries label program found
    exact ⟨entryInfo, ⟨code, domain, rfl, entryFrames, entries⟩, compiled⟩
  cases dest with
  | inl label => simpa only [findCode] using entry label lookup
  | inr reg =>
      cases value : source.regs.lookup reg with
      | none => simp [findCode, value] at lookup
      | some word =>
          cases word with
          | word bits => simp [findCode, value] at lookup
          | loc label offset =>
              cases offset with
              | zero =>
                  have found : sptLookup label source.code = some program := by
                    simpa only [findCode, value] using lookup
                  simpa only [findCode, value] using entry label found
              | succ offset => simp [findCode, value] at lookup

/-- The original tail-call callee induction hypothesis at its fixed recursive
source, guarded by actual lookup and nonzero clock. Only its compTop component
is used; the unused comp component of the paired motive is omitted. -/
abbrev TailCalleeIHB {width : Nat} [NeZero width] (C F : Type)
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) : Prop :=
  handler = none → ∀ program, findCode dest source.regs source.code = some program →
    source.clock ≠ 0 →
    ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
      (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, decClock source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info (decClock source) target →
    SimulationResultB (compTop info program) info target post result

/-- Canonical roundtrip for the actual imported evaluator state. Flapjack
representation infrastructure with no separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine NONE-return Call branch of comp_correct409-446, including arbitrary
direct/indirect lookup, invalid handlers, zero clock and all callee outcomes.
The three original source premises and guarded callee IH establish both
existential simulations. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCallTailB {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : TailCalleeIHB C F dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call none dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.call none dest handler)) info target post result ∧
    SimulationResultB (comp info (.call none dest handler)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  change SimulationResultB (.call none dest handler) info target post result ∧
    SimulationResultB (.call none dest handler) info target post result
  suffices simulation : SimulationResultB (.call none dest handler) info target post result by
    exact ⟨simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_call] at execution
  cases lookup : findCode dest source.regs source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
      rw [lookup] at execution
      cases handler with
      | some handler =>
          simp only [Prod.mk.injEq] at execution
          exact False.elim (nonerror execution.1.symm)
      | none =>
          obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
            callEntryB info source target relation dest program lookup
          have clockEq := LoopCase.stateRel_clockB info source target relation
          by_cases zero : source.clock = 0
          · simp only [zero, if_true, Prod.mk.injEq] at execution
            obtain ⟨rfl, rfl⟩ := execution
            refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace, (by first | exact hbz | clockB),
              LoopCase.stateRel_emptyEnvB info source target relation, ?_, ?_⟩
            · have targetZero : target.clock = 0 := clockEq.trans zero
              simp only [Nat.add_zero, StackSemEvaluate.evaluate_call, targetLookup,
                targetZero, if_true]
              have update : {target with clock := 0} = target := by rw [← targetZero]
              rw [update]
            · simp
          · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at execution
            rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
              ⟨bodyResult, bodyPost⟩
            rw [bodyExecution] at execution
            by_cases bad : badFunReturn bodyResult = true
            · simp only [bad, if_true, Prod.mk.injEq] at execution
              exact False.elim (nonerror execution.1.symm)
            · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
              obtain ⟨rfl, rfl⟩ := execution
              obtain ⟨clock, targetPost, space, hb_clock, postRelation, targetExecution, guard⟩ :=
                calleeIH rfl program lookup zero entryInfo (decClock target) bodyPost bodyResult
                  ⟨bodyExecution, nonerror,
                    LoopCase.stateRel_decClockB entryInfo source target entryRelation⟩
              have frames : stateOk info source.code := by
                obtain ⟨_, _, _, frames, _⟩ := relation
                exact frames
              have postFrames := stateOk_afterEvaluateB info program (decClock source)
                bodyPost bodyResult frames bodyExecution
              refine ⟨clock, targetPost, space, (by first | exact hbz | clockB),
                stateRel_changeInfoB entryInfo info bodyPost targetPost postRelation postFrames,
                ?_, guard⟩
              have targetNonzero : target.clock ≠ 0 := by omega
              have addedNonzero : target.clock + clock ≠ 0 := by omega
              rw [StackSemEvaluate.evaluate_call]
              simp only [targetLookup, addedNonzero, if_false]
              rw [StackSemEvaluateClock.fixClockEvaluate]
              simp only [StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
                targetExecution, bad, Bool.false_eq_true, if_false]
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.CallCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.CallCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.CallCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open IfCase RawCallCase

/-- Synchronized register erasure preserves the literal relation. Flapjack
infrastructure, with code and entry-frame witnesses unchanged. -/
theorem stateRel_eraseRegsB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (link : Nat) :
    stateRel info {source with regs := source.regs.eraseEq link}
      {target with regs := target.regs.eraseEq link} := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  subst target
  exact ⟨code, domain, rfl, frames, entries⟩

/-- The actual returning-call lookup erases the link register before resolving
either destination form. The entry relation is recovered on the original
states, without an assumption about the eventual target run. -/
theorem callEntryErasedB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (dest : Sum Nat Nat) (link : Nat)
    (program : HolProg width)
    (lookup : findCode dest (source.regs.eraseEq link) source.code = some program) :
    ∃ entryInfo : Spt Nat, stateRel entryInfo source target ∧
      findCode dest (target.regs.eraseEq link) target.code = some (compTop entryInfo program) := by
  obtain ⟨entryInfo, erasedRelation, targetLookup⟩ :=
    callEntryB info {source with regs := source.regs.eraseEq link}
      {target with regs := target.regs.eraseEq link}
      (stateRel_eraseRegsB info source target relation link) dest program lookup
  have entryFrames : stateOk entryInfo source.code := by
    obtain ⟨_, _, _, frames, _⟩ := erasedRelation
    exact frames
  exact ⟨entryInfo, stateRel_changeInfoB info entryInfo source target relation entryFrames,
    targetLookup⟩

/-- Synchronized return-link update preserves the literal relation. Flapjack
infrastructure over the actual canonical register maps. -/
theorem stateRel_setVarB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (link : Nat) (value : WordLocW width) :
    stateRel info (setVar link value source) (setVar link value target) := by
  obtain ⟨code, domain, equality, frames, entries⟩ := relation
  subst target
  exact ⟨code, domain, rfl, frames, entries⟩

/-- Native returning-call input commutes with an added allowance when its
original clock is nonzero. Flapjack infrastructure, no execution premise. -/
theorem returningInput_addClockB {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (link l1 l2 extra : Nat)
    (nonzero : target.clock ≠ 0) :
    decClock (setVar link (.loc l1 l2) {target with clock := target.clock + extra}) =
      {decClock (setVar link (.loc l1 l2) target) with
        clock := (decClock (setVar link (.loc l1 l2) target)).clock + extra} := by
  simp only [decClock, setVar]
  congr 1
  omega

/-- The actual SOME-return callee IH at the fixed recursive source; unused comp
component omitted. Flapjack notation for the original evaluate_ind motive. -/
abbrev ReturnCalleeIHB {width : Nat} [NeZero width] (C F : Type)
    (dest : Sum Nat Nat) (link l1 l2 : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 →
    ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
      (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (result, post) ∧ result ≠ some .error ∧
        stateRel info (decClock (setVar link (.loc l1 l2) source)) target →
      SimulationResultB (compTop info program) info target post result

/-- Original return-continuation IH, guarded by the real callee lookup, clock,
evaluation and exact matching return location. Flapjack infrastructure. -/
abbrev ReturnContinuationIHB {width : Nat} [NeZero width] (C F : Type)
    (ret : HolProg width) (dest : Sum Nat Nat) (link l1 l2 : Nat)
    (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ program, findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 → ∀ middle,
    StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.result (.loc l1 l2)), middle) → ProgramIHB C F ret middle

/-- Original exception-continuation IH, retaining the actual handler and exact
matching exception location guards. Flapjack infrastructure. -/
abbrev ExceptionContinuationIHB {width : Nat} [NeZero width] (C F : Type)
    (handler : Option (HolProg width × Nat × Nat)) (dest : Sum Nat Nat)
    (link l1 l2 : Nat) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ program h hl1 hl2,
    findCode dest (source.regs.eraseEq link) source.code = some program →
    source.clock ≠ 0 → handler = some (h, hl1, hl2) → ∀ middle,
    StackSemEvaluate.evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.exception (.loc hl1 hl2)), middle) → ProgramIHB C F h middle

/-- Derive the actual compiled callee execution and restore the outer frame
information from code monotonicity. Flapjack source-local infrastructure. -/
theorem simulateReturningCalleeB {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (link l1 l2 : Nat) (info : Spt Nat)
    (source target middle : StackSemStateFiniteExact width C F)
    (program : HolProg width) (result : Option (StackSemResult width))
    (calleeIH : ReturnCalleeIHB C F dest link l1 l2 source)
    (relation : stateRel info source target)
    (lookup : findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (execution : StackSemEvaluate.evaluate
      (program, decClock (setVar link (.loc l1 l2) source)) = (result, middle))
    (nonerror : result ≠ some .error) :
    ∃ entryInfo, findCode dest (target.regs.eraseEq link) target.code =
        some (compTop entryInfo program) ∧
      SimulationResultB (compTop entryInfo program) info
        (decClock (setVar link (.loc l1 l2) target)) middle result := by
  obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
    callEntryErasedB info source target relation dest link program lookup
  obtain ⟨clock, targetMiddle, space, hb_clock, middleRelation, targetExecution, guard⟩ :=
    calleeIH program lookup nonzero entryInfo
      (decClock (setVar link (.loc l1 l2) target)) middle result
      ⟨execution, nonerror, LoopCase.stateRel_decClockB entryInfo
        (setVar link (.loc l1 l2) source) (setVar link (.loc l1 l2) target)
        (stateRel_setVarB entryInfo source target entryRelation link (.loc l1 l2))⟩
  have frames : stateOk info source.code := by
    obtain ⟨_, _, _, frames, _⟩ := relation
    exact frames
  have middleFrames := stateOk_afterEvaluateB info program
    (decClock (setVar link (.loc l1 l2) source)) middle result frames execution
  exact ⟨entryInfo, targetLookup, clock, targetMiddle, space, hb_clock,
    stateRel_changeInfoB entryInfo info middle targetMiddle middleRelation middleFrames,
    targetExecution, guard⟩

/-- Extending a derived returning-callee run composes both allowances at the
real native call input. Flapjack clock infrastructure, not a ported case. -/
theorem extendReturningCalleeB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (target middle : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (link l1 l2 first extra : Nat)
    (nonzero : target.clock ≠ 0)
    (execution : StackSemEvaluate.evaluate
      (program, {decClock (setVar link (.loc l1 l2) target) with
        clock := (decClock (setVar link (.loc l1 l2) target)).clock + first}) =
      (result, middle)) (nonTimeout : result ≠ some .timeOut) :
    StackSemEvaluate.evaluate
      (program, decClock (setVar link (.loc l1 l2)
        {target with clock := target.clock + (first + extra)})) =
      (result, {middle with clock := middle.clock + extra}) := by
  have extended := Compiler.Backend.StackProps.evaluateAddClock extra program
    {decClock (setVar link (.loc l1 l2) target) with
      clock := (decClock (setVar link (.loc l1 l2) target)).clock + first}
    result middle ⟨execution, nonTimeout⟩
  rw [returningInput_addClockB target link l1 l2 (first + extra) nonzero]
  simpa only [Nat.add_assoc] using extended


namespace ReturnRepresentation
/-- Actual imported canonical evaluator-state roundtrip. Flapjack qualifier
infrastructure without a duplicate carrier or an assumed relation. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness
end ReturnRepresentation

/-- Genuine SOME-return Call branch409-518. The original three source premises
and exactly guarded callee, return and exception induction hypotheses establish
both existential simulations. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCallReturnB {width : Nat} [NeZero width] {C F : Type}
    (ret : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : ReturnCalleeIHB C F dest link l1 l2 source)
    (returnIH : ReturnContinuationIHB C F ret dest link l1 l2 source)
    (exceptionIH : ExceptionContinuationIHB C F handler dest link l1 l2 source)
    (hypothesis : StackSemEvaluate.evaluate
      (.call (some (ret, link, l1, l2)) dest handler, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result ∧
    SimulationResultB (comp info (.call (some (ret, link, l1, l2)) dest handler))
      info target post result := by
  classical
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  suffices simulation :
      SimulationResultB (comp info (.call (some (ret, link, l1, l2)) dest handler))
        info target post result by
    exact ⟨by simpa only [compTop] using simulation, simulation⟩
  rw [StackSemEvaluate.evaluate_call] at execution
  dsimp only at execution
  cases lookup : findCode dest (source.regs.eraseEq link) source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
      rw [lookup] at execution
      have clockEq := LoopCase.stateRel_clockB info source target relation
      by_cases zero : source.clock = 0
      · simp only [zero, if_true, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨entryInfo, _, targetLookup⟩ :=
          callEntryErasedB info source target relation dest link program lookup
        refine ⟨0, emptyEnv target, (emptyEnv target).stackSpace, (by first | exact hbz | clockB),
          LoopCase.stateRel_emptyEnvB info source target relation, ?_, by simp⟩
        have targetZero : target.clock = 0 := clockEq.trans zero
        have update : {target with clock := 0} = target := by rw [← targetZero]
        cases handler with
        | none =>
            simp only [comp, Nat.add_zero, targetZero, update,
              StackSemEvaluate.evaluate_call, targetLookup, if_true]
        | some triple =>
            obtain ⟨h, hl1, hl2⟩ := triple
            simp only [comp, Nat.add_zero, targetZero, update,
              StackSemEvaluate.evaluate_call, targetLookup, if_true]
      · simp only [zero, if_false] at execution
        rw [StackSemEvaluateClock.fixClockEvaluate] at execution
        rcases bodyExecution : StackSemEvaluate.evaluate
          (program, decClock (setVar link (.loc l1 l2) source)) with
          ⟨bodyResult, middle⟩
        rw [bodyExecution] at execution
        have bodyNonerror : bodyResult ≠ some .error := by
          intro equal
          rw [equal] at execution
          simp only [Prod.mk.injEq] at execution
          exact nonerror execution.1.symm
        obtain ⟨entryInfo, targetLookup, firstClock, targetMiddle, firstSpace,
          hb_firstClock, middleRelation, calleeExecution, firstGuard⟩ :=
          simulateReturningCalleeB dest link l1 l2 info source target middle program bodyResult
            calleeIH relation lookup zero bodyExecution bodyNonerror
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + firstClock ≠ 0 := by omega
        have calleeNative : StackSemEvaluate.evaluate
            (compTop entryInfo program, decClock (setVar link (.loc l1 l2)
              {target with clock := target.clock + firstClock})) =
            (bodyResult, {targetMiddle with stackSpace := firstSpace}) := by
          rw [returningInput_addClockB target link l1 l2 firstClock targetNonzero]
          exact calleeExecution
        cases bodyResult with
        | none =>
            simp only [Prod.mk.injEq] at execution
            exact False.elim (nonerror execution.1.symm)
        | some value =>
            cases value with
            | error => exact False.elim (bodyNonerror rfl)
            | «break» label =>
                simp only [Prod.mk.injEq] at execution
                exact False.elim (nonerror execution.1.symm)
            | «continue» label =>
                simp only [Prod.mk.injEq] at execution
                exact False.elim (nonerror execution.1.symm)
            | halt value =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, (by first | exact hbz | clockB), middleRelation, ?_, firstGuard⟩
                cases handler with
                | none =>
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
            | timeOut =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, (by first | exact hbz | clockB), middleRelation, ?_, firstGuard⟩
                cases handler with
                | none =>
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
            | finalFFI event =>
                simp only [Prod.mk.injEq] at execution
                obtain ⟨rfl, rfl⟩ := execution
                refine ⟨firstClock, targetMiddle, firstSpace, (by first | exact hbz | clockB), middleRelation, ?_, firstGuard⟩
                cases handler with
                | none =>
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup, addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
            | result value =>
                by_cases equal : value = .loc l1 l2
                · subst value
                  simp only [ne_eq, not_true_eq_false, if_false] at execution
                  have spaceEq := firstGuard (by simp)
                  subst firstSpace
                  have selfSpace : {targetMiddle with stackSpace := targetMiddle.stackSpace} =
                      targetMiddle := by cases targetMiddle; rfl
                  rw [selfSpace] at calleeExecution
                  obtain ⟨secondClock, targetPost, finalSpace, hb_secondClock, postRelation,
                    continuationExecution, finalGuard⟩ :=
                    returnIH program lookup zero middle bodyExecution info targetMiddle post result
                      ⟨execution, nonerror, middleRelation⟩
                  have extended := extendReturningCalleeB (compTop entryInfo program) target
                    targetMiddle (some (.result (.loc l1 l2))) link l1 l2 firstClock secondClock
                    targetNonzero calleeExecution (by simp)
                  have totalNonzero : target.clock + (firstClock + secondClock) ≠ 0 := by omega
                  refine ⟨firstClock + secondClock, targetPost, finalSpace, (by first | exact hbz | clockB), postRelation, ?_, finalGuard⟩
                  cases handler with
                  | none =>
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        totalNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                      simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                  | some triple =>
                      obtain ⟨h, hl1, hl2⟩ := triple
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        totalNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                      simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
                  exact False.elim (nonerror execution.1.symm)
            | exception value =>
                cases handler with
                | none =>
                    simp only [Prod.mk.injEq] at execution
                    obtain ⟨rfl, rfl⟩ := execution
                    refine ⟨firstClock, targetMiddle, firstSpace, (by first | exact hbz | clockB), middleRelation, ?_, firstGuard⟩
                    simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                      addedNonzero, if_false]
                    rw [StackSemEvaluateClock.fixClockEvaluate, calleeNative]
                | some triple =>
                    obtain ⟨h, hl1, hl2⟩ := triple
                    by_cases equal : value = .loc hl1 hl2
                    · subst value
                      simp only [ne_eq, not_true_eq_false, if_false] at execution
                      have spaceEq := firstGuard (by simp)
                      subst firstSpace
                      have selfSpace : {targetMiddle with stackSpace := targetMiddle.stackSpace} =
                          targetMiddle := by cases targetMiddle; rfl
                      rw [selfSpace] at calleeExecution
                      obtain ⟨secondClock, targetPost, finalSpace, hb_secondClock, postRelation,
                        continuationExecution, finalGuard⟩ :=
                        exceptionIH program h hl1 hl2 lookup zero rfl middle bodyExecution
                          info targetMiddle post result ⟨execution, nonerror, middleRelation⟩
                      have extended := extendReturningCalleeB (compTop entryInfo program) target
                        targetMiddle (some (.exception (.loc hl1 hl2))) link l1 l2
                        firstClock secondClock targetNonzero calleeExecution (by simp)
                      have totalNonzero : target.clock + (firstClock + secondClock) ≠ 0 := by omega
                      refine ⟨firstClock + secondClock, targetPost, finalSpace, (by first | exact hbz | clockB),
                        postRelation, ?_, finalGuard⟩
                      simp only [comp, StackSemEvaluate.evaluate_call, targetLookup,
                        totalNonzero, if_false]
                      rw [StackSemEvaluateClock.fixClockEvaluate, extended]
                      simpa only [ne_eq, not_true_eq_false, if_false] using continuationExecution
                    · simp only [ne_eq, equal, not_false_eq_true, if_true, Prod.mk.injEq] at execution
                      exact False.elim (nonerror execution.1.symm)
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.CallCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.CallAssembly
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.CallAssembly
open Flapjack Flapjack.Compiler.Backend.StackLang
open IfCase CallCase

/-- Original Call evaluate_ind hypotheses split only on the native optional
return continuation. Unused components of the paired motives are omitted.
This abbreviation is Flapjack notation, not a separate HOL declaration. -/
abbrev CallIHB {width : Nat} [NeZero width] (C F : Type)
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) : Prop :=
  match ret with
  | none => TailCalleeIHB C F dest handler source
  | some (body, link, l1, l2) =>
      ReturnCalleeIHB C F dest link l1 l2 source ∧
      ReturnContinuationIHB C F body dest link l1 l2 source ∧
      ExceptionContinuationIHB C F handler dest link l1 l2 source

/-- Canonical roundtrip of the actual imported evaluator-state owner.
Flapjack qualifier infrastructure with no duplicate carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Complete original Call case409-518. All optional return/handler and
direct/indirect destination branches retain the original source evaluation,
nonError and literal state relation premises plus only the actual guarded
recursive hypotheses. Both original existential conclusions and timeout/
Halt Word2 stackspace exceptions remain. No target execution, successful body
or final relation is assumed. Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCallB {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (induction : CallIHB C F ret dest handler source)
    (hypothesis : StackSemEvaluate.evaluate (.call ret dest handler, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.call ret dest handler)) info target post result ∧
    SimulationResultB (comp info (.call ret dest handler)) info target post result := by
  cases ret with
  | none => exact compCorrectCallTailB dest handler info source target post result induction hypothesis
  | some triple =>
      obtain ⟨body, link, l1, l2⟩ := triple
      obtain ⟨calleeIH, returnIH, exceptionIH⟩ := induction
      exact compCorrectCallReturnB body link l1 l2 dest handler info source target post result
        calleeIH returnIH exceptionIH hypothesis
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.CallAssembly

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.SeqCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.SeqCase
open Flapjack Flapjack.Compiler.Backend.StackLang
open IfCase

/-- Source-local Seq equation. The original evaluator's clock theorem removes
its redundant clamp; this is infrastructure, not a separate HOL declaration. -/
theorem evaluateSeqUnclampedB {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.seq first second, source) =
      match StackSemEvaluate.evaluate (first, source) with
      | (none, middle) => StackSemEvaluate.evaluate (second, middle)
      | (some result, middle) => (some result, middle) := by
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases StackSemEvaluate.evaluate (first, source) with ⟨result, middle⟩
  cases result <;> rfl

/-- The genuine second evaluate_ind hypothesis is available only after the
actual first NONE run. Flapjack notation, not an independent HOL declaration. -/
abbrev SeqSecondIHB {width : Nat} [NeZero width] (C F : Type)
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F) : Prop :=
  ∀ middle : StackSemStateFiniteExact width C F,
    StackSemEvaluate.evaluate (first, source) = (none, middle) →
    ProgramIHB C F second middle

/-- Complete standard composition in original175-194, before the compiler's
optimized Seq split. This source-local proof infrastructure has no separately
named HOL declaration, so carries no comp_correct tag. Its target is the actual
standard compiled Seq: the full parent still needs the optimized equal/less/
greater frame branches and the assembling theorem. Only the actual first and
guarded second evaluate_ind hypotheses supplement the original three premises.
Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
theorem simulateStandardSeqB {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ProgramIHB C F first source)
    (secondIH : SeqSecondIHB C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (.seq (comp info first) (comp info second)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  rcases firstRun : StackSemEvaluate.evaluate (first, source) with ⟨firstResult, middle⟩
  cases firstResult with
  | none =>
      rw [evaluateSeqUnclampedB, firstRun] at execution
      obtain ⟨firstClock, targetMiddle, firstSpace, hb_firstClock, middleRelation, firstTargetRun, firstGuard⟩ :=
        firstIH info target middle none ⟨firstRun, by simp, relation⟩
      have spaceEq := firstGuard (by simp)
      subst firstSpace
      have spaceSelf : { targetMiddle with stackSpace := targetMiddle.stackSpace } =
          targetMiddle := by cases targetMiddle; rfl
      rw [spaceSelf] at firstTargetRun
      obtain ⟨secondClock, targetPost, finalSpace, hb_secondClock, postRelation, secondTargetRun, finalGuard⟩ :=
        secondIH middle firstRun info targetMiddle post result
          ⟨execution, nonerror, middleRelation⟩
      have extendedFirst := Compiler.Backend.StackProps.evaluateAddClock secondClock
        (comp info first) { target with clock := target.clock + firstClock }
        none targetMiddle ⟨firstTargetRun, by simp⟩
      have inputEq : { { target with clock := target.clock + firstClock } with
          clock := ({ target with clock := target.clock + firstClock }).clock + secondClock } =
          { target with clock := target.clock + (firstClock + secondClock) } := by
        simp only [Nat.add_assoc]
      rw [inputEq] at extendedFirst
      refine ⟨firstClock + secondClock, targetPost, finalSpace, (by first | exact hbz | clockB), postRelation, ?_, finalGuard⟩
      rw [evaluateSeqUnclampedB, extendedFirst]
      exact secondTargetRun
  | some firstResult =>
      rw [evaluateSeqUnclampedB, firstRun] at execution
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
      obtain ⟨clock, targetPost, finalSpace, hb_clock, postRelation, targetRun, guard⟩ :=
        firstIH info target middle (some firstResult) ⟨firstRun, nonerror, relation⟩
      refine ⟨clock, targetPost, finalSpace, (by first | exact hbz | clockB), postRelation, ?_, guard⟩
      rw [evaluateSeqUnclampedB, targetRun]
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.SeqCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.SeqCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.SeqCase
open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps StackSemControl
open IfCase

/-- Flapjack notation for the three actual compSeq output forms. This is a
source-local expression, not a replacement compiler or separate HOL port. -/
abbrev optimizedSeqB {width : Nat} [NeZero width] (released allocated dest : Nat) : HolProg width :=
  if allocated = released then .rawCall dest
  else if allocated < released then .seq (.stackFree (released - allocated)) (.rawCall dest)
  else .seq .tick (.seq (.stackAlloc (allocated - released)) (.rawCall dest))

/-- Code-independent stack-space update of the literal relation; Flapjack
infrastructure, with no independently named HOL declaration. -/
theorem stateRel_setStackSpaceB {width : Nat} [NeZero width] {C F : Type}
    (info : Spt Nat) (source target : StackSemStateFiniteExact width C F)
    (relation : stateRel info source target) (space : Nat) :
    stateRel info {source with stackSpace := space} {target with stackSpace := space} := by
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  subst target
  exact ⟨code, domain, rfl, frames, entries⟩

/-- Native direct-call equation for an actual entry allocation. Flapjack
infrastructure exposing all allocation/error/body outcomes, not a target run
assumption or a changed evaluator. -/
theorem evaluateCallAllocB {width : Nat} [NeZero width] {C F : Type}
    (dest allocated : Nat) (body : HolProg width) (s : StackSemStateFiniteExact width C F)
    (entry : sptLookup dest s.code = some (.seq (.stackAlloc allocated) body)) :
    StackSemEvaluate.evaluate (.call none (.inl dest) none, s) =
      if s.clock = 0 then (some .timeOut, emptyEnv s)
      else if !s.useStack then (some .error, decClock s)
      else if s.stackSpace < allocated then
        (some (.halt (.word (BitVec.ofNat width 2))), emptyEnv (decClock s))
      else match StackSemEvaluate.evaluate
          (body, {decClock s with stackSpace := s.stackSpace - allocated}) with
        | (result, post) => if badFunReturn result then (some .error, post) else (result, post) := by
  rw [StackSemEvaluate.evaluate_call]
  simp only [findCode, entry]
  simp only [StackSemEvaluateClock.fixClockEvaluate]
  simp only [evaluateSeqUnclampedB, StackSemEvaluate.evaluate_stackAlloc, decClock]
  split_ifs <;> simp_all [badFunReturn]

/-- Actual successful-allocation transport for all three compiler output forms.
All body outcomes, including errors and timeouts, are preserved. The one extra
clock in the greater branch is consumed by its actual Tick. Source-local
infrastructure; its guards are derived by the final Seq case, not assumed there. -/
theorem successfulOptimizationB {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (body : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (entry : sptLookup dest s.code = some (.seq (.stackAlloc allocated) body))
    (useStack : s.useStack = true) (bounds : s.stackSpace + released ≤ s.stack.length)
    (space : allocated ≤ s.stackSpace + released) (nonzero : s.clock ≠ 0) :
    StackSemEvaluate.evaluate (optimizedSeqB released allocated dest,
      {s with clock := s.clock + (if released < allocated then 1 else 0)}) =
    StackSemEvaluate.evaluate (.call none (.inl dest) none,
      {s with stackSpace := s.stackSpace + released}) := by
  rw [evaluateCallAllocB dest allocated body {s with stackSpace := s.stackSpace + released} entry]
  by_cases equal : allocated = released
  · subst allocated
    have allocationSafe : ¬ s.stackSpace + released < released := by omega
    simp [optimizedSeqB, StackSemEvaluate.evaluate_rawCall, entry, destSeq,
      useStack, nonzero, allocationSafe, decClock]
  · by_cases less : allocated < released
    · have releaseSafe : ¬ s.stack.length < s.stackSpace + (released - allocated) := by omega
      have finalSpace : s.stackSpace + released - allocated =
          s.stackSpace + (released - allocated) := by omega
      simp [optimizedSeqB, equal, less, show ¬ released < allocated by omega,
        evaluateSeqUnclampedB, StackSemEvaluate.evaluate_stackFree,
        StackSemEvaluate.evaluate_rawCall, entry, destSeq, useStack, releaseSafe,
        nonzero, show ¬ s.stackSpace + released < allocated by omega, decClock, finalSpace]
    · have greater : released < allocated := by omega
      have allocateSafe : ¬ s.stackSpace < allocated - released := by omega
      have finalSpace : s.stackSpace + released - allocated =
          s.stackSpace - (allocated - released) := by omega
      simp [optimizedSeqB, equal, less, greater, evaluateSeqUnclampedB,
        StackSemEvaluate.evaluate_tick, StackSemEvaluate.evaluate_stackAlloc,
        StackSemEvaluate.evaluate_rawCall, entry, destSeq, useStack, allocateSafe,
        nonzero, show ¬ s.stackSpace + released < allocated by omega, decClock, finalSpace]

/-- Native zero-clock optimized outcomes. EmptyEnv retains stackSpace: the
original timeout exception permits the resulting space to differ. Infrastructure
used to derive the original guarded existential result, not a stronger claim. -/
theorem zeroOptimizationB {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (body : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (entry : sptLookup dest s.code = some (.seq (.stackAlloc allocated) body))
    (useStack : s.useStack = true) (bounds : s.stackSpace + released ≤ s.stack.length)
    (zero : s.clock = 0) :
    StackSemEvaluate.evaluate (optimizedSeqB released allocated dest, s) =
      (some .timeOut, {emptyEnv s with stackSpace :=
        if allocated < released then s.stackSpace + (released - allocated) else s.stackSpace}) := by
  by_cases equal : allocated = released
  · subst allocated
    simp [optimizedSeqB, StackSemEvaluate.evaluate_rawCall, entry, destSeq, zero, emptyEnv]
  · by_cases less : allocated < released
    · have safe : ¬ s.stack.length < s.stackSpace + (released - allocated) := by omega
      simp [optimizedSeqB, equal, less, evaluateSeqUnclampedB,
        StackSemEvaluate.evaluate_stackFree, StackSemEvaluate.evaluate_rawCall,
        entry, destSeq, useStack, safe, zero, emptyEnv]
    · simp [optimizedSeqB, equal, less, evaluateSeqUnclampedB,
        StackSemEvaluate.evaluate_tick, zero, emptyEnv]

/-- The greater-frame allocation-failure outcome uses no extra clock: Tick
consumes exactly the original Call's clock. Stack-space equality is exempt for
Halt Word2 in the original theorem. Source-local native infrastructure. -/
theorem failedOptimizationB {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (s : StackSemStateFiniteExact width C F)
    (useStack : s.useStack = true) (failure : s.stackSpace + released < allocated)
    (nonzero : s.clock ≠ 0) :
    StackSemEvaluate.evaluate (optimizedSeqB released allocated dest, s) =
      (some (.halt (.word (BitVec.ofNat width 2))), emptyEnv (decClock s)) := by
  have greater : released < allocated := by omega
  have allocationFailure : s.stackSpace < allocated - released := by omega
  simp [optimizedSeqB, show allocated ≠ released by omega,
    show ¬ allocated < released by omega, evaluateSeqUnclampedB,
    StackSemEvaluate.evaluate_tick, StackSemEvaluate.evaluate_stackAlloc,
    useStack, allocationFailure, nonzero, decClock]

/-- Tail call opened at a nonzero clock: the callee runs at `decClock`, so the
simulation witness leaves at least one source tick unused (`+ 1`). -/
theorem tailTightB {width : Nat} [NeZero width] {C F : Type}
    (dest : Nat) (info : Spt Nat) (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (calleeIH : CallCase.TailCalleeIHB C F (.inl dest) none source)
    (nonzeroS : source.clock ≠ 0)
    (hypothesis : StackSemEvaluate.evaluate (.call none (.inl dest) none, source) =
      (result, post) ∧ result ≠ some .error ∧ stateRel info source target) :
    ∃ clock targetPost stackSpace, clock + targetPost.clock + 1 ≤ target.clock ∧
      stateRel info post targetPost ∧
      StackSemEvaluate.evaluate (.call none (.inl dest) none,
        {target with clock := target.clock + clock}) =
        (result, {targetPost with stackSpace := stackSpace}) ∧
      (result ≠ some .timeOut ∧ result ≠ some (.halt (.word (BitVec.ofNat width 2))) →
        stackSpace = targetPost.stackSpace) := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rw [StackSemEvaluate.evaluate_call] at execution
  cases lookup : findCode (.inl dest) source.regs source.code with
  | none => simp [lookup] at execution; exact False.elim (nonerror execution.1.symm)
  | some program =>
      rw [lookup] at execution
      obtain ⟨entryInfo, entryRelation, targetLookup⟩ :=
        CallCase.callEntryB info source target relation (.inl dest) program lookup
      have clockEq := LoopCase.stateRel_clockB info source target relation
      simp only [nonzeroS, if_false, StackSemEvaluateClock.fixClockEvaluate] at execution
      rcases bodyExecution : StackSemEvaluate.evaluate (program, decClock source) with
        ⟨bodyResult, bodyPost⟩
      rw [bodyExecution] at execution
      by_cases bad : badFunReturn bodyResult = true
      · simp only [bad, if_true, Prod.mk.injEq] at execution
        exact False.elim (nonerror execution.1.symm)
      · simp only [bad, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨clock, targetPost, space, hbT, postRelation, targetExecution, guard⟩ :=
          calleeIH rfl program lookup nonzeroS entryInfo (decClock target) bodyPost bodyResult
            ⟨bodyExecution, nonerror,
              LoopCase.stateRel_decClockB entryInfo source target entryRelation⟩
        have frames : stateOk info source.code := by
          obtain ⟨_, _, _, frames, _⟩ := relation
          exact frames
        have postFrames := RawCallCase.stateOk_afterEvaluateB info program (decClock source)
          bodyPost bodyResult frames bodyExecution
        refine ⟨clock, targetPost, space, ?_,
          RawCallCase.stateRel_changeInfoB entryInfo info bodyPost targetPost postRelation postFrames,
          ?_, guard⟩
        · simp only [decClock] at hbT; omega
        have targetNonzero : target.clock ≠ 0 := by omega
        have addedNonzero : target.clock + clock ≠ 0 := by omega
        rw [StackSemEvaluate.evaluate_call]
        simp only [targetLookup, addedNonzero, if_false]
        rw [StackSemEvaluateClock.fixClockEvaluate]
        simp only [StackProps.EvaluateAddClock.decClock_addClock target clock targetNonzero,
          targetExecution, bad, Bool.false_eq_true, if_false]

/-- Complete optimized source subcase. The frame lookup is the compiler's
actual branch guard; the only recursive premise is the original second-program
IH after the actual StackFree NONE run. Target execution is derived from that
IH and native transport, never supplied as a theorem premise. Flapjack source-
local infrastructure for the assembling comp_correct Seq case. -/
theorem simulateOptimizedSeqB {width : Nat} [NeZero width] {C F : Type}
    (released allocated dest : Nat) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (frame : sptLookup dest info = some allocated)
    (calleeIH : CallCase.TailCalleeIHB C F (.inl dest) none
      {source with stackSpace := source.stackSpace + released})
    (hypothesis : StackSemEvaluate.evaluate
        (.seq (.stackFree released) (.call none (.inl dest) none), source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (optimizedSeqB released allocated dest) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  have originalRelation := relation
  obtain ⟨code, domain, targetEq, frames, entries⟩ := relation
  have targetSpace : target.stackSpace = source.stackSpace := by rw [targetEq]
  have targetClock : target.clock = source.clock := by rw [targetEq]
  have clockSelf : {target with clock := target.clock + 0} = target := by cases target; simp
  rw [evaluateSeqUnclampedB, StackSemEvaluate.evaluate_stackFree] at execution
  by_cases enabled : source.useStack = true
  · simp only [enabled, Bool.not_true, Bool.false_eq_true, if_false] at execution
    by_cases badBounds : source.stack.length < source.stackSpace + released
    · simp only [badBounds, if_true, Prod.mk.injEq] at execution
      exact False.elim (nonerror execution.1.symm)
    · simp only [badBounds, if_false] at execution
      have firstRun : StackSemEvaluate.evaluate (.stackFree released, source) =
          (none, {source with stackSpace := source.stackSpace + released}) := by
        simp [StackSemEvaluate.evaluate_stackFree, enabled, badBounds]
      have shiftedRelation := stateRel_setStackSpaceB info source target originalRelation
        (source.stackSpace + released)
      have targetEnabled : target.useStack = true := by simpa only [targetEq] using enabled
      have targetBounds : target.stackSpace + released ≤ target.stack.length := by
        simpa only [targetEq] using (show source.stackSpace + released ≤ source.stack.length by omega)
      obtain ⟨body, sourceEntry⟩ := frames dest allocated frame
      obtain ⟨entryInfo, _, targetLookup⟩ := RawCallCase.rawCallEntryB info source target originalRelation
        dest (.stackAlloc allocated) body sourceEntry
      have targetEntry : sptLookup dest target.code =
          some (.seq (.stackAlloc allocated) (comp entryInfo body)) := by
        simpa only [comp] using targetLookup
      replace execution : StackSemEvaluate.evaluate (.call none (.inl dest) none,
          {source with stackSpace := source.stackSpace + released}) = (result, post) := by
        simpa only [enabled] using execution
      have callExecution := execution
      rw [evaluateCallAllocB dest allocated body
        {source with stackSpace := source.stackSpace + released} sourceEntry] at execution
      by_cases zero : source.clock = 0
      · simp only [zero, if_true, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        let targetPost := emptyEnv {target with stackSpace := source.stackSpace + released}
        have hbz : 0 + targetPost.clock ≤ target.clock := by simp [targetPost, emptyEnv]
        refine ⟨0, targetPost,
          (if allocated < released then target.stackSpace + (released - allocated)
           else target.stackSpace), (by first | exact hbz | clockB), ?_, ?_, by simp⟩
        · simpa only [zero] using LoopCase.stateRel_emptyEnvB info
            {source with stackSpace := source.stackSpace + released}
            {target with stackSpace := source.stackSpace + released} shiftedRelation
        · rw [clockSelf]
          simpa only [targetPost, emptyEnv] using
            zeroOptimizationB released allocated dest (comp entryInfo body) target targetEntry
              targetEnabled targetBounds (targetClock.trans zero)
      · simp only [zero, if_false,
          if_neg (show ¬ (!source.useStack) = true by simp [enabled])] at execution
        by_cases failure : source.stackSpace + released < allocated
        · simp only [failure, if_true, Prod.mk.injEq] at execution
          obtain ⟨rfl, rfl⟩ := execution
          let targetPost := emptyEnv (decClock {target with
            stackSpace := source.stackSpace + released})
          have hbz : 0 + targetPost.clock ≤ target.clock := by simp [targetPost, emptyEnv, decClock]
          refine ⟨0, targetPost, target.stackSpace, (by first | exact hbz | clockB),
            LoopCase.stateRel_emptyEnvB info _ _
              (LoopCase.stateRel_decClockB info _ _ shiftedRelation), ?_, by simp⟩
          rw [clockSelf]
          simpa only [targetPost, emptyEnv, decClock] using
            failedOptimizationB released allocated dest target targetEnabled
              (by simpa only [targetSpace] using failure) (by simpa only [targetClock] using zero)
        · obtain ⟨clock, targetPost, finalSpace, hb_clock, postRelation, targetRun, guard⟩ :=
            tailTightB dest info {source with stackSpace := source.stackSpace + released}
              {target with stackSpace := source.stackSpace + released} post result calleeIH
              (by simpa using zero)
              ⟨callExecution, nonerror, shiftedRelation⟩
          change StackSemEvaluate.evaluate (.call none (.inl dest) none,
            {{target with stackSpace := source.stackSpace + released} with
              clock := target.clock + clock}) = (result, {targetPost with stackSpace := finalSpace}) at targetRun
          have callInput : {{target with stackSpace := source.stackSpace + released} with
              clock := target.clock + clock} =
              {{target with clock := target.clock + clock} with
                stackSpace := target.stackSpace + released} := by rw [targetSpace]
          rw [callInput] at targetRun
          have transport := successfulOptimizationB released allocated dest (comp entryInfo body)
            {target with clock := target.clock + clock} targetEntry targetEnabled targetBounds
            (by simpa only [targetSpace] using (show allocated ≤ source.stackSpace + released by omega))
            (by simp only; rw [targetClock]; omega)
          have combinedInput : {{target with clock := target.clock + clock} with
              clock := ({target with clock := target.clock + clock}).clock +
                (if released < allocated then 1 else 0)} =
              {target with clock := target.clock + (clock + (if released < allocated then 1 else 0))} := by
            simp only [Nat.add_assoc]
          rw [combinedInput] at transport
          refine ⟨clock + (if released < allocated then 1 else 0), targetPost, finalSpace, (by first | exact hbz | clockB),
            postRelation, ?_, guard⟩
          rw [transport]
          exact targetRun
  · have disabled : source.useStack = false := by cases source.useStack <;> simp_all
    simp only [disabled, Bool.not_false, if_true, Prod.mk.injEq] at execution
    exact False.elim (nonerror execution.1.symm)
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.SeqCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.SeqCase
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.SeqCase
open Flapjack Flapjack.Compiler.Backend.StackLang
open IfCase

/-- Canonical roundtrip of the actual imported evaluator state. Representation
infrastructure, with no separate HOL declaration or duplicate state carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original Seq case175-282. Both original existential simulations retain
the three source premises and only the genuine evaluate_ind hypotheses: first
at the fixed source, second after the actual first NONE run. The compiler's
fallback and every equal/less/greater-frame optimization are covered, including
zero clock, allocation failure, bad function returns and arbitrary body outcomes.
The optimized target Call execution is derived from the second IH; no extra
callee IH, target-run law, successful optimization or final relation is assumed.
The original timeout/Halt Word2 stackspace exceptions remain unchanged.
Inherits reals_as_rational_cuts, SOUNDNESS item8. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSeqB {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : ProgramIHB C F first source)
    (secondIH : SeqSecondIHB C F first second source)
    (optIH : ∀ released dest, CallCase.TailCalleeIHB C F (.inl dest) none
      {source with stackSpace := source.stackSpace + released})
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info (.seq first second)) info target post result ∧
    SimulationResultB (comp info (.seq first second)) info target post result := by
  have standard := simulateStandardSeqB first second info source target post result
    firstIH secondIH hypothesis
  constructor
  · simpa only [compTop] using standard
  · change SimulationResultB (compSeq first second info (.seq (comp info first) (comp info second)))
      info target post result
    by_cases fallback : compSeq first second info (.seq (comp info first) (comp info second)) =
        .seq (comp info first) (comp info second)
    · rw [fallback]
      exact standard
    · obtain ⟨released, dest, rfl, rfl⟩ := compSeqNeqImp first second
        (.seq (comp info first) (comp info second)) info fallback
      cases frame : sptLookup dest info with
      | none => simp [compSeq, destCase, frame] at fallback
      | some allocated =>
          simpa only [compSeq, destCase, frame] using
            simulateOptimizedSeqB released allocated dest info source target post result
              frame (optIH released dest) hypothesis
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.SeqCase

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.FullCompCorrect
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.FullCompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang
open IfCase StackSemMeasure StackSemStateOps StackSemControl

/-- Instruction case with the clock bound (witness 0). -/
theorem instSimB {width : Nat} [NeZero width] {C F : Type}
    (instruction : Compiler.Encoders.Asm.HolInst width) (info : Spt Nat)
    (source target resultState : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) =
      (result, resultState) ∧ result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (comp info (.inst instruction)) info target resultState result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  have hev := StackSemEvaluateClock.evaluateClock _ _ _ _ execution
  rw [StackSemEvaluate.evaluate_inst] at execution
  cases primitive : StackSemInst.instHOL instruction source with
  | none => simp [primitive] at execution; obtain ⟨rfl, _⟩ := execution; exact (nonerror rfl).elim
  | some state =>
    simp only [primitive, Prod.mk.injEq] at execution
    obtain ⟨rfl, rfl⟩ := execution
    obtain ⟨targetState, postRelation, targetExecution⟩ :=
      instHOL_stateRel instruction info source target state relation primitive
    refine ⟨0, targetState, targetState.stackSpace, (by first | exact hbz | clockB), postRelation, ?_, fun _ => rfl⟩
    have clockSelf : { target with clock := target.clock + 0 } = target := by
      cases target
      simp
    have stackSelf : { targetState with stackSpace := targetState.stackSpace } = targetState := by
      cases targetState
      rfl
    rw [clockSelf, stackSelf]
    simp only [comp, StackSemEvaluate.evaluate_inst, targetExecution]

/-- Well-founded assembly infrastructure for the original paired motive. -/
private theorem compCorrectMeasureB {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width)
      (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
        (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info source target →
      SimulationResultB (compTop info program) info target post result ∧
      SimulationResultB (comp info program) info target post result := by
  intro measure
  induction measure using Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm info t post r hypothesis
  subst hm
  cases p
  case skip  => exact BasicLeaves.compCorrectSkipB  info s t post r hypothesis
  case halt v => exact BasicLeaves.compCorrectHaltB v info s t post r hypothesis
  case get v n => exact BasicLeaves.compCorrectGetB v n info s t post r hypothesis
  case set n v => exact BasicLeaves.compCorrectSetB n v info s t post r hypothesis
  case opCurrHeap b d src => exact BasicLeaves.compCorrectOpCurrHeapB b d src info s t post r hypothesis
  case tick  => exact BasicLeaves.compCorrectTickB  info s t post r hypothesis
  case ret v => exact ControlLeaves.compCorrectReturnB v info s t post r hypothesis
  case raise v => exact ControlLeaves.compCorrectRaiseB v info s t post r hypothesis
  case «break» v => exact ControlLeaves.compCorrectBreakB v info s t post r hypothesis
  case «continue» v => exact ControlLeaves.compCorrectContinueB v info s t post r hypothesis
  case locValue a b c => exact StackAccessCase.compCorrectLocValueB a b c info s t post r hypothesis
  case stackAlloc n => exact StackAccessCase.compCorrectStackAllocB n info s t post r hypothesis
  case stackFree n => exact StackAccessCase.compCorrectStackFreeB n info s t post r hypothesis
  case stackLoad a b => exact StackAccessCase.compCorrectStackLoadB a b info s t post r hypothesis
  case stackLoadAny a b => exact StackAccessCase.compCorrectStackLoadAnyB a b info s t post r hypothesis
  case stackStore a b => exact StackAccessCase.compCorrectStackStoreB a b info s t post r hypothesis
  case stackStoreAny a b => exact StackAccessCase.compCorrectStackStoreAnyB a b info s t post r hypothesis
  case stackGetSize a => exact StackAccessCase.compCorrectStackGetSizeB a info s t post r hypothesis
  case stackSetSize a => exact StackAccessCase.compCorrectStackSetSizeB a info s t post r hypothesis
  case bitmapLoad a b => exact StackAccessCase.compCorrectBitmapLoadB a b info s t post r hypothesis
  case codeBufferWrite a b => exact MemoryFfiCase.compCorrectCodeBufferWriteB a b info s t post r hypothesis
  case dataBufferWrite a b => exact MemoryFfiCase.compCorrectDataBufferWriteB a b info s t post r hypothesis
  case ffi n a b c d e => exact MemoryFfiCase.compCorrectFfiB n a b c d e info s t post r hypothesis
  case alloc register => exact AllocationStoreCase.compCorrectAllocB register info s t post r hypothesis
  case storeConsts first second stub => exact AllocationStoreCase.compCorrectStoreConstsB first second stub info s t post r hypothesis
  case install a b c d e => exact InstallCase.compCorrectInstallB a b c d e info s t post r hypothesis
  case shMemOp op reg addr =>
    cases addr with
    | addr address offset =>
      exact MemoryFfiCase.compCorrectShMemOpB op reg address offset info s t post r hypothesis
  case inst instruction =>
    have simulation : SimulationResultB (comp info (.inst instruction)) info t post r :=
      instSimB instruction info s t post r hypothesis
    exact ⟨by simpa only [compTop] using simulation, simulation⟩
  case seq first second =>
    apply SeqCase.compCorrectSeqB first second info s t post r
    · intro i target out res h
      exact (ih _ (seq_first_measure_lt first second s) first s rfl i target out res h).2
    · intro middle firstRun i target out res h
      have bound := StackSemEvaluateClock.evaluateClock first s none middle firstRun
      exact (ih _ (lexNat_of_le_of_size_lt bound (seq_second_size_lt first second))
        second middle rfl i target out res h).2
    · intro released dest _ prog lookup nonzero i target out res h
      have lower : (decClock {s with stackSpace := s.stackSpace + released}).clock < s.clock := by
        simp only [decClock]; simp only at nonzero; omega
      exact (ih _ (lexNat_of_clock_lt lower) prog _ rfl i target out res h).1
    · exact hypothesis
  case ite cmp reg operand first second =>
    apply IfCase.compCorrectIfB cmp reg operand first second info s t post r
    · intro x y left right compared i target out res h
      exact (ih _ (if_first_measure_lt cmp reg operand first second s)
        first s rfl i target out res h).2
    · intro x y left right compared i target out res h
      exact (ih _ (if_second_measure_lt cmp reg operand first second s)
        second s rfl i target out res h).2
    · exact hypothesis
  case loop body =>
    apply LoopCase.compCorrectLoopB body info s t post r
    · intro i target out res h
      exact (ih _ (loop_body_measure_lt body s) body s rfl i target out res h).2
    · intro bodyResult middle bodyRun continues nonzero i target out res h
      have lower := LoopCase.loopReentryClockLessB body s middle bodyResult bodyRun nonzero
      exact (ih _ (lexNat_of_clock_lt lower) (.loop body) (decClock middle)
        rfl i target out res h).2
    · exact hypothesis
  case jumpLower r1 r2 dest =>
    apply JumpLowerCase.compCorrectJumpLowerB r1 r2 dest info s t post r
    · intro x y prog left right compared lookup nonzero i target out res h
      exact (ih _ (callee_measure_lt prog (.jumpLower r1 r2 dest) s nonzero)
        prog (decClock s) rfl i target out res h).1
    · exact hypothesis
  case rawCall dest =>
    apply RawCallCase.compCorrectRawCallB dest info s t post r
    · intro first body lookup nonzero i target out res h
      exact (ih _ (callee_measure_lt body (.rawCall dest) s nonzero)
        body (decClock s) rfl i target out res h).2
    · exact hypothesis
  case call ret dest handler =>
    apply CallAssembly.compCorrectCallB ret dest handler info s t post r
    · cases ret with
      | none =>
        intro absent prog lookup nonzero i target out res h
        exact (ih _ (callee_measure_lt prog (.call none dest handler) s nonzero)
          prog (decClock s) rfl i target out res h).1
      | some triple =>
        obtain ⟨body, link, l1, l2⟩ := triple
        refine ⟨?_, ?_, ?_⟩
        · intro prog lookup nonzero i target out res h
          have lower := callee_measure_lt prog (.call (some (body, link, l1, l2)) dest handler)
            (setVar link (.loc l1 l2) s) nonzero
          exact (ih _ lower prog (decClock (setVar link (.loc l1 l2) s))
            rfl i target out res h).1
        · intro prog lookup nonzero middle calleeRun i target out res h
          have bound := StackSemEvaluateClock.evaluateClock prog
            (decClock (setVar link (.loc l1 l2) s)) _ middle calleeRun
          have lower : middle.clock < s.clock := by
            have decreased := decClock_clock_lt (setVar link (.loc l1 l2) s) nonzero
            exact Nat.lt_of_le_of_lt bound decreased
          exact (ih _ (lexNat_of_clock_lt lower) body middle rfl i target out res h).2
        · intro prog handlerBody hl1 hl2 lookup nonzero present middle calleeRun i target out res h
          have bound := StackSemEvaluateClock.evaluateClock prog
            (decClock (setVar link (.loc l1 l2) s)) _ middle calleeRun
          have lower : middle.clock < s.clock := by
            have decreased := decClock_clock_lt (setVar link (.loc l1 l2) s) nonzero
            exact Nat.lt_of_le_of_lt bound decreased
          exact (ih _ (lexNat_of_clock_lt lower) handlerBody middle rfl i target out res h).2
    · exact hypothesis

/-- Reviewed codec for the actual imported state owner; representation
infrastructure with no separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactB
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original comp_correct: arbitrary native program and states with only
source evaluation, nonError and the literal initial state relation as premises.
Both existential target executions and the original timeout/Halt Word2
stack-space exceptions are preserved. Clock-first well-founded induction
discharges all 34 constructors and every guarded recursive hypothesis internally.
Canonical finite maps and positive-width words use the named translations;
Spt code/info and native lists retain their original carriers. The evaluator
inherits reals_as_rational_cuts (SOUNDNESS item 8); this establishes the rawcall
pass simulation, not numeric FP correspondence or whole compiler correctness. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectB {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source target : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResultB (compTop info program) info target post result ∧
    SimulationResultB (comp info program) info target post result :=
  compCorrectMeasureB (stackSemMeasure program source) program source rfl
    info target post result hypothesis
end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge.FullCompCorrect

/-! # Master: linear clock bound for StackRawCall and the end-to-end bridge -/

namespace InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Encoders.Asm

variable {width : Nat} [NeZero width]

/-- **`compCorrectB` (unfolded).** Flapjack's StackRawCall `comp_correct` with the extra
clock bounded by the clock the source actually consumes:
`extra + targetPost.clock ≤ target.clock` (and `targetPost.clock = post.clock`). -/
theorem rawCall_linearClock {C F : Type}
    (program : HolProg width) (source target post : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (nonError : result ≠ some .error) (relation : stateRel info source target) :
    ∃ extra targetPost stackSpace,
      extra + post.clock ≤ source.clock ∧ targetPost.clock = post.clock ∧
      stateRel info post targetPost ∧
      StackSemEvaluate.evaluate (comp info program, {target with clock := target.clock + extra}) =
        (result, {targetPost with stackSpace := stackSpace}) := by
  obtain ⟨extra, targetPost, space, hb, rel, tr, _⟩ :=
    (FullCompCorrect.compCorrectB program source target info result post ⟨run, nonError, relation⟩).2
  have h1 := LoopCase.stateRel_clock info post targetPost rel
  have h2 := LoopCase.stateRel_clock info source target relation
  exact ⟨extra, targetPost, space, by omega, h1, rel, tr⟩

/-- **≤ 2× clock expansion.** The target needs at most `extra ≤ source.clock` extra ticks:
total target clock `≤ 2 · source.clock`. -/
theorem rawCall_extra_le_clock {C F : Type}
    (program : HolProg width) (source target post : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (nonError : result ≠ some .error) (relation : stateRel info source target) :
    ∃ extra targetPost, extra ≤ source.clock ∧ target.clock + extra ≤ 2 * source.clock ∧
      StackSemEvaluate.evaluate (comp info program, {target with clock := target.clock + extra}) =
        (result, targetPost) := by
  obtain ⟨extra, targetPost, space, hb, _, _, tr⟩ :=
    rawCall_linearClock program source target post info result run nonError relation
  have h2 := LoopCase.stateRel_clock info source target relation
  exact ⟨extra, _, by omega, by omega, tr⟩

/-- **`entrySimulationB`**: whole-program entry simulation of `StackRawCall.compile` with the
extra clock bounded by the source clock, `extra ≤ clock` (≤ 2× expansion). -/
theorem entrySimulationB {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {source with clock := clock}) =
      (result, post)) (nonError : result ≠ some .error) :
    ∃ extra targetPost, extra + post.clock ≤ clock ∧ StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        {source with code := sptFromAList (compile code), clock := clock + extra}) =
      (result, targetPost) ∧ targetPost.ffi = post.ffi := by
  have relation := CompileSemantics.initialRelation code {source with clock := clock} distinct sourceCode
  obtain ⟨extra, targetPost, space, hb, postRelation, targetRun, _⟩ :=
    (FullCompCorrect.compCorrectB (.call none (.inl start) none)
      {source with clock := clock}
      {source with clock := clock, code := sptFromAList (compile code)}
      (collectInfo code .ln) result post ⟨run, nonError, relation⟩).2
  have hpc := LoopCase.stateRel_clock _ post targetPost postRelation
  refine ⟨extra, {targetPost with stackSpace := space}, by simp only at hb; omega, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · obtain ⟨_, _, equality, _⟩ := postRelation
    subst targetPost
    rfl

/-- `extra ≤ clock` corollary of `entrySimulationB`. -/
theorem entrySimulationB_extra_le {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {source with clock := clock}) =
      (result, post)) (nonError : result ≠ some .error) :
    ∃ extra targetPost, extra ≤ clock ∧ clock + extra ≤ 2 * clock ∧ StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        {source with code := sptFromAList (compile code), clock := clock + extra}) =
      (result, targetPost) := by
  obtain ⟨extra, targetPost, hb, tr, _⟩ :=
    entrySimulationB code source start clock result post distinct sourceCode run nonError
  exact ⟨extra, targetPost, by omega, by omega, tr⟩

/-! ## Empty info: StackRawCall is the identity -/

/-- With `info = .ln`, StackRawCall rewrites nothing (Flapjack `compLn`), so it costs
exactly 0 extra clock: the source run is the target run. -/
theorem rawCall_ln_identity {C F : Type} (body : HolProg width)
    (s : StackSemStateFiniteExact width C F) :
    compTop .ln body = body ∧ comp .ln body = body ∧
    StackSemEvaluate.evaluate (comp .ln body, s) = StackSemEvaluate.evaluate (body, s) := by
  obtain ⟨h1, h2⟩ := compLn (.ln : Spt Nat) body
  exact ⟨h1, h2, by rw [h2]⟩

/-! ## Tightness: the extra tick is real -/

/-- The greater-frame optimization really inserts a `tick`: on the target it is
`tick; stackAlloc (allocated - released); rawCall dest`. -/
theorem optimized_greater_has_tick (released allocated dest : Nat) (h : released < allocated) :
    SeqCase.optimizedSeqB (width := width) released allocated dest =
      .seq .tick (.seq (.stackAlloc (allocated - released)) (.rawCall dest)) := by
  simp [SeqCase.optimizedSeqB, show allocated ≠ released by omega, show ¬ allocated < released by omega]

/-- And with equal frames the optimization is a bare `rawCall` (no tick). -/
theorem optimized_equal_no_tick (n dest : Nat) :
    SeqCase.optimizedSeqB (width := width) n n dest = .rawCall dest := by
  simp [SeqCase.optimizedSeqB]

/-! ## End-to-end composition with StackAlloc / StackRemove -/

open InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall in
/-- **Bridge (StackRawCall → StackAlloc → StackRemove).** For every Pancake program:
* StackRawCall: any `StackRawCall.comp` run needs at most `extra ≤ source.clock` additional
  target clock (≤ 2× expansion), for every info map, in particular `collectInfo code .ln`;
* StackAlloc: identity on every section `≠ 6`, no `.alloc`, no GC call (no hypothesis);
* StackRemove: zero extra clock (≤ 1 on a final `halt`) on every user body from the live table. -/
theorem pancake_rawCall_stackAlloc_stackRemove_clock {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) :
    (∀ (program : HolProg width) (source target post : StackSemStateFiniteExact width C F)
       (result : Option (StackSemResult width)),
       StackSemEvaluate.evaluate (program, source) = (result, post) → result ≠ some .error →
       stateRel info source target →
       ∃ extra targetPost, extra ≤ source.clock ∧ target.clock + extra ≤ 2 * source.clock ∧
         StackSemEvaluate.evaluate (comp info program, {target with clock := target.clock + extra}) =
           (result, targetPost)) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        (StackAlloc.progComp y).2 = true ∧
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.NoGcCall
        (StackAlloc.progComp y).2 = true) ∧
    (∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = sptFromAList
          (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.liveSections
            (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
              arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1,
          InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true) →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget,
          InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget)) :=
  let m := pancake_stackAllocIdentity_noGc_zeroExtraClock (C := C) (F := F) arch prog wc ac perf dc info
  ⟨fun program source target post result run ne rel =>
     rawCall_extra_le_clock program source target post info result run ne rel,
   m.2.2.1, m.2.1, m.2.2.2⟩

end InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge
