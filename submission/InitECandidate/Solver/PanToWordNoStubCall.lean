import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.LoopLive.Fixedpoint
import Flapjack.Pancake.PanToWord
import InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# Discharging `hcall`: no WordLang call ever targets the `storeConsts` stub

CrepToLoop numbers user functions `64 + i` (`firstLoopName = 64`) and sends an unknown
callee to label `0`; every Loop call it emits carries `some label`. The Loop optimiser
(`loopCallCompHOL`, `shrinkHOL`, `markAllHOL`) and LoopToWord keep call targets. Hence every
call target produced from any Pancake program is `0` or `≥ 64`, never
`storeConstsStubLocation = 6`. Proof skeleton follows Flapjack's
`Pancake/CrepToLoop/Proofs/LocValueFree.lean` with the predicate changed to call targets.
-/

namespace InitECandidate.Solver.PanToWordNoStubCall

open Flapjack
open Flapjack.Compiler.Backend
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts

/-- Admissible call target: present, and `0` or a user label `≥ 64`. -/
def TgtGood : Option Nat → Prop
  | some n => n = 0 ∨ 64 ≤ n
  | none => False

/-- Every function label stored in the CrepToLoop context is `≥ 64`. -/
def FuncsGood (context : CrepToLoopContextExact) : Prop :=
  ∀ k l a, context.funcs.lookup k = some (l, a) → 64 ≤ l

theorem findLab_good (context : CrepToLoopContextExact) (name : Basis.Pure.MlString.MlString)
    (hf : FuncsGood context) :
    findLabExact context name = 0 ∨ 64 ≤ findLabExact context name := by
  unfold findLabExact
  cases h : context.funcs.lookup name with
  | none => left; rfl
  | some v => obtain ⟨l, a⟩ := v; right; exact hf name l a h

theorem fupdateList_good {α : Type} [BEq α] (P : Nat × Nat → Prop) :
    ∀ (entries : List (α × (Nat × Nat))) (f : FiniteMap α (Nat × Nat)),
      (∀ k v, f k = some v → P v) → (∀ e ∈ entries, P e.2) →
      ∀ k v, FUPDATE_LIST f entries k = some v → P v
  | [], f, hf, _, k, v, h => hf k v h
  | e :: es, f, hf, he, k, v, h => by
      rw [FUPDATE_LIST_cons] at h
      refine fupdateList_good P es _ ?_ (fun x hx => he x (List.mem_cons_of_mem _ hx)) k v h
      intro k' v' h'
      unfold FUPDATE at h'
      split at h'
      · cases h'; exact he e List.mem_cons_self
      · exact hf k' v' h'

/-- CrepToLoop's function table maps every name to a label `64 + i`. -/
theorem makeFuncs_good {β γ : Type}
    (prog : List (Basis.Pure.MlString.MlString × List β × γ)) :
    ∀ k l a, (crepToLoopMakeFuncsExactExecutable prog).lookup k = some (l, a) → 64 ≤ l := by
  intro k l a h
  have := fupdateList_good (fun v => 64 ≤ v.1) _ (HolFiniteMapExact.empty.lookup)
    (by intro k v h; simp [HolFiniteMapExact.empty] at h) ?_ k (l, a) h
  · exact this
  · intro e he
    rw [List.mem_reverse] at he
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
    simp [firstLoopName]

/-- Every Loop call has a target `some n` with `n = 0 ∨ 64 ≤ n` (never a stub label),
including inside call handlers. -/
def loopTgtOk {width : Nat} [NeZero width] :
    HolLoopProg width → Prop
  | .seq first second => loopTgtOk first ∧ loopTgtOk second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopTgtOk thenBranch ∧ loopTgtOk elseBranch
  | .loop _ body _ => loopTgtOk body
  | .mark body => loopTgtOk body
  | .call _ t _ none => TgtGood t
  | .call _ t _ (some (_, handler, normal, _)) =>
      TgtGood t ∧ loopTgtOk handler ∧ loopTgtOk normal
  | _ => True
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [HolLoopProg.call.sizeOf_spec]; omega)

/-- Every element of a list satisfies the nested LocValue-free predicate. -/
def loopListTgtOk {width : Nat} [NeZero width]
    (programs : List (HolLoopProg width)) : Prop :=
  ∀ program, program ∈ programs → loopTgtOk program

private theorem loopListTgtOk_append {width : Nat} [NeZero width]
    (first second : List (HolLoopProg width))
    (hfirst : loopListTgtOk first)
    (hsecond : loopListTgtOk second) :
    loopListTgtOk (first ++ second) := by
  intro program hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hfirst program hmem
  · exact hsecond program hmem

private theorem loopListTgtOk_append3 {width : Nat} [NeZero width]
    (first second : List (HolLoopProg width)) (last : HolLoopProg width)
    (hfirst : loopListTgtOk first)
    (hsecond : loopListTgtOk second)
    (hlast : loopListTgtOk [last]) :
    loopListTgtOk (first ++ second ++ [last]) := by
  intro program hmem
  rcases List.mem_append.mp hmem with hprefix | hlastMem
  · rcases List.mem_append.mp hprefix with hfirstMem | hsecondMem
    · exact hfirst program hfirstMem
    · exact hsecond program hsecondMem
  · exact hlast program (by simpa using hlastMem)

private theorem loopNestedSeqHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (programs : List (HolLoopProg width))
    (hfree : loopListTgtOk programs) :
    loopTgtOk (loopNestedSeqHOL programs) := by
  induction programs with
  | nil => simp [loopNestedSeqHOL, loopTgtOk]
  | cons first rest ih =>
      have hfirst := hfree first (by simp)
      have hrest : loopListTgtOk rest := by
        intro program hmem
        exact hfree program (by simp [hmem])
      simpa [loopNestedSeqHOL, loopTgtOk] using And.intro hfirst (ih hrest)

private theorem loopListTgtOk_zipWith {width : Nat} [NeZero width]
    {α β : Type} (f : α → β → HolLoopProg width)
    (hfree : ∀ x y, loopTgtOk (f x y)) :
    ∀ (xs : List α) (ys : List β), loopListTgtOk (xs.zipWith f ys)
  | [], _ => by simp [loopListTgtOk]
  | _ :: _, [] => by simp [loopListTgtOk]
  | x :: xs, y :: ys => by
      simp only [List.zipWith_cons_cons, loopListTgtOk, List.mem_cons]
      intro program hmem
      rcases hmem with rfl | hmem
      · exact hfree x y
      · exact loopListTgtOk_zipWith f hfree xs ys program hmem

private theorem compileCrepopHOLExact_codeTgtOk {width : Nat} [NeZero width]
    (operator : CrepOp) (target : Compiler.Encoders.Asm.AsmArchitecture)
    (left right tmp : Nat)
    (live : NumSet) :
    loopListTgtOk
      (compileCrepopHOLExact (width := width) operator target left right tmp live).1 := by
  cases operator with
  | mul =>
      by_cases htarget : target = .armv7 <;>
        simp [compileCrepopHOLExact, htarget,
          loopListTgtOk, loopTgtOk]

mutual
private theorem compileExpHOLExact_codeTgtOk {width : Nat} [NeZero width]
    (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∀ expression : CrepExpHOL width,
      loopListTgtOk (compileExpHOLExact context tmp live expression).1
  | .baseAddr => by simp [compileExpHOLExact, loopListTgtOk]
  | .topAddr => by simp [compileExpHOLExact, loopListTgtOk]
  | .const _ => by simp [compileExpHOLExact, loopListTgtOk]
  | .var _ => by simp [compileExpHOLExact, loopListTgtOk]
  | .load address => by
      have ih := compileExpHOLExact_codeTgtOk context tmp live address
      rcases hA : compileExpHOLExact context tmp live address with ⟨code, value, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact ih
  | .load32 address => by
      have ih := compileExpHOLExact_codeTgtOk context tmp live address
      rcases hA : compileExpHOLExact context tmp live address with ⟨code, value, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact loopListTgtOk_append code _ ih (by
        simp [loopListTgtOk, loopTgtOk])
  | .loadByte address => by
      have ih := compileExpHOLExact_codeTgtOk context tmp live address
      rcases hA : compileExpHOLExact context tmp live address with ⟨code, value, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact loopListTgtOk_append code _ ih (by
        simp [loopListTgtOk, loopTgtOk])
  | .loadGlob _ => by simp [compileExpHOLExact, loopListTgtOk]
  | .op operator expressions => by
      have ih := compileExpsHOLExact_codeTgtOk context tmp live expressions
      rcases hA : compileExpsHOLExact context tmp live expressions with
        ⟨code, values, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact ih
  | .crepOp operator expressions => by
      have ih := compileExpsHOLExact_codeTgtOk context tmp live expressions
      rcases hA : compileExpsHOLExact context tmp live expressions with
        ⟨code, values, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      rcases hC : compileCrepopHOLExact (width := width) operator context.target next (next + 1)
          (next + values.length)
          (sptListInsert ((List.range values.length).map (fun offset => next + offset)) outLive)
          with ⟨operationCode, destination⟩
      simp only [compileExpHOLExact, hA, hC]
      have hAssigned : loopListTgtOk
          ((List.range values.length).zipWith
            (fun offset value => HolLoopProg.assign (next + offset) value) values) :=
        loopListTgtOk_zipWith _
          (fun _ _ => by simp [loopTgtOk]) _ _
      have hPrefix := loopListTgtOk_append code _ ih hAssigned
      have hOperation : loopListTgtOk operationCode := by
        have h := compileCrepopHOLExact_codeTgtOk (width := width) operator context.target next
          (next + 1) (next + values.length)
          (sptListInsert ((List.range values.length).map (fun offset => next + offset)) outLive)
        rw [hC] at h
        exact h
      exact loopListTgtOk_append _ operationCode hPrefix hOperation
  | .cmp operator left right => by
      have ihLeft := compileExpHOLExact_codeTgtOk context tmp live left
      rcases hA : compileExpHOLExact context tmp live left with
        ⟨leftCode, leftValue, leftNext, leftLive⟩
      rw [hA] at ihLeft
      simp only at ihLeft
      have ihRight := compileExpHOLExact_codeTgtOk context leftNext leftLive right
      rcases hB : compileExpHOLExact context leftNext leftLive right with
        ⟨rightCode, rightValue, rightNext, rightLive⟩
      rw [hB] at ihRight
      simp only at ihRight
      simp only [compileExpHOLExact, hA, hB, progIfHOLExact]
      have htail : loopListTgtOk
          [.assign (rightNext + 1) leftValue,
           .assign (rightNext + 2) rightValue,
           .ite operator (rightNext + 1) (.reg (rightNext + 2))
             (.assign (rightNext + 1) (.const 1))
             (.assign (rightNext + 1) (.const 0))
             (sptListInsert [rightNext + 1, rightNext + 2] rightLive)] := by
        simp [loopListTgtOk, loopTgtOk]
      exact loopListTgtOk_append (leftCode ++ rightCode) _
        (loopListTgtOk_append leftCode rightCode ihLeft ihRight) htail
  | .shift operator left right => by
      have ihLeft := compileExpHOLExact_codeTgtOk context tmp live left
      rcases hA : compileExpHOLExact context tmp live left with
        ⟨leftCode, leftValue, leftNext, leftLive⟩
      rw [hA] at ihLeft
      simp only at ihLeft
      have ihRight := compileExpHOLExact_codeTgtOk context leftNext leftLive right
      rcases hB : compileExpHOLExact context leftNext leftLive right with
        ⟨rightCode, rightValue, rightNext, rightLive⟩
      rw [hB] at ihRight
      simp only at ihRight
      simp only [compileExpHOLExact, hA, hB]
      exact loopListTgtOk_append leftCode rightCode ihLeft ihRight
  termination_by expression => sizeOf expression

private theorem compileExpsHOLExact_codeTgtOk {width : Nat} [NeZero width]
    (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∀ expressions : List (CrepExpHOL width),
      loopListTgtOk (compileExpsHOLExact context tmp live expressions).1
  | [] => by simp [compileExpsHOLExact, loopListTgtOk]
  | expression :: expressions => by
      have ihExpression :=
        compileExpHOLExact_codeTgtOk context tmp live expression
      rcases hA : compileExpHOLExact context tmp live expression with
        ⟨code, value, next, outLive⟩
      rw [hA] at ihExpression
      simp only at ihExpression
      have ihTail := compileExpsHOLExact_codeTgtOk context next outLive expressions
      rcases hB : compileExpsHOLExact context next outLive expressions with
        ⟨tailCode, tailValues, finalTemp, finalLive⟩
      rw [hB] at ihTail
      simp only at ihTail
      simp only [compileExpsHOLExact, hA, hB]
      exact loopListTgtOk_append code tailCode ihExpression ihTail
  termination_by expressions => sizeOf expressions
end

private theorem compileHOLExact_tgtOk {width : Nat} [NeZero width] :
    ∀ (context : CrepToLoopContextExact) (live : NumSet)
      (program : CrepProgHOL width), FuncsGood context →
      loopTgtOk (compileHOLExact context live program)
  | context, live, .skip, hf => by simp [compileHOLExact, loopTgtOk]
  | context, live, .break _, hf => by simp [compileHOLExact, loopTgtOk]
  | context, live, .continue _, hf => by simp [compileHOLExact, loopTgtOk]
  | context, live, .tick, hf => by simp [compileHOLExact, loopTgtOk]
  | context, live, .raise exception, hf => by
      simp [compileHOLExact, loopTgtOk]
  | context, live, .shMem operator name address, hf => by
      cases hname : context.vars.lookup name with
      | none => simp [compileHOLExact, hname, loopTgtOk]
      | some mappedName =>
          rcases hA : compileExpHOLExact context (context.vmax + 1) live address with
            ⟨code, compiledAddress, next, outLive⟩
          have hcode := compileExpHOLExact_codeTgtOk context
            (context.vmax + 1) live address
          rw [hA] at hcode
          simp only at hcode
          simp only [compileHOLExact, hname, hA]
          apply loopNestedSeqHOL_preserves_tgtOk
          exact loopListTgtOk_append code _ hcode (by
            simp [loopListTgtOk, loopTgtOk])
  | context, live, .store destination source, hf => by
      rcases hD : compileExpHOLExact context (context.vmax + 1) live destination with
        ⟨destinationCode, address, nextTemporary, nextLive⟩
      rcases hS : compileExpHOLExact context nextTemporary nextLive source with
        ⟨sourceCode, value, finalTemporary, finalLive⟩
      have hDfree := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live destination
      have hSfree := compileExpHOLExact_codeTgtOk context
        nextTemporary nextLive source
      rw [hD] at hDfree
      rw [hS] at hSfree
      simp only at hDfree hSfree
      simp only [compileHOLExact, hD, hS]
      apply loopNestedSeqHOL_preserves_tgtOk
      have htail : loopListTgtOk
          [.assign finalTemporary value, .store address finalTemporary] := by
        simp [loopListTgtOk, loopTgtOk]
      apply loopListTgtOk_append
        (destinationCode ++ sourceCode) _
        (loopListTgtOk_append destinationCode sourceCode hDfree hSfree)
      exact htail
  | context, live, .store32 destination source, hf => by
      rcases hD : compileExpHOLExact context (context.vmax + 1) live destination with
        ⟨destinationCode, address, nextTemporary, nextLive⟩
      rcases hS : compileExpHOLExact context nextTemporary nextLive source with
        ⟨sourceCode, value, finalTemporary, finalLive⟩
      have hDfree := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live destination
      have hSfree := compileExpHOLExact_codeTgtOk context
        nextTemporary nextLive source
      rw [hD] at hDfree
      rw [hS] at hSfree
      simp only at hDfree hSfree
      simp only [compileHOLExact, hD, hS]
      apply loopNestedSeqHOL_preserves_tgtOk
      have htail : loopListTgtOk
          [.assign finalTemporary address, .assign (finalTemporary + 1) value,
           .store32 finalTemporary (finalTemporary + 1)] := by
        simp [loopListTgtOk, loopTgtOk]
      apply loopListTgtOk_append
        (destinationCode ++ sourceCode) _
        (loopListTgtOk_append destinationCode sourceCode hDfree hSfree)
      exact htail
  | context, live, .storeByte destination source, hf => by
      rcases hD : compileExpHOLExact context (context.vmax + 1) live destination with
        ⟨destinationCode, address, nextTemporary, nextLive⟩
      rcases hS : compileExpHOLExact context nextTemporary nextLive source with
        ⟨sourceCode, value, finalTemporary, finalLive⟩
      have hDfree := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live destination
      have hSfree := compileExpHOLExact_codeTgtOk context
        nextTemporary nextLive source
      rw [hD] at hDfree
      rw [hS] at hSfree
      simp only at hDfree hSfree
      simp only [compileHOLExact, hD, hS]
      apply loopNestedSeqHOL_preserves_tgtOk
      have htail : loopListTgtOk
          [.assign finalTemporary address, .assign (finalTemporary + 1) value,
           .storeByte finalTemporary (finalTemporary + 1)] := by
        simp [loopListTgtOk, loopTgtOk]
      apply loopListTgtOk_append
        (destinationCode ++ sourceCode) _
        (loopListTgtOk_append destinationCode sourceCode hDfree hSfree)
      exact htail
  | context, live, .storeGlob address value, hf => by
      rcases hA : compileExpHOLExact context (context.vmax + 1) live value with
        ⟨code, compiledValue, next, outLive⟩
      have hcode := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live value
      rw [hA] at hcode
      simp only at hcode
      simp only [compileHOLExact, hA]
      apply loopNestedSeqHOL_preserves_tgtOk
      exact loopListTgtOk_append code _ hcode (by
        simp [loopListTgtOk, loopTgtOk])
  | context, live, .seq first second, hf => by
      simp only [compileHOLExact, loopTgtOk]
      exact ⟨compileHOLExact_tgtOk context live first hf,
        compileHOLExact_tgtOk context live second hf⟩
  | context, live, .ite condition thenBranch elseBranch, hf => by
      rcases hC : compileExpHOLExact context (context.vmax + 1) live condition with
        ⟨conditionCode, compiledCondition, temporary, outLive⟩
      have hcode := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live condition
      rw [hC] at hcode
      simp only at hcode
      have hthen := compileHOLExact_tgtOk context live thenBranch hf
      have helse := compileHOLExact_tgtOk context live elseBranch hf
      simp only [compileHOLExact, hC]
      apply loopNestedSeqHOL_preserves_tgtOk
      have htail : loopListTgtOk
          [.assign temporary compiledCondition,
           .ite .notEqual temporary (.imm (0 : BitVec width))
             (compileHOLExact context live thenBranch)
             (compileHOLExact context live elseBranch) live] := by
        simp [loopListTgtOk, loopTgtOk, hthen, helse]
      exact loopListTgtOk_append conditionCode _ hcode htail
  | context, live, .while condition body, hf => by
      rcases hC : compileExpHOLExact context (context.vmax + 1) live condition with
        ⟨conditionCode, compiledCondition, temporary, outLive⟩
      have hcode := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live condition
      rw [hC] at hcode
      simp only at hcode
      have hbody := compileHOLExact_tgtOk context live body hf
      simp only [compileHOLExact, hC, loopTgtOk]
      apply loopNestedSeqHOL_preserves_tgtOk
      have htail : loopListTgtOk
          [.assign temporary compiledCondition,
           .ite .notEqual temporary (.imm (0 : BitVec width))
             (.seq (compileHOLExact context live body) (.continue 0)) (.break 0) live] := by
        simp [loopListTgtOk, loopTgtOk, hbody]
      exact loopListTgtOk_append conditionCode _ hcode htail
  | context, live, .assign name value, hf => by
      cases hname : context.vars.lookup name with
      | none => simp [compileHOLExact, hname, loopTgtOk]
      | some mappedName =>
          rcases hA : compileExpHOLExact context (context.vmax + 1) live value with
            ⟨code, compiledValue, next, outLive⟩
          have hcode := compileExpHOLExact_codeTgtOk context
            (context.vmax + 1) live value
          rw [hA] at hcode
          simp only at hcode
          simp only [compileHOLExact, hname, hA]
          apply loopNestedSeqHOL_preserves_tgtOk
          exact loopListTgtOk_append code _ hcode (by
            simp [loopListTgtOk, loopTgtOk])
  | context, live, .primitive destinations operator arguments, hf => by
      cases hDest : destinations.mapM context.vars.lookup <;>
        cases hArgs : arguments.mapM context.vars.lookup <;>
          simp [compileHOLExact, hDest, hArgs, loopTgtOk]
  | context, live, .dec name value body, hf => by
      rcases hA : compileExpHOLExact context (context.vmax + 1) live value with
        ⟨code, compiledValue, temporary, outLive⟩
      have hcode := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live value
      rw [hA] at hcode
      simp only at hcode
      let bodyContext :=
        { context with vars := context.vars.updateEq (name, temporary), vmax := temporary }
      let bodyLive := sptInsert temporary () live
      have hbody := compileHOLExact_tgtOk bodyContext bodyLive body hf
      simp only [compileHOLExact, hA, loopTgtOk]
      exact ⟨loopNestedSeqHOL_preserves_tgtOk code hcode, True.intro, hbody⟩
  | context, live, .call none name arguments, hf => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live arguments with
        ⟨code, values, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeTgtOk context
        (context.vmax + 1) live arguments
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := loopListTgtOk_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [loopTgtOk])
        (genTemps nextTemporary values.length) values
      have hCall : loopListTgtOk
          [HolLoopProg.call (width := width) none (some (findLabExact context name))
            (genTemps nextTemporary values.length) none] := by
        simp [loopListTgtOk, loopTgtOk, TgtGood, findLab_good context name hf]
      simp only [compileHOLExact, hA]
      apply loopNestedSeqHOL_preserves_tgtOk
      exact loopListTgtOk_append3 code
        (List.zipWith HolLoopProg.assign (genTemps nextTemporary values.length) values)
        (HolLoopProg.call none (some (findLabExact context name))
          (genTemps nextTemporary values.length) none)
        hcode hAssignments hCall
  | context, live, .call (some (returns, none)) name arguments, hf => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live arguments with
        ⟨code, values, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeTgtOk context
        (context.vmax + 1) live arguments
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := loopListTgtOk_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [loopTgtOk])
        (genTemps nextTemporary values.length) values
      have hCall : loopListTgtOk
          [HolLoopProg.call (width := width)
            (some ((match returns.mapM context.vars.lookup with
              | none => [context.vmax + 2]
              | some names => names), live))
            (some (findLabExact context name)) (genTemps nextTemporary values.length)
            (some (context.vmax + 1, .raise (context.vmax + 1), .skip, live))] := by
        simp [loopListTgtOk, loopTgtOk, TgtGood, findLab_good context name hf]
      rw [compileHOLExact]
      simp only [hA]
      apply loopNestedSeqHOL_preserves_tgtOk
      exact loopListTgtOk_append3 code
        (List.zipWith HolLoopProg.assign (genTemps nextTemporary values.length) values)
        (HolLoopProg.call
          (some ((match returns.mapM context.vars.lookup with
            | none => [context.vmax + 2]
            | some names => names), live))
          (some (findLabExact context name)) (genTemps nextTemporary values.length)
          (some (context.vmax + 1, .raise (context.vmax + 1), .skip, live)))
        hcode hAssignments hCall
  | context, live, .call (some (returns, some (exception, handler))) name arguments, hf => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live arguments with
        ⟨code, values, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeTgtOk context
        (context.vmax + 1) live arguments
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := loopListTgtOk_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [loopTgtOk])
        (genTemps nextTemporary values.length) values
      have hhandler := compileHOLExact_tgtOk context live handler hf
      have hCall : loopListTgtOk
          [HolLoopProg.call (width := width)
            (some ((match returns.mapM context.vars.lookup with
              | none => [context.vmax + 2]
              | some names => names), live))
            (some (findLabExact context name)) (genTemps nextTemporary values.length)
            (some (context.vmax + 1,
              .ite .notEqual (context.vmax + 1) (.imm exception) (.raise (context.vmax + 1))
                (.seq .tick (compileHOLExact context live handler)) live,
              .skip, live))] := by
        simp [loopListTgtOk, loopTgtOk, TgtGood, findLab_good context name hf, hhandler]
      rw [compileHOLExact]
      simp only [hA]
      apply loopNestedSeqHOL_preserves_tgtOk
      exact loopListTgtOk_append3 code
        (List.zipWith HolLoopProg.assign (genTemps nextTemporary values.length) values)
        (HolLoopProg.call
          (some ((match returns.mapM context.vars.lookup with
            | none => [context.vmax + 2]
            | some names => names), live))
          (some (findLabExact context name)) (genTemps nextTemporary values.length)
          (some (context.vmax + 1,
            .ite .notEqual (context.vmax + 1) (.imm exception)
              (.raise (context.vmax + 1)) (.seq .tick (compileHOLExact context live handler)) live,
            .skip, live)))
        hcode hAssignments hCall
  | context, live, .extCall function configuration configurationLength array arrayLength, hf => by
      rw [compileHOLExact]
      split <;> simp [loopTgtOk]
  | context, live, .return values, hf => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live values with
        ⟨code, compiledValues, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeTgtOk context
        (context.vmax + 1) live values
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := loopListTgtOk_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [loopTgtOk])
        (genTemps nextTemporary compiledValues.length) compiledValues
      have hReturn : loopListTgtOk
          [HolLoopProg.return (width := width)
            (genTemps nextTemporary compiledValues.length)] := by
        simp [loopListTgtOk, loopTgtOk]
      unfold compileHOLExact
      simp only [hA]
      apply loopNestedSeqHOL_preserves_tgtOk
      exact loopListTgtOk_append3 code
        (List.zipWith HolLoopProg.assign
          (genTemps nextTemporary compiledValues.length) compiledValues)
        (HolLoopProg.return (width := width)
          (genTemps nextTemporary compiledValues.length))
        hcode hAssignments hReturn
termination_by _ _ program => sizeOf program
decreasing_by
  all_goals simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepProgHOL.dec.sizeOf_spec, CrepProgHOL.seq.sizeOf_spec,
        CrepProgHOL.ite.sizeOf_spec, CrepProgHOL.while.sizeOf_spec,
        CrepProgHOL.call.sizeOf_spec]; omega)

/-- The exact loop-call optimizer does not introduce `locValue` into a
program that was recursively free of it.  The live-set parameter is
generalized so the `Seq` case can use the second induction hypothesis at the
live set returned by compiling the first child. -/
theorem loopCallCompHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (program : HolLoopProg width) (live : Spt Nat)
    (hfree : loopTgtOk program) :
    loopTgtOk (loopCallCompHOL live program).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    ∀ live, loopTgtOk p →
      loopTgtOk (loopCallCompHOL live p).1
  let mPair : HolLoopProg width × NumSet → Prop := fun _ => True
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop := fun _ => True
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop := fun _ => True
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop :=
    fun _ => True
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_2 =>
      intro name value live
      intro hfree
      cases value with
      | var m => simp [loopCallCompHOL.eq_5, loopTgtOk]
      | const value => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | lookup address => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | load address => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | op operator args => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | shift operator left right => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | baseAddr => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | topAddr => simp [loopCallCompHOL.eq_6, loopTgtOk]
    case refine_4 =>
      intro operation live
      intro hfree
      cases operation with
      | longMul => simp [loopCallCompHOL.eq_19, loopTgtOk]
      | longDiv => simp [loopCallCompHOL.eq_20, loopTgtOk]
      | div => simp [loopCallCompHOL.eq_21, loopTgtOk]
    case refine_23 =>
      intro returns target arguments handler ih live hfree
      cases target with
      | none => cases handler with
        | none => simp [loopTgtOk, TgtGood] at hfree
        | some e => rcases e with ⟨_, _, _, _⟩; simp [loopTgtOk, TgtGood] at hfree
      | some t => cases handler with
        | none => simpa [loopCallCompHOL.eq_2, loopTgtOk] using hfree
        | some e =>
            rcases e with ⟨_, _, _, _⟩
            simpa [loopCallCompHOL.eq_2, loopTgtOk] using hfree
    all_goals simp_all [mProg, mPair, mTriple, mQuad, mHandler,
      loopTgtOk, loopCallCompHOL.eq_1, loopCallCompHOL.eq_2,
      loopCallCompHOL.eq_3, loopCallCompHOL.eq_4, loopCallCompHOL.eq_5,
      loopCallCompHOL.eq_6, loopCallCompHOL.eq_7, loopCallCompHOL.eq_8,
      loopCallCompHOL.eq_9, loopCallCompHOL.eq_10, loopCallCompHOL.eq_11,
      loopCallCompHOL.eq_12, loopCallCompHOL.eq_13, loopCallCompHOL.eq_14,
      loopCallCompHOL.eq_15, loopCallCompHOL.eq_16, loopCallCompHOL.eq_17,
      loopCallCompHOL.eq_18, loopCallCompHOL.eq_19, loopCallCompHOL.eq_20,
      loopCallCompHOL.eq_21, loopCallCompHOL.eq_22]
  exact hgeneral live hfree

/-- `shrinkHOL` cannot introduce the runtime-only `locValue` constructor.
This is Flapjack-specific infrastructure: it supplies the optimizer half of
the parser-routed compile-path invariant and is not an additional HOL result.
The loop branch uses the reviewed `fixedpoint_thm` equation to reduce a
successful fixedpoint result to one structural `shrinkHOL` call on its body. -/
theorem shrinkHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (program : HolLoopProg width) (live : NumSet)
    (hfree : loopTgtOk program) :
    loopTgtOk (shrinkHOL [] program live).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    ∀ lt live, loopTgtOk p →
      loopTgtOk (shrinkHOL lt p live).1
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_2 =>
      intro name value lt live hfree
      simp only [shrinkHOL.eq_15]
      cases hlookup : sptLookup name live <;>
        simp [loopTgtOk]
    case refine_12 =>
      intro operator condition right thenBranch elseBranch branchLive
        ihThen ihElse lt live hfree
      simp only [loopTgtOk] at hfree
      rcases hfree with ⟨hthen, helse⟩
      cases right with
      | reg r =>
          simp only [shrinkHOL.eq_3]
          rcases hsThen : shrinkHOL lt thenBranch (sptInter live branchLive) with
            ⟨then', liveThen⟩
          rcases hsElse : shrinkHOL lt elseBranch (sptInter live branchLive) with
            ⟨else', liveElse⟩
          have hthenFree := ihThen lt (sptInter live branchLive) hthen
          have helseFree := ihElse lt (sptInter live branchLive) helse
          rw [hsThen] at hthenFree
          rw [hsElse] at helseFree
          simp only [loopTgtOk]
          exact ⟨hthenFree, helseFree⟩
      | imm value =>
          simp only [shrinkHOL.eq_4]
          rcases hsThen : shrinkHOL lt thenBranch (sptInter live branchLive) with
            ⟨then', liveThen⟩
          rcases hsElse : shrinkHOL lt elseBranch (sptInter live branchLive) with
            ⟨else', liveElse⟩
          have hthenFree := ihThen lt (sptInter live branchLive) hthen
          have helseFree := ihElse lt (sptInter live branchLive) helse
          rw [hsThen] at hthenFree
          rw [hsElse] at helseFree
          simp only [loopTgtOk]
          exact ⟨hthenFree, helseFree⟩
    case refine_13 =>
      intro liveIn body liveOut ihBody lt live hfree
      simp only [shrinkHOL.eq_2]
      have hfreeBody : loopTgtOk body := by
        simpa [loopTgtOk] using hfree
      cases hfp : fixedpointHOL lt liveIn .ln
          (sptUnion liveIn (sptInter liveOut live)) body with
      | none =>
          have hbody := ihBody ((liveIn, sptInter liveOut live) :: lt)
            (sptUnion liveIn (sptInter liveOut live)) hfreeBody
          simp only [loopTgtOk]
          exact hbody
      | some result =>
          rcases result with ⟨body', liveBody⟩
          have hfixed := fixedpoint_thm lt liveIn .ln
            (sptUnion liveIn (sptInter liveOut live)) body liveBody body' hfp
          have hfreeBody' : loopTgtOk body' := by
            have h := ihBody
              ((sptInter liveIn liveBody, sptUnion liveIn (sptInter liveOut live)) :: lt)
              (sptUnion liveIn (sptInter liveOut live)) hfreeBody
            rw [hfixed] at h
            exact h
          simp only [loopTgtOk]
          exact hfreeBody'
    case refine_22 =>
      intro d s lt live _
      cases h : sptLookup d live <;> simp_all [shrinkHOL, loopTgtOk]
    case refine_23 =>
      intro returns target arguments handler hHandler lt live hfree
      have ht : TgtGood target := by
        cases handler with
        | none => simpa [loopTgtOk] using hfree
        | some e => rcases e with ⟨_, _, _, _⟩; simp only [loopTgtOk] at hfree; exact hfree.1
      cases returns with
      | none => simp only [shrinkHOL.eq_19, loopTgtOk]; exact ht
      | some returnData =>
          rcases returnData with ⟨returnNames, returnLive⟩
          cases handler with
          | none => simp only [shrinkHOL.eq_20, loopTgtOk]; exact ht
          | some entry =>
              rcases entry with ⟨exception, handler, normal, liveOut⟩
              rw [shrinkHOL.eq_21]
              rcases hHandler with ⟨ihHandler, ihNormal⟩
              simp only [loopTgtOk] at hfree
              rcases hfree with ⟨-, hHandlerFree, hNormalFree⟩
              rcases hsNormal : shrinkHOL lt normal live with ⟨normal', liveNormal⟩
              rcases hsHandler : shrinkHOL lt handler live with ⟨handler', liveHandler⟩
              have hNormal' := ihNormal lt live hNormalFree
              have hHandler' := ihHandler lt live hHandlerFree
              rw [hsNormal] at hNormal'
              rw [hsHandler] at hHandler'
              simp only [loopTgtOk]
              exact ⟨ht, hHandler', hNormal'⟩
    all_goals
      simp_all [mProg, mPair, mTriple, mQuad, mHandler,
        loopTgtOk, shrinkHOL, shrinkHOL.eq_1, shrinkHOL.eq_2,
        shrinkHOL.eq_3, shrinkHOL.eq_4, shrinkHOL.eq_5, shrinkHOL.eq_6,
        shrinkHOL.eq_7, shrinkHOL.eq_8, shrinkHOL.eq_9, shrinkHOL.eq_10,
        shrinkHOL.eq_11, shrinkHOL.eq_12, shrinkHOL.eq_13, shrinkHOL.eq_14,
        shrinkHOL.eq_15, shrinkHOL.eq_16, shrinkHOL.eq_17, shrinkHOL.eq_18,
        shrinkHOL.eq_19, shrinkHOL.eq_20, shrinkHOL.eq_21, shrinkHOL.eq_22,
        shrinkHOL.eq_23, shrinkHOL.eq_24, shrinkHOL.eq_25, shrinkHOL.eq_26,
        shrinkHOL.eq_27]
  exact hgeneral [] live hfree

/-- `markAllHOL` preserves the Flapjack-only recursive absence of `locValue`,
including in both programs stored by a call handler. This is infrastructure
for the parser-routed compile-path invariant, not an additional HOL result. -/
theorem markAllHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (program : HolLoopProg width)
    (hfree : loopTgtOk program) :
    loopTgtOk (markAllHOL program).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    loopTgtOk p →
      loopTgtOk (markAllHOL p).1
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_11 =>
      intro first second ihFirst ihSecond hfree
      simp only [loopTgtOk] at hfree
      rcases hfree with ⟨hFirst, hSecond⟩
      have hFirst' := ihFirst hFirst
      have hSecond' := ihSecond hSecond
      simp only [markAllHOL]
      cases hmarkFirst : markAllHOL first with
      | mk first' firstMarked =>
              cases hmarkSecond : markAllHOL second with
              | mk second' secondMarked =>
              rw [hmarkFirst] at hFirst'
              rw [hmarkSecond] at hSecond'
              cases firstMarked <;> cases secondMarked <;>
                simp [loopTgtOk, hFirst', hSecond']
    case refine_12 =>
      intro operator condition right thenBranch elseBranch branchLive ihThen ihElse hfree
      simp only [loopTgtOk] at hfree
      rcases hfree with ⟨hthen, helse⟩
      have hthen' := ihThen hthen
      have helse' := ihElse helse
      simp only [markAllHOL]
      cases hmarkThen : markAllHOL thenBranch with
      | mk then' thenMarked =>
          cases hmarkElse : markAllHOL elseBranch with
          | mk else' elseMarked =>
              rw [hmarkThen] at hthen'
              rw [hmarkElse] at helse'
              cases thenMarked <;> cases elseMarked <;>
                simp [loopTgtOk, hthen', helse']
    case refine_23 =>
      intro returns target arguments handler hHandler hfree
      cases handler with
      | none => simpa [markAllHOL, loopTgtOk] using hfree
      | some entry =>
          rcases entry with ⟨exception, handler, normal, liveOut⟩
          rcases hHandler with ⟨ihHandler, ihNormal⟩
          simp only [loopTgtOk] at hfree
          rcases hfree with ⟨ht, hHandlerFree, hNormalFree⟩
          have hHandler' := ihHandler hHandlerFree
          have hNormal' := ihNormal hNormalFree
          simp only [markAllHOL]
          cases hmarkHandler : markAllHOL handler with
          | mk handler' handlerMarked =>
              cases hmarkNormal : markAllHOL normal with
              | mk normal' normalMarked =>
                  rw [hmarkHandler] at hHandler'
                  rw [hmarkNormal] at hNormal'
                  cases handlerMarked <;> cases normalMarked <;>
                    simp [loopTgtOk, ht, hHandler', hNormal']
    all_goals
      intros
      simp_all [mProg, mPair, mTriple, mQuad, mHandler,
        loopTgtOk, markAllHOL]
  exact hgeneral hfree

private theorem compHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (program : HolLoopProg width) (hfree : loopTgtOk program) :
    loopTgtOk (compHOL program) := by
  exact markAllHOL_preserves_tgtOk _
    (shrinkHOL_preserves_tgtOk program .ln hfree)

private theorem optimiseHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (program : HolLoopProg width) (hfree : loopTgtOk program) :
    loopTgtOk (optimiseHOL program) := by
  apply compHOL_preserves_tgtOk
  exact loopCallCompHOL_preserves_tgtOk program .ln hfree


/-! ## Whole CrepToLoop output -/

theorem zipWith_fst_mem {α β γ : Type} (g : α → β → γ) :
    ∀ (l1 : List α) (l2 : List β) (x : α × γ),
      x ∈ List.zipWith (fun n e => (n, g n e)) l1 l2 → x.1 ∈ l1
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, x, h => by
      rw [List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (zipWith_fst_mem g as bs x h)

/-- (1) CrepToLoop numbers every user function `64 + i`. -/
theorem compileProgHOLExact_names {width : Nat} [NeZero width]
    (target : Compiler.Encoders.Asm.AsmArchitecture)
    (program : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width)) :
    ∀ x ∈ compileProgHOLExact target program, ∃ i, x.1 = 64 + i ∧ i < program.length := by
  intro x hx
  unfold compileProgHOLExact at hx
  have := zipWith_fst_mem (fun (_ : Nat) (entry : Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width) => (List.range entry.2.1.length,
      optimiseHOL (compFuncHOLExact target (crepToLoopMakeFuncsExactExecutable program)
        entry.2.1 (crepSimpProgHOL entry.2.2)))) _ _ x hx
  obtain ⟨i, hi, he⟩ := List.mem_map.1 this
  exact ⟨i, by rw [← he, firstLoopName]; omega, List.mem_range.1 hi⟩


/-- Every body emitted by CrepToLoop (after the Loop optimiser) only calls admissible targets. -/
theorem compileProgHOLExact_bodiesTgtOk {width : Nat} [NeZero width]
    (target : Compiler.Encoders.Asm.AsmArchitecture)
    (program : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width)) :
    ∀ x ∈ compileProgHOLExact target program, loopTgtOk x.2.2 := by
  intro x hx
  unfold compileProgHOLExact at hx
  have key : ∀ (l1 : List Nat) (l2 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
      (y : Nat × List Nat × HolLoopProg width),
      y ∈ List.zipWith (fun (n : Nat) (entry : Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width) => (n, List.range entry.2.1.length,
        optimiseHOL (compFuncHOLExact target (crepToLoopMakeFuncsExactExecutable program)
          entry.2.1 (crepSimpProgHOL entry.2.2)))) l1 l2 → loopTgtOk y.2.2 := by
    intro l1
    induction l1 with
    | nil => intro l2 y h; simp at h
    | cons a as ih =>
        intro l2 y h
        cases l2 with
        | nil => simp at h
        | cons b bs =>
            rw [List.zipWith_cons_cons, List.mem_cons] at h
            rcases h with rfl | h
            · apply optimiseHOL_preserves_tgtOk
              unfold compFuncHOLExact
              exact compileHOLExact_tgtOk _ _ _ (makeFuncs_good program)
            · exact ih bs y h
  exact key _ _ x hx

/-! ## LoopToWord keeps call targets -/

theorem tgt_ne {t : Option Nat} (h : TgtGood t) : (t != some storeConstsStubLocation) = true := by
  cases t with
  | none => exact absurd h id
  | some n =>
      simp only [TgtGood] at h
      have : n ≠ 6 := by omega
      simp [storeConstsStubLocation, wordNumStubs, stackNumStubs, this]

theorem compHOL_noStub {width : Nat} [NeZero width] (ctx : Spt Nat) :
    ∀ (p : HolLoopProg width) (l : Nat × Nat), loopTgtOk p →
      WordNoStubCall (LoopToWord.compHOL ctx p l).1 = true
  | .seq a b, l, h => by
      simp only [loopTgtOk] at h
      have ha := compHOL_noStub ctx a l h.1
      rcases ha' : LoopToWord.compHOL ctx a l with ⟨w1, l1⟩
      have hb := compHOL_noStub ctx b l1 h.2
      rcases hb' : LoopToWord.compHOL ctx b l1 with ⟨w2, l2⟩
      rw [ha'] at ha; rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp only [ha', hb', WordNoStubCall, Bool.and_eq_true]
      exact ⟨ha, hb⟩
  | .ite o c r a b lv, l, h => by
      simp only [loopTgtOk] at h
      have ha := compHOL_noStub ctx a l h.1
      rcases ha' : LoopToWord.compHOL ctx a l with ⟨w1, l1⟩
      have hb := compHOL_noStub ctx b l1 h.2
      rcases hb' : LoopToWord.compHOL ctx b l1 with ⟨w2, l2⟩
      rw [ha'] at ha; rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [ha', hb', WordNoStubCall, ha, hb]
  | .loop li b lo, l, h => by
      simp only [loopTgtOk] at h
      have hb := compHOL_noStub ctx b l h
      rcases hb' : LoopToWord.compHOL ctx b l with ⟨w, l1⟩
      rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [hb', WordNoStubCall, hb]
  | .mark b, l, h => by
      simp only [loopTgtOk] at h
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); exact compHOL_noStub ctx b l h
  | .call none t args hd, l, h => by
      have ht : TgtGood t := by
        cases hd with
        | none => simpa [loopTgtOk] using h
        | some e => rcases e with ⟨_, _, _, _⟩; simp only [loopTgtOk] at h; exact h.1
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [WordNoStubCall, tgt_ne ht]
  | .call (some (vs, live)) t args none, l, h => by
      have ht : TgtGood t := by simpa [loopTgtOk] using h
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [WordNoStubCall, tgt_ne ht]
  | .call (some (vs, live)) t args (some (n, p1, p2, lo)), l, h => by
      simp only [loopTgtOk] at h
      obtain ⟨ht, h1, h2⟩ := h
      have hw1 := compHOL_noStub ctx p1 (l.1, l.2 + 1) h1
      rcases hw1' : LoopToWord.compHOL ctx p1 (l.1, l.2 + 1) with ⟨w1, l1⟩
      have hw2 := compHOL_noStub ctx p2 l1 h2
      rcases hw2' : LoopToWord.compHOL ctx p2 l1 with ⟨w2, l2⟩
      rw [hw1'] at hw1; rw [hw2'] at hw2
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [hw1', hw2', WordNoStubCall, tgt_ne ht, hw1, hw2]
  | .skip, _, _ => by rw [LoopToWord.compHOL]; rfl
  | .assign .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .store .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .setGlobal .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .load32 .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .loadByte .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .store32 .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .storeByte .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .break .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .continue .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .raise .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .return .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .tick, _, _ => by rw [LoopToWord.compHOL]; rfl
  | .fail, _, _ => by rw [LoopToWord.compHOL]; rfl
  | .locValue .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .ffi .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .shMem .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .primitive ds .addCarry as, _, _ => by
      rw [LoopToWord.compHOL.eq_def]; dsimp only; split <;> rfl
  | .arith (.longMul ..), _, _ => by rw [LoopToWord.compHOL]; rfl
  | .arith (.longDiv ..), _, _ => by rw [LoopToWord.compHOL]; rfl
  | .arith (.div ..), _, _ => by rw [LoopToWord.compHOL]; rfl
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

/-! ## Pancake → … → LoopToWord: `WordNoStubCall`, no hypothesis -/

theorem loopToWordCompile_noStub {width : Nat} [NeZero width]
    (code : List (Nat × List Nat × HolLoopProg width)) (h : ∀ x ∈ code, loopTgtOk x.2.2) :
    ∀ y ∈ loopToWordCompileHOL code, WordNoStubCall y.2.2 = true := by
  intro y hy
  unfold loopToWordCompileHOL loopToWordCompileProgHOL at hy
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
  unfold loopToWordCompFuncHOL
  exact compHOL_noStub _ _ _ (h e he)

/-- Main result: every WordLang function produced from **any** Pancake program by
PanSimp → PanStructs → PanGlobals → PanToCrep → CrepToLoop → LoopToWord has no call
targeting `storeConstsStubLocation`. -/
theorem panToWord_NoStubCall {width : Nat} [NeZero width]
    (arch : Compiler.Encoders.Asm.AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width)) :
    ∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true := by
  unfold panToWordCompileProgHOL
  exact loopToWordCompile_noStub _ (compileProgHOLExact_bodiesTgtOk _ _)

/-- And every function name is a user label `≥ 64`. -/
theorem panToWord_names {width : Nat} [NeZero width]
    (arch : Compiler.Encoders.Asm.AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width)) :
    ∀ y ∈ panToWordCompileProgHOL arch prog, 64 ≤ y.1 := by
  intro y hy
  unfold panToWordCompileProgHOL loopToWordCompileHOL loopToWordCompileProgHOL at hy
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
  obtain ⟨i, hi, -⟩ := compileProgHOLExact_names _ _ e he
  show 64 ≤ e.1; omega

/-! ## Witnesses -/

theorem tgtGood_rejects_stub : ¬ TgtGood (some storeConstsStubLocation) := by
  simp [TgtGood, storeConstsStubLocation, wordNumStubs, stackNumStubs]

theorem tgtGood_accepts : TgtGood (some 0) ∧ TgtGood (some 64) ∧ ¬ TgtGood none := by
  simp [TgtGood]

theorem findLab_empty (t : Compiler.Encoders.Asm.AsmArchitecture)
    (name : Basis.Pure.MlString.MlString) :
    findLabExact (mkCtxtExact t HolFiniteMapExact.empty HolFiniteMapExact.empty 0) name = 0 := rfl

theorem wordNoStubCall_tight {α : Type} :
    WordNoStubCall (WordLangProgHOL.call (α := α) none (some storeConstsStubLocation) [] none)
      = false ∧
    WordNoStubCall (WordLangProgHOL.call (α := α) none (some 64) [] none) = true := by
  refine ⟨?_, ?_⟩ <;> simp [WordNoStubCall, storeConstsStubLocation, wordNumStubs, stackNumStubs]


end InitECandidate.Solver.PanToWordNoStubCall
