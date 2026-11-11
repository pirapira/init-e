import InitECandidate.Solver.GuestBound.CostLogic

/-!
# Syntactic cost of expressions and leaf statements

The counted expression evaluator returns exactly `panValueExpStepCost e` steps
whenever it returns, so condition and leaf-statement costs are syntactic and
hold in every state, for every memory model and FFI oracle.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A condition costs its syntactic step cost, in every state. -/
theorem condCost (P : St σ → Prop) (c : Exp Word) :
    CondCost E P c (panValueExpStepCost c) := by
  intro s v k _ h
  simp only [Env.cond, panValueIteCondition, evalPanValueExpCounted] at h
  cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord c E.memoryAccess with
  | none => rw [hv] at h; simp at h
  | some value =>
    rw [hv] at h
    cases value <;> simp at h
    exact Nat.le_of_eq h.2.symm

/-- A local assignment costs at most the expression cost plus one. -/
theorem Costs.assignLocal (name : VarName) (value : Exp Word) :
    Costs E (.assign .local name value) (panValueExpStepCost value + 1) := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    simp only [panValueAssignLocalResult, evalPanValueExpCounted] at hrun
    refine ⟨?_, trivial⟩
    cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord value E.memoryAccess with
    | none =>
      rw [hv] at hrun
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some evaluated =>
      rw [hv] at hrun
      simp only [Option.map_some] at hrun
      split at hrun <;>
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun <;> omega

end InitECandidate.Solver.GuestBound
