import InitECandidate.Solver.GuestBound.DecCall

/-!
# Unconditional costs of the remaining leaves

Primitive operations, shared-memory accesses, external calls, `tick` and
annotations. The bounds do not depend on the FFI oracle or handler.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem Costs.tick : Costs E .tick 1 := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run, evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at hrun
    exact ⟨by omega, trivial⟩

theorem Costs.annot (key value : String) : Costs E (.annot key value) 1 := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run, evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at hrun
    exact ⟨by omega, trivial⟩

theorem Costs.primitive (name : VarName) (operator : PrimOp) (arguments : List (Exp Word)) :
    Costs E (.primitive name operator arguments) (panValueExpsStepCost arguments + 1) := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    simp only [panValuePrimitiveResult, evalPanValueExpsCounted] at hrun
    cases hv : evalPanValueExps E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord arguments E.memoryAccess with
    | none =>
      rw [hv] at hrun
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some values =>
      rw [hv] at hrun
      simp only [Option.map_some] at hrun
      repeat' split at hrun
      all_goals (simp only [Option.some.injEq, Prod.mk.injEq] at hrun; omega)

theorem Costs.shMemLoad (size : OpSize) (kind : VarKind) (name : VarName) (address : Exp Word) :
    Costs E (.shMemLoad size kind name address) (panValueExpStepCost address + 1) := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    simp only [panValueShMemLoadResult, evalPanValueExpCounted] at hrun
    cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord address E.memoryAccess with
    | none =>
      rw [hv] at hrun
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some evaluated =>
      rw [hv] at hrun
      simp only [Option.map_some] at hrun
      repeat' split at hrun
      all_goals (simp only [Option.some.injEq, Prod.mk.injEq] at hrun; omega)

theorem Costs.shMemStore (size : OpSize) (address value : Exp Word) :
    Costs E (.shMemStore size address value)
      (panValueExpStepCost address + panValueExpStepCost value + 1) := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    simp only [panValueShMemStoreResult, evalPanValueExpCounted] at hrun
    cases ha : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord address E.memoryAccess with
    | none =>
      rw [ha] at hrun
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some evaluatedAddress =>
      rw [ha] at hrun
      simp only [Option.map_some] at hrun
      cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
          E.topAddress E.bytesInWord value E.memoryAccess with
      | none =>
        rw [hv] at hrun
        simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      | some evaluated =>
        rw [hv] at hrun
        simp only [Option.map_some] at hrun
        repeat' split at hrun
        all_goals (simp only [Option.some.injEq, Prod.mk.injEq] at hrun; omega)

theorem Costs.extCall (function : FunName)
    (configuration configurationLength array arrayLength : Exp Word) :
    Costs E (.extCall function configuration configurationLength array arrayLength)
      (panValueExpsStepCost [configuration, configurationLength, array, arrayLength] + 1) := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    simp only [panValueFfiExtCallSteps, evalPanValueExpsCounted] at hrun
    cases hv : evalPanValueExps E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord [configuration, configurationLength, array, arrayLength]
        E.memoryAccess with
    | none =>
      rw [hv] at hrun
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some values =>
      rw [hv] at hrun
      simp only [Option.map_some, Option.bind_eq_bind, Option.pure_def] at hrun
      repeat' split at hrun
      all_goals first
        | (simp only [Option.some.injEq, Prod.mk.injEq] at hrun; omega)
        | (simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at hrun
           obtain ⟨_, _, _, h⟩ := hrun
           omega)

end InitECandidate.Solver.GuestBound
