import InitECandidate.Solver.GuestBound.Call

/-!
# Unconditional costs of leaf statements and of `dec`

Each leaf costs the syntactic cost of its expressions plus one, in every state.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

set_option hygiene false in
/-- Prove the cost of a one-expression leaf whose evaluator helper is `helper`. -/
local macro "leaf_one" helper:ident value:ident : tactic => `(tactic| (
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    simp only [$helper:ident, evalPanValueExpCounted] at hrun
    cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord $value E.memoryAccess with
    | none =>
      rw [hv] at hrun
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some evaluated =>
      rw [hv] at hrun
      simp only [Option.map_some] at hrun
      split at hrun <;>
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun <;> omega))

set_option hygiene false in
/-- Prove the cost of a two-expression (address, value) leaf. -/
local macro "leaf_two" helper:ident address:ident value:ident : tactic => `(tactic| (
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    simp only [$helper:ident, evalPanValueExpCounted] at hrun
    cases ha : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord $address E.memoryAccess with
    | none =>
      rw [ha] at hrun
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some evaluatedAddress =>
      rw [ha] at hrun
      simp only [Option.map_some] at hrun
      cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
          E.bytesInWord $value E.memoryAccess with
      | none =>
        rw [hv] at hrun
        simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      | some evaluated =>
        rw [hv] at hrun
        simp only [Option.map_some] at hrun
        repeat' split at hrun
        all_goals (simp only [Option.some.injEq, Prod.mk.injEq] at hrun; omega)))

theorem Costs.assignGlobal (name : VarName) (value : Exp Word) :
    Costs E (.assign .global name value) (panValueExpStepCost value + 1) := by
  leaf_one panValueAssignGlobalResult value

theorem Costs.return (value : Exp Word) :
    Costs E (.return value) (panValueExpStepCost value + 1) := by
  leaf_one panValueReturnResult value

theorem Costs.raise (exception : ExceptionId) (value : Exp Word) :
    Costs E (.raise exception value) (panValueExpStepCost value + 1) := by
  leaf_one panValueRaiseResult value

theorem Costs.store (address value : Exp Word) :
    Costs E (.store address value)
      (panValueExpStepCost address + panValueExpStepCost value + 1) := by
  leaf_two panValueStoreResult address value

theorem Costs.store32 (address value : Exp Word) :
    Costs E (.store32 address value)
      (panValueExpStepCost address + panValueExpStepCost value + 1) := by
  leaf_two panValueStore32Result address value

theorem Costs.storeByte (address value : Exp Word) :
    Costs E (.storeByte address value)
      (panValueExpStepCost address + panValueExpStepCost value + 1) := by
  leaf_two panValueStoreByteResult address value

/-- One-step leaves. -/
theorem Costs.skip : Costs E .skip 1 :=
  (Triple.skip (P := fun _ => True)).consequence (fun _ h => h) (Nat.le_refl _) (fun _ _ => trivial)

theorem Costs.break : Costs E .break 1 := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run, evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at hrun
    exact ⟨by omega, trivial⟩

theorem Costs.continue : Costs E .continue 1 := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run, evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
      Prod.mk.injEq] at hrun
    exact ⟨by omega, trivial⟩

/-- Unconditional sequencing and branching. -/
theorem Costs.seq {first second : Prog Word} {B₁ B₂ : Nat}
    (h₁ : Costs E first B₁) (h₂ : Costs E second B₂) :
    Costs E (.seq first second) (B₁ + B₂ + 1) :=
  Triple.seq (Mid := fun _ => True) (Q := fun _ => True)
    (h₁.consequence (fun _ h => h) (Nat.le_refl _) (fun r _ => by cases r <;> trivial)) h₂

theorem Costs.ite (c : Exp Word) {thenBranch elseBranch : Prog Word} {B₁ B₂ : Nat}
    (h₁ : Costs E thenBranch B₁) (h₂ : Costs E elseBranch B₂) :
    Costs E (.ite c thenBranch elseBranch) (panValueExpStepCost c + max B₁ B₂ + 1) :=
  Triple.ite (condCost _ c) h₁ h₂

/-- A declaration costs its initialiser, its body and one step. -/
theorem Costs.dec (name : VarName) (shape : Shape) (value : Exp Word) {body : Prog Word}
    {B : Nat} (h : Costs E body B) :
    Costs E (.dec name shape value body) (panValueExpStepCost value + B + 1) := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory value E.memoryAccess shape with
    | none =>
      rw [hacc] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some accepted =>
      rw [hacc] at hrun
      simp only [Option.elim_some] at hrun
      have hsteps : accepted.2 = panValueExpStepCost value := by
        simp only [panValueDecAccepted, evalPanValueExpCounted] at hacc
        cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
            E.topAddress E.bytesInWord value E.memoryAccess with
        | none => rw [hv] at hacc; simp at hacc
        | some evaluated =>
          rw [hv] at hacc
          simp only [Option.map_some] at hacc
          split at hacc
          · simp only [Option.some.injEq] at hacc
            rw [← hacc]
          · simp at hacc
      cases hbody : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel
          (updatePanValueMap s.locals name accepted.1) s.globals s.memory s.ffi body
          (memoryAccess := E.memoryAccess) (contracts := E.contracts)
          (memoryHandler := E.memoryHandler) with
      | none => rw [hbody] at hrun; simp at hrun
      | some bodyPair =>
        obtain ⟨rb, nb⟩ := bodyPair
        rw [hbody] at hrun
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        have hnb : nb ≤ B :=
          (h fuel ⟨updatePanValueMap s.locals name accepted.1, s.globals, s.memory, s.ffi⟩
            rb nb trivial hbody (by cases rb <;> first | rfl | cases hne)).1
        omega

end InitECandidate.Solver.GuestBound
