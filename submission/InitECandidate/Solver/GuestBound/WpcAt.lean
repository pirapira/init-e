import InitECandidate.Solver.GuestBound.Wpc
import InitECandidate.Solver.GuestBound.CallAt

/-!
# `WPc` rules for conditionals and for calls bounded at the call state

`WPc.ite_both` only asks for the branch that is taken; `WPc.call_at` uses a
`FunCostAt` bound. Together with the rules in `Wpc.lean` they let a caller use
a callee bound that holds under a precondition.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Conditional from one state: only the branch selected by the condition is needed. -/
theorem Triple.ite_at {c : Exp Word} {p q : Prog Word} {B₁ B₂ : Nat}
    (h₁ : ∀ v k, E.cond s c = some (v, k) → (v != 0) = true →
      Triple E (fun a => a = s) p B₁ Q)
    (h₂ : ∀ v k, E.cond s c = some (v, k) → ¬ (v != 0) = true →
      Triple E (fun a => a = s) q B₂ Q) :
    Triple E (fun a => a = s) (.ite c p q) (expCost c + max B₁ B₂ + 1) Q := by
  unfold Triple
  intro fuel a r n ha hrun hne
  rw [ha] at hrun
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory c E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      cases hne
    | some pair =>
      obtain ⟨v, k⟩ := pair
      rw [hcond] at hrun
      have hk : k ≤ expCost c := (condCost_exp (I := fun _ => True) c) s v k trivial hcond
      simp only [Option.elim_some] at hrun
      by_cases hv : (v != 0) = true
      · rw [if_pos hv] at hrun
        cases hbranch : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi p (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hbranch] at hrun; simp at hrun
        | some branchPair =>
          obtain ⟨r₁, n₁⟩ := branchPair
          rw [hbranch] at hrun
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨hn₁, hQ⟩ := h₁ v k hcond hv fuel s r₁ n₁ rfl hbranch hne
          exact ⟨by omega, hQ⟩
      · rw [if_neg hv] at hrun
        cases hbranch : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi q (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hbranch] at hrun; simp at hrun
        | some branchPair =>
          obtain ⟨r₂, n₂⟩ := branchPair
          rw [hbranch] at hrun
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨hn₂, hQ⟩ := h₂ v k hcond hv fuel s r₂ n₂ rfl hbranch hne
          exact ⟨by omega, hQ⟩

/-- Conditional: the branch taken is the only one that has to be bounded. -/
theorem WPc.ite_both {c : Exp Word} {p q : Prog Word} {B₁ B₂ : Nat}
    (h : ∀ w, E.eval s c = some (.word w) →
      if w = 0 then WPc E s q B₂ Q else WPc E s p B₁ Q) :
    WPc E s (.ite c p q) (expCost c + max B₁ B₂ + 1) Q := by
  refine ⟨Triple.ite_at ?_ ?_, WPs.ite_both (fun w hw => ?_)⟩
  · intro v k hc hv
    have := h v (cond_of_eval hc)
    rw [if_neg (by simpa using hv)] at this
    exact this.1
  · intro v k hc hv
    have := h v (cond_of_eval hc)
    rw [if_pos (by simpa using hv)] at this
    exact this.1
  · have := h w hw
    split
    · rename_i hw0
      rw [if_pos hw0] at this
      exact this.2
    · rename_i hw0
      rw [if_neg hw0] at this
      exact this.2

/-- A call statement whose callee is bounded for this call. -/
theorem WPc.call_at {f : FunName} {args : List (Exp Word)} {B : Nat}
    {d : Option (VarKind × VarName)} (hf : FunCostAt E f B s args)
    (h : WPs E s (.call (some (d, none)) f args) Q) :
    WPc E s (.call (some (d, none)) f args) (panValueExpsStepCost args + B + 0 + 1) Q :=
  ⟨call_cost_at (H := 0) args hf trivial, h⟩

end InitECandidate.Solver.GuestBound
