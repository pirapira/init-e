import InitECandidate.Solver.GuestBound.CounterLoop
import InitECandidate.Solver.GuestBound.SymEval

/-!
# Counter loops with a conjunctive guard

`while (i < e) && other { … i = i + 1 … }`: the loop runs only while the first
conjunct holds, so the counter argument applies to it.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The first conjunct of a guard `a && b`. -/
def andGuard : Exp Word → Option (Exp Word)
  | .op .and [.cmp .notEqual (.const k) first, _] => if k == 0 then some first else none
  | _ => none

/-- A counter loop on the first conjunct of its guard. -/
def andCounterLoop (c : Exp Word) (body : Prog Word) : Bool :=
  match andGuard c with
  | some first =>
      match guardKind first with
      | some (kind, i) => stepsBack (effect kind.mode i body)
      | none => false
  | none => false

/-- If `a && b` holds then `a` holds. -/
theorem and_first (hE : WordEnv E) {c first : Exp Word} (hc : andGuard c = some first)
    {s : St σ} (h : CondTrue E s c) : CondTrue E s first := by
  unfold andGuard at hc
  split at hc
  · rename_i k first' second
    split at hc
    · rename_i hk
      simp only [Option.some.injEq] at hc
      subst hc
      have hk0 : k = 0 := by simpa using hk
      subst hk0
      obtain ⟨v, n, hcond, hv⟩ := h
      obtain ⟨va, vb, w, ha, -, hop, hw⟩ := eval_op2_inv hE (cond_of_eval hcond)
      simp only [PanValue.word.injEq] at hw
      subst hw
      obtain ⟨z, x, hz, hx, hcmp⟩ := cmp_eval hE ha
      simp only [PanValue.word.injEq] at hcmp
      change E.eval s (.const 0) = some (.word z) at hz
      change E.eval s first' = some (.word x) at hx
      simp only [eval_const, Option.some.injEq, PanValue.word.injEq] at hz
      subst hz
      simp only [wordOp, Option.some.injEq, List.foldr] at hop
      subst hop
      have hxne : x ≠ 0 := by
        intro hx0
        subst hx0
        subst hcmp
        simp [evalPanCmp] at hv
        exact hv (by show (0#64 &&& _) = 0#64; exact BitVec.zero_and)
      refine ⟨x, panValueExpStepCost first', ?_, by simpa using hxne⟩
      simp only [Env.cond, panValueIteCondition, evalPanValueExpCounted]
      rw [show evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord first' E.memoryAccess = some (.word x) from hx]
      rfl
    · cases hc
  · cases hc

theorem andCounterLoop_costs (hE : WordEnv E) (c : Exp Word) (body : Prog Word) (b : Nat)
    (hcheck : andCounterLoop c body = true) (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  unfold andCounterLoop at hcheck
  split at hcheck
  · rename_i first hfirst
    split at hcheck
    · rename_i kind i hk
      exact variant_loop_costs hE c body b kind.mode i (measure kind) (measure_lt kind)
        (fun s hc => guard_step hE hk (and_first hE hfirst hc)) hcheck hbody
    · cases hcheck
  · cases hcheck

end InitECandidate.Solver.GuestBound
