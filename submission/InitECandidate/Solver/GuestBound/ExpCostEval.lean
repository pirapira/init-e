import InitECandidate.Solver.GuestBound.CostLogic

/-!
# A kernel-reducible expression cost

`Flapjack.panValueExpStepCost` is defined by well-founded recursion and does
not reduce in the kernel. `expCost` is the same function by structural
recursion, so closed cost bounds can be checked by `decide`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

mutual
  def expCost : Exp Word → Nat
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => 1
    | .rStruct fields => expsCost fields + 1
    | .rField _ expression | .nField _ expression | .load32 expression
    | .loadByte expression => expCost expression + 1
    | .nStruct _ fields => fieldsCost fields + 1
    | .load _ address => expCost address + 1
    | .op _ arguments | .panOp _ arguments => expsCost arguments + 1
    | .cmp _ left right | .shift _ left right => expCost left + expCost right + 1
  termination_by structural e => e

  def expsCost : List (Exp Word) → Nat
    | [] => 0
    | expression :: expressions => expCost expression + expsCost expressions
  termination_by structural es => es

  def fieldsCost : List (FieldName × Exp Word) → Nat
    | [] => 0
    | (_, expression) :: fields => expCost expression + fieldsCost fields
  termination_by structural fs => fs
end

mutual
  theorem stepCost_eq : ∀ e : Exp Word, panValueExpStepCost e = expCost e
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => by
        simp [panValueExpStepCost, expCost]
    | .rStruct fields => by
        simp only [panValueExpStepCost, expCost]
        rw [stepsCost_eq' fields]
    | .rField _ expression | .nField _ expression | .load32 expression
    | .loadByte expression => by
        simp only [panValueExpStepCost, expCost]
        rw [stepCost_eq expression]
    | .nStruct _ fields => by
        simp only [panValueExpStepCost, expCost]
        rw [fieldsCost_eq' fields]
    | .load _ address => by
        simp only [panValueExpStepCost, expCost]
        rw [stepCost_eq address]
    | .op _ arguments | .panOp _ arguments => by
        simp only [panValueExpStepCost, expCost]
        rw [stepsCost_eq' arguments]
    | .cmp _ left right | .shift _ left right => by
        simp only [panValueExpStepCost, expCost]
        rw [stepCost_eq left, stepCost_eq right]

  theorem stepsCost_eq' : ∀ es : List (Exp Word),
      panValueExpStepCost.panValueExpsStepCost es = expsCost es
    | [] => by simp [panValueExpStepCost.panValueExpsStepCost, expsCost]
    | e :: es => by
        simp only [panValueExpStepCost.panValueExpsStepCost, expsCost]
        rw [stepCost_eq e, stepsCost_eq' es]

  theorem fieldsCost_eq' : ∀ fs : List (FieldName × Exp Word),
      panValueExpStepCost.panValueFieldsStepCost fs = fieldsCost fs
    | [] => by simp [panValueExpStepCost.panValueFieldsStepCost, fieldsCost]
    | (_, e) :: fs => by
        simp only [panValueExpStepCost.panValueFieldsStepCost, fieldsCost]
        rw [stepCost_eq e, fieldsCost_eq' fs]
end

theorem stepsCost_eq (es : List (Exp Word)) : panValueExpsStepCost es = expsCost es :=
  stepsCost_eq' es

end InitECandidate.Solver.GuestBound
