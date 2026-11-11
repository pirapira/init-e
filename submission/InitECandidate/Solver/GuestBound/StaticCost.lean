import InitECandidate.Solver.GuestBound.FfiLeaves

/-!
# Syntactic cost of a program

`staticCost F W p` bounds the steps of `p` given a cost `F f` for every
function it calls and a cost `W c body` for every loop it contains.
`staticCost_sound` reduces the bound to exactly those facts (`CostFacts`), so
loop-free code and call composition need no further proof.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- Syntactic step bound, relative to callee costs `F` and loop costs `W`. -/
def staticCost (F : FunName → Nat) (W : Exp Word → Prog Word → Nat) : Prog Word → Nat
  | .skip | .break | .continue | .tick | .annot _ _ => 1
  | .dec _ _ value body => panValueExpStepCost value + staticCost F W body + 1
  | .assign _ _ value => panValueExpStepCost value + 1
  | .primitive _ _ arguments => panValueExpsStepCost arguments + 1
  | .store address value | .store32 address value | .storeByte address value =>
      panValueExpStepCost address + panValueExpStepCost value + 1
  | .seq first second => staticCost F W first + staticCost F W second + 1
  | .ite condition thenBranch elseBranch =>
      panValueExpStepCost condition +
        max (staticCost F W thenBranch) (staticCost F W elseBranch) + 1
  | .while condition body => W condition body
  | .call (some (_, some (_, _, handlerProgram))) function arguments =>
      panValueExpsStepCost arguments + F function + staticCost F W handlerProgram + 1
  | .call _ function arguments => panValueExpsStepCost arguments + F function + 0 + 1
  | .decCall _ _ function arguments body =>
      panValueExpsStepCost arguments + F function + staticCost F W body + 1
  | .extCall _ configuration configurationLength array arrayLength =>
      panValueExpsStepCost [configuration, configurationLength, array, arrayLength] + 1
  | .raise _ value | .return value => panValueExpStepCost value + 1
  | .shMemLoad _ _ _ address => panValueExpStepCost address + 1
  | .shMemStore _ address value =>
      panValueExpStepCost address + panValueExpStepCost value + 1

/-- The semantic facts `staticCost` relies on: a cost for each callee and for
each loop (a loop's body is covered by the loop's own fact). -/
def CostFacts {σ : Type} (E : Env σ) (F : FunName → Nat) (W : Exp Word → Prog Word → Nat) :
    Prog Word → Prop
  | .dec _ _ _ body => CostFacts E F W body
  | .seq first second => CostFacts E F W first ∧ CostFacts E F W second
  | .ite _ thenBranch elseBranch => CostFacts E F W thenBranch ∧ CostFacts E F W elseBranch
  | .while condition body => Costs E (.while condition body) (W condition body)
  | .call (some (_, some (_, _, handlerProgram))) function _ =>
      FunCost E function (F function) ∧ CostFacts E F W handlerProgram
  | .call _ function _ => FunCost E function (F function)
  | .decCall _ _ function _ body => FunCost E function (F function) ∧ CostFacts E F W body
  | _ => True

variable {σ : Type} {E : Env σ} {F : FunName → Nat} {W : Exp Word → Prog Word → Nat}

/-- `staticCost` is a step bound whenever its callee and loop facts hold. -/
theorem staticCost_sound : ∀ (p : Prog Word), CostFacts E F W p → Costs E p (staticCost F W p)
  | .skip, _ => Costs.skip
  | .break, _ => Costs.break
  | .continue, _ => Costs.continue
  | .tick, _ => Costs.tick
  | .annot key value, _ => Costs.annot key value
  | .dec name shape value body, h => by
      simp only [CostFacts] at h
      simpa only [staticCost] using Costs.dec name shape value (staticCost_sound body h)
  | .assign .local name value, _ => Costs.assignLocal name value
  | .assign .global name value, _ => Costs.assignGlobal name value
  | .primitive name operator arguments, _ => Costs.primitive name operator arguments
  | .store address value, _ => Costs.store address value
  | .store32 address value, _ => Costs.store32 address value
  | .storeByte address value, _ => Costs.storeByte address value
  | .seq first second, h => by
      simp only [CostFacts] at h
      simpa only [staticCost] using
        Costs.seq (staticCost_sound first h.1) (staticCost_sound second h.2)
  | .ite condition thenBranch elseBranch, h => by
      simp only [CostFacts] at h
      simpa only [staticCost] using
        Costs.ite condition (staticCost_sound thenBranch h.1) (staticCost_sound elseBranch h.2)
  | .while condition body, h => by
      simp only [CostFacts] at h
      simpa only [staticCost] using h
  | .call (some (destination, some (exception, handlerVar, handlerProgram))) function arguments,
      h => by
      simp only [CostFacts] at h
      simpa only [staticCost] using
        Costs.call (info := some (destination, some (exception, handlerVar, handlerProgram)))
          arguments h.1 (staticCost_sound handlerProgram h.2)
  | .call (some (destination, none)) function arguments, h => by
      simp only [CostFacts] at h
      simpa only [staticCost] using
        Costs.call (info := some (destination, none)) (H := 0) arguments h trivial
  | .call none function arguments, h => by
      simp only [CostFacts] at h
      simpa only [staticCost] using Costs.call (info := none) (H := 0) arguments h trivial
  | .decCall name shape function arguments body, h => by
      simp only [CostFacts] at h
      simpa only [staticCost] using
        Costs.decCall name shape arguments h.1 (staticCost_sound body h.2)
  | .extCall function configuration configurationLength array arrayLength, _ =>
      Costs.extCall function configuration configurationLength array arrayLength
  | .raise exception value, _ => Costs.raise exception value
  | .return value, _ => Costs.return value
  | .shMemLoad size kind name address, _ => Costs.shMemLoad size kind name address
  | .shMemStore size address value, _ => Costs.shMemStore size address value

end InitECandidate.Solver.GuestBound
