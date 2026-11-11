import InitECandidate.Solver.GuestBound.NoReturn

/-!
# Guest rules for loops over struct-valued locals

The calls allowed in `shapeOk` statements of the guest: read-only functions,
and `trap_with`, which never returns.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Callees allowed in shape-keeping statements. -/
def shapeCallee (f : FunName) : Bool := quietFn Guest.Software.guestAst f || f == "trap_with"

theorem FunNoReturn.stops {f : FunName} (h : FunNoReturn E f) : FunStops E f := by
  intro parameters body hlookup fuel s r n hrun l g m ffi values hr
  have := (h parameters body hlookup fuel s r n hrun).1
  rw [hr] at this
  cases this

theorem shapeCallee_sound (hE : GuestEnv E) (f : FunName) (h : shapeCallee f = true) :
    FunKeeps (quietKeeper E) f ∨ FunStops E f := by
  simp only [shapeCallee, Bool.or_eq_true] at h
  rcases h with h | h
  · exact Or.inl (keepFn_sound (quietKeeper E) hE.functions calmDepth f h)
  · have : f = "trap_with" := by simpa using h
    subst this
    exact Or.inr (trap_with_noReturn hE).stops

namespace X

theorem inSeq (σ : Type) (E : Env σ) (hE : GuestEnv E) (D : List (VarName × Shape))
    (first second : Prog Word) (B₁ B₂ : Nat)
    (hcheck : shapeOk shapeCallee (loopVars first) first = true)
    (h₁ : CostsIn E D first B₁) (h₂ : CostsIn E D second B₂) :
    CostsIn E D (.seq first second) (B₁ + B₂ + 1) :=
  CostsIn.seq _ (shapeCallee_sound hE) _ hcheck h₁ h₂

theorem whileShape (σ : Type) (E : Env σ) (hE : GuestEnv E) (D : List (VarName × Shape))
    (c : Exp Word) (body : Prog Word) (b : Nat)
    (hcheck : shapeLoop shapeCallee D body = true) (hbody : CostsIn E D body b) :
    CostsIn E D (.while c body)
      (shapeIters (flatMax D (loopVars body)) (loopVars body).length * (expCost c + b + 1)) :=
  shapeLoop_costs _ (shapeCallee_sound hE) D c body b hcheck hbody

end X
end InitECandidate.Solver.GuestBound
