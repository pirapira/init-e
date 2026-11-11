import InitECandidate.Solver.GuestBound.CallInv
import InitECandidate.Solver.GuestBound.GuestEnv

/-!
# Functions that never return

A body that is a sequence of shared-memory stores and host calls ending in
`raise` never finishes normally and never returns (`trap_with`). A call to
such a function therefore never continues the caller.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The result ends the function or loop from inside: returned, broke or continued. -/
def _root_.Flapjack.PanValueFfiControlResult.leaves {σ : Type} : Result σ → Bool
  | .returned _ _ _ _ _ | .broke _ _ _ _ | .continued _ _ _ _ => true
  | _ => false

/-- The result is `.normal`. -/
def _root_.Flapjack.PanValueFfiControlResult.isNormal {σ : Type} : Result σ → Bool
  | .normal _ _ _ _ => true
  | _ => false

theorem shMemStore_leaves {fuel : Nat} {s : St σ} {size : OpSize} {a v : Exp Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.shMemStore size a v) = some (r, n)) :
    r.leaves = false := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueShMemStoreResult] at h
    repeat' split at h
    all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at h))
    all_goals (obtain ⟨rfl, -⟩ := h)
    all_goals rfl

theorem extCall_leaves {fuel : Nat} {s : St σ} {f : FunName} {a b c d : Exp Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.extCall f a b c d) = some (r, n)) :
    r.leaves = false := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueFfiExtCallSteps] at h
    repeat' split at h
    all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq, Option.pure_def,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at h))
    all_goals first
      | (obtain ⟨rfl, -⟩ := h; rfl)
      | (obtain ⟨_, _, rfl, -⟩ := h; rfl)

theorem raise_stops {fuel : Nat} {s : St σ} {exception : ExceptionId} {v : Exp Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.raise exception v) = some (r, n)) :
    r.leaves = false ∧ r.isNormal = false := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueRaiseResult] at h
    repeat' split at h
    all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at h))
    all_goals (obtain ⟨rfl, -⟩ := h)
    all_goals exact ⟨rfl, rfl⟩

/-- A sequence of shared-memory stores and host calls ending in `raise`. -/
def endsRaise : Prog Word → Bool
  | .raise _ _ => true
  | .seq (.shMemStore _ _ _) rest => endsRaise rest
  | .seq (.extCall _ _ _ _ _) rest => endsRaise rest
  | _ => false

/-- Such a body never finishes normally, returns, breaks or continues. -/
theorem endsRaise_sound : ∀ (p : Prog Word), endsRaise p = true →
    ∀ (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat), E.run fuel s p = some (r, n) →
      r.leaves = false ∧ r.isNormal = false
  | .raise _ _, _, _, _, _, _, h => raise_stops h
  | .seq (.shMemStore _ _ _) rest, hp, fuel, s, r, n, h => by
      simp only [endsRaise] at hp
      obtain ⟨fuel', r₁, n₁, h₁, h₂⟩ := seq_run_inv h
      have hl := shMemStore_leaves h₁
      cases r₁ with
      | normal l g m f =>
        obtain ⟨n₂, h₂⟩ := h₂
        exact endsRaise_sound rest hp fuel' _ r n₂ h₂
      | _ =>
        simp only at h₂
        subst h₂
        first | exact ⟨rfl, rfl⟩ | cases hl
  | .seq (.extCall _ _ _ _ _) rest, hp, fuel, s, r, n, h => by
      simp only [endsRaise] at hp
      obtain ⟨fuel', r₁, n₁, h₁, h₂⟩ := seq_run_inv h
      have hl := extCall_leaves h₁
      cases r₁ with
      | normal l g m f =>
        obtain ⟨n₂, h₂⟩ := h₂
        exact endsRaise_sound rest hp fuel' _ r n₂ h₂
      | _ =>
        simp only at h₂
        subst h₂
        first | exact ⟨rfl, rfl⟩ | cases hl
  | .skip, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .dec _ _ _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .assign _ _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .primitive _ _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .store _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .store32 _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .storeByte _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .ite _ _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .while _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .break, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .continue, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .call _ _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .decCall _ _ _ _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .extCall _ _ _ _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .return _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .shMemLoad _ _ _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .shMemStore _ _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .tick, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .annot _ _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.skip) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.dec _ _ _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.assign _ _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.primitive _ _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.store _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.store32 _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.storeByte _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.seq _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.ite _ _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.while _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.break) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.continue) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.call _ _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.decCall _ _ _ _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.raise _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.return _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.shMemLoad _ _ _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.tick) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp
  | .seq (.annot _ _) _, hp, _, _, _, _, _ => by simp [endsRaise] at hp

/-- No run of a body registered for `f` returns. -/
def FunNoReturn (E : Env σ) (f : FunName) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    ∀ fuel s r n, E.run fuel s body = some (r, n) → r.leaves = false ∧ r.isNormal = false

/-- `trap_with` never returns. -/
theorem trap_with_noReturn (hE : GuestEnv E) : FunNoReturn E "trap_with" := by
  intro parameters body hlookup fuel s r n hrun
  have hbody := (fun_of_index 3 hE.functions (by guest_decl_at 3) (by decide +kernel)
    hlookup).1
  subst hbody
  exact endsRaise_sound _ (by decide) fuel s r n hrun

/-- A call without a handler to a function that never returns does not finish
normally, break or continue. -/
theorem call_noReturn {f : FunName} (hf : FunNoReturn E f)
    (destination : Option (Option (VarKind × VarName))) {fuel : Nat} {s : St σ}
    {arguments : List (Exp Word)} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.call (destination.map fun dest => (dest, none)) f arguments) =
      some (r, n)) :
    r.leaves = false ∧ r.isNormal = false := by
  rcases call_run_inv destination h with herr | ⟨fuel', parameters, body, values, calleeLocals,
    rb, nb, hlookup, -, -, hbody, hout⟩
  · cases r <;> simp only [PanValueFfiControlResult.isError] at herr <;>
      first | exact ⟨rfl, rfl⟩ | cases herr
  · obtain ⟨hleaves, hnormal⟩ := hf parameters body hlookup fuel' _ rb nb hbody
    cases rb with
    | returned l g m f' vs => cases hleaves
    | normal l g m f' => cases hnormal
    | broke l g m f' => cases hleaves
    | continued l g m f' => cases hleaves
    | raised l g m f' ex v =>
      simp only [CallOutcome] at hout
      subst hout
      exact ⟨rfl, rfl⟩
    | finalFfi l g m f' ev =>
      simp only [CallOutcome] at hout
      subst hout
      exact ⟨rfl, rfl⟩
    | error l g m f' =>
      simp only [CallOutcome] at hout
      cases r <;> simp only [PanValueFfiControlResult.isError] at hout <;>
        first | exact ⟨rfl, rfl⟩ | cases hout

end InitECandidate.Solver.GuestBound
