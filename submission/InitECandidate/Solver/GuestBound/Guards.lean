import InitECandidate.Solver.GuestBound.ScratchAlloc

/-!
# Inversion of guard statements

`if c { fail(...); } rest` and `if c { A } rest`, the shapes that validation
code is made of.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The result neither continues the caller nor returns from it. -/
def Stops (r : Result σ) : Prop := r.leaves = false ∧ r.isNormal = false

theorem Stops.of_error {r : Result σ} (h : r.isError = true) : Stops r := by
  cases r <;> first | exact ⟨rfl, rfl⟩ | cases h

/-- `raise …; rest` stops. -/
theorem seq_raise_stops {fuel : Nat} {s : St σ} {exception : ExceptionId} {v : Exp Word}
    {rest : Prog Word} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.seq (.raise exception v) rest) = some (r, n)) : Stops r := by
  obtain ⟨fuel', r₁, n₁, h₁, h₂⟩ := seq_run_inv h
  obtain ⟨hl, hn⟩ := raise_stops h₁
  cases r₁ with
  | normal l g m f => cases hn
  | _ =>
    simp only at h₂
    subst h₂
    exact ⟨hl, hn⟩

/-- `rlp_fail` never returns. -/
theorem rlp_fail_noReturn (hE : GuestEnv E) : FunNoReturn E "rlp_fail" := by
  intro parameters body hlookup fuel s r n hrun
  have hbody := (fun_of_index 105 hE.functions (by guest_decl_at 105) (by decide +kernel)
    hlookup).1
  subst hbody
  exact seq_raise_stops hrun

/-- `if c { f(...); } rest` with `f` never returning: the run stops, or the
guard was false and `rest` ran from the same state. -/
theorem guard_fail_inv {f : FunName} (hf : FunNoReturn E f) {fuel : Nat} {s : St σ}
    {c : Exp Word} {arguments : List (Exp Word)} {rest : Prog Word} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.seq (.ite c (.call (some (none, none)) f arguments) .skip) rest) =
      some (r, n)) :
    Stops r ∨ (E.eval s c = some (.word 0) ∧ ∃ fuel' n', E.run fuel' s rest = some (r, n')) := by
  obtain ⟨fuel₁, r₁, n₁, h₁, h₂⟩ := seq_run_inv h
  rcases ite_run_inv h₁ with herr | ⟨fuel₂, v, n', hc, hbranch⟩
  · cases r₁ with
    | error l g m ffi =>
      simp only at h₂
      subst h₂
      exact Or.inl ⟨rfl, rfl⟩
    | _ => cases herr
  · rcases hbranch with ⟨-, hcall⟩ | ⟨hz, hskip⟩
    · obtain ⟨hl, hn⟩ := call_noReturn hf (some none) hcall
      cases r₁ with
      | normal l g m ffi => cases hn
      | _ =>
        simp only at h₂
        subst h₂
        exact Or.inl ⟨hl, hn⟩
    · have hs := skip_inv hskip
      subst hs
      simp only at h₂
      obtain ⟨n₂, h₂⟩ := h₂
      subst hz
      exact Or.inr ⟨hc, fuel₁, n₂, h₂⟩

/-- After `A` ended in `rA`: `rest` ran if `rA` is normal, otherwise `rA` is the result. -/
def Continues (E : Env σ) (rA r : Result σ) (rest : Prog Word) : Prop :=
  match rA with
  | .normal l g m f => ∃ fuel n, E.run fuel ⟨l, g, m, f⟩ rest = some (r, n)
  | _ => r = rA

/-- `if c { A } rest`: an error; or the guard was true, `A` ran, and `rest`
followed if `A` finished normally; or the guard was false and `rest` ran. -/
theorem ite_then_inv {fuel : Nat} {s : St σ} {c : Exp Word} {thenBranch rest : Prog Word}
    {r : Result σ} {n : Nat}
    (h : E.run fuel s (.seq (.ite c thenBranch .skip) rest) = some (r, n)) :
    r.isError = true ∨
      (∃ v fuel' rA nA, E.eval s c = some (.word v) ∧ v ≠ 0 ∧
        E.run fuel' s thenBranch = some (rA, nA) ∧ Continues E rA r rest) ∨
      (E.eval s c = some (.word 0) ∧ ∃ fuel' n', E.run fuel' s rest = some (r, n')) := by
  obtain ⟨fuel₁, r₁, n₁, h₁, h₂⟩ := seq_run_inv h
  rcases ite_run_inv h₁ with herr | ⟨fuel₂, v, n', hc, hbranch⟩
  · cases r₁ with
    | error l g m ffi =>
      simp only at h₂
      subst h₂
      exact Or.inl rfl
    | _ => cases herr
  · rcases hbranch with ⟨hne, hrun⟩ | ⟨hz, hskip⟩
    · refine Or.inr (Or.inl ⟨v, fuel₂, r₁, n', hc, hne, hrun, ?_⟩)
      cases r₁ with
      | normal l g m ffi =>
        simp only [Continues] at h₂ ⊢
        obtain ⟨n₂, h₂⟩ := h₂
        exact ⟨fuel₁, n₂, h₂⟩
      | _ => exact h₂
    · have hs := skip_inv hskip
      subst hs
      simp only at h₂
      obtain ⟨n₂, h₂⟩ := h₂
      subst hz
      exact Or.inr (Or.inr ⟨hc, fuel₁, n₂, h₂⟩)

/-- A three-field struct literal evaluates its fields. -/
theorem eval_rStruct3_inv {s : St σ} {e₁ e₂ e₃ : Exp Word} {v : PanValue Word}
    (h : E.eval s (.rStruct [e₁, e₂, e₃]) = some v) :
    ∃ v₁ v₂ v₃, E.eval s e₁ = some v₁ ∧ E.eval s e₂ = some v₂ ∧ E.eval s e₃ = some v₃ ∧
      v = .rStruct [v₁, v₂, v₃] := by
  simp only [Env.eval] at h ⊢
  cases h₁ : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord e₁ E.memoryAccess with
  | none => simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, h₁] at h
  | some v₁ =>
    cases h₂ : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord e₂ E.memoryAccess with
    | none => simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, h₁, h₂] at h
    | some v₂ =>
      cases h₃ : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
          E.bytesInWord e₃ E.memoryAccess with
      | none => simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, h₁, h₂, h₃] at h
      | some v₃ =>
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, h₁, h₂, h₃] at h
        exact ⟨v₁, v₂, v₃, rfl, rfl, rfl, h.symm⟩

end InitECandidate.Solver.GuestBound
