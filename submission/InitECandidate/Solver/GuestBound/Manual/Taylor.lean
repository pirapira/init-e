import InitECandidate.Solver.GuestBound.U256Zero
import InitECandidate.Solver.GuestBound.Manual.BlsInv

/-!
# `taylor_exponential`

The loop `while nz == 0 { …; di = u256_from_word(i) * den; acc = p / di;
i = i + 1; nz = u256_is_zero(acc) }` has no guard on `i`, but when `i` is 0 at
the start of an iteration, `di` is 0, the division by zero returns 0 and `nz`
becomes 1. So the loop runs at most `2^64 + 1` times from any state.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A call assigning to the local `y`, whose callee is known to end in `.error`
or return `v` without changing the rest of the state. -/
theorem callAssign_of_spec {f : FunName} {y : VarName} {arguments : List (Exp Word)}
    {s : St σ} {r : Result σ} {v : PanValue Word}
    (hspec : ∀ parameters body values calleeLocals rb,
      lookupPanFunction f E.functions = some (parameters, body) →
      E.evalArgs s arguments = some values →
      bindPanValueParameters parameters values = some calleeLocals →
      Runs E ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body rb →
      rb.isError = true ∨ ∃ l, rb = .returned l s.globals s.memory s.ffi [v])
    (h : Runs E s (.call (some (some (.local, y), none)) f arguments) r) :
    r.isError = true ∨ r = .normal (updatePanValueMap s.locals y v) s.globals s.memory s.ffi := by
  rcases runs_call_inv (some (some (.local, y))) h with herr | ⟨parameters, body, values,
    calleeLocals, rb, hlookup, hvalues, hbind, hcallee, hout⟩
  · exact Or.inl herr
  rcases hspec parameters body values calleeLocals rb hlookup hvalues hbind hcallee with herr |
    ⟨l, rfl⟩
  · cases rb with
    | error l g m f =>
      simp only [CallOutcome] at hout
      exact Or.inl hout
    | _ => cases herr
  · simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl herr
    simp only [assignPanValueCallResult] at hassign
    split at hassign
    · simp only [Option.some.injEq, Prod.mk.injEq] at hassign
      obtain ⟨rfl, rfl⟩ := hassign
      exact Or.inr rfl
    · cases hassign

/-- `if c { trap_with(…); }` leaves the state alone or does not end normally. -/
theorem trapIte_runs (hE : GuestEnv E) {c : Exp Word} {arguments : List (Exp Word)} {s : St σ}
    {r : Result σ} :
    Runs E s (.ite c (.call (some (none, none)) "trap_with" arguments) .skip) r →
    match r with
    | .normal l g m f => l = s.locals ∧ g = s.globals ∧ m = s.memory ∧ f = s.ffi
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  intro h
  rw [runs_ite] at h
  split at h
  · split at h
    · rw [runs_skip] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨fuel, n, hrun⟩ := h
      have hnr := call_noReturn (trap_with_noReturn hE) (some none) hrun
      cases r with
      | normal l g m f => cases hnr.2
      | continued l g m f => cases hnr.1
      | broke l g m f => cases hnr.1
      | _ => trivial
  · subst h
    simp [St.err]

end InitECandidate.Solver.GuestBound
