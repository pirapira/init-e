import InitECandidate.Solver.GuestBound.Wpr

/-!
# Calls with an exception handler

`callH_run_inv` is `call_run_inv` for `try f(…) catch exc => hv { hp }`: the
callee returned and the result was assigned, or it raised `exc` and the
handler program ran with `hv` bound to the exception value (the binding is
not undone afterwards), or it raised another exception or ended in a final
foreign call, which propagate. `runs_callH_inv` is the same for `Runs`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- How the result `rb` of the callee's body turns into the result `r` of a
call statement with destination `dest` and handler `catch exc => hv { hp }`. -/
def HandlerOutcome (E : Env σ) (s : St σ) (dest : Option (VarKind × VarName))
    (exc : ExceptionId) (hv : VarName) (hp : Prog Word) (rb r : Result σ) : Prop :=
  match rb with
  | .returned _ g m f values =>
      r.isError = true ∨ ∃ l' g', assignPanValueCallResult s.locals g dest values
        (structs := E.structs) = some (l', g') ∧ r = .normal l' g' m f
  | .raised _ g m f exception value =>
      (exception ≠ exc ∧ r = .raised (fun _ => none) g m f exception value) ∨
        (exception = exc ∧ ∃ fuel n,
          E.run fuel ⟨updatePanValueMap s.locals hv value, g, m, f⟩ hp = some (r, n))
  | .finalFfi _ g m f event => r = .finalFfi (fun _ => none) g m f event
  | _ => r.isError = true

theorem callStepsH_inv {f : FunName} (dest : Option (VarKind × VarName)) (exc : ExceptionId)
    (hv : VarName) (hp : Prog Word)
    (fuel : Nat) (s : St σ) (arguments : List (Exp Word)) (preserve : Bool) (r : Result σ)
    (n : Nat)
    (hrun : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
      E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi
      (some (dest, some (exc, hv, hp))) f arguments (memoryAccess := E.memoryAccess)
      (contracts := E.contracts) (memoryHandler := E.memoryHandler)
      (preserveReturnLocals := preserve) = some (r, n)) :
    r.isError = true ∨ ∃ fuel' parameters body values calleeLocals rb nb,
      lookupPanFunction f E.functions = some (parameters, body) ∧
      E.evalArgs s arguments = some values ∧
      bindPanValueParameters parameters values = some calleeLocals ∧
      E.run fuel' ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body = some (rb, nb) ∧
      HandlerOutcome E s dest exc hv hp rb r := by
  cases fuel with
  | zero => simp [evalPanValueFfiCallSteps] at hrun
  | succ fuel =>
    rw [evalPanValueFfiCallSteps] at hrun
    cases hargs : panValueCallArguments E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory arguments E.memoryAccess with
    | none =>
      rw [hargs] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact Or.inl rfl
    | some argumentPair =>
      obtain ⟨values, argumentSteps⟩ := argumentPair
      rw [hargs] at hrun
      have hvalues : E.evalArgs s arguments = some values := by
        simp only [panValueCallArguments, evalPanValueExpsCounted, Option.map_eq_some_iff,
          Prod.mk.injEq] at hargs
        obtain ⟨vs, hvs, rfl, -⟩ := hargs
        exact hvs
      simp only [Option.elim_some] at hrun
      cases htarget : panValueCallTarget E.structs E.contracts f E.functions values with
      | none =>
        rw [htarget] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact Or.inl rfl
      | some callTarget =>
        obtain ⟨body, calleeLocals⟩ := callTarget
        rw [htarget] at hrun
        simp only [Option.elim_some] at hrun
        have hlookup : ∃ parameters, lookupPanFunction f E.functions = some (parameters, body) ∧
            bindPanValueParameters parameters values = some calleeLocals := by
          simp only [panValueCallTarget] at htarget
          split at htarget
          · simp at htarget
          · rename_i parameters body' hlookup
            split at htarget
            · split at htarget
              · rename_i locals hbind
                simp only [Option.some.injEq, Prod.mk.injEq] at htarget
                obtain ⟨rfl, rfl⟩ := htarget
                exact ⟨parameters, hlookup, hbind⟩
              · simp at htarget
            · simp at htarget
        obtain ⟨parameters, hlookup, hbind⟩ := hlookup
        cases hbody : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel calleeLocals s.globals
            s.memory s.ffi body (memoryAccess := E.memoryAccess) (contracts := E.contracts)
            (memoryHandler := E.memoryHandler) with
        | none => rw [hbody] at hrun; simp at hrun
        | some bodyPair =>
          obtain ⟨rb, nb⟩ := bodyPair
          rw [hbody] at hrun
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          refine Or.inr ⟨fuel, parameters, body, values, calleeLocals, rb, nb, hlookup, hvalues,
            hbind, hbody, ?_⟩
          cases rb with
          | returned l g m ffi returned =>
            simp only at hrun
            split at hrun
            · cases hassign : assignPanValueCallResult s.locals g dest returned
                  (structs := E.structs) with
              | none => rw [hassign] at hrun; simp at hrun
              | some assigned =>
                obtain ⟨locals', globals'⟩ := assigned
                rw [hassign] at hrun
                simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                  Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                exact Or.inr ⟨locals', globals', hassign, rfl⟩
            · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact Or.inl rfl
          | raised l g m ffi exception value =>
            simp only at hrun
            split at hrun
            · split at hrun
              · rename_i hcaught
                have hexc : exception = exc := (beq_iff_eq.mp hcaught).symm
                split at hrun
                · cases hh : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                      E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                      (updatePanValueMap s.locals hv value) g m ffi hp
                      (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                      (memoryHandler := E.memoryHandler) with
                  | none => rw [hh] at hrun; simp at hrun
                  | some hpair =>
                    obtain ⟨rh, nh⟩ := hpair
                    rw [hh] at hrun
                    simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                      Prod.mk.injEq] at hrun
                    obtain ⟨rfl, -⟩ := hrun
                    exact Or.inr ⟨hexc, fuel, nh, hh⟩
                · simp at hrun
              · rename_i hcaught
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                refine Or.inl ⟨fun hexc => hcaught (by rw [hexc]; simp), hrun.1.symm⟩
            · simp at hrun
          | finalFfi l g m ffi event =>
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            exact hrun.1.symm
          | _ =>
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            rfl

/-- Inversion of a call statement with a handler, for `Runs`. -/
theorem runs_callH_inv {f : FunName} {dest : Option (VarKind × VarName)} {exc : ExceptionId}
    {hv : VarName} {hp : Prog Word} {s : St σ} {arguments : List (Exp Word)} {r : Result σ}
    (h : Runs E s (.call (some (dest, some (exc, hv, hp))) f arguments) r) :
    r.isError = true ∨ ∃ parameters body values calleeLocals rb,
      lookupPanFunction f E.functions = some (parameters, body) ∧
      E.evalArgs s arguments = some values ∧
      bindPanValueParameters parameters values = some calleeLocals ∧
      Runs E ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body rb ∧
      match rb with
      | .returned _ g m f values =>
          r.isError = true ∨ ∃ l' g', assignPanValueCallResult s.locals g dest values
            (structs := E.structs) = some (l', g') ∧ r = .normal l' g' m f
      | .raised _ g m f exception value =>
          (exception ≠ exc ∧ r = .raised (fun _ => none) g m f exception value) ∨
            (exception = exc ∧ Runs E ⟨updatePanValueMap s.locals hv value, g, m, f⟩ hp r)
      | .finalFfi _ g m f event => r = .finalFfi (fun _ => none) g m f event
      | _ => r.isError = true := by
  obtain ⟨fuel, n, h⟩ := h
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
        E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi
        (some (dest, some (exc, hv, hp))) f arguments (memoryAccess := E.memoryAccess)
        (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
    | none => rw [hcall] at h; simp at h
    | some pair =>
      obtain ⟨rc, nc⟩ := pair
      rw [hcall] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      rcases callStepsH_inv dest exc hv hp fuel s arguments false _ nc hcall with herr |
        ⟨fuel', parameters, body, values, cl, rb, nb, hlookup, hvalues, hbind, hrun', hout⟩
      · exact Or.inl herr
      refine Or.inr ⟨parameters, body, values, cl, rb, hlookup, hvalues, hbind,
        ⟨fuel', nb, hrun'⟩, ?_⟩
      cases rb with
      | raised l g m ffi exception value =>
        rcases hout with h1 | ⟨h1, fuel2, n2, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, fuel2, n2, h2⟩
      | _ => exact hout

/-- Some run of a body registered for `f`, on the arguments evaluated in `s`,
ended in `rb`. -/
def CalleeRuns (E : Env σ) (s : St σ) (f : FunName) (arguments : List (Exp Word))
    (rb : Result σ) : Prop :=
  ∃ parameters body values calleeLocals,
    lookupPanFunction f E.functions = some (parameters, body) ∧
    E.evalArgs s arguments = some values ∧
    bindPanValueParameters parameters values = some calleeLocals ∧
    Runs E ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body rb

/-- A call statement with a handler: one obligation per way the callee can end. -/
theorem WPr.callH {s : St σ} {Q : Result σ → Prop} {f : FunName}
    {dest : Option (VarKind × VarName)} {exc : ExceptionId} {hv : VarName} {hp : Prog Word}
    {args : List (Exp Word)}
    (h : ∀ rb, CalleeRuns E s f args rb →
      match rb with
      | .returned _ g m ffi vs => ∀ l' g', assignPanValueCallResult s.locals g dest vs
          (structs := E.structs) = some (l', g') → Q (.normal l' g' m ffi)
      | .raised _ g m ffi e v =>
          (e ≠ exc → Q (.raised (fun _ => none) g m ffi e v)) ∧
            (e = exc → WPr E ⟨updatePanValueMap s.locals hv v, g, m, ffi⟩ hp Q)
      | .finalFfi _ g m ffi ev => Q (.finalFfi (fun _ => none) g m ffi ev)
      | _ => True) :
    WPr E s (.call (some (dest, some (exc, hv, hp))) f args) Q := by
  intro r hr
  rcases runs_callH_inv hr with herr | ⟨parameters, body, values, cl, rb, hlookup, hvalues,
    hbind, hrun, hout⟩
  · exact Or.inl herr
  have hb := h rb ⟨parameters, body, values, cl, hlookup, hvalues, hbind, hrun⟩
  cases rb with
  | returned l g m ffi vs =>
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl herr
    · exact Or.inr (hb l' g' hassign)
  | raised l g m ffi e v =>
    rcases hout with ⟨hne, rfl⟩ | ⟨heq, hrunh⟩
    · exact Or.inr (hb.1 hne)
    · exact hb.2 heq r hrunh
  | finalFfi l g m ffi ev =>
    subst hout
    exact Or.inr hb
  | _ => exact Or.inl hout

end InitECandidate.Solver.GuestBound
