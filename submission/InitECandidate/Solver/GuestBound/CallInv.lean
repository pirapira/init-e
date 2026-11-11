import InitECandidate.Solver.GuestBound.HalvingLoop

/-!
# Inversion of calls

A run of a call without a handler is an `.error`, or a run of a registered
body from the bound parameters whose result determines the call's result.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Evaluation of an argument list at the environment's parameters. -/
def Env.evalArgs (E : Env σ) (s : St σ) (arguments : List (Exp Word)) :
    Option (List (PanValue Word)) :=
  evalPanValueExps E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
    E.bytesInWord arguments E.memoryAccess

/-- How the result `r` of a call without a handler follows from the callee's result `rb`. -/
def CallOutcome (E : Env σ) (s : St σ) (destination : Option (Option (VarKind × VarName)))
    (rb r : Result σ) : Prop :=
  match rb with
  | .returned _ g m f values =>
      match destination with
      | none => r.isError = true ∨ ∃ l, r = .returned l g m f values
      | some dest =>
          r.isError = true ∨ ∃ l' g', assignPanValueCallResult s.locals g dest values
            (structs := E.structs) = some (l', g') ∧ r = .normal l' g' m f
  | .raised _ g m f exception value => r = .raised (fun _ => none) g m f exception value
  | .finalFfi _ g m f event => r = .finalFfi (fun _ => none) g m f event
  | _ => r.isError = true

/-- Inversion of the call evaluator for calls without a handler. -/
theorem callSteps_inv {f : FunName} (destination : Option (Option (VarKind × VarName)))
    (fuel : Nat) (s : St σ) (arguments : List (Exp Word)) (preserve : Bool) (r : Result σ)
    (n : Nat)
    (hrun : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
      E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi
      (destination.map fun dest => (dest, none)) f arguments (memoryAccess := E.memoryAccess)
      (contracts := E.contracts) (memoryHandler := E.memoryHandler)
      (preserveReturnLocals := preserve) = some (r, n)) :
    r.isError = true ∨ ∃ fuel' parameters body values calleeLocals rb nb,
      lookupPanFunction f E.functions = some (parameters, body) ∧
      E.evalArgs s arguments = some values ∧
      bindPanValueParameters parameters values = some calleeLocals ∧
      E.run fuel' ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body = some (rb, nb) ∧
      CallOutcome E s destination rb r := by
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
            · cases destination with
              | none =>
                simp only [Option.map_none, Option.pure_def, Option.some.injEq,
                  Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                exact Or.inr ⟨_, rfl⟩
              | some dest =>
                simp only [Option.map_some] at hrun
                cases hassign : assignPanValueCallResult s.locals g dest returned
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
              cases destination with
              | none => exact Or.inl rfl
              | some dest => exact Or.inl rfl
          | raised l g m ffi exception value =>
            simp only at hrun
            split at hrun
            · cases destination with
              | none =>
                simp only [Option.map_none, Option.pure_def, Option.some.injEq,
                  Prod.mk.injEq] at hrun
                exact hrun.1.symm
              | some dest =>
                simp only [Option.map_some, Option.pure_def, Option.some.injEq,
                  Prod.mk.injEq] at hrun
                exact hrun.1.symm
            · simp at hrun
          | finalFfi l g m ffi event =>
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            exact hrun.1.symm
          | _ =>
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            rfl

/-- Inversion of a call statement without a handler. -/
theorem call_run_inv {f : FunName} (destination : Option (Option (VarKind × VarName)))
    {fuel : Nat} {s : St σ} {arguments : List (Exp Word)} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.call (destination.map fun dest => (dest, none)) f arguments) =
      some (r, n)) :
    r.isError = true ∨ ∃ fuel' parameters body values calleeLocals rb nb,
      lookupPanFunction f E.functions = some (parameters, body) ∧
      E.evalArgs s arguments = some values ∧
      bindPanValueParameters parameters values = some calleeLocals ∧
      E.run fuel' ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body = some (rb, nb) ∧
      CallOutcome E s destination rb r := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
        E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi
        (destination.map fun dest => (dest, none)) f arguments (memoryAccess := E.memoryAccess)
        (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
    | none => rw [hcall] at h; simp at h
    | some pair =>
      obtain ⟨rc, nc⟩ := pair
      rw [hcall] at h
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact callSteps_inv destination fuel s arguments false rc nc hcall

/-- Inversion of a declaring call: the callee returned one value of the declared
shape and the rest of the block ran with it bound, or the callee's exception or
final foreign call ended the statement, or the result is `.error`. -/
theorem decCall_run_inv {f : FunName} {fuel : Nat} {s : St σ} {x : VarName} {shape : Shape}
    {arguments : List (Exp Word)} {body : Prog Word} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.decCall x shape f arguments body) = some (r, n)) :
    r.isError = true ∨ ∃ fuel₁ parameters calleeBody values calleeLocals rb nb,
      lookupPanFunction f E.functions = some (parameters, calleeBody) ∧
      E.evalArgs s arguments = some values ∧
      bindPanValueParameters parameters values = some calleeLocals ∧
      E.run fuel₁ ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ calleeBody = some (rb, nb) ∧
      match rb with
      | .returned _ g m ffi [value] =>
          ∃ fuel₂ r' n', panShapeMatches (panValueShape E.structs value) shape = true ∧
            E.run fuel₂ ⟨updatePanValueMap s.locals x value, g, m, ffi⟩ body =
              some (r', n') ∧
            r = restorePanValueFfiLocal x (s.locals x) r'
      | .raised _ g m ffi exception value => r = .raised (fun _ => none) g m ffi exception value
      | .finalFfi _ g m ffi event => r = .finalFfi (fun _ => none) g m ffi event
      | _ => False := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
        E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi none f
        arguments (memoryAccess := E.memoryAccess) (contracts := E.contracts)
        (memoryHandler := E.memoryHandler) (preserveReturnLocals := true) with
    | none => rw [hcall] at h; simp at h
    | some pair =>
      obtain ⟨rc, nc⟩ := pair
      rw [hcall] at h
      simp only [Option.bind_eq_bind, Option.bind_some] at h
      have herror : rc.isError = true → r.isError = true := by
        intro herr
        cases rc with
        | error l g m ffi =>
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rfl
        | _ => cases herr
      rcases callSteps_inv (E := E) none fuel s arguments true rc nc hcall with herr |
        ⟨fuel₁, parameters, calleeBody, values, calleeLocals, rb, nb, hlookup, hvalues, hbind,
          hbody, hout⟩
      · exact Or.inl (herror herr)
      · cases rb with
        | returned l g m ffi values' =>
          simp only [CallOutcome] at hout
          rcases hout with herr | ⟨l', rfl⟩
          · exact Or.inl (herror herr)
          · cases values' with
            | nil => simp at h
            | cons value rest =>
              cases rest with
              | cons value' rest' => simp at h
              | nil =>
                simp only at h
                split at h
                · rename_i hshape
                  cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                      E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                      (updatePanValueMap s.locals x value) g m ffi body
                      (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                      (memoryHandler := E.memoryHandler) with
                  | none => rw [hb] at h; simp at h
                  | some pair =>
                    obtain ⟨r', n'⟩ := pair
                    rw [hb] at h
                    simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                      Prod.mk.injEq] at h
                    obtain ⟨rfl, -⟩ := h
                    exact Or.inr ⟨fuel₁, parameters, calleeBody, values, calleeLocals, _, nb,
                      hlookup, hvalues, hbind, hbody, fuel, r', n', hshape, hb, rfl⟩
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, -⟩ := h
                  exact Or.inl rfl
        | raised l g m ffi exception value =>
          simp only [CallOutcome] at hout
          subst hout
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact Or.inr ⟨fuel₁, parameters, calleeBody, values, calleeLocals, _, nb, hlookup,
            hvalues, hbind, hbody, rfl⟩
        | finalFfi l g m ffi event =>
          simp only [CallOutcome] at hout
          subst hout
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact Or.inr ⟨fuel₁, parameters, calleeBody, values, calleeLocals, _, nb, hlookup,
            hvalues, hbind, hbody, rfl⟩
        | _ => exact Or.inl (herror (by simpa only [CallOutcome] using hout))

end InitECandidate.Solver.GuestBound
