import InitECandidate.Solver.GuestBound.ExpCost

/-!
# Cost of calls

A call costs its argument expressions, the callee body, the handler (when the
callee raises the caught exception) and one step. `FunCost` is an
unconditional bound on a function's body, which is what composition over the
acyclic call graph uses.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Every body registered for `f` costs at most `B`, from any state. -/
def FunCost (E : Env σ) (f : FunName) (B : Nat) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    Costs E body B

/-- The handler program of a call, if any, costs at most `H`. -/
def HandlerCost (E : Env σ)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word)))
    (H : Nat) : Prop :=
  match info with
  | some (_, some (_, _, handlerProgram)) => Costs E handlerProgram H
  | _ => True

/-- Step bound for the call evaluator, for results other than `.error`. -/
theorem callSteps_le {f : FunName} {B H : Nat}
    {info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word))}
    (hf : FunCost E f B) (hh : HandlerCost E info H)
    (fuel : Nat) (s : St σ) (arguments : List (Exp Word)) (preserve : Bool)
    (r : Result σ) (n : Nat)
    (hrun : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
      E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi info f
      arguments (memoryAccess := E.memoryAccess) (contracts := E.contracts)
      (memoryHandler := E.memoryHandler) (preserveReturnLocals := preserve) = some (r, n))
    (hne : r.isError = false) :
    n ≤ panValueExpsStepCost arguments + B + H := by
  cases fuel with
  | zero => simp [evalPanValueFfiCallSteps] at hrun
  | succ fuel =>
    rw [evalPanValueFfiCallSteps] at hrun
    cases hargs : panValueCallArguments E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory arguments E.memoryAccess with
    | none =>
      rw [hargs] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some argumentPair =>
      obtain ⟨values, argumentSteps⟩ := argumentPair
      rw [hargs] at hrun
      have hsteps : argumentSteps = panValueExpsStepCost arguments := by
        simp only [panValueCallArguments, evalPanValueExpsCounted, Option.map_eq_some_iff,
          Prod.mk.injEq] at hargs
        obtain ⟨_, _, _, h⟩ := hargs
        exact h.symm
      simp only [Option.elim_some] at hrun
      cases htarget : panValueCallTarget E.structs E.contracts f E.functions values with
      | none =>
        rw [htarget] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      | some callTarget =>
        obtain ⟨body, calleeLocals⟩ := callTarget
        rw [htarget] at hrun
        simp only [Option.elim_some] at hrun
        have hbodyCost : Costs E body B := by
          simp only [panValueCallTarget] at htarget
          split at htarget
          · simp at htarget
          · rename_i parameters body' hlookup
            split at htarget
            · split at htarget
              · simp only [Option.some.injEq, Prod.mk.injEq] at htarget
                obtain ⟨rfl, _⟩ := htarget
                exact hf parameters _ hlookup
              · simp at htarget
            · simp at htarget
        cases hbody : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel calleeLocals s.globals
            s.memory s.ffi body (memoryAccess := E.memoryAccess) (contracts := E.contracts)
            (memoryHandler := E.memoryHandler) with
        | none => rw [hbody] at hrun; simp at hrun
        | some bodyPair =>
          obtain ⟨rb, nb⟩ := bodyPair
          rw [hbody] at hrun
          have hnb : rb.isError = false → nb ≤ B := fun hrb =>
            (hbodyCost fuel ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb nb trivial hbody hrb).1
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases rb with
          | raised l g m ffi exception value =>
            have hnb := hnb rfl
            simp only at hrun
            split at hrun
            · cases info with
              | none =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                omega
              | some pair =>
                obtain ⟨destination, handlerInfo⟩ := pair
                cases handlerInfo with
                | none =>
                  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                  omega
                | some triple =>
                  obtain ⟨caught, handlerVariable, handlerProgram⟩ := triple
                  simp only at hrun
                  split at hrun
                  · split at hrun
                    · cases hhandler : evalPanValueFfiProgSteps E.context E.primitive E.handler
                          E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                          (updatePanValueMap s.locals handlerVariable value) g m ffi
                          handlerProgram (memoryAccess := E.memoryAccess)
                          (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
                      | none => rw [hhandler] at hrun; simp at hrun
                      | some handlerPair =>
                        obtain ⟨rh, nh⟩ := handlerPair
                        rw [hhandler] at hrun
                        simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                          Prod.mk.injEq] at hrun
                        obtain ⟨rfl, rfl⟩ := hrun
                        have hnh : nh ≤ H :=
                          (hh fuel ⟨updatePanValueMap s.locals handlerVariable value, g, m, ffi⟩
                            rh nh trivial hhandler hne).1
                        omega
                    · simp at hrun
                  · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                    omega
            · simp at hrun
          | returned l g m ffi returned =>
            have hnb := hnb rfl
            simp only at hrun
            split at hrun
            · cases info with
              | none =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                omega
              | some pair =>
                obtain ⟨destination, handlerInfo⟩ := pair
                simp only at hrun
                cases hassign : assignPanValueCallResult s.locals g destination returned
                    (structs := E.structs) with
                | none => rw [hassign] at hrun; simp at hrun
                | some assigned =>
                  rw [hassign] at hrun
                  simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                    Prod.mk.injEq] at hrun
                  omega
            · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              omega
          | finalFfi l g m ffi event =>
            have hnb := hnb rfl
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            omega
          | _ =>
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            cases hne

/-- A call statement costs its arguments, the callee, the handler and one step. -/
theorem Costs.call {f : FunName} {B H : Nat}
    {info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word))}
    (arguments : List (Exp Word)) (hf : FunCost E f B) (hh : HandlerCost E info H) :
    Costs E (.call info f arguments) (panValueExpsStepCost arguments + B + H + 1) := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
        E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi info f
        arguments (memoryAccess := E.memoryAccess) (contracts := E.contracts)
        (memoryHandler := E.memoryHandler) with
    | none => rw [hcall] at hrun; simp at hrun
    | some callPair =>
      obtain ⟨rc, nc⟩ := callPair
      rw [hcall] at hrun
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      have := callSteps_le hf hh fuel s arguments false rc nc hcall hne
      omega

end InitECandidate.Solver.GuestBound
