import InitECandidate.Solver.GuestBound.ProgramBound

/-!
# A program bound from a bound on the entry function at the initial state

`programStepped_le` asks for a bound on the entry function from every state.
Here the bound is only required from the state the declarations leave.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- `callSteps_le` with the callee bound required only for the bodies this call runs. -/
theorem callSteps_le_at {f : FunName} {B H : Nat}
    {info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word))}
    (hh : HandlerCost E info H)
    (fuel : Nat) (s : St σ) (arguments : List (Exp Word)) (preserve : Bool)
    (hf : ∀ parameters body cl, lookupPanFunction f E.functions = some (parameters, body) →
      ∀ rb nb, E.run (fuel - 1) ⟨cl, s.globals, s.memory, s.ffi⟩ body = some (rb, nb) →
        rb.isError = false → nb ≤ B)
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
        have hbodyCost : ∀ rb nb, E.run fuel ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body =
            some (rb, nb) → rb.isError = false → nb ≤ B := by
          simp only [panValueCallTarget] at htarget
          split at htarget
          · simp at htarget
          · rename_i parameters body' hlookup
            split at htarget
            · split at htarget
              · simp only [Option.some.injEq, Prod.mk.injEq] at htarget
                obtain ⟨rfl, _⟩ := htarget
                exact hf parameters _ calleeLocals hlookup
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
          have hnb : rb.isError = false → nb ≤ B := fun hrb => hbodyCost rb nb hbody hrb
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

/-- `programStepped_le` with the entry bound required only from the state the
declarations leave. -/
theorem programStepped_le_at (context : PanValueFfiContext Word)
    (initial : PanValueFfiProgramState Word σ) (primitive : PanPrimitiveHandler Word)
    (handler : PanValueStatefulFfiHandler Word σ) (fuel : Nat)
    (declarations : List (Decl Word)) (entry : FunName) (arguments : List (Exp Word))
    (memoryAccess : Option (PanValueMemoryAccess Word))
    (memoryHandler : Option (PanValueMemoryFfiHandler Word σ)) (B : Nat)
    (hentry : ∀ state,
      evalPanValueDeclarations initial.source declarations (memoryAccess := memoryAccess) =
        some state →
      ∀ parameters body cl, lookupPanFunction entry state.functions = some (parameters, body) →
      ∀ fuel' rb nb,
        (programEnv context primitive handler memoryAccess memoryHandler state).run fuel'
          ⟨cl, state.globals, state.memory, initial.ffi⟩ body = some (rb, nb) →
        rb.isError = false → nb ≤ B)
    (r : Result σ) (n : Nat)
    (hrun : evalPanValueFfiProgramStepped context initial primitive handler fuel declarations
      entry arguments (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
        some (r, n))
    (hne : r.isError = false) :
    n ≤ panValueExpsStepCost arguments + B := by
  unfold evalPanValueFfiProgramStepped at hrun
  cases hdecl : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) with
  | none => rw [hdecl] at hrun; simp at hrun
  | some state =>
    rw [hdecl] at hrun
    simp only [Option.bind_eq_bind, Option.bind_some] at hrun
    cases hcall : evalPanValueFfiCallSteps context primitive handler state.structs
        state.functions state.baseAddress state.topAddress state.bytesInWord fuel
        (fun _ => none) state.globals state.memory initial.ffi none entry arguments
        (memoryAccess := memoryAccess)
        (contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
          state.parameterShapes))
        (memoryHandler := memoryHandler) with
    | none => rw [hcall] at hrun; simp at hrun
    | some callPair =>
      obtain ⟨rc, nc⟩ := callPair
      rw [hcall] at hrun
      have hncOf : rc.isError = false → nc ≤ panValueExpsStepCost arguments + B + 0 := fun hrc =>
        callSteps_le_at (E := programEnv context primitive handler memoryAccess memoryHandler state)
          (info := none) (H := 0) trivial fuel
          ⟨fun _ => none, state.globals, state.memory, initial.ffi⟩ arguments false
          (fun parameters body cl hl rb nb h hrb =>
            hentry state hdecl parameters body cl hl _ rb nb h hrb) rc nc hcall hrc
      simp only [Option.bind_some] at hrun
      cases rc with
      | error l g m f =>
        repeat' split at hrun
        all_goals first
          | (simp at hrun; done)
          | (simp only [Option.some.injEq, Prod.mk.injEq] at hrun
             obtain ⟨rfl, -⟩ := hrun
             exact Bool.noConfusion hne)
          | (rename_i heq _; simp at heq; done)
          | (rename_i heq; simp at heq; done)
      | _ =>
        have hnc := hncOf rfl
        repeat' split at hrun
        all_goals first
          | (simp at hrun; done)
          | (simp only [Option.some.injEq, Prod.mk.injEq] at *; omega)

end InitECandidate.Solver.GuestBound
