import InitECandidate.Solver.GuestBound.Call
import InitECandidate.Solver.GuestBound.CallInv

/-!
# Cost of a call whose callee bound depends on the call state

`FunCostAt E f B s args` bounds the body of `f` only for the run started by
this call (the callee's locals are the bound arguments, its globals, memory
and FFI state are those of `s`). Needed where a callee is bounded only under
a precondition, e.g. `fq12_inv` on canonical input. The proofs are those of
`Call.lean` with the unconditional bound replaced.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The body of `f`, run as called from `s` with `arguments`, takes at most `B` steps. -/
def FunCostAt (E : Env σ) (f : FunName) (B : Nat) (s : St σ) (arguments : List (Exp Word)) :
    Prop :=
  ∀ parameters body values calleeLocals,
    lookupPanFunction f E.functions = some (parameters, body) →
    E.evalArgs s arguments = some values →
    bindPanValueParameters parameters values = some calleeLocals →
    ∀ fuel r n, E.run fuel ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body = some (r, n) →
      r.isError = false → n ≤ B

/-- Step bound for the call evaluator, for results other than `.error`. -/
theorem callSteps_le_at {f : FunName} {B H : Nat}
    {info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word))}
    (fuel : Nat) (s : St σ) (arguments : List (Exp Word)) (hf : FunCostAt E f B s arguments)
    (hh : HandlerCost E info H) (preserve : Bool)
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
      have hvalues : E.evalArgs s arguments = some values := by
        have hargs' := hargs
        simp only [panValueCallArguments, evalPanValueExpsCounted, Option.map_eq_some_iff,
          Prod.mk.injEq] at hargs'
        obtain ⟨vs, hvs, rfl, -⟩ := hargs'
        exact hvs
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
          have hnb : rb.isError = false → nb ≤ B := fun hrb =>
            hf parameters body values calleeLocals hlookup hvalues hbind fuel rb nb hbody hrb
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

/-- A call statement from state `s`, with a callee bound that holds for this call. -/
theorem call_cost_at {f : FunName} {B H : Nat} {s : St σ}
    {info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word))}
    (arguments : List (Exp Word)) (hf : FunCostAt E f B s arguments)
    (hh : HandlerCost E info H) :
    Triple E (fun a => a = s) (.call info f arguments)
      (panValueExpsStepCost arguments + B + H + 1) (fun _ => True) := by
  unfold Triple
  intro fuel a r n ha hrun hne
  rw [ha] at hrun
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
      have := callSteps_le_at fuel s arguments hf hh false rc nc hcall hne
      omega

end InitECandidate.Solver.GuestBound
