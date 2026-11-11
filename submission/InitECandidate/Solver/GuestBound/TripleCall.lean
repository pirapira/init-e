import InitECandidate.Solver.GuestBound.TripleRules
import InitECandidate.Solver.GuestBound.EvalSimp

/-!
# A declaring-call rule that exposes the callee's run

`Triple.decCallRun` is `Triple.decCall` with one more fact for the scope of
the declared variable: some run of the callee's body returned the bound value.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Some run of a body registered for `f`, on the arguments evaluated in `s`,
returned `v` with globals `g`, memory `m` and FFI state `ffi`. -/
def CalleeReturned (E : Env σ) (s : St σ) (f : FunName) (arguments : List (Exp Word))
    (v : PanValue Word) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (ffi : FfiState σ) : Prop :=
  ∃ parameters body values calleeLocals l,
    lookupPanFunction f E.functions = some (parameters, body) ∧
    E.evalArgs s arguments = some values ∧
    bindPanValueParameters parameters values = some calleeLocals ∧
    Runs E ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body (.returned l g m ffi [v])

/-- A declaring call, with the precondition carried into its scope together
with the fact that the callee's body returned the bound value. -/
theorem Triple.decCallRun {P P' : St σ → Prop} (name : VarName) (shape : Shape) {f : FunName}
    (arguments : List (Exp Word)) {body : Prog Word} {B C : Nat}
    (hf : FunCost E f B)
    (hP : ∀ s v g m ffi, P s → CalleeReturned E s f arguments v g m ffi →
      panShapeMatches (panValueShape E.structs v) shape = true →
      P' ⟨updatePanValueMap s.locals name v, g, m, ffi⟩)
    (hbody : Triple E P' body C (fun _ => True)) :
    Triple E P (.decCall name shape f arguments body)
      (panValueExpsStepCost arguments + B + C + 1) (fun _ => True) := by
  unfold Triple
  intro fuel s r n hD hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
        E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi none f
        arguments (memoryAccess := E.memoryAccess) (contracts := E.contracts)
        (memoryHandler := E.memoryHandler) (preserveReturnLocals := true) with
    | none => rw [hcall] at hrun; simp at hrun
    | some callPair =>
      obtain ⟨rc, nc⟩ := callPair
      rw [hcall] at hrun
      have hncOf : rc.isError = false → nc ≤ panValueExpsStepCost arguments + B + 0 := fun hrc =>
        callSteps_le (info := none) (H := 0) hf trivial fuel s arguments true rc nc hcall hrc
      simp only [Option.bind_eq_bind, Option.bind_some] at hrun
      split at hrun
      · have hnc := hncOf rfl
        split at hrun
        · rename_i returnedLocals g m ffi value hshape
          have hcr : CalleeReturned E s f arguments value g m ffi := by
            rcases callSteps_inv none fuel s arguments true _ nc hcall with herr |
              ⟨fuel', parameters, cbody, values, calleeLocals, rb, nb', hlookup, hvalues, hbind,
                hrun', hout⟩
            · cases herr
            · cases rb with
              | returned l' g' m' f' values' =>
                simp only [CallOutcome] at hout
                rcases hout with herr | ⟨l'', heq⟩
                · cases herr
                · simp only [PanValueFfiControlResult.returned.injEq] at heq
                  obtain ⟨-, rfl, rfl, rfl, rfl⟩ := heq
                  exact ⟨parameters, cbody, values, calleeLocals, l', hlookup, hvalues, hbind,
                    ⟨fuel', nb', hrun'⟩⟩
              | raised l' g' m' f' ex v' =>
                simp only [CallOutcome] at hout
                cases hout
              | finalFfi l' g' m' f' ev =>
                simp only [CallOutcome] at hout
                cases hout
              | _ =>
                simp only [CallOutcome] at hout
                cases hout
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel
              (updatePanValueMap s.locals name value) g m ffi body
              (memoryAccess := E.memoryAccess) (contracts := E.contracts)
              (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some bodyPair =>
            obtain ⟨rb, nb⟩ := bodyPair
            rw [hb] at hrun
            simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            have hnb : nb ≤ C :=
              (hbody fuel ⟨updatePanValueMap s.locals name value, g, m, ffi⟩ rb nb
                (hP s value g m ffi hD hcr hshape) hb
                (by cases rb <;> first | rfl | cases hne)).1
            omega
        · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          cases hne
      · have hnc := hncOf rfl
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      · have hnc := hncOf rfl
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        cases hne
      · simp at hrun

end InitECandidate.Solver.GuestBound
