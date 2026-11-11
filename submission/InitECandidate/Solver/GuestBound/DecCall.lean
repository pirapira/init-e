import InitECandidate.Solver.GuestBound.Leaves

/-! # Cost of a declaring call (`var x = f(args); rest`) -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A declaring call costs its arguments, the callee, the rest of the block and one step. -/
theorem Costs.decCall (name : VarName) (shape : Shape) {f : FunName}
    (arguments : List (Exp Word)) {body : Prog Word} {B C : Nat}
    (hf : FunCost E f B) (hbody : Costs E body C) :
    Costs E (.decCall name shape f arguments body)
      (panValueExpsStepCost arguments + B + C + 1) := by
  unfold Costs Triple
  intro fuel s r n _ hrun hne
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
        · rename_i returnedLocals g m ffi value _
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
              (hbody fuel ⟨updatePanValueMap s.locals name value, g, m, ffi⟩ rb nb trivial hb
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
