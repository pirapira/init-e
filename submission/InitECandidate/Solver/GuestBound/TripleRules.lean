import InitECandidate.Solver.GuestBound.SymEval
import InitECandidate.Solver.GuestBound.DecCall

/-!
# Rules for hand-proved function bodies

A body whose loop bound depends on facts established earlier in the function
is bounded by threading a precondition along the spine of declarations:
`Triple.dec` and `Triple.decCall` pass it into the declared scope, and
`Triple.of_costs` attaches a postcondition (proved from the run alone) to an
unconditional step bound.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- An unconditional bound, with a postcondition proved separately. -/
theorem Triple.of_costs {P : St σ → Prop} {Q : Result σ → Prop} {p : Prog Word} {B : Nat}
    (h : Costs E p B)
    (hpost : ∀ fuel s r n, P s → E.run fuel s p = some (r, n) → r.isError = false → Q r) :
    Triple E P p B Q := by
  intro fuel s r n hP hrun hne
  exact ⟨(h fuel s r n trivial hrun hne).1, hpost fuel s r n hP hrun hne⟩

/-- A declaration, with the precondition carried into its scope. -/
theorem Triple.dec {P P' : St σ → Prop} (name : VarName) (shape : Shape) (value : Exp Word)
    {body : Prog Word} {B : Nat}
    (hP : ∀ s v, P s → E.eval s value = some v →
      panShapeMatches (panValueShape E.structs v) shape = true →
      P' ⟨updatePanValueMap s.locals name v, s.globals, s.memory, s.ffi⟩)
    (h : Triple E P' body B (fun _ => True)) :
    Triple E P (.dec name shape value body) (panValueExpStepCost value + B + 1)
      (fun _ => True) := by
  unfold Triple
  intro fuel s r n hD hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory value E.memoryAccess shape with
    | none =>
      rw [hacc] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some accepted =>
      rw [hacc] at hrun
      simp only [Option.elim_some] at hrun
      have hacc' : accepted.2 = panValueExpStepCost value ∧
          E.eval s value = some accepted.1 ∧
          panShapeMatches (panValueShape E.structs accepted.1) shape = true := by
        simp only [panValueDecAccepted, evalPanValueExpCounted] at hacc
        cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
            E.topAddress E.bytesInWord value E.memoryAccess with
        | none => rw [hv] at hacc; simp at hacc
        | some evaluated =>
          rw [hv] at hacc
          simp only [Option.map_some] at hacc
          split at hacc
          · rename_i hm
            simp only [Option.some.injEq] at hacc
            rw [← hacc]
            exact ⟨rfl, hv, hm⟩
          · simp at hacc
      obtain ⟨hsteps, hval, hshape⟩ := hacc'
      cases hbody : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel
          (updatePanValueMap s.locals name accepted.1) s.globals s.memory s.ffi body
          (memoryAccess := E.memoryAccess) (contracts := E.contracts)
          (memoryHandler := E.memoryHandler) with
      | none => rw [hbody] at hrun; simp at hrun
      | some bodyPair =>
        obtain ⟨rb, nb⟩ := bodyPair
        rw [hbody] at hrun
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        have hnb : nb ≤ B :=
          (h fuel ⟨updatePanValueMap s.locals name accepted.1, s.globals, s.memory, s.ffi⟩
            rb nb (hP s accepted.1 hD hval hshape) hbody
            (by cases rb <;> first | rfl | cases hne)).1
        omega

/-- A declaring call, with the precondition carried into its scope. The callee
may have changed globals, memory and the FFI state. -/
theorem Triple.decCall {P P' : St σ → Prop} (name : VarName) (shape : Shape) {f : FunName}
    (arguments : List (Exp Word)) {body : Prog Word} {B C : Nat}
    (hf : FunCost E f B)
    (hP : ∀ s v g m ffi, P s → panShapeMatches (panValueShape E.structs v) shape = true →
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
                (hP s value g m ffi hD hshape) hb
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

/-- A shared-memory load into a local fails, ends the run with a final FFI
event, or stores a word in that local and changes only the FFI state. -/
theorem shMemLoad_local_inv {fuel : Nat} {s : St σ} {size : OpSize} {x : VarName}
    {a : Exp Word} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.shMemLoad size .local x a) = some (r, n)) :
    r.isError = true ∨ (∃ g m ffi event, r = .finalFfi (fun _ => none) g m ffi event) ∨
      ∃ w ffi, r = .normal (updatePanValueMap s.locals x (.word w)) s.globals s.memory ffi := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueShMemLoadResult] at h
    repeat' split at h
    all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at h))
    all_goals (obtain ⟨rfl, -⟩ := h)
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)
      | exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- A word store fails or changes only memory. -/
theorem store_inv {fuel : Nat} {s : St σ} {a v : Exp Word} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.store a v) = some (r, n)) :
    r.isError = true ∨ ∃ m, r = .normal s.locals s.globals m s.ffi := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueStoreResult] at h
    repeat' split at h
    all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at h))
    all_goals (obtain ⟨rfl, -⟩ := h)
    all_goals first
      | exact Or.inl rfl
      | exact Or.inr ⟨_, rfl⟩

end InitECandidate.Solver.GuestBound
