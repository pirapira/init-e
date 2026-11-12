import InitECandidate.Solver.GuestBound.WpcAt
import InitECandidate.Solver.GuestBound.HeapKeep
import InitECandidate.Solver.GuestBound.PolyCalls

/-!
# Declaring calls of conditionally bounded callees

`Triple.decCallAt` and `WPc.decCall_at` are `Triple.decCallRun` and
`WPc.decCall` for a callee that is only bounded for this call (`FunCostAt`),
and they hand the scope the shape of the returned value as well. They are
what a caller of `bn254_pairing_check` needs: that callee is bounded only
from states whose heap pointer is in the heap.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- An unconditional bound is a bound for every call. -/
theorem FunCost.at {f : FunName} {B : Nat} (h : FunCost E f B) (s : St σ)
    (arguments : List (Exp Word)) : FunCostAt E f B s arguments := by
  intro parameters body values cl hlookup _ _ fuel r n hrun hne
  exact (h parameters body hlookup fuel _ r n trivial hrun hne).1

/-- A declaring call whose callee is bounded for the calls made from `P`-states. -/
theorem Triple.decCallAt {P P' : St σ → Prop} (name : VarName) (shape : Shape) {f : FunName}
    (arguments : List (Exp Word)) {body : Prog Word} {B C : Nat}
    (hf : ∀ s, P s → FunCostAt E f B s arguments)
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
        callSteps_le_at (info := none) (H := 0) fuel s arguments (hf s hD) trivial true rc nc hcall hrc
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

/-- A declaring call of a callee bounded for this call; the scope may use
that the callee's body returned a value of the declared shape. -/
theorem WPc.decCall_at {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} {B C : Nat} (hf : FunCostAt E f B s args)
    (h : ∀ v g m ffi, CalleeReturned E s f args v g m ffi →
      panShapeMatches (panValueShape E.structs v) sh = true →
      WPc E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body C
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPc E s (.decCall x sh f args body) (panValueExpsStepCost args + B + C + 1) Q := by
  refine ⟨?_, ?_⟩
  · refine Triple.decCallAt (P := fun a => a = s) (P' := fun a' => ∃ v g m ffi,
      CalleeReturned E s f args v g m ffi ∧
      panShapeMatches (panValueShape E.structs v) sh = true ∧
      a' = ⟨updatePanValueMap s.locals x v, g, m, ffi⟩) x sh args ?_ ?_ ?_
    · rintro a rfl
      exact hf
    · rintro a v g m ffi rfl hret hsh
      exact ⟨v, g, m, ffi, hret, hsh, rfl⟩
    · rintro fuel a r n ⟨v, g, m, ffi, hret, hsh, rfl⟩ hrun hne
      exact (h v g m ffi hret hsh).1 fuel _ r n rfl hrun hne
  · intro r hr
    rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
      hbind, hcallee, hout⟩
    · exact Or.inl (Stopped.of_error herr)
    cases rb with
    | returned lr g m ffi vs =>
      cases vs with
      | nil => exact hout.elim
      | cons v rest =>
        cases rest with
        | cons v' rest' => exact hout.elim
        | nil =>
          obtain ⟨r', hsh, hrun', rfl⟩ := hout
          rcases (h v g m ffi ⟨parameters, cbody, values, cl, lr, hlookup, hvalues, hbind,
            hcallee⟩ hsh).2 r' hrun' with hs | hq
          · exact Or.inl hs.restore
          · exact Or.inr hq
    | raised lr g m ffi ex v =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m ffi ev =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | _ => exact hout.elim

/-- `WPc.decCall_at` in budget form. -/
theorem WPc.decCall_at_sub {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} {B N : Nat} (hf : FunCostAt E f B s args)
    (hle : panValueExpsStepCost args + B + 1 ≤ N)
    (h : ∀ v g m ffi, CalleeReturned E s f args v g m ffi →
      panShapeMatches (panValueShape E.structs v) sh = true →
      WPc E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body
        (N - (panValueExpsStepCost args + B + 1))
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPc E s (.decCall x sh f args body) N Q :=
  (WPc.decCall_at hf h).mono (by omega) (fun _ h => h)

/-- What a returning callee leaves keeps the heap pointer in the heap. -/
theorem CalleeRet.heapOk (hE : GuestEnv E) {f : FunName} {args : List (Exp Word)}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ} (hf : f ≠ "heap_release")
    (h : CalleeRet E s f args vs g m ffi) (hH : HeapOk s.globals) : HeapOk g := by
  obtain ⟨parameters, body, values, cl, l, hlookup, -, -, fuel, n, hrun⟩ := h
  exact fun_heap_keep hE hf parameters body hlookup fuel ⟨cl, s.globals, s.memory, s.ffi⟩ _ n hH
    hrun

end InitECandidate.Solver.GuestBound
