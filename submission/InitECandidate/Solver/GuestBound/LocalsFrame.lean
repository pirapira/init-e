import InitECandidate.Solver.GuestBound.ShapeFrame

/-!
# Which locals a statement can change

`localsOk M` accepts statements that assign no local outside `M` (and the
locals they declare themselves), whatever the functions they call do to
globals and memory. `locals_sound`: after such a statement every other local
has its old value.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Statements that assign no local outside `M`. -/
def localsOk : List VarName → Prog Word → Bool
  | _, .skip | _, .tick | _, .annot _ _ | _, .break | _, .continue | _, .return _
  | _, .raise _ _ => true
  | M, .assign .local name _ => M.contains name
  | M, .seq first second => localsOk M first && localsOk M second
  | M, .ite _ thenBranch elseBranch => localsOk M thenBranch && localsOk M elseBranch
  | M, .while _ body => localsOk M body
  | M, .dec name _ _ body => localsOk (name :: M) body
  | _, .call none _ _ => true
  | M, .call (some (destination, none)) _ _ => destIn M destination
  | M, .decCall name _ _ _ body => localsOk (name :: M) body
  | _, _ => false

/-- No local outside `M` changed, for the results that keep running. -/
def LocalsPost (M : List VarName) (s : St σ) : Result σ → Prop
  | .normal l _ _ _ | .continued l _ _ _ | .broke l _ _ _ => ∀ x, x ∉ M → l x = s.locals x
  | _ => True

theorem LocalsPost.of_error {M : List VarName} {s : St σ} {r : Result σ}
    (h : r.isError = true) : LocalsPost M s r := by
  cases r <;> first | trivial | cases h

theorem LocalsPost.trans {M : List VarName} {s : St σ} {l g : VarName → Option (PanValue Word)}
    {mem : Word → Option (PanValue Word)} {f : FfiState σ} {r : Result σ}
    (h₁ : ∀ x, x ∉ M → l x = s.locals x) (h₂ : LocalsPost M ⟨l, g, mem, f⟩ r) :
    LocalsPost M s r := by
  cases r <;> simp only [LocalsPost] at h₂ ⊢
  all_goals exact fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem LocalsPost.restore {M : List VarName} {name : VarName} {s : St σ}
    {value : PanValue Word} {g : VarName → Option (PanValue Word)}
    {mem : Word → Option (PanValue Word)} {f : FfiState σ} {r : Result σ}
    (h : LocalsPost (name :: M) ⟨updatePanValueMap s.locals name value, g, mem, f⟩ r) :
    LocalsPost M s (restorePanValueFfiLocal name (s.locals name) r) := by
  cases r <;> simp only [LocalsPost, restorePanValueFfiLocal] at h ⊢
  all_goals
    intro x hx
    by_cases hxn : x = name
    · subst hxn
      simp [restorePanValueLocal]
    · have hxn' : (x == name) = false := by simpa using hxn
      simp only [restorePanValueLocal, hxn', Bool.false_eq_true, if_false]
      rw [h x (by simp [hxn, hx])]
      simp [updatePanValueMap, hxn']

set_option hygiene false in
/-- Finish a leaf whose keep-running results leave the state alone. -/
local macro "locals_same" : tactic => `(tactic| (
  simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  exact fun _ _ => rfl))

/-- `localsOk` statements change no local outside `M`. -/
theorem locals_sound :
    ∀ (fuel : Nat) (M : List VarName) (p : Prog Word) (s : St σ) (r : Result σ) (n : Nat),
      localsOk M p = true → E.run fuel s p = some (r, n) → LocalsPost M s r := by
  intro fuel
  induction fuel with
  | zero =>
    intro M p s r n _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro M p s r n hs hrun
    simp only [Env.run] at hrun
    cases p with
    | skip =>
      simp only [evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact (fun _ _ => rfl)
    | tick => locals_same
    | annot key text => locals_same
    | «break» => locals_same
    | «continue» => locals_same
    | «return» value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueReturnResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [LocalsPost])
    | raise exception value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueRaiseResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [LocalsPost])
    | assign kind name value =>
      cases kind with
      | global => simp [localsOk] at hs
      | «local» =>
        have hmem : name ∈ M := by simpa [localsOk] using hs
        rw [evalPanValueFfiProgSteps] at hrun
        simp only [panValueAssignLocalResult, evalPanValueExpCounted] at hrun
        cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
            E.topAddress E.bytesInWord value E.memoryAccess with
        | none =>
          rw [hv] at hrun
          simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [LocalsPost]
        | some evaluated =>
          rw [hv] at hrun
          simp only [Option.map_some] at hrun
          split at hrun
          · rename_i hvalid
            simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact (update_frame hmem hvalid).1
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            simp only [LocalsPost]
    | seq first second =>
      simp only [localsOk, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases h₁ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi first (memoryAccess := E.memoryAccess) (contracts := E.contracts)
          (memoryHandler := E.memoryHandler) with
      | none => rw [h₁] at hrun; simp at hrun
      | some pair =>
        obtain ⟨r₁, n₁⟩ := pair
        rw [h₁] at hrun
        have p₁ := ih M first s r₁ n₁ hs.1 h₁
        cases r₁ with
        | normal l g m f =>
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases h₂ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f second
              (memoryAccess := E.memoryAccess) (contracts := E.contracts)
              (memoryHandler := E.memoryHandler) with
          | none => rw [h₂] at hrun; simp at hrun
          | some pair₂ =>
            obtain ⟨r₂, n₂⟩ := pair₂
            rw [h₂] at hrun
            simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact LocalsPost.trans p₁ (ih M second ⟨l, g, m, f⟩ r₂ n₂ hs.2 h₂)
        | _ =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact p₁
    | ite condition thenBranch elseBranch =>
      simp only [localsOk, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [LocalsPost]
      | some pair =>
        obtain ⟨c, kc⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hc : (c != 0) = true
        · rw [if_pos hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi thenBranch (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih M thenBranch s rb nb hs.1 hb
        · rw [if_neg hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi elseBranch (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih M elseBranch s rb nb hs.2 hb
    | «while» c body =>
      have hs' : localsOk M body = true := by simpa only [localsOk] using hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory c E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [LocalsPost]
      | some pair =>
        obtain ⟨v, kc⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hv : (v == 0) = true
        · rw [if_pos hv] at hrun
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact (fun _ _ => rfl)
        · rw [if_neg hv] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi body (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            have pb := ih M body s rb nb hs' hb
            have again : ∀ l g mem f, (∀ x, x ∉ M → l x = s.locals x) →
                (do
                  let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                    E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                    l g mem f (.while c body) (memoryAccess := E.memoryAccess)
                    (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                  pure (loopResult, kc + nb + loopSteps + 1)) = some (r, n) →
                LocalsPost M s r := by
              intro l g mem f hfr hrun
              cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                  E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g mem f
                  (.while c body) (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                  (memoryHandler := E.memoryHandler) with
              | none => rw [hloop] at hrun; simp at hrun
              | some pair =>
                obtain ⟨rl, nl⟩ := pair
                rw [hloop] at hrun
                simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                  Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                exact LocalsPost.trans hfr (ih M (.while c body) ⟨l, g, mem, f⟩ rl nl hs hloop)
            cases rb with
            | normal l g mem f => exact again l g mem f pb hrun
            | continued l g mem f => exact again l g mem f pb hrun
            | broke l g mem f =>
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact pb
            | _ =>
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              simp only [LocalsPost]
    | dec name shape value body =>
      simp only [localsOk] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory value E.memoryAccess shape with
      | none =>
        rw [hacc] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [LocalsPost]
      | some accepted =>
        rw [hacc] at hrun
        simp only [Option.elim_some] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel
            (updatePanValueMap s.locals name accepted.1) s.globals s.memory s.ffi body
            (memoryAccess := E.memoryAccess) (contracts := E.contracts)
            (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at hrun
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact LocalsPost.restore (s := s) (ih (name :: M) body ⟨updatePanValueMap s.locals name
            accepted.1, s.globals, s.memory, s.ffi⟩ rb nb hs hb)
    | call info f arguments =>
      have hparts : ∃ destination : Option (Option (VarKind × VarName)),
          info = destination.map (fun dest => (dest, none)) ∧
          ∀ d, destination = some d → destIn M d = true := by
        cases info with
        | none => exact ⟨none, rfl, fun _ h => by cases h⟩
        | some pair =>
          obtain ⟨destination, handlerInfo⟩ := pair
          cases handlerInfo with
          | some h => simp [localsOk] at hs
          | none =>
            simp only [localsOk] at hs
            refine ⟨some destination, rfl, ?_⟩
            intro d hd
            simp only [Option.some.injEq] at hd
            exact hd ▸ hs
      obtain ⟨destination, rfl, hdest⟩ := hparts
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi (destination.map fun dest => (dest, none)) f arguments
          (memoryAccess := E.memoryAccess)
          (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
      | none => rw [hcall] at hrun; simp at hrun
      | some pair =>
        obtain ⟨rc, nc⟩ := pair
        rw [hcall] at hrun
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rcases callSteps_inv destination fuel s arguments false rc nc hcall with herr |
          ⟨fuel', parameters, calleeBody, values, calleeLocals, rb, nb, -, -, -, -, hout⟩
        · exact LocalsPost.of_error herr
        cases rb with
        | returned l g m ffi values' =>
          simp only [CallOutcome] at hout
          cases destination with
          | none =>
            simp only at hout
            rcases hout with herr | ⟨l', rfl⟩
            · exact LocalsPost.of_error herr
            · simp only [LocalsPost]
          | some d =>
            simp only at hout
            rcases hout with herr | ⟨l', g', hassign, rfl⟩
            · exact LocalsPost.of_error herr
            · exact (assignResult_frame (structs := E.structs) (hdest d rfl) hassign).2.1
        | raised l g m ffi exception value =>
          simp only [CallOutcome] at hout
          subst hout
          simp only [LocalsPost]
        | finalFfi l g m ffi event =>
          simp only [CallOutcome] at hout
          subst hout
          simp only [LocalsPost]
        | _ =>
          simp only [CallOutcome] at hout
          exact LocalsPost.of_error hout
    | decCall name shape f arguments body =>
      simp only [localsOk] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi none f arguments (memoryAccess := E.memoryAccess)
          (contracts := E.contracts) (memoryHandler := E.memoryHandler)
          (preserveReturnLocals := true) with
      | none => rw [hcall] at hrun; simp at hrun
      | some pair =>
        obtain ⟨rc, nc⟩ := pair
        rw [hcall] at hrun
        simp only [Option.bind_eq_bind, Option.bind_some] at hrun
        split at hrun
        · split at hrun
          · rename_i returnedLocals g m ffi value _
            cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                (updatePanValueMap s.locals name value) g m ffi body
                (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                (memoryHandler := E.memoryHandler) with
            | none => rw [hb] at hrun; simp at hrun
            | some pair =>
              obtain ⟨rb, nb⟩ := pair
              rw [hb] at hrun
              simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact LocalsPost.restore (s := s) (ih (name :: M) body ⟨updatePanValueMap s.locals name
                value, g, m, ffi⟩ rb nb hs hb)
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            simp only [LocalsPost]
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [LocalsPost]
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [LocalsPost]
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [LocalsPost]
        · simp at hrun
    | _ => simp [localsOk] at hs

end InitECandidate.Solver.GuestBound
