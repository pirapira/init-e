import InitECandidate.Solver.GuestBound.Decls

/-!
# Call-tree properties of the non-local state

A `Keeper` is a reflexive, transitive relation between the globals, memory and
FFI state before and after a run, together with a filter saying which leaf
statements respect it. `keepWith` extends the filter through control flow and
calls, and `keepWith_sound` shows every result state is related to the entry
state. Instances: "nothing but locals changes" and "one global is unchanged".
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type}

/-- A relation on states that ignores locals, with the leaf statements that respect it. -/
structure Keeper (E : Env σ) where
  rel : St σ → St σ → Prop
  refl : ∀ s, rel s s
  trans : ∀ {a b c}, rel a b → rel b c → rel a c
  right_locals : ∀ {s l g m f} (l' : VarName → Option (PanValue Word)),
    rel s ⟨l, g, m, f⟩ → rel s ⟨l', g, m, f⟩
  left_locals : ∀ {s' l g m f} (l' : VarName → Option (PanValue Word)),
    rel ⟨l, g, m, f⟩ s' → rel ⟨l', g, m, f⟩ s'
  allow : Prog Word → Bool
  leaf : ∀ fuel p s r n, allow p = true → E.run fuel s p = some (r, n) → rel s r.st

/-- The destination of a call result is not a global. -/
def destLocal : Option (VarKind × VarName) → Bool
  | some (.global, _) => false
  | _ => true

/-- Leaves pass the filter, calls go to functions satisfying `callee`, and call
results are not assigned to globals. -/
def keepWith (allow : Prog Word → Bool) (callee : FunName → Bool) : Prog Word → Bool
  | .seq first second => keepWith allow callee first && keepWith allow callee second
  | .ite _ thenBranch elseBranch =>
      keepWith allow callee thenBranch && keepWith allow callee elseBranch
  | .while _ body => keepWith allow callee body
  | .dec _ _ _ body => keepWith allow callee body
  | .call (some (destination, some (_, _, handlerProgram))) f _ =>
      callee f && destLocal destination && keepWith allow callee handlerProgram
  | .call (some (destination, none)) f _ => callee f && destLocal destination
  | .call none f _ => callee f
  | .decCall _ _ f _ body => callee f && keepWith allow callee body
  | p => allow p

/-- Every declaration named `f` passes `keepWith`, following calls `depth` levels deep. -/
def keepFn (allow : Prog Word → Bool) (decls : List (Decl Word)) : Nat → FunName → Bool
  | 0, _ => false
  | depth + 1, f =>
      decls.all fun decl =>
        match decl with
        | .function d => d.name != f || keepWith allow (keepFn allow decls depth) d.body
        | _ => true

variable {E : Env σ}

/-- Every run of a body registered for `f` relates its entry and result states. -/
def FunKeeps (K : Keeper E) (f : FunName) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    ∀ fuel s r n, E.run fuel s body = some (r, n) → K.rel s r.st

theorem assign_globals_of_destLocal {structs : StructContext}
    {locals globals locals' globals' : VarName → Option (PanValue Word)}
    {destination : Option (VarKind × VarName)} {values : List (PanValue Word)}
    (hdest : destLocal destination = true)
    (h : assignPanValueCallResult locals globals destination values (structs := structs) =
      some (locals', globals')) : globals' = globals := by
  unfold assignPanValueCallResult at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
    · simp at h
  · simp [destLocal] at hdest
  · simp at h

/-- A call to a kept function, with a kept handler and a non-global destination. -/
theorem callSteps_keeps (K : Keeper E) {f : FunName}
    {info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word))}
    (hf : FunKeeps K f)
    (hdest : ∀ destination handlerInfo, info = some (destination, handlerInfo) →
      destLocal destination = true)
    (fuel : Nat)
    (hh : ∀ destination exception handlerVar handlerProgram,
      info = some (destination, some (exception, handlerVar, handlerProgram)) →
      ∀ s r n, E.run (fuel - 1) s handlerProgram = some (r, n) → K.rel s r.st)
    (s : St σ) (arguments : List (Exp Word)) (preserve : Bool) (r : Result σ) (n : Nat)
    (hrun : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
      E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi info f
      arguments (memoryAccess := E.memoryAccess) (contracts := E.contracts)
      (memoryHandler := E.memoryHandler) (preserveReturnLocals := preserve) = some (r, n)) :
    K.rel s r.st := by
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
      exact K.refl s
    | some argumentPair =>
      obtain ⟨values, argumentSteps⟩ := argumentPair
      rw [hargs] at hrun
      simp only [Option.elim_some] at hrun
      cases htarget : panValueCallTarget E.structs E.contracts f E.functions values with
      | none =>
        rw [htarget] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact K.refl s
      | some callTarget =>
        obtain ⟨body, calleeLocals⟩ := callTarget
        rw [htarget] at hrun
        simp only [Option.elim_some] at hrun
        have hbodyKeeps : ∀ fuel s r n, E.run fuel s body = some (r, n) → K.rel s r.st := by
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
          have hrel : K.rel s rb.st :=
            K.left_locals s.locals
              (hbodyKeeps fuel ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb nb hbody)
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases rb with
          | returned l g m ffi returned =>
            simp only at hrun
            split at hrun
            · cases info with
              | none =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                exact K.right_locals _ hrel
              | some pair =>
                obtain ⟨destination, handlerInfo⟩ := pair
                simp only at hrun
                cases hassign : assignPanValueCallResult s.locals g destination returned
                    (structs := E.structs) with
                | none => rw [hassign] at hrun; simp at hrun
                | some assigned =>
                  obtain ⟨locals', globals'⟩ := assigned
                  rw [hassign] at hrun
                  simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                    Prod.mk.injEq] at hrun
                  obtain ⟨rfl, -⟩ := hrun
                  have hg := assign_globals_of_destLocal (hdest _ _ rfl) hassign
                  subst hg
                  exact K.right_locals _ hrel
            · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact K.right_locals _ hrel
          | raised l g m ffi exception value =>
            simp only at hrun
            split at hrun
            · cases info with
              | none =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                exact K.right_locals _ hrel
              | some pair =>
                obtain ⟨destination, handlerInfo⟩ := pair
                cases handlerInfo with
                | none =>
                  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                  obtain ⟨rfl, -⟩ := hrun
                  exact K.right_locals _ hrel
                | some triple =>
                  obtain ⟨caught, handlerVar, handlerProgram⟩ := triple
                  simp only at hrun
                  split at hrun
                  · split at hrun
                    · cases hhandler : evalPanValueFfiProgSteps E.context E.primitive E.handler
                          E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                          (updatePanValueMap s.locals handlerVar value) g m ffi
                          handlerProgram (memoryAccess := E.memoryAccess)
                          (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
                      | none => rw [hhandler] at hrun; simp at hrun
                      | some handlerPair =>
                        obtain ⟨rh, nh⟩ := handlerPair
                        rw [hhandler] at hrun
                        simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                          Prod.mk.injEq] at hrun
                        obtain ⟨rfl, -⟩ := hrun
                        have hrh := hh destination caught handlerVar handlerProgram rfl
                          ⟨updatePanValueMap s.locals handlerVar value, g, m, ffi⟩ rh nh hhandler
                        exact K.trans (K.right_locals _ hrel) hrh
                    · simp at hrun
                  · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨rfl, -⟩ := hrun
                    exact K.right_locals _ hrel
            · simp at hrun
          | _ =>
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact K.right_locals _ hrel

theorem st_restore (name : VarName) (old : Option (PanValue Word)) (r : Result σ) :
    ∃ l, (restorePanValueFfiLocal name old r).st = ⟨l, r.st.globals, r.st.memory, r.st.ffi⟩ := by
  cases r <;> exact ⟨_, rfl⟩

/-- `keepWith` programs with kept callees relate every result state to the entry state. -/
theorem keepWith_sound (K : Keeper E) (callee : FunName → Bool)
    (hcallee : ∀ f, callee f = true → FunKeeps K f) :
    ∀ (fuel : Nat) (p : Prog Word) (s : St σ) (r : Result σ) (n : Nat),
      keepWith K.allow callee p = true → E.run fuel s p = some (r, n) → K.rel s r.st := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel sih =>
  cases fuel with
  | zero =>
    intro p s r n _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    have ih := sih fuel (Nat.lt_succ_self fuel)
    intro p s r n hs hrun0
    have hrun := hrun0
    simp only [Env.run] at hrun
    cases p with
    | seq first second =>
      simp only [keepWith, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases h₁ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi first (memoryAccess := E.memoryAccess) (contracts := E.contracts)
          (memoryHandler := E.memoryHandler) with
      | none => rw [h₁] at hrun; simp at hrun
      | some pair =>
        obtain ⟨r₁, n₁⟩ := pair
        rw [h₁] at hrun
        have p₁ := ih first s r₁ n₁ hs.1 h₁
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
            exact K.trans p₁ (ih second ⟨l, g, m, f⟩ r₂ n₂ hs.2 h₂)
        | _ =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact p₁
    | ite condition thenBranch elseBranch =>
      simp only [keepWith, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact K.refl s
      | some pair =>
        obtain ⟨c, k⟩ := pair
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
            exact ih thenBranch s rb nb hs.1 hb
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
            exact ih elseBranch s rb nb hs.2 hb
    | dec name shape value body =>
      simp only [keepWith] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory value E.memoryAccess shape with
      | none =>
        rw [hacc] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact K.refl s
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
          have pb := ih body ⟨updatePanValueMap s.locals name accepted.1, s.globals, s.memory,
            s.ffi⟩ rb nb hs hb
          obtain ⟨l, hl⟩ := st_restore name (s.locals name) rb
          rw [hl]
          exact K.right_locals _ (K.left_locals s.locals pb)
    | «while» condition body =>
      have hsb : keepWith K.allow callee body = true := by simpa only [keepWith] using hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact K.refl s
      | some pair =>
        obtain ⟨c, k⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hc : (c == 0) = true
        · rw [if_pos hc] at hrun
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact K.refl s
        · rw [if_neg hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi body (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            have pb := ih body s rb nb hsb hb
            have again : ∀ l g m f, K.rel s ⟨l, g, m, f⟩ → (do
                  let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                    E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord
                    fuel l g m f (.while condition body) (memoryAccess := E.memoryAccess)
                    (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                  pure (loopResult, k + nb + loopSteps + 1)) = some (r, n) →
                K.rel s r.st := by
              intro l g m f hrel hrun
              cases hl : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                  E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f
                  (.while condition body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
              | none => rw [hl] at hrun; simp at hrun
              | some pair =>
                obtain ⟨rl, nl⟩ := pair
                rw [hl] at hrun
                simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                  Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                exact K.trans hrel (ih (.while condition body) ⟨l, g, m, f⟩ rl nl hs hl)
            cases rb with
            | normal l g m f => exact again l g m f pb hrun
            | continued l g m f => exact again l g m f pb hrun
            | broke l g m f =>
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact pb
            | _ =>
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact pb
    | call info f arguments =>
      have hparts : callee f = true ∧
          (∀ destination handlerInfo, info = some (destination, handlerInfo) →
            destLocal destination = true) ∧
          (∀ destination exception handlerVar handlerProgram,
            info = some (destination, some (exception, handlerVar, handlerProgram)) →
            keepWith K.allow callee handlerProgram = true) := by
        cases info with
        | none =>
          exact ⟨by simpa only [keepWith] using hs, fun _ _ h => (by cases h),
            fun _ _ _ _ h => (by cases h)⟩
        | some pair =>
          obtain ⟨destination, handlerInfo⟩ := pair
          cases handlerInfo with
          | none =>
            simp only [keepWith, Bool.and_eq_true] at hs
            refine ⟨hs.1, fun _ _ h => ?_, fun _ _ _ _ h => (by cases h)⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]; exact hs.2
          | some triple =>
            obtain ⟨exception, handlerVar, handlerProgram⟩ := triple
            simp only [keepWith, Bool.and_eq_true] at hs
            refine ⟨hs.1.1, fun _ _ h => ?_, fun _ _ _ _ h => ?_⟩
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              rw [← h.1]; exact hs.1.2
            · simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨-, h2⟩ := h
              obtain ⟨-, -, rfl⟩ := h2
              exact hs.2
      obtain ⟨hf, hdest, hhandler⟩ := hparts
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi info f arguments (memoryAccess := E.memoryAccess)
          (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
      | none => rw [hcall] at hrun; simp at hrun
      | some pair =>
        obtain ⟨rc, nc⟩ := pair
        rw [hcall] at hrun
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        refine callSteps_keeps K (hcallee f hf) hdest fuel ?_ s arguments false rc nc hcall
        intro destination exception handlerVar handlerProgram hinfo s' r' n' hrun'
        cases fuel with
        | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun'
        | succ k =>
          exact sih k (by omega) handlerProgram s' r' n'
            (hhandler destination exception handlerVar handlerProgram hinfo) hrun'
    | decCall name shape f arguments body =>
      simp only [keepWith, Bool.and_eq_true] at hs
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
        have hrc : K.rel s rc.st :=
          callSteps_keeps K (info := none) (hcallee f hs.1) (fun _ _ h => (by cases h)) fuel
            (fun _ _ _ _ h => (by cases h)) s arguments true rc nc hcall
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
              have pb := ih body ⟨updatePanValueMap s.locals name value, g, m, ffi⟩ rb nb hs.2 hb
              obtain ⟨l, hl⟩ := st_restore name (s.locals name) rb
              rw [hl]
              exact K.right_locals _ (K.trans (K.right_locals _ hrc) pb)
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact K.right_locals _ hrc
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact K.right_locals _ hrc
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact K.right_locals _ hrc
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact K.right_locals _ hrc
        · simp at hrun
    | skip => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | tick => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | annot key text => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | «break» => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | «continue» => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | «return» value => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | raise exception value => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | assign kind name value => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | primitive name operator arguments =>
      exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | store address value => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | store32 address value => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | storeByte address value => exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | shMemLoad size kind name address =>
      exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | shMemStore size address value =>
      exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0
    | extCall function configuration configurationLength array arrayLength =>
      exact K.leaf _ _ s r n (by simpa only [keepWith] using hs) hrun0

/-- A function accepted by `keepFn` is kept. -/
theorem keepFn_sound (K : Keeper E) {decls : List (Decl Word)}
    (hfrom : FunctionsFrom E.functions decls) :
    ∀ (depth : Nat) (f : FunName), keepFn K.allow decls depth f = true → FunKeeps K f := by
  intro depth
  induction depth with
  | zero => intro f h; simp [keepFn] at h
  | succ depth ih =>
    intro f h parameters body hlookup fuel s r n hrun
    obtain ⟨d, hmem, hname, hbody, -⟩ := hfrom f parameters body (lookupPanFunction_mem hlookup)
    simp only [keepFn, List.all_eq_true] at h
    have hd := h _ hmem
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hd
    rcases hd with hd | hd
    · exact absurd hname hd
    · rw [← hbody] at hrun
      exact keepWith_sound K (keepFn K.allow decls depth) ih fuel d.body s r n hd hrun

end InitECandidate.Solver.GuestBound
