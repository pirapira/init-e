import InitECandidate.Solver.GuestBound.Decls

/-!
# Calm programs

A program is calm when no run of it ends in an uncaught exception or a final
foreign call: nothing in its call tree raises, calls the host, or touches
shared memory. `calmFn decls depth f` checks this for a declared function by
following calls up to `depth` levels into the declaration list.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The result is neither `raised` nor `finalFfi`. -/
def _root_.Flapjack.PanValueFfiControlResult.isCalm {σ : Type} : Result σ → Bool
  | .raised _ _ _ _ _ _ | .finalFfi _ _ _ _ _ => false
  | _ => true

/-- No statement raises, calls the host or touches shared memory, and every
callee satisfies `callee`. -/
def calmWith (callee : FunName → Bool) : Prog Word → Bool
  | .skip | .tick | .annot _ _ | .break | .continue | .return _ | .assign _ _ _
  | .store _ _ | .store32 _ _ | .storeByte _ _ | .primitive _ _ _ => true
  | .seq first second => calmWith callee first && calmWith callee second
  | .ite _ thenBranch elseBranch => calmWith callee thenBranch && calmWith callee elseBranch
  | .while _ body => calmWith callee body
  | .dec _ _ _ body => calmWith callee body
  | .call (some (_, some (_, _, handlerProgram))) f _ =>
      callee f && calmWith callee handlerProgram
  | .call _ f _ => callee f
  | .decCall _ _ f _ body => callee f && calmWith callee body
  | _ => false

/-- Every declaration named `f` has a calm body, following calls `depth` levels deep. -/
def calmFn (decls : List (Decl Word)) : Nat → FunName → Bool
  | 0, _ => false
  | depth + 1, f =>
      decls.all fun decl =>
        match decl with
        | .function d => d.name != f || calmWith (calmFn decls depth) d.body
        | _ => true

/-- No run of a body registered for `f` ends raised or in a final foreign call. -/
def FunCalm (E : Env σ) (f : FunName) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    ∀ fuel s r n, E.run fuel s body = some (r, n) → r.isCalm = true

/-- A call to a calm function, with a calm handler, has a calm result. -/
theorem callSteps_calm {f : FunName}
    {info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word))}
    (hf : FunCalm E f) (fuel : Nat) (s : St σ) (arguments : List (Exp Word)) (preserve : Bool)
    (r : Result σ) (n : Nat)
    (hrun : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
      E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi info f
      arguments (memoryAccess := E.memoryAccess) (contracts := E.contracts)
      (memoryHandler := E.memoryHandler) (preserveReturnLocals := preserve) = some (r, n)) :
    r.isCalm = true := by
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
      rfl
    | some argumentPair =>
      obtain ⟨values, argumentSteps⟩ := argumentPair
      rw [hargs] at hrun
      simp only [Option.elim_some] at hrun
      cases htarget : panValueCallTarget E.structs E.contracts f E.functions values with
      | none =>
        rw [htarget] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rfl
      | some callTarget =>
        obtain ⟨body, calleeLocals⟩ := callTarget
        rw [htarget] at hrun
        simp only [Option.elim_some] at hrun
        have hbodyCalm : ∀ fuel s r n, E.run fuel s body = some (r, n) → r.isCalm = true := by
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
          have hcalm := hbodyCalm fuel ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb nb hbody
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases rb with
          | raised l g m ffi exception value => cases hcalm
          | finalFfi l g m ffi event => cases hcalm
          | returned l g m ffi returned =>
            simp only at hrun
            split at hrun
            · cases info with
              | none =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                rfl
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
                  obtain ⟨rfl, -⟩ := hrun
                  rfl
            · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              rfl
          | _ =>
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            rfl

set_option hygiene false in
/-- Finish a leaf none of whose outcomes is `raised` or `finalFfi`. -/
local macro "calm_leaf" helper:ident : tactic => `(tactic| (
  rw [evalPanValueFfiProgSteps] at hrun
  simp only [$helper:ident] at hrun
  repeat' split at hrun
  all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
  all_goals (obtain ⟨rfl, -⟩ := hrun)
  all_goals rfl))

set_option hygiene false in
/-- Finish a one-step leaf. -/
local macro "calm_same" : tactic => `(tactic| (
  simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  rfl))

/-- A calm program with calm callees has only calm results. -/
theorem calmWith_sound (callee : FunName → Bool)
    (hcallee : ∀ f, callee f = true → FunCalm E f) :
    ∀ (fuel : Nat) (p : Prog Word) (s : St σ) (r : Result σ) (n : Nat),
      calmWith callee p = true → E.run fuel s p = some (r, n) → r.isCalm = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro p s r n _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro p s r n hs hrun
    simp only [Env.run] at hrun
    cases p with
    | skip =>
      simp only [evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      rfl
    | tick => calm_same
    | annot key text => calm_same
    | «break» => calm_same
    | «continue» => calm_same
    | «return» value => calm_leaf panValueReturnResult
    | assign kind name value =>
      cases kind with
      | global => calm_leaf panValueAssignGlobalResult
      | «local» => calm_leaf panValueAssignLocalResult
    | store address value => calm_leaf panValueStoreResult
    | store32 address value => calm_leaf panValueStore32Result
    | storeByte address value => calm_leaf panValueStoreByteResult
    | primitive name operator arguments => calm_leaf panValuePrimitiveResult
    | seq first second =>
      simp only [calmWith, Bool.and_eq_true] at hs
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
            exact ih second ⟨l, g, m, f⟩ r₂ n₂ hs.2 h₂
        | _ =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact p₁
    | ite condition thenBranch elseBranch =>
      simp only [calmWith, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rfl
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
      simp only [calmWith] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory value E.memoryAccess shape with
      | none =>
        rw [hacc] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rfl
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
          cases rb <;> first | rfl | exact pb
    | «while» condition body =>
      have hsb : calmWith callee body = true := by simpa only [calmWith] using hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rfl
      | some pair =>
        obtain ⟨c, k⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hc : (c == 0) = true
        · rw [if_pos hc] at hrun
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          rfl
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
            have again : ∀ l g m f, (do
                  let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                    E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord
                    fuel l g m f (.while condition body) (memoryAccess := E.memoryAccess)
                    (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                  pure (loopResult, k + nb + loopSteps + 1)) = some (r, n) →
                r.isCalm = true := by
              intro l g m f hrun
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
                exact ih (.while condition body) ⟨l, g, m, f⟩ rl nl hs hl
            cases rb with
            | normal l g m f => exact again l g m f hrun
            | continued l g m f => exact again l g m f hrun
            | broke l g m f =>
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              rfl
            | _ =>
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact pb
    | call info f arguments =>
      have hf : FunCalm E f := by
        cases info with
        | none => exact hcallee f (by simpa only [calmWith] using hs)
        | some pair =>
          obtain ⟨destination, handlerInfo⟩ := pair
          cases handlerInfo with
          | none => exact hcallee f (by simpa only [calmWith] using hs)
          | some triple =>
            obtain ⟨exception, handlerVar, handlerProgram⟩ := triple
            simp only [calmWith, Bool.and_eq_true] at hs
            exact hcallee f hs.1
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
        exact callSteps_calm hf fuel s arguments false rc nc hcall
    | decCall name shape f arguments body =>
      simp only [calmWith, Bool.and_eq_true] at hs
      have hf : FunCalm E f := hcallee f hs.1
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
        have hcalm := callSteps_calm hf fuel s arguments true rc nc hcall
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
              cases rb <;> first | rfl | exact pb
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            rfl
        · cases hcalm
        · cases hcalm
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          rfl
        · simp at hrun
    | _ => simp [calmWith] at hs

/-- A function accepted by `calmFn` is calm. -/
theorem calmFn_sound {decls : List (Decl Word)} (hfrom : FunctionsFrom E.functions decls) :
    ∀ (depth : Nat) (f : FunName), calmFn decls depth f = true → FunCalm E f := by
  intro depth
  induction depth with
  | zero => intro f h; simp [calmFn] at h
  | succ depth ih =>
    intro f h parameters body hlookup fuel s r n hrun
    obtain ⟨d, hmem, hname, hbody, -⟩ := hfrom f parameters body (lookupPanFunction_mem hlookup)
    simp only [calmFn, List.all_eq_true] at h
    have hd := h _ hmem
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hd
    rcases hd with hd | hd
    · exact absurd hname hd
    · rw [← hbody] at hrun
      exact calmWith_sound (calmFn decls depth) ih fuel d.body s r n hd hrun

end InitECandidate.Solver.GuestBound
