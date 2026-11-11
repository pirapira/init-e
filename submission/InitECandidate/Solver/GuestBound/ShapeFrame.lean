import InitECandidate.Solver.GuestBound.CallInv
import InitECandidate.Solver.GuestBound.Keepers

/-!
# Frame analysis keeping the shapes of locals

`shapeOk callee M` accepts statements (including nested loops and calls that
assign their result) which change nothing but the locals in `M`. Assignments
in Pancake keep the shape of the assigned variable, so after such a statement
every local still has the shape it had before. This is what bounds the number
of distinct loop-head states of a loop over struct-valued locals.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Equal, or both present with the same shape. -/
def SameShape (structs : StructContext) (a b : Option (PanValue Word)) : Prop :=
  a = b ∨ ∃ va vb, a = some va ∧ b = some vb ∧
    panValueShape structs va = panValueShape structs vb

theorem SameShape.refl {structs : StructContext} (a : Option (PanValue Word)) :
    SameShape structs a a := Or.inl rfl

theorem SameShape.trans {structs : StructContext} {a b c : Option (PanValue Word)}
    (h₁ : SameShape structs a b) (h₂ : SameShape structs b c) : SameShape structs a c := by
  rcases h₁ with rfl | ⟨va, vb, rfl, rfl, hab⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨vb', vc, hb, rfl, hbc⟩
    · exact Or.inr ⟨va, vb, rfl, rfl, hab⟩
    · simp only [Option.some.injEq] at hb
      subst hb
      exact Or.inr ⟨va, vc, rfl, rfl, hab.trans hbc⟩

/-- Only the locals in `M` changed, and every local kept its shape. -/
def ShapeFrame (E : Env σ) (M : List VarName) (s : St σ)
    (l g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) : Prop :=
  g = s.globals ∧ m = s.memory ∧ f = s.ffi ∧ (∀ x, x ∉ M → l x = s.locals x) ∧
    ∀ x, SameShape E.structs (l x) (s.locals x)

/-- `ShapeFrame` for the results that keep running. -/
def ShapePost (E : Env σ) (M : List VarName) (s : St σ) : Result σ → Prop
  | .normal l g m f | .continued l g m f | .broke l g m f => ShapeFrame E M s l g m f
  | _ => True

theorem ShapeFrame.refl (M : List VarName) (s : St σ) :
    ShapeFrame E M s s.locals s.globals s.memory s.ffi :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ => SameShape.refl _⟩

theorem ShapePost.of_error {M : List VarName} {s : St σ} {r : Result σ}
    (h : r.isError = true) : ShapePost E M s r := by
  cases r <;> first | trivial | cases h

theorem ShapePost.trans {M : List VarName} {s : St σ} {l g : VarName → Option (PanValue Word)}
    {mem : Word → Option (PanValue Word)} {f : FfiState σ} {r : Result σ}
    (h₁ : ShapeFrame E M s l g mem f) (h₂ : ShapePost E M ⟨l, g, mem, f⟩ r) :
    ShapePost E M s r := by
  obtain ⟨hg, hm, hf, hl, hv⟩ := h₁
  cases r <;> simp only [ShapePost] at h₂ ⊢
  all_goals
    obtain ⟨hg', hm', hf', hl', hv'⟩ := h₂
    exact ⟨hg'.trans hg, hm'.trans hm, hf'.trans hf, fun x hx => (hl' x hx).trans (hl x hx),
      fun x => (hv' x).trans (hv x)⟩

theorem ShapeFrame.restore {M : List VarName} {name : VarName} {s : St σ}
    {value : PanValue Word} {l g : VarName → Option (PanValue Word)}
    {mem : Word → Option (PanValue Word)} {f : FfiState σ}
    (h : ShapeFrame E (name :: M) ⟨updatePanValueMap s.locals name value, s.globals, s.memory,
      s.ffi⟩ l g mem f) :
    ShapeFrame E M s (restorePanValueLocal l name (s.locals name)) g mem f := by
  obtain ⟨hg, hm, hf, hl, hv⟩ := h
  refine ⟨hg, hm, hf, ?_, ?_⟩
  · intro x hx
    by_cases hxn : x = name
    · subst hxn
      simp [restorePanValueLocal]
    · have hxn' : (x == name) = false := by simpa using hxn
      simp only [restorePanValueLocal, hxn']
      rw [hl x (by simp [hxn, hx])]
      simp [updatePanValueMap, hxn']
  · intro x
    by_cases hxn : x = name
    · subst hxn
      simp only [restorePanValueLocal, beq_self_eq_true, if_true]
      exact SameShape.refl _
    · have hxn' : (x == name) = false := by simpa using hxn
      have := hv x
      simp only [updatePanValueMap, hxn', Bool.false_eq_true, if_false] at this
      simpa only [restorePanValueLocal, hxn', Bool.false_eq_true, if_false] using this

theorem ShapePost.restore {M : List VarName} {name : VarName} {s : St σ} {value : PanValue Word}
    {r : Result σ}
    (h : ShapePost E (name :: M) ⟨updatePanValueMap s.locals name value, s.globals, s.memory,
      s.ffi⟩ r) :
    ShapePost E M s (restorePanValueFfiLocal name (s.locals name) r) := by
  cases r <;> simp only [ShapePost, restorePanValueFfiLocal] at h ⊢
  all_goals exact ShapeFrame.restore h

/-- A valid assignment keeps the shape. -/
theorem assignValid_shape {structs : StructContext}
    {locals globals : VarName → Option (PanValue Word)} {name : VarName} {value : PanValue Word}
    (h : panValueAssignmentValid structs locals globals .local name value = true) :
    ∃ old, locals name = some old ∧ panValueShape structs value = panValueShape structs old := by
  unfold panValueAssignmentValid at h
  simp only at h
  split at h
  · rename_i old hold
    exact ⟨old, hold, (panShapeMatches_eq_true _ _).mp h⟩
  · cases h

theorem update_frame {structs : StructContext} {M : List VarName}
    {locals globals : VarName → Option (PanValue Word)} {name : VarName} {value : PanValue Word}
    (hmem : name ∈ M)
    (h : panValueAssignmentValid structs locals globals .local name value = true) :
    (∀ x, x ∉ M → updatePanValueMap locals name value x = locals x) ∧
      ∀ x, SameShape structs (updatePanValueMap locals name value x) (locals x) := by
  obtain ⟨old, hold, hshape⟩ := assignValid_shape h
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx' : (x == name) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h => hx (h ▸ hmem)
    simp [updatePanValueMap, hx']
  · intro x
    by_cases hxn : x = name
    · subst hxn
      simp only [updatePanValueMap, beq_self_eq_true, if_true]
      exact Or.inr ⟨value, old, rfl, hold, hshape⟩
    · have hxn' : (x == name) = false := by simpa using hxn
      simp only [updatePanValueMap, hxn']
      exact SameShape.refl _

/-- The destination of a call is absent or a local in `M`. -/
def destIn (M : List VarName) : Option (VarKind × VarName) → Bool
  | none => true
  | some (.local, x) => M.contains x
  | some (.global, _) => false

theorem assignResult_frame {structs : StructContext} {M : List VarName}
    {locals g l' g' : VarName → Option (PanValue Word)} {d : Option (VarKind × VarName)}
    {values : List (PanValue Word)} (hd : destIn M d = true)
    (h : assignPanValueCallResult locals g d values (structs := structs) = some (l', g')) :
    g' = g ∧ (∀ x, x ∉ M → l' x = locals x) ∧ ∀ x, SameShape structs (l' x) (locals x) := by
  unfold assignPanValueCallResult at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ _ => rfl, fun _ => SameShape.refl _⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ _ => rfl, fun _ => SameShape.refl _⟩
  · split at h
    · rename_i name value hvalid
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hmem : name ∈ M := by simpa [destIn] using hd
      exact ⟨rfl, update_frame hmem hvalid⟩
    · simp at h
  · simp [destIn] at hd
  · simp at h

/-- No registered body of `f` returns to its caller. -/
def FunStops (E : Env σ) (f : FunName) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    ∀ fuel s r n, E.run fuel s body = some (r, n) → ∀ l g m ffi values,
      r ≠ .returned l g m ffi values

/-- Statements that change nothing but the locals in `M` (and locals they declare). -/
def shapeOk (callee : FunName → Bool) : List VarName → Prog Word → Bool
  | _, .skip | _, .tick | _, .annot _ _ | _, .break | _, .continue | _, .return _
  | _, .raise _ _ => true
  | M, .assign .local name _ => M.contains name
  | M, .seq first second => shapeOk callee M first && shapeOk callee M second
  | M, .ite _ thenBranch elseBranch => shapeOk callee M thenBranch && shapeOk callee M elseBranch
  | M, .while _ body => shapeOk callee M body
  | M, .dec name _ _ body => shapeOk callee (name :: M) body
  | _, .call none f _ => callee f
  | M, .call (some (destination, none)) f _ => callee f && destIn M destination
  | M, .decCall name _ f _ body => callee f && shapeOk callee (name :: M) body
  | _, _ => false

set_option hygiene false in
/-- Finish a leaf whose keep-running results leave the state alone. -/
local macro "shape_same" : tactic => `(tactic| (
  simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  exact ShapeFrame.refl _ _))

/-- `shapeOk` statements change only `M` and keep every local's shape. -/
theorem shape_sound (callee : FunName → Bool)
    (hcallee : ∀ f, callee f = true → FunKeeps (quietKeeper E) f ∨ FunStops E f) :
    ∀ (fuel : Nat) (M : List VarName) (p : Prog Word) (s : St σ) (r : Result σ) (n : Nat),
      shapeOk callee M p = true → E.run fuel s p = some (r, n) → ShapePost E M s r := by
  intro fuel
  induction fuel with
  | zero =>
    intro M p s r n _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro M p s r n hs hrun
    have hrun0 := hrun
    simp only [Env.run] at hrun
    cases p with
    | skip =>
      simp only [evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact ShapeFrame.refl _ _
    | tick => shape_same
    | annot key text => shape_same
    | «break» => shape_same
    | «continue» => shape_same
    | «return» value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueReturnResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [ShapePost])
    | raise exception value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueRaiseResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [ShapePost])
    | assign kind name value =>
      cases kind with
      | global => simp [shapeOk] at hs
      | «local» =>
        have hmem : name ∈ M := by simpa [shapeOk] using hs
        rw [evalPanValueFfiProgSteps] at hrun
        simp only [panValueAssignLocalResult, evalPanValueExpCounted] at hrun
        cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
            E.topAddress E.bytesInWord value E.memoryAccess with
        | none =>
          rw [hv] at hrun
          simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [ShapePost]
        | some evaluated =>
          rw [hv] at hrun
          simp only [Option.map_some] at hrun
          split at hrun
          · rename_i hvalid
            simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            obtain ⟨h1, h2⟩ := update_frame hmem hvalid
            exact ⟨rfl, rfl, rfl, h1, h2⟩
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            simp only [ShapePost]
    | seq first second =>
      simp only [shapeOk, Bool.and_eq_true] at hs
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
            exact ShapePost.trans p₁ (ih M second ⟨l, g, m, f⟩ r₂ n₂ hs.2 h₂)
        | _ =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact p₁
    | ite condition thenBranch elseBranch =>
      simp only [shapeOk, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [ShapePost]
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
      have hs' : shapeOk callee M body = true := by simpa only [shapeOk] using hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory c E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [ShapePost]
      | some pair =>
        obtain ⟨v, kc⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hv : (v == 0) = true
        · rw [if_pos hv] at hrun
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact ShapeFrame.refl _ _
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
            have again : ∀ l g mem f, ShapeFrame E M s l g mem f →
                (do
                  let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                    E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                    l g mem f (.while c body) (memoryAccess := E.memoryAccess)
                    (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                  pure (loopResult, kc + nb + loopSteps + 1)) = some (r, n) →
                ShapePost E M s r := by
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
                exact ShapePost.trans hfr (ih M (.while c body) ⟨l, g, mem, f⟩ rl nl hs hloop)
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
              simp only [ShapePost]
    | dec name shape value body =>
      simp only [shapeOk] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory value E.memoryAccess shape with
      | none =>
        rw [hacc] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [ShapePost]
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
          exact ShapePost.restore (ih (name :: M) body ⟨updatePanValueMap s.locals name
            accepted.1, s.globals, s.memory, s.ffi⟩ rb nb hs hb)
    | call info f arguments =>
      have hparts : ∃ destination : Option (Option (VarKind × VarName)),
          info = destination.map (fun dest => (dest, none)) ∧ callee f = true ∧
          ∀ d, destination = some d → destIn M d = true := by
        cases info with
        | none => exact ⟨none, rfl, by simpa only [shapeOk] using hs, fun _ h => by cases h⟩
        | some pair =>
          obtain ⟨destination, handlerInfo⟩ := pair
          cases handlerInfo with
          | some h => simp [shapeOk] at hs
          | none =>
            simp only [shapeOk, Bool.and_eq_true] at hs
            refine ⟨some destination, rfl, hs.1, ?_⟩
            intro d hd
            simp only [Option.some.injEq] at hd
            exact hd ▸ hs.2
      obtain ⟨destination, rfl, hf, hdest⟩ := hparts
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
          ⟨fuel', parameters, calleeBody, values, calleeLocals, rb, nb, hlookup, -, -, hcalleeRun,
            hout⟩
        · exact ShapePost.of_error herr
        rcases hcallee f hf with hquiet | hstop
        · have hq := hquiet parameters calleeBody hlookup fuel'
            ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb nb hcalleeRun
          cases rb with
          | returned l g m ffi values' =>
            obtain ⟨hg, hm, hffi⟩ := hq
            simp only [PanValueFfiControlResult.st] at hg hm hffi
            subst hg hm hffi
            simp only [CallOutcome] at hout
            cases destination with
            | none =>
              simp only at hout
              rcases hout with herr | ⟨l', rfl⟩
              · exact ShapePost.of_error herr
              · simp only [ShapePost]
            | some d =>
              simp only at hout
              rcases hout with herr | ⟨l', g', hassign, rfl⟩
              · exact ShapePost.of_error herr
              · obtain ⟨rfl, h1, h2⟩ := assignResult_frame (hdest d rfl) hassign
                exact ⟨rfl, rfl, rfl, h1, h2⟩
          | raised l g m ffi exception value =>
            simp only [CallOutcome] at hout
            subst hout
            simp only [ShapePost]
          | finalFfi l g m ffi event =>
            simp only [CallOutcome] at hout
            subst hout
            simp only [ShapePost]
          | _ =>
            simp only [CallOutcome] at hout
            exact ShapePost.of_error hout
        · have hnr := hstop parameters calleeBody hlookup fuel'
            ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb nb hcalleeRun
          cases rb with
          | returned l g m ffi values' => exact absurd rfl (hnr l g m ffi values')
          | raised l g m ffi exception value =>
            simp only [CallOutcome] at hout
            subst hout
            simp only [ShapePost]
          | finalFfi l g m ffi event =>
            simp only [CallOutcome] at hout
            subst hout
            simp only [ShapePost]
          | _ =>
            simp only [CallOutcome] at hout
            exact ShapePost.of_error hout
    | decCall name shape f arguments body =>
      simp only [shapeOk, Bool.and_eq_true] at hs
      obtain ⟨hf, hbodyOk⟩ := hs
      rcases hcallee f hf with hquiet | hstop
      rotate_left
      · rcases decCall_run_inv hrun0 with herr | ⟨fuel₁, parameters, calleeBody, values,
          calleeLocals, rb, nb, hlookup, -, -, hcalleeRun, hout⟩
        · exact ShapePost.of_error herr
        have hnr := hstop parameters calleeBody hlookup fuel₁
          ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb nb hcalleeRun
        cases rb with
        | returned l g m ffi values' => exact absurd rfl (hnr l g m ffi values')
        | raised l g m ffi exception value =>
          simp only at hout
          subst hout
          simp only [ShapePost]
        | finalFfi l g m ffi event =>
          simp only at hout
          subst hout
          simp only [ShapePost]
        | _ => exact hout.elim
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
        have hq := callSteps_keeps (quietKeeper E) (info := none) hquiet
          (fun _ _ h => (by cases h)) fuel (fun _ _ _ _ h => (by cases h)) s arguments true
          rc nc hcall
        simp only [Option.bind_eq_bind, Option.bind_some] at hrun
        split at hrun
        · split at hrun
          · rename_i returnedLocals g m ffi value _
            obtain ⟨hg, hm, hffi⟩ := hq
            simp only [PanValueFfiControlResult.st] at hg hm hffi
            subst hg hm hffi
            cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                (updatePanValueMap s.locals name value) s.globals s.memory s.ffi body
                (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                (memoryHandler := E.memoryHandler) with
            | none => rw [hb] at hrun; simp at hrun
            | some pair =>
              obtain ⟨rb, nb⟩ := pair
              rw [hb] at hrun
              simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact ShapePost.restore (ih (name :: M) body ⟨updatePanValueMap s.locals name
                value, s.globals, s.memory, s.ffi⟩ rb nb hbodyOk hb)
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            simp only [ShapePost]
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [ShapePost]
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [ShapePost]
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [ShapePost]
        · simp at hrun
    | _ => simp [shapeOk] at hs

end InitECandidate.Solver.GuestBound
