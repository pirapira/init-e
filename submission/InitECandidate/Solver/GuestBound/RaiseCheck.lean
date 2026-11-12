import InitECandidate.Solver.GuestBound.SepArena

/-!
# Which exceptions a function can raise

`raiseFn A decls depth f` is a syntactic check: every `raise` in `f` and in the
functions it calls (to the given depth) has an exception accepted by `A`, and
no call has a handler. `raiseFn_sound` turns it into `FunRaises E A f`: every
raised result of `f` carries an exception accepted by `A`.

`WPr.while` is the loop rule for `WPr`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A loop whose body keeps an invariant, breaks, or leaves with `Q`. -/
theorem WPr.while {I : St σ → Prop} {c : Exp Word} {body : Prog Word} (hinit : I s)
    (hbody : ∀ a, I a → CondTrue E a c → WPr E a body (fun r => match r with
      | .normal l g m f | .continued l g m f => I ⟨l, g, m, f⟩
      | .broke l g m f => Q (.normal l g m f)
      | r => Q r))
    (hexit : ∀ a k, I a → E.cond a c = some (0, k) →
      Q (.normal a.locals a.globals a.memory a.ffi)) :
    WPr E s (.while c body) Q := by
  intro r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  refine while_inv (I := I) (Q := fun r => r.isError = true ∨ Q r)
    (fun r hr => Or.inl hr) (fun a k hI hc => Or.inr (hexit a k hI hc)) ?_
    fuel s r n hinit hrun
  intro fuel' a r' n' hI hct hrun'
  rcases hbody a hI hct r' (Runs.of_run hrun') with he | hpost
  · cases r' with
    | error l g m f => exact Or.inl rfl
    | _ => cases he
  · cases r' with
    | normal l g m f => exact hpost
    | continued l g m f => exact hpost
    | broke l g m f => exact Or.inr hpost
    | _ => exact Or.inr hpost

/-- A raised result carries an exception accepted by `A`. -/
def RaiseIn (A : ExceptionId → Bool) : Result σ → Prop
  | .raised _ _ _ _ e _ => A e = true
  | _ => True

theorem RaiseIn.restore {A : ExceptionId → Bool} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : RaiseIn A r) : RaiseIn A (restorePanValueFfiLocal x old r) := by
  cases r <;> exact h

/-- The result is not `.raised`. -/
def _root_.Flapjack.PanValueFfiControlResult.notRaised {σ : Type} : Result σ → Bool
  | .raised _ _ _ _ _ _ => false
  | _ => true

/-- Statements without sub-statements that never raise. -/
def calmLeaf : Prog Word → Bool
  | .skip | .tick | .annot _ _ | .break | .continue | .return _ | .assign _ _ _
  | .primitive _ _ _ | .store _ _ | .store32 _ _ | .storeByte _ _ | .shMemStore _ _ _
  | .extCall _ _ _ _ _ => true
  | _ => false

set_option hygiene false in
local macro "calm_leaf" helper:ident : tactic => `(tactic| (
  rw [evalPanValueFfiProgSteps] at hrun
  simp only [$helper:ident] at hrun
  repeat' split at hrun
  all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
  all_goals (obtain ⟨rfl, -⟩ := hrun)
  all_goals rfl))

set_option hygiene false in
local macro "calm_same" : tactic => `(tactic| (
  simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  rfl))

theorem calmLeaf_sound (p : Prog Word) (hp : calmLeaf p = true) (fuel : Nat) (s : St σ)
    (r : Result σ) (n : Nat) (hrun : E.run fuel s p = some (r, n)) : r.notRaised = true := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
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
    | primitive name operator arguments => calm_leaf panValuePrimitiveResult
    | store address value => calm_leaf panValueStoreResult
    | store32 address value => calm_leaf panValueStore32Result
    | storeByte address value => calm_leaf panValueStoreByteResult
    | shMemStore size address value => calm_leaf panValueShMemStoreResult
    | assign kind name value =>
      cases kind with
      | «local» => calm_leaf panValueAssignLocalResult
      | global => calm_leaf panValueAssignGlobalResult
    | extCall f a b c d =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueFfiExtCallSteps] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq, Option.pure_def,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun))
      all_goals first
        | (obtain ⟨rfl, -⟩ := hrun; rfl)
        | (obtain ⟨_, _, rfl, -⟩ := hrun; rfl)
    | _ => simp [calmLeaf] at hp

theorem calmLeaf_wpr {A : ExceptionId → Bool} {p : Prog Word} (hp : calmLeaf p = true)
    (s : St σ) : WPr E s p (RaiseIn A) := by
  rintro r ⟨fuel, n, hrun⟩
  have h := calmLeaf_sound p hp fuel s r n hrun
  cases r <;> first | exact Or.inr trivial | cases h

/-- Every `raise` is accepted by `A`, calls go to functions accepted by
`callee`, and no call has a handler. -/
def raiseOk (A : ExceptionId → Bool) (callee : FunName → Bool) : Prog Word → Bool
  | .seq a b => raiseOk A callee a && raiseOk A callee b
  | .ite _ a b => raiseOk A callee a && raiseOk A callee b
  | .while _ b => raiseOk A callee b
  | .dec _ _ _ b => raiseOk A callee b
  | .raise e _ => A e
  | .call none f _ => callee f
  | .call (some (_, none)) f _ => callee f
  | .call (some (_, some _)) _ _ => false
  | .decCall _ _ f _ b => callee f && raiseOk A callee b
  | p => calmLeaf p

/-- `raiseOk` for the body of `f`, with callees checked to depth `depth`. -/
def raiseFn (A : ExceptionId → Bool) (decls : List (Decl Word)) : Nat → FunName → Bool
  | 0, _ => false
  | depth + 1, f =>
      decls.all fun decl =>
        match decl with
        | .function d => d.name != f || raiseOk A (raiseFn A decls depth) d.body
        | _ => true

/-- Every raised result of a body registered for `f` is accepted by `A`. -/
def FunRaises (E : Env σ) (A : ExceptionId → Bool) (f : FunName) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    ∀ s, WPr E s body (RaiseIn A)

theorem raise_call {A : ExceptionId → Bool} {f : FunName}
    (destination : Option (Option (VarKind × VarName))) {args : List (Exp Word)}
    (hf : FunRaises E A f) (s : St σ) :
    WPr E s (.call (destination.map fun dest => (dest, none)) f args) (RaiseIn A) := by
  intro r hr
  rcases runs_call_inv destination hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl herr
  have hcal := hf parameters body hlookup _ rb hcallee
  cases rb with
  | returned lr g m ffi vs =>
    simp only [CallOutcome] at hout
    cases destination with
    | none =>
      rcases hout with herr | ⟨l, rfl⟩
      · exact Or.inl herr
      · exact Or.inr trivial
    | some dest =>
      rcases hout with herr | ⟨l', g', -, rfl⟩
      · exact Or.inl herr
      · exact Or.inr trivial
  | raised lr g m ffi ex v =>
    simp only [CallOutcome] at hout
    subst hout
    rcases hcal with he | hq
    · cases he
    · exact Or.inr hq
  | finalFfi lr g m ffi ev =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inr trivial
  | _ =>
    simp only [CallOutcome] at hout
    exact Or.inl hout

theorem raiseOk_sound {A : ExceptionId → Bool} {callee : FunName → Bool}
    (hcallee : ∀ f, callee f = true → FunRaises E A f) :
    ∀ (p : Prog Word), raiseOk A callee p = true → ∀ s : St σ, WPr E s p (RaiseIn A)
  | .seq a b, hp, s => by
      simp only [raiseOk, Bool.and_eq_true] at hp
      refine WPr.seq (fun _ => True)
        (WPr.conseq (raiseOk_sound hcallee a hp.1 s) (fun r hr => ?_))
        (fun s' _ => raiseOk_sound hcallee b hp.2 s')
      cases r <;> trivial
  | .ite _ a b, hp, s => by
      simp only [raiseOk, Bool.and_eq_true] at hp
      refine WPr.ite_both (fun w _ => ?_)
      split
      · exact raiseOk_sound hcallee b hp.2 s
      · exact raiseOk_sound hcallee a hp.1 s
  | .while _ b, hp, s => by
      simp only [raiseOk] at hp
      refine WPr.while (I := fun _ => True) trivial
        (fun a _ _ => WPr.conseq (raiseOk_sound hcallee b hp a) (fun r hr => ?_))
        (fun _ _ _ _ => trivial)
      cases r <;> trivial
  | .dec _ _ _ b, hp, s => by
      simp only [raiseOk] at hp
      exact WPr.dec_ev (fun v _ => WPr.conseq (Q' := RaiseIn A) (raiseOk_sound hcallee b hp _)
        (fun _ hr => RaiseIn.restore hr))
  | .raise e _, hp, s => by
      simp only [raiseOk] at hp
      exact WPr.raise (fun v _ => hp)
  | .call none f _, hp, s => by
      simp only [raiseOk] at hp
      exact raise_call none (hcallee f hp) s
  | .call (some (d, none)) f _, hp, s => by
      simp only [raiseOk] at hp
      exact raise_call (some d) (hcallee f hp) s
  | .call (some (_, some _)) _ _, hp, _ => by simp [raiseOk] at hp
  | .decCall x sh f args b, hp, s => by
      simp only [raiseOk, Bool.and_eq_true] at hp
      refine WPr.decCall_spec (RaiseIn A) (fun parameters cbody _ _ hlk _ _ =>
        hcallee f hp.1 parameters cbody hlk _)
        (fun _ _ _ _ _ _ => WPr.conseq (Q' := RaiseIn A) (raiseOk_sound hcallee b hp.2 _)
          (fun _ hr => RaiseIn.restore hr))
        (fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ => trivial)
  | .skip, _, s => calmLeaf_wpr rfl s
  | .tick, _, s => calmLeaf_wpr rfl s
  | .annot _ _, _, s => calmLeaf_wpr rfl s
  | .break, _, s => calmLeaf_wpr rfl s
  | .continue, _, s => calmLeaf_wpr rfl s
  | .return _, _, s => calmLeaf_wpr rfl s
  | .assign _ _ _, _, s => calmLeaf_wpr rfl s
  | .primitive _ _ _, _, s => calmLeaf_wpr rfl s
  | .store _ _, _, s => calmLeaf_wpr rfl s
  | .store32 _ _, _, s => calmLeaf_wpr rfl s
  | .storeByte _ _, _, s => calmLeaf_wpr rfl s
  | .shMemStore _ _ _, _, s => calmLeaf_wpr rfl s
  | .extCall _ _ _ _ _, _, s => calmLeaf_wpr rfl s
  | .shMemLoad _ _ _ _, hp, _ => by simp [raiseOk, calmLeaf] at hp

theorem raiseFn_sound (A : ExceptionId → Bool) {decls : List (Decl Word)}
    (hfrom : FunctionsFrom E.functions decls) :
    ∀ (depth : Nat) (f : FunName), raiseFn A decls depth f = true → FunRaises E A f := by
  intro depth
  induction depth with
  | zero => intro f h; simp [raiseFn] at h
  | succ depth ih =>
    intro f h parameters body hlookup s
    obtain ⟨d, hmem, hname, hbody, -⟩ := hfrom f parameters body (lookupPanFunction_mem hlookup)
    simp only [raiseFn, List.all_eq_true] at h
    have hd := h _ hmem
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hd
    rcases hd with hd | hd
    · exact absurd hname hd
    · rw [← hbody]
      exact raiseOk_sound ih d.body hd s

/-- `memcpy` never raises. -/
theorem memcpy_raises (hE : GuestEnv E) : FunRaises E (fun _ => false) "memcpy" :=
  raiseFn_sound _ hE.functions 1 "memcpy"
    (show raiseFn (fun _ => false) Guest.Software.guestAst 1 "memcpy" = true by decide +kernel)

end InitECandidate.Solver.GuestBound
