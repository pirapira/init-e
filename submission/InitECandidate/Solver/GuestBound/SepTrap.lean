import InitECandidate.Solver.GuestBound.SepRegion
import InitECandidate.Solver.GuestBound.ScratchRuns
import InitECandidate.Solver.GuestBound.NoReturn

/-!
# Traps, and the scratch allocator as a framed specification

A trap (`trap_with`) ends in a host call or raises `TrapErr`, which no handler
in the interpreter catches. `WPFt` is `WPFr` with such results exempt: nothing
is claimed about the state a trap leaves.

`scratch_alloc_framed` owns only the two arena pointers. The block it returns
lies inside the old free interval; the caller takes it out of its free-space
assertion with `Assn.owns_split`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The run was ended by a trap: a host call, or a raised `TrapErr`. -/
def Trap : Result σ → Prop
  | .finalFfi _ _ _ _ _ => True
  | .raised _ _ _ _ e _ => e = "TrapErr"
  | _ => False

/-- `.error`, or a trap. -/
def TrapOr : Result σ → Prop
  | .error _ _ _ _ => True
  | r => Trap r

/-- Not raised, or raised `TrapErr`. -/
def RaiseIsTrap : Result σ → Prop
  | .raised _ _ _ _ e _ => e = "TrapErr"
  | _ => True

theorem Trap.restore {x : VarName} {old : Option (PanValue Word)} {r : Result σ} (h : Trap r) :
    Trap (restorePanValueFfiLocal x old r) := by
  cases r <;> exact h

theorem RaiseIsTrap.restore {x : VarName} {old : Option (PanValue Word)} {r : Result σ}
    (h : RaiseIsTrap r) : RaiseIsTrap (restorePanValueFfiLocal x old r) := by
  cases r <;> exact h

/-- Normal, `.error` or a host call. -/
def _root_.Flapjack.PanValueFfiControlResult.calmOrHost {σ : Type} : Result σ → Bool
  | .normal _ _ _ _ | .error _ _ _ _ | .finalFfi _ _ _ _ _ => true
  | _ => false

theorem shMemStore_plain {fuel : Nat} {s : St σ} {size : OpSize} {a v : Exp Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.shMemStore size a v) = some (r, n)) :
    r.calmOrHost = true := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueShMemStoreResult] at h
    repeat' split at h
    all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at h))
    all_goals (obtain ⟨rfl, -⟩ := h)
    all_goals rfl

theorem extCall_plain {fuel : Nat} {s : St σ} {f : FunName} {a b c d : Exp Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.extCall f a b c d) = some (r, n)) :
    r.calmOrHost = true := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueFfiExtCallSteps] at h
    repeat' split at h
    all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq, Option.pure_def,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at h))
    all_goals first
      | (obtain ⟨rfl, -⟩ := h; rfl)
      | (obtain ⟨_, _, rfl, -⟩ := h; rfl)

theorem raise_trapOr {fuel : Nat} {s : St σ} {v : Exp Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.raise "TrapErr" v) = some (r, n)) :
    TrapOr r := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueRaiseResult] at h
    repeat' split at h
    all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at h))
    all_goals (obtain ⟨rfl, -⟩ := h)
    all_goals trivial

/-- Shared-memory stores and host calls ending in `raise TrapErr`. -/
def endsTrap : Prog Word → Bool
  | .raise e _ => e == "TrapErr"
  | .seq (.shMemStore _ _ _) rest => endsTrap rest
  | .seq (.extCall _ _ _ _ _) rest => endsTrap rest
  | _ => false

theorem endsTrap_sound : ∀ (p : Prog Word), endsTrap p = true →
    ∀ (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat), E.run fuel s p = some (r, n) → TrapOr r
  | .raise e _, hp, _, _, _, _, h => by
      simp only [endsTrap, beq_iff_eq] at hp
      subst hp
      exact raise_trapOr h
  | .seq (.shMemStore _ _ _) rest, hp, fuel, s, r, n, h => by
      simp only [endsTrap] at hp
      obtain ⟨fuel', r₁, n₁, h₁, h₂⟩ := seq_run_inv h
      have hl := shMemStore_plain h₁
      cases r₁ with
      | normal l g m f =>
        obtain ⟨n₂, h₂⟩ := h₂
        exact endsTrap_sound rest hp fuel' _ r n₂ h₂
      | _ =>
        simp only at h₂
        subst h₂
        trivial
  | .seq (.extCall _ _ _ _ _) rest, hp, fuel, s, r, n, h => by
      simp only [endsTrap] at hp
      obtain ⟨fuel', r₁, n₁, h₁, h₂⟩ := seq_run_inv h
      have hl := extCall_plain h₁
      cases r₁ with
      | normal l g m f =>
        obtain ⟨n₂, h₂⟩ := h₂
        exact endsTrap_sound rest hp fuel' _ r n₂ h₂
      | _ =>
        simp only at h₂
        subst h₂
        trivial
  | .skip, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .dec _ _ _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .assign _ _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .primitive _ _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .store _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .store32 _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .storeByte _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .shMemLoad _ _ _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .shMemStore _ _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .ite _ _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .while _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .break, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .continue, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .call _ _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .decCall _ _ _ _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .extCall _ _ _ _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .return _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .tick, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .annot _ _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq .skip _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.dec _ _ _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.assign _ _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.primitive _ _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.store _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.store32 _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.storeByte _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.shMemLoad _ _ _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.seq _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.ite _ _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.while _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq .break _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq .continue _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.call _ _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.decCall _ _ _ _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.raise _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.return _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq .tick _, hp, _, _, _, _, _ => by simp [endsTrap] at hp
  | .seq (.annot _ _) _, hp, _, _, _, _, _ => by simp [endsTrap] at hp

/-- Every result of `trap_with` is `.error` or a trap. -/
theorem trap_with_traps (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "trap_with" E.functions = some (parameters, body))
    (c : St σ) : WPr E c body Trap := by
  have hbody := (fun_of_index 3 hE.functions (by guest_decl_at 3) (by decide +kernel)
    hlookup).1
  subst hbody
  rintro r ⟨fuel, n, hrun⟩
  have h := endsTrap_sound _ (by decide) fuel c r n hrun
  cases r with
  | error l g m f => exact Or.inl rfl
  | _ => exact Or.inr h

/-- `f(args)` with no destination, for a callee described by a predicate on its result. -/
theorem WPr.call_spec {f : FunName} {args : List (Exp Word)} (C : Result σ → Prop)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody C)
    (hret : ∀ l g m ffi vs, C (.returned l g m ffi vs) → Q (.normal s.locals g m ffi))
    (hraise : ∀ l g m ffi exc v, C (.raised l g m ffi exc v) →
      Q (.raised (fun _ => none) g m ffi exc v))
    (hffi : ∀ l g m ffi ev, C (.finalFfi l g m ffi ev) → Q (.finalFfi (fun _ => none) g m ffi ev)) :
    WPr E s (.call (some (none, none)) f args) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl herr
  have hcal := hc parameters body values cl hlookup hvalues hbind rb hcallee
  cases rb with
  | returned lr g m ffi vs =>
    simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl herr
    · obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
      have : l' = s.locals := funext (fun x => hl x (by simp))
      subst this
      rcases hcal with he | hq
      · cases he
      · exact Or.inr (hret lr _ m ffi vs hq)
  | raised lr g m ffi ex v =>
    simp only [CallOutcome] at hout
    subst hout
    rcases hcal with he | hq
    · cases he
    · exact Or.inr (hraise lr g m ffi ex v hq)
  | finalFfi lr g m ffi ev =>
    simp only [CallOutcome] at hout
    subst hout
    rcases hcal with he | hq
    · cases he
    · exact Or.inr (hffi lr g m ffi ev hq)
  | _ =>
    simp only [CallOutcome] at hout
    exact Or.inl hout

/-- A call of `trap_with` satisfies anything that holds of traps. -/
theorem WPr.trap_call (hE : GuestEnv E) {args : List (Exp Word)} (hQ : ∀ r, Trap r → Q r) :
    WPr E s (.call (some (none, none)) "trap_with" args) Q :=
  WPr.call_spec Trap (fun p b _ _ hlk _ _ => trap_with_traps hE p b hlk _)
    (fun _ _ _ _ _ h => h.elim) (fun _ _ _ _ _ _ h => hQ _ h) (fun _ _ _ _ _ _ => hQ _ trivial)

/-- An assignment to a global, for whatever it assigns. -/
theorem WPr.assign_global_any {x : VarName} {e : Exp Word}
    (h : ∀ g, Q (.normal s.locals g s.memory s.ffi)) : WPr E s (.assign .global x e) Q := by
  intro r hr
  rw [runs_assign_global] at hr
  cases hy : E.eval s e with
  | none => rw [hy] at hr; simp only at hr; subst hr; exact Or.inl rfl
  | some y =>
    rw [hy] at hr
    simp only at hr
    split at hr
    · subst hr; exact Or.inr (h _)
    · subst hr; exact Or.inl rfl

/-- `scratch_alloc` raises nothing but `TrapErr`. -/
theorem scratch_alloc_traps (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "scratch_alloc" E.functions = some (parameters, body))
    (c : St σ) : WPr E c body RaiseIsTrap := by
  have hbody := (fun_of_index 13 hE.functions (by guest_decl_at 13) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hQ : ∀ r : Result σ, Trap r → (match r with
      | .normal _ _ _ _ => True
      | r1 => RaiseIsTrap r1) := by
    intro r hr
    cases r <;> trivial
  refine WPr.dec_ev (fun v _ => WPr.conseq (Q' := RaiseIsTrap) ?_ (fun _ hr => RaiseIsTrap.restore hr))
  refine WPr.seq (fun _ => True) (WPr.ite_both (fun w _ => ?_)) (fun s' _ => ?_)
  · split
    · exact WPr.skip trivial
    · exact WPr.trap_call hE hQ
  refine WPr.dec_ev (fun v _ => WPr.conseq (Q' := RaiseIsTrap) ?_ (fun _ hr => RaiseIsTrap.restore hr))
  refine WPr.seq (fun _ => True) (WPr.ite_both (fun w _ => ?_)) (fun s'' _ => ?_)
  · split
    · exact WPr.skip trivial
    · exact WPr.trap_call hE hQ
  exact WPr.seq (fun _ => True) (WPr.assign_global_any (fun _ => trivial))
    (fun _ _ => WPr.ret_any (fun _ _ => trivial))

/-- `WPFr` with traps exempt. -/
def WPFt (E : Env σ) (s : St σ) (p : Prog Word) (P : Assn) (Q : Result σ → Assn) : Prop :=
  ∀ R : Assn, (P ⋆ R).holds s → WPr E s p (fun r => Trap r ∨ (Q r ⋆ R).holds r.st)

theorem WPFr.toT {p : Prog Word} {P : Assn} {Q : Result σ → Assn} (h : WPFr E s p P Q) :
    WPFt E s p P Q :=
  fun R hR => WPr.conseq (h R hR) (fun _ hr => Or.inr hr)

theorem upd_setGlobal (s : St σ) (x : VarName) (w : PanValue Word)
    (l : VarName → Option (PanValue Word)) (f : FfiState σ) :
    Upd s.view (St.view (⟨l, updatePanValueMap s.globals x w, s.memory, f⟩ : St σ)) (.glob x) w := by
  refine ⟨by simp [St.view, updatePanValueMap], ?_⟩
  intro k' hk'
  cases k' with
  | mem b => rfl
  | glob y =>
    have : y ≠ x := fun e => hk' (by rw [e])
    simp [St.view, updatePanValueMap, this]

/-- An assignment to an owned global anywhere in a chain. -/
theorem Assn.setGlobal_at {A A' R : Assn} {x : VarName} {w : PanValue Word}
    {l : VarName → Option (PanValue Word)} {f : FfiState σ} (h : (A ⋆ R).holds s)
    (hstep : Step (.glob x) w A A') :
    (A' ⋆ R).holds (⟨l, updatePanValueMap s.globals x w, s.memory, f⟩ : St σ) :=
  hstep _ _ _ (upd_setGlobal s x w l f) h

/-- The two pointers that bound the free part of the scratch arena. -/
def ArenaPtrs (pv fv : Word) : Assn :=
  .glob "scratch_ptr" ↦ .word pv ⋆ .glob "frame_mem_ptr" ↦ .word fv

/-- `scratch_alloc(n)`: traps, or returns an aligned `q` with
`frame_mem_ptr ≤ q` and `q + n ≤` the old `scratch_ptr`, and sets
`scratch_ptr := q`. No memory is touched. -/
theorem scratch_alloc_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "scratch_alloc" E.functions = some (parameters, body))
    (s : St σ) (pv fv nv : Word) (hn : s.locals "n" = some (.word nv))
    (hfp : fv.toNat ≤ pv.toNat) :
    WPFt E s body (ArenaPtrs pv fv) (fun r => Assn.ex fun qv : Word =>
      ⌜(fv.toNat ≤ qv.toNat ∧ qv.toNat + nv.toNat ≤ pv.toNat ∧ qv.toNat % 8 = 0) ∧
        ∃ l g m, r = .returned l g m s.ffi [.word qv]⌝ ⋆ ArenaPtrs qv fv) := by
  intro R hR r hr
  unfold ArenaPtrs at hR
  have hp : s.globals "scratch_ptr" = some (.word pv) := Assn.glob_at hR (by look)
  have hf : s.globals "frame_mem_ptr" = some (.word fv) := Assn.glob_at hR (by look)
  have hpost := scratch_alloc_runs hE parameters body hlookup s r pv fv nv hn hp hf hfp hr
  have ht := scratch_alloc_traps hE parameters body hlookup s r hr
  cases r with
  | returned l g m f vs =>
    obtain ⟨rfl, rfl, qv, rfl, rfl, h1, h2, h3⟩ := hpost
    refine Or.inr (Or.inr (Assn.holdsV_ex.mpr ⟨qv, ?_⟩))
    exact Assn.holds_pure_intro ⟨⟨h1, h2, h3⟩, _, _, _, rfl⟩ (Assn.setGlobal_at hR (by step))
  | error l g m f => exact Or.inl rfl
  | raised l g m f e v =>
    rcases ht with he | ht
    · cases he
    · exact Or.inr (Or.inl ht)
  | finalFfi l g m f ev => exact Or.inr (Or.inl trivial)
  | normal l g m f => exact hpost.elim
  | continued l g m f => exact hpost.elim
  | broke l g m f => exact hpost.elim

end InitECandidate.Solver.GuestBound
