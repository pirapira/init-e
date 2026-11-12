import InitECandidate.Solver.GuestBound.HtabTruncate
import InitECandidate.Solver.GuestBound.TripleCall
import InitECandidate.Solver.GuestBound.HtabSetAux

/-!
# Step counts and results in one judgment

`WPc E s p B Q`: from state `s`, every non-error run of `p` takes at most `B`
steps, and every run stops or ends in `Q`. It is the pair of a `Triple` on the
single state `s` and a `WPs`, so each rule is the pair of an existing rule of
the cost logic and an existing symbolic-execution rule. It is meant for the
statements on the path from a function body down to a loop whose bound needs
facts about the state; the rest is covered by `WPc.of_costs`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

def WPc (E : Env σ) (s : St σ) (p : Prog Word) (B : Nat) (Q : Result σ → Prop) : Prop :=
  Triple E (fun a => a = s) p B (fun _ => True) ∧ WPs E s p Q

/-- An unconditional bound with a separately proved result. -/
theorem WPc.of_costs {p : Prog Word} {B : Nat} (hc : Costs E p B) (h : WPs E s p Q) :
    WPc E s p B Q :=
  ⟨hc.consequence (fun _ _ => trivial) (Nat.le_refl _) (fun _ h => h), h⟩

theorem WPc.mono {p : Prog Word} {B B' : Nat} {Q' : Result σ → Prop} (h : WPc E s p B Q')
    (hle : B ≤ B') (hq : ∀ r, Q' r → Q r) : WPc E s p B' Q :=
  ⟨h.1.consequence (fun _ h => h) hle (fun _ h => h), WPs.conseq h.2 hq⟩

/-- The step bound of a `WPc`. -/
theorem WPc.steps {p : Prog Word} {B : Nat} (h : WPc E s p B Q) {fuel : Nat} {r : Result σ}
    {n : Nat} (hrun : E.run fuel s p = some (r, n)) (hne : r.isError = false) : n ≤ B :=
  (h.1 fuel s r n rfl hrun hne).1

/-- A declaration. -/
theorem WPc.dec {x : VarName} {sh : Shape} {e : Exp Word} {body : Prog Word} {C : Nat}
    (h : ∀ v, E.eval s e = some v →
      WPc E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body C
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPc E s (.dec x sh e body) (panValueExpStepCost e + C + 1) Q := by
  refine ⟨?_, ?_⟩
  · refine Triple.dec (P := fun a => a = s) (P' := fun a' => ∃ v, E.eval s e = some v ∧
      a' = ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩) x sh e ?_ ?_
    · rintro a v rfl hv -
      exact ⟨v, hv, rfl⟩
    · rintro fuel a r n ⟨v, hv, rfl⟩ hrun hne
      exact (h v hv).1 fuel _ r n rfl hrun hne
  · intro r hr
    rw [runs_dec] at hr
    cases hv : E.eval s e with
    | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
    | some v =>
      rw [hv] at hr
      simp only at hr
      split at hr
      · obtain ⟨rb, hrb, rfl⟩ := hr
        rcases (h v hv).2 rb hrb with hs | hq
        · exact Or.inl hs.restore
        · exact Or.inr hq
      · subst hr
        exact Or.inl (Stopped.err s)

/-- A declaring call: the scope may use that the callee's body returned. -/
theorem WPc.decCall {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} {B C : Nat} (hf : FunCost E f B)
    (h : ∀ v g m ffi, CalleeReturned E s f args v g m ffi →
      WPc E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body C
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPc E s (.decCall x sh f args body) (panValueExpsStepCost args + B + C + 1) Q := by
  refine ⟨?_, ?_⟩
  · refine Triple.decCallRun (P := fun a => a = s) (P' := fun a' => ∃ v g m ffi,
      CalleeReturned E s f args v g m ffi ∧
      a' = ⟨updatePanValueMap s.locals x v, g, m, ffi⟩) x sh args hf ?_ ?_
    · rintro a v g m ffi rfl hret -
      exact ⟨v, g, m, ffi, hret, rfl⟩
    · rintro fuel a r n ⟨v, g, m, ffi, hret, rfl⟩ hrun hne
      exact (h v g m ffi hret).1 fuel _ r n rfl hrun hne
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
          obtain ⟨r', -, hrun', rfl⟩ := hout
          rcases (h v g m ffi ⟨parameters, cbody, values, cl, lr, hlookup, hvalues, hbind,
            hcallee⟩).2 r' hrun' with hs | hq
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

/-- Sequencing. -/
theorem WPc.seq {p q : Prog Word} {B₁ B₂ : Nat} (R : St σ → Prop)
    (hp : WPc E s p B₁ (fun r1 => match r1 with
      | .normal l g m f => R ⟨l, g, m, f⟩
      | r1 => Q r1))
    (hq : ∀ s', R s' → WPc E s' q B₂ Q) : WPc E s (.seq p q) (B₁ + B₂ + 1) Q := by
  refine ⟨?_, WPs.seqG R hp.2 (fun s' hR => (hq s' hR).2)⟩
  refine Triple.seq (Mid := R) ?_ ?_
  · intro fuel a r n ha hrun hne
    refine ⟨(hp.1 fuel a r n ha hrun hne).1, ?_⟩
    subst ha
    cases r with
    | normal l g m f =>
      rcases hp.2 _ (Runs.of_run hrun) with hs | hR
      · exact absurd hs Stopped.not_normal
      · exact hR
    | _ => trivial
  · intro fuel a r n hR hrun hne
    exact (hq a hR).1 fuel a r n rfl hrun hne

/-- A loop with an invariant and a variant that is at most `M` on entry. -/
theorem WPc.while {I : St σ → Prop} {μ : St σ → Nat} {c : Exp Word} {body : Prog Word}
    {b : Nat} (M : Nat) (hinit : I s) (hμ : μ s ≤ M)
    (hbody : ∀ a, I a → CondTrue E a c → WPc E a body b (fun r => match r with
      | .normal l g m f | .continued l g m f => I ⟨l, g, m, f⟩ ∧ μ ⟨l, g, m, f⟩ < μ a
      | .broke l g m f => Q (.normal l g m f)
      | r => Q r))
    (hexit : ∀ a k, I a → E.cond a c = some (0, k) →
      Q (.normal a.locals a.globals a.memory a.ffi)) :
    WPc E s (.while c body) ((M + 1) * (expCost c + b + 1)) Q := by
  refine ⟨?_, ?_⟩
  · refine (Triple.while_exit (I := I) (μ := μ) (Q := fun _ => True) M (condCost_exp _)
      (fun _ _ _ => trivial) ?_).consequence (fun a ha => by subst ha; exact ⟨hinit, hμ⟩)
      (Nat.le_refl _) (fun _ h => h)
    intro k fuel a r n ⟨hI, hk, hct⟩ hrun hne
    refine ⟨((hbody a hI hct).1 fuel a r n rfl hrun hne).1, ?_⟩
    rcases (hbody a hI hct).2 r (Runs.of_run hrun) with hs | hpost
    · cases r with
      | normal l g m f => exact absurd hs Stopped.not_normal
      | continued l g m f => exact absurd hs (fun h => h)
      | error l g m f => cases hne
      | _ => trivial
    · cases r with
      | normal l g m f => exact ⟨hpost.1, hk ▸ hpost.2⟩
      | continued l g m f => exact ⟨hpost.1, hk ▸ hpost.2⟩
      | _ => trivial
  · refine WPs.loopB (I := I) hinit (fun a hI hct => WPs.conseq (hbody a hI hct).2 ?_) hexit
    intro r hr
    cases r with
    | normal l g m f => exact hr.1
    | continued l g m f => exact hr.1
    | _ => exact hr

end InitECandidate.Solver.GuestBound
