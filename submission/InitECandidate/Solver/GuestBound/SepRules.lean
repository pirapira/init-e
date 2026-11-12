import InitECandidate.Solver.GuestBound.Sep

/-!
# Statement rules for `WPF`

Each rule wraps the `WPs` rule of the same name and carries the frame along.
`WPF.intro_frame` gives access to the precondition as a fact about the state,
for evaluating expressions that read owned cells or globals.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ}

/-- The precondition, with any frame, may be used as a fact about `s`. -/
theorem WPF.intro_frame {p : Prog Word} {P : Assn} {Q : Result σ → Assn}
    (h : (∀ R : Assn, (P ⋆ R).holds s → False) ∨ ((∃ R : Assn, (P ⋆ R).holds s) → WPF E s p P Q)) :
    WPF E s p P Q := by
  intro R hR
  rcases h with h | h
  · exact (h R hR).elim
  · exact h ⟨R, hR⟩ R hR

theorem restore_view (x : VarName) (o : Option (PanValue Word)) (r : Result σ) :
    (restorePanValueFfiLocal x o r).st.view = r.st.view := by
  cases r <;> rfl

/-- A declaration of a word-valued local. -/
theorem WPF.dec {x : VarName} {e : Exp Word} {body : Prog Word} {w : Word} {P : Assn}
    {Q : Result σ → Assn}
    (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : WPF E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩ body P
      (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPF E s (.dec x .one e body) P Q := by
  intro R hR
  refine WPs.dec he (WPs.conseq (h R hR) (fun r hr => ?_))
  unfold Assn.holds at hr ⊢
  dsimp only at hr ⊢
  rw [restore_view]
  exact hr

/-- A conditional. -/
theorem WPF.ite {c : Exp Word} {p q : Prog Word} {P : Assn} {Q : Result σ → Assn}
    (h : ∀ w, E.eval s c = some (.word w) → if w = 0 then WPF E s q P Q else WPF E s p P Q) :
    WPF E s (.ite c p q) P Q := by
  intro R hR
  refine WPs.ite_both (fun w hw => ?_)
  have := h w hw
  split
  · rename_i hz; rw [if_pos hz] at this; exact this R hR
  · rename_i hz; rw [if_neg hz] at this; exact this R hR

/-- A loop whose invariant is an assertion depending on the state reached. -/
theorem WPF.while {I : St σ → Assn} {c : Exp Word} {body : Prog Word} {Q : Result σ → Assn}
    (hbody : ∀ a, CondTrue E a c → WPF E a body (I a) (fun r => match r with
      | .normal l g m f | .continued l g m f => I ⟨l, g, m, f⟩
      | .broke l g m f => Q (.normal l g m f)
      | r => Q r))
    (hexit : ∀ a k, E.cond a c = some (0, k) → ∀ h, I a h →
      Q (.normal a.locals a.globals a.memory a.ffi) h) :
    WPF E s (.while c body) (I s) Q := by
  intro R hR
  refine WPs.loopB (I := fun a => (I a ⋆ R).holds a) hR
    (fun a hI hct => WPs.conseq (hbody a hct R hI) (fun r hr => ?_))
    (fun a k hI hc => Assn.holdsV_mono (Assn.sep_mono (hexit a k hc) (fun _ h => h)) hI)
  cases r <;> exact hr

/-- An assignment to an owned global. -/
theorem WPF.assign_global {x : VarName} {e : Exp Word} {old v : PanValue Word}
    (hv : ∀ y, E.eval s e = some y → y = v) :
    WPF E s (.assign .global x e) (.glob x ↦ old)
      (fun r => ⌜∃ g m, r = .normal s.locals g m s.ffi⌝ ⋆ .glob x ↦ v) := by
  intro R hR r hr
  rw [runs_assign_global] at hr
  cases hy : E.eval s e with
  | none => rw [hy] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some y =>
    have := hv y hy
    subst this
    rw [hy] at hr
    simp only at hr
    split at hr
    · subst hr
      refine Or.inr ?_
      show ((⌜_⌝ ⋆ _) ⋆ R).holds _
      rw [Assn.sep_assoc]
      exact Assn.holdsV_pure.mpr ⟨⟨_, _, rfl⟩, Assn.holds_setGlobal hR⟩
    · subst hr
      exact Or.inl (Stopped.err s)

/-- A declaring call. The callee's body is specified from the call state with
its own pre- and postcondition; the scope starts from the callee's
postcondition, with the caller's frame untouched. -/
theorem WPF.decCall {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} {Pc : Assn} {Qc Q : Result σ → Assn}
    (hf : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPF E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody Pc Qc)
    (h : ∀ v l g m ffi,
      WPF E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body (Qc (.returned l g m ffi [v]))
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPF E s (.decCall x sh f args body) Pc Q := by
  intro R hR r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hcal := hf parameters cbody values cl hlookup hvalues hbind R
    (Assn.holds_congr rfl rfl hR) rb hcallee
  cases rb with
  | returned lr g m ffi vs =>
    cases vs with
    | nil => exact hout.elim
    | cons v rest =>
      cases rest with
      | cons v' rest' => exact hout.elim
      | nil =>
        obtain ⟨r', -, hrun', rfl⟩ := hout
        rcases hcal with hs | hq
        · exact hs.elim
        rcases h v lr g m ffi R (Assn.holds_congr rfl rfl hq) r' hrun' with hs | hq'
        · exact Or.inl hs.restore
        · refine Or.inr ?_
          unfold Assn.holds at hq' ⊢
          dsimp only at hq' ⊢
          rw [restore_view]
          exact hq'
  | raised lr g m ffi ex v =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m ffi ev =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | _ => exact hout.elim

end InitECandidate.Solver.GuestBound
