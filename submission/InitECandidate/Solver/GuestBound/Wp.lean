import InitECandidate.Solver.GuestBound.HtabCells

/-!
# Stepping through straight-line code

`WPs E s p Q`: every run of `p` from `s` is stopped (an error, an exception or
a final FFI event) or ends in `Q`. The rules below step through sequences,
conditionals, declarations, stores and returns.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

def WPs (E : Env σ) (s : St σ) (p : Prog Word) (Q : Result σ → Prop) : Prop :=
  ∀ r, Runs E s p r → Stopped r ∨ Q r

variable {s : St σ} {Q : Result σ → Prop}

theorem Stopped.not_normal {l g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {f : FfiState σ} : ¬ Stopped (.normal l g m f : Result σ) :=
  fun h => h

theorem WPs.conseq {p : Prog Word} {Q' : Result σ → Prop} (h : WPs E s p Q')
    (hq : ∀ r, Q' r → Q r) : WPs E s p Q := by
  intro r hr
  rcases h r hr with hs | hq'
  · exact Or.inl hs
  · exact Or.inr (hq r hq')

/-- Sequencing through an intermediate assertion on the state. -/
theorem WPs.seq {p q : Prog Word} (R : St σ → Prop)
    (hp : WPs E s p (fun r1 => ∃ l g m f, r1 = .normal l g m f ∧ R ⟨l, g, m, f⟩))
    (hq : ∀ s', R s' → WPs E s' q Q) : WPs E s (.seq p q) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  rcases hp r1 h1 with hs | ⟨l, g, m, f, rfl, hR⟩
  · cases r1 with
    | normal l g m f => exact absurd hs Stopped.not_normal
    | _ => simp only at hrest; subst hrest; exact Or.inl hs
  · exact hq _ hR r hrest

theorem WPs.skip (h : Q (.normal s.locals s.globals s.memory s.ffi)) : WPs E s .skip Q := by
  intro r hr
  rw [runs_skip] at hr
  subst hr
  exact Or.inr h

/-- A conditional whose test evaluates to a known word. -/
theorem WPs.ite {c : Exp Word} {p q : Prog Word} {w : Word}
    (hc : ∀ x, E.eval s c = some x → x = .word w)
    (h : if w = 0 then WPs E s q Q else WPs E s p Q) : WPs E s (.ite c p q) Q := by
  intro r hr
  rw [runs_ite] at hr
  cases he : E.eval s c with
  | none => rw [he] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some x =>
    have := hc x he
    subst this
    rw [he] at hr
    simp only at hr
    split at hr
    · rename_i hw
      rw [if_pos hw] at h
      exact h r hr
    · rename_i hw
      rw [if_neg hw] at h
      exact h r hr

/-- A conditional whose test is not known: both branches. -/
theorem WPs.ite_both {c : Exp Word} {p q : Prog Word}
    (h : ∀ w, E.eval s c = some (.word w) → if w = 0 then WPs E s q Q else WPs E s p Q) :
    WPs E s (.ite c p q) Q := by
  intro r hr
  rw [runs_ite] at hr
  cases he : E.eval s c with
  | none => rw [he] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some x =>
    rw [he] at hr
    cases x with
    | word w =>
      have hw := h w he
      simp only at hr
      split at hr
      · rename_i hz
        rw [if_pos hz] at hw
        exact hw r hr
      · rename_i hz
        rw [if_neg hz] at hw
        exact hw r hr
    | _ => simp only at hr; subst hr; exact Or.inl (Stopped.err s)

/-- A one-word declaration whose value, if it evaluates, is `w`. -/
theorem WPs.dec {x : VarName} {e : Exp Word} {body : Prog Word} {w : Word}
    (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : WPs E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩ body
      (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.dec x .one e body) Q := by
  intro r hr
  cases hv : E.eval s e with
  | none =>
    rw [runs_dec, hv] at hr
    simp only at hr
    subst hr
    exact Or.inl (Stopped.err s)
  | some y =>
    have := he y hv
    subst this
    obtain ⟨r', hr', rfl⟩ := dec_word_runs hv hr
    rcases h r' hr' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

/-- A word store at a known address of a value that, if it evaluates, is `w`. -/
theorem WPs.store (hE : GuestEnv E) {a val : Exp Word} {addr w : Word}
    (ha : E.eval s a = some (.word addr)) (hv : ∀ y, E.eval s val = some y → y = .word w)
    (h : Q (.normal s.locals s.globals (setCell s.memory addr w) s.ffi)) :
    WPs E s (.store a val) Q := by
  intro r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  rcases store_word_inv hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · exact Or.inl (Stopped.of_error herr)
  rw [ha] at ha'
  simp only [Option.some.injEq, PanValue.word.injEq] at ha'
  subst ha'
  have := hv y hy
  subst this
  rw [hm w rfl]
  exact Or.inr h

theorem WPs.ret {e : Exp Word} {w : Word} (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : Q (.returned (fun _ => none) s.globals s.memory s.ffi [.word w])) :
    WPs E s (.return e) Q := by
  intro r hr
  rw [runs_return] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some y =>
    have := he y hv
    subst this
    rw [hv] at hr
    simp only [payload_word, if_true] at hr
    subst hr
    exact Or.inr h

/-- Assigning to a local that holds a word a value that, if it evaluates, is `w`. -/
theorem WPs.assign {x : VarName} {e : Exp Word} {w old : Word}
    (hx : s.locals x = some (.word old)) (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : Q (.normal (updatePanValueMap s.locals x (.word w)) s.globals s.memory s.ffi)) :
    WPs E s (.assign .local x e) Q := by
  intro r hr
  rw [runs_assign_local] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some y =>
    have := he y hv
    subst this
    rw [hv] at hr
    simp only [panValueAssignmentValid, hx, shape_word, shape_matches_self, if_true] at hr
    subst hr
    exact Or.inr h

/-- Undoing a declaration that was not assigned restores the locals. -/
theorem restore_update (l : VarName → Option (PanValue Word)) (x : VarName)
    (v : PanValue Word) :
    restorePanValueLocal (updatePanValueMap l x v) x (l x) = l := by
  funext y
  simp only [restorePanValueLocal, update_lookup]
  by_cases h : (y == x) = true
  · simp only [h, if_true]
    rw [beq_iff_eq.mp h]
  · simp only [h]
    rfl

/-- Storing the word a cell already holds changes nothing. -/
theorem setCell_same {m : Word → Option (PanValue Word)} {a w : Word} (h : Rd m a w) :
    setCell m a w = m := by
  funext b
  unfold setCell
  by_cases hb : (b == a) = true
  · rw [if_pos hb, beq_iff_eq.mp hb]
    exact h.symm
  · rw [if_neg hb]

end InitECandidate.Solver.GuestBound
