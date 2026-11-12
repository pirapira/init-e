import InitECandidate.Solver.GuestBound.PolyCalls

/-!
# Postconditions that cover exceptions

`WPs` treats a raised exception as "the run stopped". Inside the interpreter
that is not enough: `run_frames` catches `EvmErr` and carries on from the
state the exception left, so specifications of the opcode handlers have to
say what holds when they raise. `WPr E s p Q` says every run of `p` from `s`
ends in `.error` (a failing source semantics, not covered by the challenge)
or in a result satisfying `Q`, where `Q` ranges over all other results:
normal, returned, raised, break, continue and final FFI events.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Every run of `p` from `s` ends in `.error` or in a result satisfying `Q`. -/
def WPr (E : Env σ) (s : St σ) (p : Prog Word) (Q : Result σ → Prop) : Prop :=
  ∀ r, Runs E s p r → r.isError = true ∨ Q r

theorem WPr.conseq {p : Prog Word} {Q' : Result σ → Prop} (h : WPr E s p Q')
    (hQ : ∀ r, Q' r → Q r) : WPr E s p Q :=
  fun r hr => (h r hr).imp id (hQ r)

/-- The weaker judgement follows when `Q` only matters on results that keep going. -/
theorem WPr.wps {p : Prog Word} {Q' : Result σ → Prop} (h : WPr E s p Q')
    (hQ : ∀ r, Q' r → Stopped r ∨ Q r) : WPs E s p Q := by
  intro r hr
  rcases h r hr with he | hq
  · exact Or.inl (Stopped.of_error he)
  · exact hQ r hq

theorem isError_restore {x : VarName} {old : Option (PanValue Word)} {r : Result σ}
    (h : r.isError = true) : (restorePanValueFfiLocal x old r).isError = true := by
  cases r <;> first | rfl | cases h

theorem WPr.skip (h : Q (.normal s.locals s.globals s.memory s.ffi)) : WPr E s .skip Q := by
  intro r hr
  rw [runs_skip] at hr
  subst hr
  exact Or.inr h

/-- Sequencing: `p` ends normally in an `R`-state, or its abrupt result already
satisfies `Q`. -/
theorem WPr.seq {p q : Prog Word} (R : St σ → Prop)
    (hp : WPr E s p (fun r1 =>
      match r1 with
      | .normal l g m f => R ⟨l, g, m, f⟩
      | r1 => Q r1))
    (hq : ∀ s', R s' → WPr E s' q Q) : WPr E s (.seq p q) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  rcases hp r1 h1 with he | h
  · cases r1 with
    | error l g m f => simp only at hrest; subst hrest; exact Or.inl rfl
    | _ => cases he
  · cases r1 with
    | normal l g m f => exact hq _ h r hrest
    | _ => simp only at hrest; subst hrest; exact Or.inr h

/-- A declaration, for whatever value the initialiser has. -/
theorem WPr.dec_ev {x : VarName} {sh : Shape} {e : Exp Word} {body : Prog Word}
    (h : ∀ v, E.eval s e = some v →
      WPr E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.dec x sh e body) Q := by
  intro r hr
  rw [runs_dec] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl rfl
  | some v =>
    rw [hv] at hr
    simp only at hr
    split at hr
    · obtain ⟨rb, hrb, rfl⟩ := hr
      rcases h v hv rb hrb with he | hq
      · exact Or.inl (isError_restore he)
      · exact Or.inr hq
    · subst hr
      exact Or.inl rfl

/-- Conditional on a word condition: only the branch taken has to be handled. -/
theorem WPr.ite_both {c : Exp Word} {p q : Prog Word}
    (h : ∀ w, E.eval s c = some (.word w) → if w = 0 then WPr E s q Q else WPr E s p Q) :
    WPr E s (.ite c p q) Q := by
  intro r hr
  rw [runs_ite] at hr
  cases he : E.eval s c with
  | none => rw [he] at hr; simp only at hr; subst hr; exact Or.inl rfl
  | some x =>
    rw [he] at hr
    cases x with
    | word w =>
      simp only at hr
      have := h w he
      split at hr
      · rename_i h0
        rw [if_pos (by simpa using h0)] at this
        exact this r hr
      · rename_i h0
        rw [if_neg (by simpa using h0)] at this
        exact this r hr
    | _ => simp only at hr; subst hr; exact Or.inl rfl

/-- A store of a word at a word address. -/
theorem WPr.store (hE : GuestEnv E) {a val : Exp Word} {addr w : Word}
    (ha : E.eval s a = some (.word addr)) (hv : ∀ y, E.eval s val = some y → y = .word w)
    (h : Q (.normal s.locals s.globals (setCell s.memory addr w) s.ffi)) :
    WPr E s (.store a val) Q := by
  intro r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  rcases store_word_inv hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · exact Or.inl herr
  rw [ha] at ha'
  simp only [Option.some.injEq, PanValue.word.injEq] at ha'
  subst ha'
  have := hv y hy
  subst this
  rw [hm w rfl]
  exact Or.inr h

/-- A store at a word address of whatever word the value expression gives. -/
theorem WPr.store_ev (hE : GuestEnv E) {a val : Exp Word} {addr : Word}
    (ha : E.eval s a = some (.word addr))
    (h : ∀ y, E.eval s val = some y → ∃ w, y = .word w ∧
      Q (.normal s.locals s.globals (setCell s.memory addr w) s.ffi)) :
    WPr E s (.store a val) Q := by
  intro r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  rcases store_word_inv hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · exact Or.inl herr
  rw [ha] at ha'
  simp only [Option.some.injEq, PanValue.word.injEq] at ha'
  subst ha'
  obtain ⟨w, rfl, hq⟩ := h y hy
  rw [hm w rfl]
  exact Or.inr hq

/-- Returning a word. -/
theorem WPr.ret {e : Exp Word} {w : Word} (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : Q (.returned (fun _ => none) s.globals s.memory s.ffi [.word w])) :
    WPr E s (.return e) Q := by
  intro r hr
  rw [runs_return] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl rfl
  | some y =>
    have := he y hv
    subst this
    rw [hv] at hr
    simp only at hr
    split at hr
    · subst hr; exact Or.inr h
    · subst hr; exact Or.inl rfl

/-- What a `raise` statement leaves: the state as it was, with empty locals. -/
theorem runs_raise_inv {exc : ExceptionId} {e : Exp Word} {r : Result σ}
    (h : Runs E s (.raise exc e) r) :
    r.isError = true ∨ ∃ v, E.eval s e = some v ∧
      r = .raised (fun _ => none) s.globals s.memory s.ffi exc v := by
  obtain ⟨fuel, n, h⟩ := h
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueRaiseResult, evalPanValueExpCounted, Env.eval] at h ⊢
    cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord e E.memoryAccess with
    | none =>
      rw [hv] at h
      simp at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inl rfl
    | some v =>
      rw [hv] at h
      simp only [Option.map_some] at h
      split at h
      · simp at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inr ⟨v, rfl, rfl⟩
      · simp at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl rfl

theorem WPr.raise {exc : ExceptionId} {e : Exp Word}
    (h : ∀ v, E.eval s e = some v →
      Q (.raised (fun _ => none) s.globals s.memory s.ffi exc v)) :
    WPr E s (.raise exc e) Q := by
  intro r hr
  rcases runs_raise_inv hr with he | ⟨v, hv, rfl⟩
  · exact Or.inl he
  · exact Or.inr (h v hv)

end InitECandidate.Solver.GuestBound
