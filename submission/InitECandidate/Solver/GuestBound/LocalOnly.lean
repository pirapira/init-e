import InitECandidate.Solver.GuestBound.HtabDiff
import InitECandidate.Solver.GuestBound.ScratchAlloc

/-!
# Statements that only compute on locals

`localOnly x p` accepts programs built from `skip`, sequencing, conditionals,
loops, word declarations and assignments to locals other than `x`.
`localOnly_sound`: such a program stops or ends normally with the same
globals, memory and FFI state and the same value of `x`; if every local held
a word before, every local holds a word after. Used for the round loop of
`keccak_f1600`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Every defined local is a word. -/
def AllW (l : VarName → Option (PanValue Word)) : Prop :=
  ∀ y v, l y = some v → ∃ w : Word, v = .word w

theorem AllW.update {l : VarName → Option (PanValue Word)} (h : AllW l) (x : VarName)
    (w : Word) : AllW (updatePanValueMap l x (.word w)) := by
  intro y v hy
  rw [update_lookup] at hy
  split at hy
  · exact ⟨w, (Option.some.inj hy).symm⟩
  · exact h y v hy

theorem AllW.restore {l l0 : VarName → Option (PanValue Word)} (h : AllW l) (h0 : AllW l0)
    (x : VarName) : AllW (restorePanValueLocal l x (l0 x)) := by
  intro y v hy
  simp only [restorePanValueLocal] at hy
  split at hy
  · rename_i hyx
    cases hl : l0 x with
    | none => rw [hl] at hy; simp at hy
    | some v0 =>
      rw [hl] at hy
      simp at hy
      obtain ⟨w, hw⟩ := h0 x v0 hl
      exact ⟨w, by rw [← hy]; exact hw⟩
  · exact h y v hy

def localOnly (x : VarName) : Prog Word → Bool
  | .skip => true
  | .seq a b => localOnly x a && localOnly x b
  | .dec y .one _ body => (y != x) && localOnly x body
  | .assign .local y _ => y != x
  | .ite _ a b => localOnly x a && localOnly x b
  | .while _ body => localOnly x body
  | _ => false

/-- Outcome of a locals-only program. -/
def LoPost (x : VarName) (s : St σ) (r : Result σ) : Prop :=
  ∃ l, r = .normal l s.globals s.memory s.ffi ∧ l x = s.locals x ∧ (AllW s.locals → AllW l)

theorem localOnly_sound (x : VarName) :
    (p : Prog Word) → localOnly x p = true → ∀ s : St σ, WPs E s p (LoPost x s)
  | .skip, _, s => WPs.skip ⟨s.locals, rfl, rfl, id⟩
  | .seq a b, h, s => by
    simp only [localOnly, Bool.and_eq_true] at h
    refine WPs.seqG (fun s' => s'.globals = s.globals ∧ s'.memory = s.memory ∧
      s'.ffi = s.ffi ∧ s'.locals x = s.locals x ∧ (AllW s.locals → AllW s'.locals))
      (WPs.conseq (localOnly_sound x a h.1 s) ?_) ?_
    · rintro r ⟨l, rfl, hx, hw⟩
      exact ⟨rfl, rfl, rfl, hx, hw⟩
    · rintro ⟨l', g', m', f'⟩ ⟨hg, hm, hf, hx, hw⟩
      dsimp only at hg hm hf hx hw
      subst hg hm hf
      exact WPs.conseq (localOnly_sound x b h.2 _) (by
        rintro r ⟨l, rfl, hx2, hw2⟩
        exact ⟨l, rfl, hx2.trans hx, fun h0 => hw2 (hw h0)⟩)
  | .dec y .one e body, h, s => by
    simp only [localOnly, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    intro r hr
    rw [runs_dec] at hr
    cases hv : E.eval s e with
    | none =>
      rw [hv] at hr
      simp only at hr
      subst hr
      exact Or.inl (Stopped.err s)
    | some v =>
      rw [hv] at hr
      simp only at hr
      split at hr
      · rename_i hsh
        obtain ⟨w, rfl⟩ := word_of_shape_one hsh
        obtain ⟨rb, hrb, rfl⟩ := hr
        rcases localOnly_sound x body h.2 _ rb hrb with hs | ⟨l, rfl, hx, hw⟩
        · exact Or.inl hs.restore
        · refine Or.inr ⟨restorePanValueLocal l y (s.locals y), rfl, ?_,
            fun h0 => (hw (h0.update y w)).restore h0 y⟩
          have hxy : (x == y) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]
            exact fun e => h.1 e.symm
          simp only [restorePanValueLocal, hxy]
          dsimp only at hx
          rw [hx, update_lookup, hxy]
          rfl
      · subst hr
        exact Or.inl (Stopped.err s)
  | .assign .local y e, h, s => by
    simp only [localOnly, bne_iff_ne, ne_eq] at h
    intro r hr
    rw [runs_assign_local] at hr
    cases hv : E.eval s e with
    | none =>
      rw [hv] at hr
      simp only at hr
      subst hr
      exact Or.inl (Stopped.err s)
    | some v =>
      rw [hv] at hr
      simp only at hr
      split at hr
      · rename_i hval
        subst hr
        have hxy : (x == y) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun e => h e.symm
        refine Or.inr ⟨_, rfl, by rw [update_lookup, hxy]; rfl, fun h0 => ?_⟩
        intro z u hz
        rw [update_lookup] at hz
        split at hz
        · have hvu : v = u := Option.some.inj hz
          subst hvu
          simp only [panValueAssignmentValid] at hval
          cases ho : s.locals y with
          | none => rw [ho] at hval; simp at hval
          | some old =>
            rw [ho] at hval
            obtain ⟨wo, rfl⟩ := h0 y old ho
            simp only [shape_word] at hval
            exact word_of_shape_one hval
        · exact h0 z u hz
      · subst hr
        exact Or.inl (Stopped.err s)
  | .ite c a b, h, s => by
    simp only [localOnly, Bool.and_eq_true] at h
    refine WPs.ite_both (fun w _ => ?_)
    split
    · exact localOnly_sound x b h.2 s
    · exact localOnly_sound x a h.1 s
  | .while c body, h, s => by
    simp only [localOnly] at h
    refine WPs.loopG (I := fun a => a.globals = s.globals ∧ a.memory = s.memory ∧
      a.ffi = s.ffi ∧ a.locals x = s.locals x ∧ (AllW s.locals → AllW a.locals))
      ⟨rfl, rfl, rfl, rfl, id⟩ (fun a hI _ => ?_) (fun a k hI _ => ?_)
    · obtain ⟨hg, hm, hf, hx, hw⟩ := hI
      refine WPs.conseq (localOnly_sound x body h a) ?_
      rintro r ⟨l, rfl, hx2, hw2⟩
      exact ⟨hg, hm, hf, hx2.trans hx, fun h0 => hw2 (hw h0)⟩
    · obtain ⟨hg, hm, hf, hx, hw⟩ := hI
      exact ⟨a.locals, by rw [hg, hm, hf], hx, hw⟩
  | .dec _ (.comb _) _ _, h, _ => by simp [localOnly] at h
  | .assign .global _ _, h, _ => by simp [localOnly] at h
  | .primitive _ _ _, h, _ => by simp [localOnly] at h
  | .store _ _, h, _ => by simp [localOnly] at h
  | .store32 _ _, h, _ => by simp [localOnly] at h
  | .storeByte _ _, h, _ => by simp [localOnly] at h
  | .break, h, _ => by simp [localOnly] at h
  | .continue, h, _ => by simp [localOnly] at h
  | .call _ _ _, h, _ => by simp [localOnly] at h
  | .decCall _ _ _ _ _, h, _ => by simp [localOnly] at h
  | .extCall _ _ _ _ _, h, _ => by simp [localOnly] at h
  | .raise _ _, h, _ => by simp [localOnly] at h
  | .return _, h, _ => by simp [localOnly] at h
  | .shMemLoad _ _ _ _, h, _ => by simp [localOnly] at h
  | .shMemStore _ _ _, h, _ => by simp [localOnly] at h
  | .tick, h, _ => by simp [localOnly] at h
  | .annot _ _, h, _ => by simp [localOnly] at h

end InitECandidate.Solver.GuestBound
