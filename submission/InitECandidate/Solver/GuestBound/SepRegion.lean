import InitECandidate.Solver.GuestBound.SepPop

/-!
# Owning a set of cells with unknown contents

`Owns S` owns exactly the keys in `S`, whatever they hold (possibly nothing
yet). It is what an arena's free space and a freshly allocated block are.
A store into an owned key keeps `Owns S`; `Owns` of a disjoint union splits
into `⋆`, which is how an allocator hands a block out of its free space.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- Exactly the keys in `S` are owned. -/
def Assn.Owns (S : Key → Prop) : Assn := fun h => ∀ k, h k ≠ none ↔ S k

/-- A store into a key of an owned set. -/
theorem Step.owns {S : Key → Prop} {k : Key} {w : PanValue Word} (hk : S k) :
    Step k w (Assn.Owns S) (Assn.Owns S) := by
  rintro V V' R ⟨hVk, hVo⟩ ⟨h, hs, h1, h2, hd, rfl, hp, hr⟩
  have h2k : h2 k = none := by
    rcases hd k with e | e
    · exact absurd e ((hp k).mpr hk)
    · exact e
  obtain ⟨hs1, hs2⟩ := (Heap.sub_union hd).mp hs
  let h1' : Heap := fun k' => if k' = k then some (some w) else h1 k'
  have hd' : Heap.Disj h1' h2 := by
    intro k'
    by_cases e : k' = k
    · subst e; exact Or.inr h2k
    · rcases hd k' with e1 | e1
      · exact Or.inl (by simp [h1', e, e1])
      · exact Or.inr e1
  refine ⟨_, (Heap.sub_union hd').mpr ⟨?_, ?_⟩, h1', h2, hd', rfl, ?_, hr⟩
  · intro k' c hc
    by_cases e : k' = k
    · subst e
      simp [h1'] at hc
      rw [← hc]
      exact hVk
    · simp [h1', e] at hc
      rw [hVo k' e]
      exact hs1 k' c hc
  · intro k' c hc
    have e : k' ≠ k := by
      rintro rfl
      rw [h2k] at hc; cases hc
    rw [hVo k' e]
    exact hs2 k' c hc
  · intro k'
    by_cases e : k' = k
    · subst e
      simp [h1', hk]
    · simp [h1', e]
      exact hp k'

/-- A store into a cell owned with any content. -/
theorem Step.cell {k : Key} {c : Option (PanValue Word)} {w : PanValue Word} :
    Step k w (Assn.cell k c) (k ↦ w) :=
  fun _ _ _ hu h => Assn.holdsV_update h hu.1 hu.2

/-- An owned set splits along a partition. -/
theorem Assn.owns_split {S S1 S2 : Key → Prop} (hS : ∀ k, S k ↔ S1 k ∨ S2 k)
    (hdis : ∀ k, S1 k → S2 k → False) : Assn.Owns S = (Assn.Owns S1 ⋆ Assn.Owns S2) := by
  classical
  funext h
  apply propext
  constructor
  · intro hp
    refine ⟨fun k => if S1 k then h k else none, fun k => if S1 k then none else h k, ?_, ?_,
      ?_, ?_⟩
    · intro k
      by_cases e : S1 k
      · exact Or.inr (by simp [e])
      · exact Or.inl (by simp [e])
    · funext k
      unfold Heap.union
      by_cases e : S1 k
      · simp only [e, if_true]
        cases h k <;> rfl
      · simp [e]
    · intro k
      by_cases e : S1 k
      · simp only [e, if_true, iff_true]
        exact (hp k).mpr ((hS k).mpr (Or.inl e))
      · simp [e]
    · intro k
      by_cases e : S1 k
      · simp only [e, if_true, ne_eq, not_true_eq_false, false_iff]
        exact fun h2 => hdis k e h2
      · simp only [e, if_false]
        rw [hp k, hS k]
        exact ⟨fun h' => h'.resolve_left e, Or.inr⟩
  · rintro ⟨h1, h2, hd, rfl, hp1, hp2⟩ k
    rw [hS k, ← hp1 k, ← hp2 k]
    unfold Heap.union
    cases e : h1 k with
    | none => simp
    | some c => simp

/-- A single owned cell, as an owned set. -/
theorem Assn.owns_single (k : Key) :
    Assn.Owns (fun k' => k' = k) = Assn.ex (fun c => Assn.cell k c) := by
  funext h
  apply propext
  constructor
  · intro hp
    cases hk : h k with
    | none => exact absurd hk ((hp k).mpr rfl)
    | some c =>
      refine ⟨c, ?_⟩
      funext k'
      by_cases e : k' = k
      · subst e; rw [hk, Heap.single_self]
      · rw [Heap.single_ne c e]
        by_contra hne
        exact e ((hp k').mp hne)
  · rintro ⟨c, rfl⟩ k'
    by_cases e : k' = k
    · subst e; simp [Heap.single_self]
    · simp [Heap.single_ne c e, e]

/-- The word cells of `[a, a + 8n)`. -/
def Assn.Words (a : Word) (n : Nat) : Assn :=
  Assn.Owns (fun k => ∃ i, i < n ∧ k = .mem (a + BitVec.ofNat 64 (8 * i)))

/-- A word store at index `i` of an owned block. -/
theorem Step.words {a : Word} {n i : Nat} {w : PanValue Word} (hi : i < n) :
    Step (.mem (a + BitVec.ofNat 64 (8 * i))) w (Assn.Words a n) (Assn.Words a n) :=
  Step.owns ⟨i, hi, rfl⟩

end InitECandidate.Solver.GuestBound
