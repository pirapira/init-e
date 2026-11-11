import Mathlib.Data.Fintype.Prod
import InitECandidate.Solver.GuestBound.MemLaws
import InitECandidate.Solver.GuestBound.WalkLoopBound

/-!
# Memory that only gains bits

`MemGe m m'`: every cell of `m'` is the cell of `m`, or both are words and the
later one has at least the bits of the earlier one. The number of set bits is
a bounded potential that separates distinct memories in this order.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- The cell is unchanged, or a word that gained bits. -/
def CellGe (a b : Option (PanValue Word)) : Prop :=
  a = b ∨ ∃ w w', a = some (.word w) ∧ b = some (.word w') ∧ w &&& w' = w

/-- Every cell is unchanged or gained bits. -/
def MemGe (m m' : Word → Option (PanValue Word)) : Prop := ∀ x, CellGe (m x) (m' x)

theorem MemGe.refl (m : Word → Option (PanValue Word)) : MemGe m m := fun _ => Or.inl rfl

theorem MemGe.trans {a b c : Word → Option (PanValue Word)} (h₁ : MemGe a b) (h₂ : MemGe b c) :
    MemGe a c := by
  intro x
  rcases h₁ x with h | ⟨w, w', hw, hw', hand⟩
  · rw [h]; exact h₂ x
  · rcases h₂ x with h | ⟨v, v', hv, hv', hand'⟩
    · rw [← h]; exact Or.inr ⟨w, w', hw, hw', hand⟩
    · rw [hw'] at hv
      simp only [Option.some.injEq, PanValue.word.injEq] at hv
      subst hv
      refine Or.inr ⟨w, v', hw, hv', ?_⟩
      rw [← hand, BitVec.and_assoc, hand']

/-- Or-ing bits into a word cell. -/
theorem setCell_ge {m : Word → Option (PanValue Word)} {x old y : Word}
    (h : m x = some (.word old)) : MemGe m (setCell m x (old ||| y)) := by
  intro a
  by_cases hax : (a == x) = true
  · have : a = x := by simpa using hax
    subst this
    refine Or.inr ⟨old, old ||| y, h, by simp [setCell], ?_⟩
    ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_or]
    cases old[i] <;> simp
  · exact Or.inl (by simp [setCell, hax])

open Classical in
/-- The set bits of the word cells. -/
noncomputable def bitsOf (m : Word → Option (PanValue Word)) : Finset (Word × Fin 64) :=
  Finset.univ.filter fun p => ∃ w, m p.1 = some (.word w) ∧ w.getLsbD p.2.val = true

theorem bitsOf_mono {m m' : Word → Option (PanValue Word)} (h : MemGe m m') :
    bitsOf m ⊆ bitsOf m' := by
  intro p hp
  simp only [bitsOf, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨w, hw, hbit⟩ := hp
  rcases h p.1 with heq | ⟨v, v', hv, hv', hand⟩
  · exact ⟨w, heq ▸ hw, hbit⟩
  · rw [hv] at hw
    simp only [Option.some.injEq, PanValue.word.injEq] at hw
    subst hw
    refine ⟨v', hv', ?_⟩
    have := congrArg (fun z => z.getLsbD p.2.val) hand
    simp only [BitVec.getLsbD_and, hbit, Bool.true_and] at this
    exact this

theorem bitsOf_card_le (m : Word → Option (PanValue Word)) :
    (bitsOf m).card ≤ 2 ^ 64 * 64 := by
  refine Nat.le_trans (Finset.card_le_univ _) ?_
  rw [Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_le_mul_right _ word_card

/-- A later memory with no more set bits is the same memory. -/
theorem memGe_eq {m m' : Word → Option (PanValue Word)} (h : MemGe m m')
    (hc : (bitsOf m').card ≤ (bitsOf m).card) : m = m' := by
  have hset : bitsOf m = bitsOf m' := Finset.eq_of_subset_of_card_le (bitsOf_mono h) hc
  funext x
  rcases h x with heq | ⟨w, w', hw, hw', hand⟩
  · exact heq
  · rw [hw, hw']
    have : w = w' := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      cases hb : w'.getLsbD i with
      | true =>
        have hmem : ((x, ⟨i, hi⟩) : Word × Fin 64) ∈ bitsOf m' := by
          simp only [bitsOf, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w', hw', hb⟩
        rw [← hset] at hmem
        simp only [bitsOf, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        obtain ⟨w0, hw0, hbit⟩ := hmem
        rw [hw] at hw0
        simp only [Option.some.injEq, PanValue.word.injEq] at hw0
        subst hw0
        exact hbit
      | false =>
        have := congrArg (fun z => z.getLsbD i) hand
        simp only [BitVec.getLsbD_and, hb, Bool.and_false] at this
        exact this.symm
    rw [this]

end InitECandidate.Solver.GuestBound
