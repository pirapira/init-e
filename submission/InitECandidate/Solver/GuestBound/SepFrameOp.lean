import InitECandidate.Solver.GuestBound.SepPushWord

/-!
# The scratch region of a frame, in a form every stack step preserves

A frame owns every address of its scratch interval `[pv, M)`: the tracked
cells (a fixed set `K`, owned elsewhere), the stack buffer, and the rest,
`JunkW M K pv base cap`. Allocations lower `pv`, so the junk grows; when the
stack moves, the old buffer joins the junk and the new one leaves it
(`junk_realloc`). When the frame ends, the whole interval can be given back.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- The addresses satisfying `P` are owned, with unknown content. -/
def Assn.OwnsW (P : Word → Prop) : Assn := Assn.Owns (fun k => ∃ x, k = .mem x ∧ P x)

theorem Assn.ownsW_split {P P1 P2 : Word → Prop} (hS : ∀ x, P x ↔ P1 x ∨ P2 x)
    (hd : ∀ x, P1 x → P2 x → False) : Assn.OwnsW P = (Assn.OwnsW P1 ⋆ Assn.OwnsW P2) := by
  refine Assn.owns_split (fun k => ?_) (fun k => ?_)
  · constructor
    · rintro ⟨x, rfl, hx⟩
      rcases (hS x).mp hx with h | h
      · exact Or.inl ⟨x, rfl, h⟩
      · exact Or.inr ⟨x, rfl, h⟩
    · rintro (⟨x, rfl, hx⟩ | ⟨x, rfl, hx⟩)
      · exact ⟨x, rfl, (hS x).mpr (Or.inl hx)⟩
      · exact ⟨x, rfl, (hS x).mpr (Or.inr hx)⟩
  · rintro ⟨x, rfl, hx⟩ ⟨y, hy, hy'⟩
    cases hy
    exact hd x hx hy'

theorem Assn.range_eq_ownsW (a b : Word) :
    Assn.Range a b = Assn.OwnsW (fun x => a.toNat ≤ x.toNat ∧ x.toNat < b.toNat) := rfl

/-- The part of a frame's scratch interval `[pv, M)` that is neither the stack
buffer nor a tracked cell. -/
def JunkW (M : Word) (K : Word → Prop) (pv base cap : Word) : Assn :=
  Assn.OwnsW (fun x => pv.toNat ≤ x.toNat ∧ x.toNat < M.toNat ∧
    ¬ (base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + 32 * cap.toNat) ∧ ¬ K x)

/-- The stack moved to a fresh block `[qv, qv + 32·nc)` below the old scratch
pointer: the unused tail of the allocation and the old buffer join the junk. -/
theorem junk_realloc {M : Word} {K : Word → Prop} {pv base cap qv nc : Word}
    (hT : (qv + 32#64 * nc).toNat = qv.toNat + 32 * nc.toNat)
    (hhi : (base + 32#64 * cap).toNat = base.toNat + 32 * cap.toNat)
    (hq : qv.toNat + 32 * nc.toNat ≤ pv.toNat) (hpb : pv.toNat ≤ base.toNat)
    (hbM : base.toNat + 32 * cap.toNat ≤ M.toNat)
    (hKpv : ∀ x, K x → pv.toNat ≤ x.toNat)
    (hKst : ∀ x, K x → ¬ (base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + 32 * cap.toNat)) :
    (Assn.Range (qv + 32#64 * nc) pv ⋆ Assn.Range base (base + 32#64 * cap) ⋆
      JunkW M K pv base cap) = JunkW M K qv qv nc := by
  classical
  rw [Assn.range_eq_ownsW, Assn.range_eq_ownsW]
  unfold JunkW
  rw [← Assn.ownsW_split (P := fun x => (base.toNat ≤ x.toNat ∧
      x.toNat < (base + 32#64 * cap).toNat) ∨ (pv.toNat ≤ x.toNat ∧ x.toNat < M.toNat ∧
      ¬ (base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + 32 * cap.toNat) ∧ ¬ K x))
    (fun x => Iff.rfl) (fun x h1 h2 => h2.2.2.1 ⟨h1.1, by omega⟩)]
  refine (Assn.ownsW_split (fun x => ?_) (fun x h1 h2 => ?_)).symm
  · constructor
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hx : x.toNat < pv.toNat
      · exact Or.inl ⟨by omega, hx⟩
      · right
        by_cases hb : base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + 32 * cap.toNat
        · exact Or.inl ⟨hb.1, by omega⟩
        · exact Or.inr ⟨by omega, h2, hb, h4⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨by omega, by omega, by omega, fun hk => by have := hKpv x hk; omega⟩
      · exact ⟨by omega, by omega, by omega, fun hk => hKst x hk ⟨h1, by omega⟩⟩
      · exact ⟨by omega, h2, by omega, h4⟩
  · rcases h2 with ⟨h2, h3⟩ | ⟨h2, -⟩
    · omega
    · omega

/-- An allocation that is not used for the stack: the block joins the junk. -/
theorem junk_alloc {M : Word} {K : Word → Prop} {pv base cap qv : Word}
    (hq : qv.toNat ≤ pv.toNat) (hpb : pv.toNat ≤ base.toNat) (hpM : pv.toNat ≤ M.toNat)
    (hKpv : ∀ x, K x → pv.toNat ≤ x.toNat) :
    (Assn.Range qv pv ⋆ JunkW M K pv base cap) = JunkW M K qv base cap := by
  rw [Assn.range_eq_ownsW]
  unfold JunkW
  refine (Assn.ownsW_split (fun x => ?_) (fun x h1 h2 => ?_)).symm
  · constructor
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hx : x.toNat < pv.toNat
      · exact Or.inl ⟨h1, hx⟩
      · exact Or.inr ⟨by omega, h2, h3, h4⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨h1, by omega, by omega, fun hk => by have := hKpv x hk; omega⟩
      · exact ⟨by omega, h2, h3, h4⟩
  · omega

end InitECandidate.Solver.GuestBound
