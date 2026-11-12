import InitECandidate.Solver.GuestBound.PolyRules

/-!
# `fq_poly_submul`

`a[s + i] -= q * b[i]` for `i ≤ db`, on canonical coefficients in disjoint
buffers.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Memory after storing four words at `a`. -/
abbrev set4 (m : Word → Option (PanValue Word)) (a w0 w1 w2 w3 : Word) :
    Word → Option (PanValue Word) :=
  setCell (setCell (setCell (setCell m a w0) (a + 8#64) w1) (a + 8#64 + 8#64) w2)
    (a + 8#64 + 8#64 + 8#64) w3

theorem a8_toNat {a : Word} (h : a.toNat + 32 ≤ 2 ^ 64) : (a + 8#64).toNat = a.toNat + 8 := by
  rw [off8]; exact off_toNat (by omega)

theorem a16_toNat {a : Word} (h : a.toNat + 32 ≤ 2 ^ 64) :
    (a + 8#64 + 8#64).toNat = a.toNat + 16 := by
  rw [off16]; exact off_toNat (by omega)

theorem a24_toNat {a : Word} (h : a.toNat + 32 ≤ 2 ^ 64) :
    (a + 8#64 + 8#64 + 8#64).toNat = a.toNat + 24 := by
  rw [off24]; exact off_toNat (by omega)

theorem set4_other {m : Word → Option (PanValue Word)} {a w0 w1 w2 w3 x : Word}
    (h64 : a.toNat + 32 ≤ 2 ^ 64) (hx : x.toNat < a.toNat ∨ a.toNat + 32 ≤ x.toNat) :
    set4 m a w0 w1 w2 w3 x = m x := by
  have NE : ∀ {p q : Word}, p.toNat ≠ q.toNat → p ≠ q := fun h e => h (congrArg _ e)
  unfold set4
  rw [setCell_ne' _ (NE (by rw [a24_toNat h64]; omega)),
    setCell_ne' _ (NE (by rw [a16_toNat h64]; omega)),
    setCell_ne' _ (NE (by rw [a8_toNat h64]; omega)), setCell_ne' _ (NE (by omega))]

theorem fe_set4 {m : Word → Option (PanValue Word)} {a w0 w1 w2 w3 : Word}
    (h64 : a.toNat + 32 ≤ 2 ^ 64) : Fe (set4 m a w0 w1 w2 w3) a (limbsVal [w0, w1, w2, w3]) := by
  have NE : ∀ {p q : Word}, p.toNat ≠ q.toNat → p ≠ q := fun h e => h (congrArg _ e)
  have h8 := a8_toNat h64
  have h16 := a16_toNat h64
  have h24 := a24_toNat h64
  unfold set4
  refine ⟨w0, w1, w2, w3, ?_, ?_, ?_, ?_, rfl⟩
  · exact (((Rd.here m a w0).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))
  · exact ((Rd.here _ _ w1).frame _ (NE (by omega))).frame _ (NE (by omega))
  · exact (Rd.here _ _ w2).frame _ (NE (by omega))
  · exact Rd.here _ _ w3

theorem fe_congr {m m' : Word → Option (PanValue Word)} {a : Word} {n : Nat}
    (h64 : a.toNat + 32 ≤ 2 ^ 64)
    (h : ∀ x : Word, a.toNat ≤ x.toNat → x.toNat < a.toNat + 32 → m' x = m x)
    (hfe : Fe m a n) : Fe m' a n := by
  obtain ⟨w0, w1, w2, w3, c0, c1, c2, c3, hn⟩ := hfe
  refine ⟨w0, w1, w2, w3, ?_, ?_, ?_, ?_, hn⟩
  · rw [h a (Nat.le_refl _) (by omega)]; exact c0
  · rw [h _ (by rw [a8_toNat h64]; omega) (by rw [a8_toNat h64]; omega)]; exact c1
  · rw [h _ (by rw [a16_toNat h64]; omega) (by rw [a16_toNat h64]; omega)]; exact c2
  · rw [h _ (by rw [a24_toNat h64]; omega) (by rw [a24_toNat h64]; omega)]; exact c3

end InitECandidate.Solver.GuestBound
