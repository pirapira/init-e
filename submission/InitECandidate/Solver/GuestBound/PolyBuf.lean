import InitECandidate.Solver.GuestBound.MemZero
import InitECandidate.Solver.GuestBound.HtabGrowInv

/-!
# Polynomial buffers: zeroing, copying, frames, and the degree read from memory
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m m' m0 : Word → Option (PanValue Word)}

theorem Fe.unique {a : Word} {n n' : Nat} (h : Fe m a n) (h' : Fe m a n') : n = n' := by
  obtain ⟨w0, w1, w2, w3, c0, c1, c2, c3, hn⟩ := h
  obtain ⟨v0, v1, v2, v3, e0, e1, e2, e3, hn'⟩ := h'
  rw [c0] at e0
  rw [c1] at e1
  rw [c2] at e2
  rw [c3] at e3
  simp only [Option.some.injEq, PanValue.word.injEq] at e0 e1 e2 e3
  subst e0 e1 e2 e3
  exact hn.symm.trans hn'

/-- A buffer keeps its polynomial when its cells are unchanged. -/
theorem PolyAt.frame {A : Word} {c : Nat → Nat} {n : Nat} (h64 : A.toNat + 32 * n ≤ 2 ^ 64)
    (h : ∀ x : Word, A.toNat ≤ x.toNat → x.toNat < A.toNat + 32 * n → m' x = m x)
    (hp : PolyAt m A c n) : PolyAt m' A c n := by
  intro i hi
  have hc := coefAddr_toNat (a := A) (i := i) (by omega)
  exact fe_congr (by rw [hc]; omega) (fun x h1 h2 => h x (by rw [hc] at h1; omega)
    (by rw [hc] at h2; omega)) (hp i hi)

/-- A zeroed block is the zero polynomial. -/
theorem PolyAt.of_zero {A : Word} {n : Nat} (hal : A.toNat % 8 = 0)
    (h64 : A.toNat + 32 * n ≤ 2 ^ 64) (h : ZeroRel m m' A (32 * n)) :
    PolyAt m' A (fun _ => 0) n := by
  intro i hi
  have hc := coefAddr_toNat (a := A) (i := i) (by omega)
  have hb : (coefAddr A i).toNat + 32 ≤ 2 ^ 64 := by rw [hc]; omega
  refine ⟨0#64, 0#64, 0#64, 0#64, ?_, ?_, ?_, ?_, show limbsVal [0#64, 0#64, 0#64, 0#64] = 0 by decide⟩
  · rw [h, if_pos ⟨by rw [hc]; omega, by rw [hc]; omega, by rw [hc]; omega⟩]
  · rw [h, if_pos ⟨by rw [a8_toNat hb, hc]; omega, by rw [a8_toNat hb, hc]; omega,
      by rw [a8_toNat hb, hc]; omega⟩]
  · rw [h, if_pos ⟨by rw [a16_toNat hb, hc]; omega, by rw [a16_toNat hb, hc]; omega,
      by rw [a16_toNat hb, hc]; omega⟩]
  · rw [h, if_pos ⟨by rw [a24_toNat hb, hc]; omega, by rw [a24_toNat hb, hc]; omega,
      by rw [a24_toNat hb, hc]; omega⟩]

/-- One aligned cell carried across a copy. -/
theorem CopyInv.cell {dst src : Word} {n : Nat} (h : CopyInv m0 dst src n m)
    (hd8 : dst.toNat % 8 = 0) (hs8 : src.toNat % 8 = 0) (hd : dst.toNat + n < 2 ^ 64)
    (hs : src.toNat + n < 2 ^ 64) {X Y : Word} {o : Nat} (hX : X.toNat = src.toNat + o)
    (hY : Y.toNat = dst.toNat + o) (ho : o % 8 = 0) (hon : o + 8 ≤ n) {w : Word}
    (hw : m0 X = some (.word w)) : m Y = some (.word w) := by
  refine (rd_iff_bytes (M := m0) (M' := m) (X := X) (Y := Y) w (by omega) (by omega) (by omega)
    (by omega) ?_).mp hw
  intro k hk
  have e1 : off X k = off src (o + k) := by
    apply BitVec.eq_of_toNat_eq
    rw [off_toNat (by omega), off_toNat (by omega)]
    omega
  have e2 : off Y k = off dst (o + k) := by
    apply BitVec.eq_of_toNat_eq
    rw [off_toNat (by omega), off_toNat (by omega)]
    omega
  rw [e1, e2]
  exact (h.copied (o + k) (by omega)).symm

/-- A copied buffer holds the same polynomial. -/
theorem PolyAt.of_copy {dst src : Word} {c : Nat → Nat} {n : Nat}
    (h : CopyInv m0 dst src (32 * n) m) (hd8 : dst.toNat % 8 = 0) (hs8 : src.toNat % 8 = 0)
    (hd : dst.toNat + 32 * n < 2 ^ 64) (hs : src.toNat + 32 * n < 2 ^ 64)
    (hp : PolyAt m0 src c n) : PolyAt m dst c n := by
  intro i hi
  obtain ⟨w0, w1, w2, w3, c0, c1, c2, c3, hn⟩ := hp i hi
  have hcs := coefAddr_toNat (a := src) (i := i) (by omega)
  have hcd := coefAddr_toNat (a := dst) (i := i) (by omega)
  have hbs : (coefAddr src i).toNat + 32 ≤ 2 ^ 64 := by rw [hcs]; omega
  have hbd : (coefAddr dst i).toNat + 32 ≤ 2 ^ 64 := by rw [hcd]; omega
  refine ⟨w0, w1, w2, w3, ?_, ?_, ?_, ?_, hn⟩
  · exact h.cell hd8 hs8 hd hs (o := 32 * i) hcs hcd (by omega) (by omega) c0
  · exact h.cell hd8 hs8 hd hs (o := 32 * i + 8) (by rw [a8_toNat hbs, hcs]; omega)
      (by rw [a8_toNat hbd, hcd]; omega) (by omega) (by omega) c1
  · exact h.cell hd8 hs8 hd hs (o := 32 * i + 16) (by rw [a16_toNat hbs, hcs]; omega)
      (by rw [a16_toNat hbd, hcd]; omega) (by omega) (by omega) c2
  · exact h.cell hd8 hs8 hd hs (o := 32 * i + 24) (by rw [a24_toNat hbs, hcs]; omega)
      (by rw [a24_toNat hbd, hcd]; omega) (by omega) (by omega) c3

open Classical in
/-- Index of the highest nonzero coefficient among the 13 at `A` (0 if none). -/
noncomputable def topIdx (m : Word → Option (PanValue Word)) (A : Word) : Nat :=
  Nat.findGreatest (fun i => ¬ Fe m (coefAddr A i) 0) 12

open Classical in
theorem topIdx_eq {A : Word} {c : Nat → Nat} {d : Nat} (hp : PolyAt m A c 13) (hd : d < 13)
    (hnz : c d ≠ 0) (hz : ∀ i, d < i → i < 13 → c i = 0) : topIdx m A = d := by
  unfold topIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun _ hfe => hnz ((hp d hd).unique hfe), ?_⟩
  intro n hn hn12 hnot
  have := hp n (by omega)
  rw [hz n hn (by omega)] at this
  exact hnot this

open Classical in
theorem topIdx_zero {A : Word} {c : Nat → Nat} (hp : PolyAt m A c 13)
    (hz : ∀ i, i < 13 → c i = 0) : topIdx m A = 0 := by
  unfold topIdx
  rw [Nat.findGreatest_eq_iff]
  refine ⟨Nat.zero_le _, fun h => absurd rfl h, ?_⟩
  intro n hn hn12 hnot
  have := hp n (by omega)
  rw [hz n (by omega)] at this
  exact hnot this

end InitECandidate.Solver.GuestBound
