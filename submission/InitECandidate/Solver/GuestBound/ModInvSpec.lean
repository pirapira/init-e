import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic
import InitECandidate.Solver.GuestBound.Manual.ModInv
import InitECandidate.Solver.GuestBound.ModHalf
import InitECandidate.Solver.GuestBound.HtabDiff

/-!
# `modinv_bin` computes a modular inverse

Partial correctness of the binary extended Euclid: with `m` odd, the loop
keeps `u ≡ x1 * a` and `v ≡ x2 * a` modulo `m`, so the value returned when
`u = 1` (or `v = 1`) is an inverse of `a`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- Halving both sides keeps `u ≡ x * a (mod m)` when `m` is odd. -/
theorem half_inv {U X A M : Nat} (hM : M % 2 = 1) (hU : U % 2 = 0)
    (h : U % M = X * A % M) :
    (U / 2) % M = (if X % 2 = 0 then X / 2 else (X + M) / 2) * A % M := by
  have hcop : Nat.gcd M 2 = 1 := by
    rw [Nat.gcd_comm, Nat.gcd_rec, hM]
    exact Nat.gcd_one_left 2
  have h2 : 2 * (if X % 2 = 0 then X / 2 else (X + M) / 2) ≡ X [MOD M] := by
    by_cases hx : X % 2 = 0
    · rw [if_pos hx]
      have : 2 * (X / 2) = X := by omega
      rw [this]
    · rw [if_neg hx]
      have : 2 * ((X + M) / 2) = X + M := by omega
      rw [this]
      exact Nat.add_modEq_right
  have hU2 : 2 * (U / 2) = U := by omega
  have key : 2 * (U / 2) ≡ 2 * ((if X % 2 = 0 then X / 2 else (X + M) / 2) * A) [MOD M] := by
    rw [hU2, ← Nat.mul_assoc]
    exact (show U ≡ X * A [MOD M] from h).trans (h2.mul_right A).symm
  exact Nat.ModEq.cancel_left_of_coprime hcop key

/-- Subtracting keeps the congruences. -/
theorem sub_inv {U V X1 X2 A M : Nat} (hX2 : X2 < M) (hVU : V ≤ U)
    (hu : U % M = X1 * A % M) (hv : V % M = X2 * A % M) :
    (U - V) % M = (if X1 < X2 then X1 + M - X2 else X1 - X2) * A % M := by
  have hd : (if X1 < X2 then X1 + M - X2 else X1 - X2) + X2 ≡ X1 [MOD M] := by
    by_cases hlt : X1 < X2
    · rw [if_pos hlt]
      have : X1 + M - X2 + X2 = X1 + M := by omega
      rw [this]
      exact Nat.add_modEq_right
    · rw [if_neg hlt]
      have : X1 - X2 + X2 = X1 := by omega
      rw [this]
  have h1 : (if X1 < X2 then X1 + M - X2 else X1 - X2) * A + X2 * A ≡ (U - V) + X2 * A [MOD M] := by
    rw [← Nat.add_mul]
    have hUV : U - V + V = U := by omega
    calc ((if X1 < X2 then X1 + M - X2 else X1 - X2) + X2) * A ≡ X1 * A [MOD M] := hd.mul_right A
      _ ≡ U [MOD M] := (show U ≡ X1 * A [MOD M] from hu).symm
      _ = U - V + V := hUV.symm
      _ ≡ U - V + X2 * A [MOD M] := Nat.ModEq.add_left _ (show V ≡ X2 * A [MOD M] from hv)
  exact (Nat.ModEq.add_right_cancel' _ h1).symm

end InitECandidate.Solver.GuestBound
