import InitECandidate.Solver.SourceTerminationBound


set_option autoImplicit false

/-!
# Yukon verification-speed score bounds

This module records the exact natural-number encoding used by the Yukon score,
the five-percent record rule, and the sharp IEEE-754 exact-integer bound.
-/

namespace InitECandidate.Solver

/-- Yukon orders a candidate first by `K`, then by capped verification minutes. -/
def yukonScore (K verifyMinutes : Nat) : Nat :=
  K * 10000 + min verifyMinutes 9999

/-- A candidate improves the verification-time record by at least five percent. -/
def improvesRecordByFivePercent (verifySeconds recordSeconds : Nat) : Prop :=
  verifySeconds * 20 ≤ recordSeconds * 19

theorem improvesRecordByFivePercent_iff (verifySeconds recordSeconds : Nat) :
    improvesRecordByFivePercent verifySeconds recordSeconds ↔
      verifySeconds * 20 ≤ recordSeconds * 19 := by
  rfl

/-- The capped minute component is always a valid four-digit suffix. -/
theorem yukonScore_suffix_bound (K verifyMinutes : Nat) :
    yukonScore K verifyMinutes ≤ K * 10000 + 9999 := by
  simp [yukonScore, Nat.min_le_right]

/-- Sharp uniform bound ensuring that every capped Yukon score is exactly
representable as a JavaScript/IEEE-754 integer below `2^53 - 1`. -/
theorem yukonScore_lt_two_pow_53_sub_one
    {K verifyMinutes : Nat} (hK : K ≤ 900719925473) :
    yukonScore K verifyMinutes < 2 ^ 53 - 1 := by
  unfold yukonScore
  have hm : min verifyMinutes 9999 ≤ 9999 := Nat.min_le_right _ _
  omega

/-- At the next `K`, exact representability holds precisely while the capped
minute suffix is at most `990`. -/
theorem yukonScore_boundary_iff (verifyMinutes : Nat) :
    yukonScore 900719925474 verifyMinutes < 2 ^ 53 - 1 ↔
      min verifyMinutes 9999 ≤ 990 := by
  unfold yukonScore
  omega

/-- Consequently, the proposed uniform bound `K ≤ 900719925474` is false. -/
theorem yukonScore_requested_bound_counterexample :
    900719925474 ≤ 900719925474 ∧
      ¬ yukonScore 900719925474 9999 < 2 ^ 53 - 1 := by
  unfold yukonScore
  omega

end InitECandidate.Solver
