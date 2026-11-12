import Mathlib.Tactic

/-!
# The arithmetic of a 64×64 → 128 bit product from 32-bit partial products
-/

namespace InitECandidate.Solver.GuestBound

/-- With `mid = p01 + p10` split into its low 64 bits and carry, and the low
word's carry, the high and low words recombine to the full product. The partial
products only need their size bounds. -/
theorem m64_nat (p00 p01 p10 p11 : Nat) (b00 : p00 ≤ 4294967295 * 4294967295)
    (b01 : p01 ≤ 4294967295 * 4294967295) (b10 : p10 ≤ 4294967295 * 4294967295)
    (b11 : p11 ≤ 4294967295 * 4294967295) (mid0 mid1 sh lo0 lo1 q : Nat)
    (hmid0 : mid0 = (p01 + p10) % 18446744073709551616)
    (hmid1 : mid1 = if 18446744073709551616 ≤ p01 + p10 then 1 else 0)
    (hsh : sh = mid0 * 4294967296 % 18446744073709551616)
    (hlo0 : lo0 = (p00 + sh) % 18446744073709551616)
    (hlo1 : lo1 = if 18446744073709551616 ≤ p00 + sh then 1 else 0)
    (hq : q = mid0 / 4294967296) :
    (p11 + q + mid1 * 4294967296 + lo1) % 18446744073709551616 * 18446744073709551616 + lo0 =
      p11 * 18446744073709551616 + (p01 + p10) * 4294967296 + p00 := by
  subst hmid0 hsh hlo0 hq
  split_ifs at hmid1 hlo1 <;> subst hmid1 hlo1 <;> omega

end InitECandidate.Solver.GuestBound
