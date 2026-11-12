import Mathlib.Tactic.Ring

/-!
# Carry chains on 64-bit limbs

Pure arithmetic behind the multi-limb helpers of the guest: subtracting limb
lists by adding the complement with a carry chain.
-/

namespace InitECandidate.Solver.GuestBound

/-- The number represented by little-endian limbs. -/
def nval : List Nat → Nat
  | [] => 0
  | x :: xs => x + 2 ^ 64 * nval xs

/-- Limbs of `a + ~b + c`, as computed by a chain of add-with-carry steps. -/
def subLimbs : List Nat → List Nat → Nat → List Nat
  | a :: as, b :: bs, c =>
      (a + (2 ^ 64 - 1 - b) + c) % 2 ^ 64 ::
        subLimbs as bs (if 2 ^ 64 ≤ a + (2 ^ 64 - 1 - b) + c then 1 else 0)
  | _, _, _ => []

theorem nval_lt : ∀ (xs : List Nat), (∀ x ∈ xs, x < 2 ^ 64) → nval xs < 2 ^ (64 * xs.length)
  | [], _ => by simp [nval]
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := nval_lt xs (fun y hy => h y (by simp [hy]))
    have hpow : 2 ^ (64 * (x :: xs).length) = 2 ^ 64 * 2 ^ (64 * xs.length) := by
      rw [List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [hpow]
    simp only [nval]
    generalize 2 ^ (64 * xs.length) = W at ih ⊢
    generalize nval xs = N at ih ⊢
    have : 2 ^ 64 * N + 2 ^ 64 ≤ 2 ^ 64 * W := by
      have : N + 1 ≤ W := ih
      calc 2 ^ 64 * N + 2 ^ 64 = 2 ^ 64 * (N + 1) := by ring
        _ ≤ 2 ^ 64 * W := Nat.mul_le_mul_left _ this
    omega

theorem subLimbs_lt : ∀ (as bs : List Nat) (c : Nat), ∀ x ∈ subLimbs as bs c, x < 2 ^ 64
  | [], _, _ => by simp [subLimbs]
  | _ :: _, [], _ => by simp [subLimbs]
  | a :: as, b :: bs, c => by
    intro x hx
    simp only [subLimbs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by decide)
    · exact subLimbs_lt as bs _ x hx

theorem subLimbs_length : ∀ (as bs : List Nat) (c : Nat), as.length = bs.length →
    (subLimbs as bs c).length = as.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, c, h => by
    simp only [subLimbs, List.length_cons]
    rw [subLimbs_length as bs _ (by simpa using h)]

/-- The carry chain computes `a - b - 1 + c` modulo `2^(64 n)`, with a carry out. -/
theorem subLimbs_val : ∀ (as bs : List Nat) (c : Nat), as.length = bs.length →
    (∀ x ∈ as, x < 2 ^ 64) → (∀ x ∈ bs, x < 2 ^ 64) → c ≤ 1 →
    ∃ c', c' ≤ 1 ∧ nval (subLimbs as bs c) + c' * 2 ^ (64 * as.length) + nval bs + 1 =
      nval as + 2 ^ (64 * as.length) + c
  | [], [], c, _, _, _, hc => ⟨c, hc, by simp [subLimbs, nval]; omega⟩
  | [], _ :: _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, h, _, _, _ => by simp at h
  | a :: as, b :: bs, c, h, ha, hb, hc => by
    have ha0 := ha a (by simp)
    have hb0 := hb b (by simp)
    obtain ⟨c', hc', ih⟩ := subLimbs_val as bs (if 2 ^ 64 ≤ a + (2 ^ 64 - 1 - b) + c then 1 else 0)
      (by simpa using h) (fun y hy => ha y (by simp [hy])) (fun y hy => hb y (by simp [hy]))
      (by split_ifs <;> omega)
    refine ⟨c', hc', ?_⟩
    have hpow : 2 ^ (64 * (a :: as).length) = 2 ^ 64 * 2 ^ (64 * as.length) := by
      rw [List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [hpow]
    simp only [subLimbs, nval]
    generalize 2 ^ (64 * as.length) = W at ih ⊢
    generalize nval (subLimbs as bs (if 2 ^ 64 ≤ a + (2 ^ 64 - 1 - b) + c then 1 else 0)) = D
      at ih ⊢
    generalize nval as = A at ih ⊢
    generalize nval bs = B at ih ⊢
    have hmod := Nat.mod_add_div (a + (2 ^ 64 - 1 - b) + c) (2 ^ 64)
    have hcarry : (if 2 ^ 64 ≤ a + (2 ^ 64 - 1 - b) + c then 1 else 0) =
        (a + (2 ^ 64 - 1 - b) + c) / 2 ^ 64 := by
      split_ifs <;> omega
    rw [hcarry] at ih
    generalize (a + (2 ^ 64 - 1 - b) + c) / 2 ^ 64 = q at ih hmod
    generalize (a + (2 ^ 64 - 1 - b) + c) % 2 ^ 64 = d at hmod ⊢
    have h64 : 2 ^ 64 * (D + c' * W + B + 1) = 2 ^ 64 * (A + W + q) := by rw [ih]
    have e1 : c' * (2 ^ 64 * W) = 2 ^ 64 * (c' * W) := by ring
    rw [e1]
    generalize c' * W = CW at h64 ⊢
    omega

/-- Without a borrow, the low limbs are the limbs of the difference. -/
theorem subLimbs_sub (as bs : List Nat) (h : as.length = bs.length)
    (ha : ∀ x ∈ as, x < 2 ^ 64) (hb : ∀ x ∈ bs, x < 2 ^ 64) (hle : nval bs ≤ nval as) :
    nval (subLimbs as bs 1) = nval as - nval bs := by
  obtain ⟨c', hc', hval⟩ := subLimbs_val as bs 1 h ha hb (Nat.le_refl 1)
  have hd := nval_lt (subLimbs as bs 1) (subLimbs_lt as bs 1)
  rw [subLimbs_length as bs 1 h] at hd
  have hA := nval_lt as ha
  generalize 2 ^ (64 * as.length) = W at hval hd hA
  generalize nval (subLimbs as bs 1) = D at hval hd ⊢
  generalize nval as = A at hval hA hle ⊢
  generalize nval bs = B at hval hle ⊢
  rcases Nat.lt_or_ge c' 1 with h0 | h1
  · have : c' = 0 := by omega
    subst this
    omega
  · have : c' = 1 := by omega
    subst this
    omega

/-- Limbs of `a + b + c`, as computed by a chain of add-with-carry steps. -/
def addLimbs : List Nat → List Nat → Nat → List Nat
  | a :: as, b :: bs, c =>
      (a + b + c) % 2 ^ 64 :: addLimbs as bs (if 2 ^ 64 ≤ a + b + c then 1 else 0)
  | _, _, _ => []

theorem addLimbs_lt : ∀ (as bs : List Nat) (c : Nat), ∀ x ∈ addLimbs as bs c, x < 2 ^ 64
  | [], _, _ => by simp [addLimbs]
  | _ :: _, [], _ => by simp [addLimbs]
  | a :: as, b :: bs, c => by
    intro x hx
    simp only [addLimbs, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by decide)
    · exact addLimbs_lt as bs _ x hx

theorem addLimbs_length : ∀ (as bs : List Nat) (c : Nat), as.length = bs.length →
    (addLimbs as bs c).length = as.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, c, h => by
    simp only [addLimbs, List.length_cons]
    rw [addLimbs_length as bs _ (by simpa using h)]

/-- The carry chain computes `a + b + c` modulo `2^(64 n)`, with a carry out. -/
theorem addLimbs_val : ∀ (as bs : List Nat) (c : Nat), as.length = bs.length →
    (∀ x ∈ as, x < 2 ^ 64) → (∀ x ∈ bs, x < 2 ^ 64) → c ≤ 1 →
    ∃ c', c' ≤ 1 ∧ nval (addLimbs as bs c) + c' * 2 ^ (64 * as.length) =
      nval as + nval bs + c
  | [], [], c, _, _, _, hc => ⟨c, hc, by simp [addLimbs, nval]⟩
  | [], _ :: _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, h, _, _, _ => by simp at h
  | a :: as, b :: bs, c, h, ha, hb, hc => by
    have ha0 := ha a (by simp)
    have hb0 := hb b (by simp)
    obtain ⟨c', hc', ih⟩ := addLimbs_val as bs (if 2 ^ 64 ≤ a + b + c then 1 else 0)
      (by simpa using h) (fun y hy => ha y (by simp [hy])) (fun y hy => hb y (by simp [hy]))
      (by split_ifs <;> omega)
    refine ⟨c', hc', ?_⟩
    have hpow : 2 ^ (64 * (a :: as).length) = 2 ^ 64 * 2 ^ (64 * as.length) := by
      rw [List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    rw [hpow]
    simp only [addLimbs, nval]
    generalize 2 ^ (64 * as.length) = W at ih ⊢
    generalize nval (addLimbs as bs (if 2 ^ 64 ≤ a + b + c then 1 else 0)) = D at ih ⊢
    generalize nval as = A at ih ⊢
    generalize nval bs = B at ih ⊢
    have hmod := Nat.mod_add_div (a + b + c) (2 ^ 64)
    have hcarry : (if 2 ^ 64 ≤ a + b + c then 1 else 0) = (a + b + c) / 2 ^ 64 := by
      split_ifs <;> omega
    rw [hcarry] at ih
    generalize (a + b + c) / 2 ^ 64 = q at ih hmod
    generalize (a + b + c) % 2 ^ 64 = d at hmod ⊢
    have h64 : 2 ^ 64 * (D + c' * W) = 2 ^ 64 * (A + B + q) := by rw [ih]
    have e1 : c' * (2 ^ 64 * W) = 2 ^ 64 * (c' * W) := by ring
    rw [e1]
    generalize c' * W = CW at h64 ⊢
    omega

/-- Limbs of the number shifted right by one bit. -/
def shrLimbs : List Nat → List Nat
  | [] => []
  | [x] => [x / 2]
  | x :: y :: rest => (x / 2 + (y % 2) * 2 ^ 63) :: shrLimbs (y :: rest)

theorem nval_parity : ∀ (xs : List Nat), nval xs % 2 = (xs.headD 0) % 2
  | [] => rfl
  | x :: xs => by
    simp only [nval, List.headD_cons]
    omega

/-- Shifting the limbs right by one bit halves the number. -/
theorem shrLimbs_val : ∀ (xs : List Nat), nval (shrLimbs xs) = nval xs / 2
  | [] => rfl
  | [x] => by simp [shrLimbs, nval]
  | x :: y :: rest => by
    have ih := shrLimbs_val (y :: rest)
    have hp := nval_parity (y :: rest)
    simp only [List.headD_cons] at hp
    simp only [shrLimbs, nval] at ih hp ⊢
    generalize nval (shrLimbs (y :: rest)) = D at ih ⊢
    generalize y + 2 ^ 64 * nval rest = N at ih hp ⊢
    omega

end InitECandidate.Solver.GuestBound
