import InitECandidate.Solver.GuestBound.HtabDel

/-!
# Hash tables: a fresh table satisfies the invariant
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

theorem strideOf_ge (kl : Word) (hkl : kl.toNat * 8 < 2 ^ 64) :
    kl.toNat ≤ (strideOf kl).toNat := by
  unfold strideOf
  rw [and_m8]
  have h7 : (7#64 + 0 : Word).toNat = 7 := by decide
  rw [BitVec.toNat_add, h7, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The table written by `htab_new` satisfies `HtabOK`, for sizes that do not wrap. -/
theorem htab_new_ok (m : Word → Option (PanValue Word)) (t kl cp keys nodes order q4 : Word)
    (rep : KeyRep) (h1 : t.toNat + 88 ≤ keys.toNat)
    (h2 : keys.toNat + ((ncapOf cp + 1#64) * strideOf kl).toNat ≤ nodes.toNat)
    (h3 : nodes.toNat + ((ncapOf cp + 1#64) * 32#64).toNat ≤ order.toNat)
    (h4 : order.toNat + ((ncapOf cp + 1#64) * 8#64).toNat ≤ q4.toNat)
    (h5 : q4.toNat ≤ 2952790016) (h8 : keys.toNat % 8 = 0) (hn8 : nodes.toNat % 8 = 0)
    (ho8 : order.toNat % 8 = 0) (hkl : kl.toNat * 8 < 2 ^ 64)
    (hcap : (ncapOf cp).toNat + 1 < 2 ^ 58)
    (hnw : ((ncapOf cp).toNat + 1) * (strideOf kl).toNat < 2 ^ 64) :
    HtabOK (htabHeader m t kl cp keys nodes order) t
      ⟨kl, strideOf kl, cp, ncapOf cp, 0#64, keys, nodes, order, 0#64, 1#64, 0#64⟩
      (fun _ => .free) rep := by
  have hone : (1#64 : Word).toNat = 1 := by decide
  have hadd : (ncapOf cp + 1#64).toNat = (ncapOf cp).toNat + 1 := by
    rw [BitVec.toNat_add, hone]
    exact Nat.mod_eq_of_lt (by omega)
  have h32 : (32#64 : Word).toNat = 32 := by decide
  have h8' : (8#64 : Word).toNat = 8 := by decide
  rw [BitVec.toNat_mul, hadd, Nat.mod_eq_of_lt hnw] at h2
  rw [BitVec.toNat_mul, hadd, h32, Nat.mod_eq_of_lt (by omega)] at h3
  rw [BitVec.toNat_mul, hadd, h8', Nat.mod_eq_of_lt (by omega)] at h4
  have hlay : HtabLayout t
      ⟨kl, strideOf kl, cp, ncapOf cp, 0#64, keys, nodes, order, 0#64, 1#64, 0#64⟩ :=
    ⟨h1, h2, h3, by show order.toNat + ((ncapOf cp).toNat + 1) * 8 ≤ 2952790016; omega⟩
  have hncp : 1 ≤ (ncapOf cp).toNat := by
    unfold ncapOf
    split
    · decide
    · rename_i hcp
      rw [BitVec.lt_def] at hcp
      have h2 : (2#64 : Word).toNat = 2 := by decide
      omega
  refine ⟨htabWF_new m t kl cp keys nodes order hlay, ⟨?_⟩, h8, hn8, ho8, hncp, strideOf_ge kl hkl,
    hkl, ?_⟩
  · intro i _ _ h
    cases h
  · intro i _ _ h
    cases h

end InitECandidate.Solver.GuestBound
