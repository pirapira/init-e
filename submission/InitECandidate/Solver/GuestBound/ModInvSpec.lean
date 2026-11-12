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

variable {σ : Type} {E : Env σ} {Q : Result σ → Prop}

set_option maxHeartbeats 4000000 in
/-- `if (x.1 | x.2 | x.3) == 0 { if x.0 == 1 { return y; } }; rest`: returns
`y` only when `x` holds 1. -/
theorem retCheck4_wp (hE : GuestEnv E) {x y : VarName} {rest : Prog Word} {s : St σ}
    {w0 w1 w2 w3 y0 y1 y2 y3 : Word}
    (hx : s.locals x = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (hy : s.locals y = some (.rStruct [.word y0, .word y1, .word y2, .word y3]))
    (hcont : WPs E s rest Q)
    (hret : limbsVal [w0, w1, w2, w3] = 1 →
      Q (.returned (fun _ => none) s.globals s.memory s.ffi
        [.rStruct [.word y0, .word y1, .word y2, .word y3]])) :
    WPs E s (.seq (retCheck4 x y) rest) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  rw [runs_ite] at h1
  simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_op hE.word, evalF_rField,
    evalF_local, eval_const, evalArgs_cons, evalArgs_nil, hx, Option.map_some,
    List.getElem?_cons_zero, List.getElem?_cons_succ, wordsProj_nil, wordsProj_cons, wordOp,
    List.foldr] at h1
  have skip : r1 = .normal s.locals s.globals s.memory s.ffi → Stopped r ∨ Q r := by
    intro e
    subst e
    exact hcont r hrest
  obtain ⟨W, hW⟩ : ∃ W : Word, W = OrOp.or w1 (OrOp.or w2 (OrOp.or w3 (0 : Word))) := ⟨_, rfl⟩
  rw [← hW] at h1
  by_cases hz : W = 0#64
  · have hc : evalPanCmp .equal W 0#64 = 1#64 := by
      rw [hz]
      rfl
    rw [hc, if_neg (by decide)] at h1
    rw [runs_ite] at h1
    simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_rField, evalF_local,
      eval_const, hx, List.getElem?_cons_zero] at h1
    by_cases h01 : w0 = 1#64
    · have hc2 : evalPanCmp .equal w0 1#64 = 1#64 := by simp [evalPanCmp, h01]
      rw [hc2, if_neg (by decide)] at h1
      rw [runs_return] at h1
      simp (config := { decide := true }) only [evalF_local, hy, payload_words4, if_true] at h1
      subst h1
      simp only at hrest
      subst hrest
      refine Or.inr (hret ?_)
      have hz' : w1 ||| (w2 ||| (w3 ||| (0 : Word))) = 0#64 := hW.symm.trans hz
      rw [BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff] at hz'
      obtain ⟨e1, e2, e3, -⟩ := hz'
      subst h01 e1 e2 e3
      rfl
    · have hc2 : evalPanCmp .equal w0 1#64 = 0#64 := by simp [evalPanCmp, h01]
      rw [hc2, if_pos (show (0#64 : Word) = 0 from rfl), runs_skip] at h1
      exact skip h1
  · have hc : evalPanCmp .equal W 0#64 = 0#64 := by
      simp [evalPanCmp, hz]
    rw [hc, if_pos (show (0#64 : Word) = 0 from rfl), runs_skip] at h1
    exact skip h1

end InitECandidate.Solver.GuestBound
