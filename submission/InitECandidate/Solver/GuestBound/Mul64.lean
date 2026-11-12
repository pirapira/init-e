import InitECandidate.Solver.GuestBound.PureSpecs
import InitECandidate.Solver.GuestBound.U256Zero
import InitECandidate.Solver.GuestBound.Mul64Nat

/-!
# `mul64x64` computes the 128-bit product

The function splits both operands into 32-bit halves. `m64_bv` is the
arithmetic of its result on the halves; `mul64x64_runs` is the function.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem pow64_zero : (2#64 : Word) ^ 64 = 0#64 := by
  rw [show (64 : Nat) = 32 + 32 from rfl, pow_add]
  have h : (2#64 : Word) ^ 32 = 4294967296#64 := by
    rw [show (32 : Nat) = 16 + 16 from rfl, pow_add]
    have h16 : (2#64 : Word) ^ 16 = 65536#64 := by decide
    rw [h16]
    decide
  rw [h]
  decide

/-- The shift amount the evaluator produces for a shift by 32. -/
theorem shift32_amount : ((32 : Word) % 2 ^ 64) = 32#64 := by
  rw [show ((2 : Word) ^ 64) = 0#64 from pow64_zero]
  decide

theorem mask32 : AndOp.and (4294967295#64) (~~~(0 : BitVec 64)) = 4294967295#64 := by
  show (4294967295#64 &&& ~~~(0 : BitVec 64)) = 4294967295#64
  simp

set_option maxHeartbeats 4000000 in
/-- The schoolbook product of two 64-bit numbers from their 32-bit halves, in
the form the evaluator produces. -/
theorem m64_bv (a0 a1 b0 b1 : Word) (h0 : a0.toNat < 2 ^ 32) (h1 : a1.toNat < 2 ^ 32)
    (h2 : b0.toNat < 2 ^ 32) (h3 : b1.toNat < 2 ^ 32) :
    (a1 * b1 + (BitVec.ofNat 64 (BitVec.toNat (a0 * b1) + BitVec.toNat (a1 * b0) + 0) >>>
        ((32 : Word) % 2 ^ 64) + (BitVec.ofNat 64 (if 2 ^ 64 ≤ BitVec.toNat (a0 * b1) +
          BitVec.toNat (a1 * b0) + 0 then 1 else 0) <<< ((32 : Word) % 2 ^ 64) +
        (BitVec.ofNat 64 (if 2 ^ 64 ≤ BitVec.toNat (a0 * b0) + (BitVec.ofNat 64
          (BitVec.toNat (a0 * b1) + BitVec.toNat (a1 * b0) + 0) <<< ((32 : Word) % 2 ^ 64)).toNat + 0
          then 1 else 0) + 0)))).toNat * 2 ^ 64 +
      (BitVec.ofNat 64 (BitVec.toNat (a0 * b0) + (BitVec.ofNat 64 (BitVec.toNat (a0 * b1) +
        BitVec.toNat (a1 * b0) + 0) <<< ((32 : Word) % 2 ^ 64)).toNat + 0)).toNat =
      (a1.toNat * 2 ^ 32 + a0.toNat) * (b1.toNat * 2 ^ 32 + b0.toNat) := by
  have hm : ∀ x y : Word, x.toNat < 2 ^ 32 → y.toNat < 2 ^ 32 →
      (x * y).toNat = x.toNat * y.toNat ∧ x.toNat * y.toNat ≤ 4294967295 * 4294967295 := by
    intro x y hx hy
    have hb : x.toNat * y.toNat ≤ 4294967295 * 4294967295 :=
      Nat.mul_le_mul (by omega) (by omega)
    refine ⟨?_, hb⟩
    rw [BitVec.toNat_mul]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨m00, b00⟩ := hm a0 b0 h0 h2
  obtain ⟨m01, b01⟩ := hm a0 b1 h0 h3
  obtain ⟨m10, b10⟩ := hm a1 b0 h1 h2
  obtain ⟨m11, b11⟩ := hm a1 b1 h1 h3
  have hs : ((32 : Word) % 2 ^ 64) = 32#64 := shift32_amount
  have h264 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have h232 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  simp only [hs, h264, h232]
  have hexp : (a1.toNat * 4294967296 + a0.toNat) * (b1.toNat * 4294967296 + b0.toNat) =
      a1.toNat * b1.toNat * 18446744073709551616 +
        (a0.toNat * b1.toNat + a1.toNat * b0.toNat) * 4294967296 + a0.toNat * b0.toNat := by ring
  rw [hexp]
  have hshl : ∀ w : Word, (w <<< (32#64 : Word)).toNat =
      w.toNat * 4294967296 % 18446744073709551616 := by
    intro w
    rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    norm_num
  have hshr : ∀ w : Word, (w >>> (32#64 : Word)).toNat = w.toNat / 4294967296 := by
    intro w
    rw [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    norm_num
  have hite : ∀ c : Prop, [Decidable c] →
      (BitVec.ofNat 64 (if c then 1 else 0)).toNat = if c then 1 else 0 := by
    intro c _
    split_ifs <;> rfl
  have hMID : (BitVec.ofNat 64 (BitVec.toNat (a0 * b1) + BitVec.toNat (a1 * b0) + 0)).toNat =
      (a0.toNat * b1.toNat + a1.toNat * b0.toNat) % 18446744073709551616 := by
    rw [BitVec.toNat_ofNat, Nat.add_zero, m01, m10, h264]
  obtain ⟨mid0, hmid0⟩ : ∃ x : Nat, x = (a0.toNat * b1.toNat + a1.toNat * b0.toNat) %
      18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨mid1, hmid1⟩ : ∃ x : Nat, x = if 18446744073709551616 ≤
      a0.toNat * b1.toNat + a1.toNat * b0.toNat then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨sh, hsh⟩ : ∃ x : Nat, x = mid0 * 4294967296 % 18446744073709551616 := ⟨_, rfl⟩
  obtain ⟨lo0, hlo0⟩ : ∃ x : Nat, x = (a0.toNat * b0.toNat + sh) % 18446744073709551616 :=
    ⟨_, rfl⟩
  obtain ⟨lo1, hlo1⟩ : ∃ x : Nat, x = if 18446744073709551616 ≤ a0.toNat * b0.toNat + sh
      then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ x : Nat, x = mid0 / 4294967296 := ⟨_, rfl⟩
  have key := m64_nat (a0.toNat * b0.toNat) (a0.toNat * b1.toNat) (a1.toNat * b0.toNat)
    (a1.toNat * b1.toNat) b00 b01 b10 b11 mid0 mid1 sh lo0 lo1 q hmid0 hmid1 hsh hlo0 hlo1 hq
  have hSH : (BitVec.ofNat 64 (BitVec.toNat (a0 * b1) + BitVec.toNat (a1 * b0) + 0) <<<
      (32#64 : Word)).toNat = sh := by
    rw [hshl, hMID, hsh, hmid0]
  have hLO : (BitVec.ofNat 64 (BitVec.toNat (a0 * b0) + (BitVec.ofNat 64 (BitVec.toNat (a0 * b1) +
      BitVec.toNat (a1 * b0) + 0) <<< (32#64 : Word)).toNat + 0)).toNat = lo0 := by
    rw [BitVec.toNat_ofNat, hSH, m00, Nat.add_zero, h264, hlo0]
  have hC1 : (BitVec.ofNat 64 (if 18446744073709551616 ≤ BitVec.toNat (a0 * b1) +
      BitVec.toNat (a1 * b0) + 0 then 1 else 0)).toNat = mid1 := by
    rw [hite, m01, m10, Nat.add_zero, hmid1]
  have hC2 : (BitVec.ofNat 64 (if 18446744073709551616 ≤ BitVec.toNat (a0 * b0) + (BitVec.ofNat 64
      (BitVec.toNat (a0 * b1) + BitVec.toNat (a1 * b0) + 0) <<< (32#64 : Word)).toNat + 0
      then 1 else 0)).toNat = lo1 := by
    rw [hite, hSH, m00, Nat.add_zero, hlo1]
  have hQ : (BitVec.ofNat 64 (BitVec.toNat (a0 * b1) + BitVec.toNat (a1 * b0) + 0) >>>
      (32#64 : Word)).toNat = q := by
    rw [hshr, hMID, hq, hmid0]
  have hm1 : mid1 ≤ 1 := by rw [hmid1]; split_ifs <;> omega
  have hl1 : lo1 ≤ 1 := by rw [hlo1]; split_ifs <;> omega
  have hHI : (a1 * b1 + (BitVec.ofNat 64 (BitVec.toNat (a0 * b1) + BitVec.toNat (a1 * b0) + 0) >>>
        (32#64 : Word) + (BitVec.ofNat 64 (if 18446744073709551616 ≤ BitVec.toNat (a0 * b1) +
          BitVec.toNat (a1 * b0) + 0 then 1 else 0) <<< (32#64 : Word) +
        (BitVec.ofNat 64 (if 18446744073709551616 ≤ BitVec.toNat (a0 * b0) + (BitVec.ofNat 64
          (BitVec.toNat (a0 * b1) + BitVec.toNat (a1 * b0) + 0) <<< (32#64 : Word)).toNat + 0
          then 1 else 0) + 0)))).toNat =
      (a1.toNat * b1.toNat + q + mid1 * 4294967296 + lo1) % 18446744073709551616 := by
    have hz0 : BitVec.toNat (0 : Word) = 0 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, m11, hQ,
      hshl, hC1, hC2, hz0, h264]
    omega
  rw [hHI, hLO]
  exact key

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `mul64x64(a, b)` returns `<lo, hi>` with `hi·2^64 + lo = a·b`, and changes nothing. -/
theorem mul64x64_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "mul64x64" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a b : Word) (ha : s.locals "a" = some (.word a))
    (hb : s.locals "b" = some (.word b)) (h : Runs E s body r) :
    ∃ l lo hi, r = .returned l s.globals s.memory s.ffi [.rStruct [.word lo, .word hi]] ∧
      hi.toNat * 2 ^ 64 + lo.toNat = a.toNat * b.toNat := by
  have hbody := (fun_of_index 59 hE.functions (by guest_decl_at 59) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp (config := { decide := true }) only [runs_seq, runs_dec, runs_primitive', runs_return,
    evalF_rStruct, evalF_rField, evalF_local, eval_const, evalF_op hE.word,
    evalF_shift hE.word, evalF_panOp, evalArgs_cons, evalArgs_nil, ha, hb,
    hE.prim.addCarry, Option.map_some, List.getElem?_cons_zero, List.getElem?_cons_succ,
    shape_word, shape_rStruct, shape_matches_self, wordsProj_nil, wordsProj_cons,
    update_lookup, addCarryResult, List.map_cons, List.map_nil, if_true, if_false, wordOp,
    List.foldr, RiscV.panRiscVShift, BitVec.toNat_ofNat, evalPanOp_mul,
    restorePanValueFfiLocal, payload_words2, exists_eq_left] at h
  have ha0 : (AndOp.and a (AndOp.and (4294967295#64) (~~~(0 : BitVec 64)))).toNat =
      a.toNat % 2 ^ 32 := by
    have hmask : AndOp.and (4294967295#64) (~~~(0 : BitVec 64)) = 4294967295#64 := mask32
    rw [hmask]
    show (a &&& 4294967295#64).toNat = a.toNat % 2 ^ 32
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod a.toNat 32
  have hb0 : (AndOp.and b (AndOp.and (4294967295#64) (~~~(0 : BitVec 64)))).toNat =
      b.toNat % 2 ^ 32 := by
    have hmask : AndOp.and (4294967295#64) (~~~(0 : BitVec 64)) = 4294967295#64 := mask32
    rw [hmask]
    show (b &&& 4294967295#64).toNat = b.toNat % 2 ^ 32
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod b.toNat 32
  have hs : ((32 : Word) % 2 ^ 64) = 32#64 := shift32_amount
  have ha1 : (a >>> ((32 : Word) % 2 ^ 64)).toNat = a.toNat / 2 ^ 32 := by
    rw [hs, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    norm_num
  have hb1 : (b >>> ((32 : Word) % 2 ^ 64)).toNat = b.toNat / 2 ^ 32 := by
    rw [hs, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    norm_num
  refine ⟨_, _, _, h, ?_⟩
  have key := m64_bv (AndOp.and a (AndOp.and (4294967295#64) (~~~(0 : BitVec 64))))
    (a >>> ((32 : Word) % 2 ^ 64)) (AndOp.and b (AndOp.and (4294967295#64) (~~~(0 : BitVec 64))))
    (b >>> ((32 : Word) % 2 ^ 64))
    (by rw [ha0]; exact Nat.mod_lt _ (by norm_num))
    (by rw [ha1]; have := a.isLt; omega)
    (by rw [hb0]; exact Nat.mod_lt _ (by norm_num))
    (by rw [hb1]; have := b.isLt; omega)
  rw [ha0, ha1, hb0, hb1] at key
  have e1 : a.toNat / 2 ^ 32 * 2 ^ 32 + a.toNat % 2 ^ 32 = a.toNat := Nat.div_add_mod' _ _
  have e2 : b.toNat / 2 ^ 32 * 2 ^ 32 + b.toNat % 2 ^ 32 = b.toNat := Nat.div_add_mod' _ _
  rw [e1, e2] at key
  exact key

end InitECandidate.Solver.GuestBound
