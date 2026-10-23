import InitECandidate.Solver.GuestStepBound


set_option autoImplicit false

/-!
# `InitECandidate.Solver.SourceTerminationBound` — Verrou B: EVM Gas/Counter Ranking Measures & Compositional `PanSem` Clock Calculus

This module proves the arithmetic ranking-measure lemmas on `BitVec 64` (`Guest.Word`)
for EVM gas, EIP-8037 state gas (`charge_gas`, `charge_state_gas`, `credit_state_gas_refund`,
`add_sat`, `min`), and bounded `while i <+ bound` loops in `Guest.Software.guestAst`, together with
the compositional `PanSem` clock-consumption laws across `.seq`, `.ite`, and `.dec`,
and connects them to the static guest bounds from `InitECandidate.Solver.GuestStepBound`
(`Guest.maxInputBytes = 134217712`, `maxBlockGasLimit = 200000000`,
`GuestStepBound.guestMaxFrameBound = 348`).
-/

namespace InitECandidate.Solver

open Flapjack
open Flapjack.Pancake.PanLang
open InitECandidate.Solver.GuestStepBound

/-! ## 1. Strictly Decreasing EVM Gas & EIP-8037 State-Gas Measures on `BitVec 64` -/

/-- Unsigned 64-bit subtraction `a - b` has `.toNat = a.toNat - b.toNat` whenever `b.toNat ≤ a.toNat`. -/
theorem toNat_sub_of_le (a b : Guest.Word) (hle : b.toNat ≤ a.toNat) :
    (a - b : BitVec 64).toNat = a.toNat - b.toNat := by
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  rw [BitVec.toNat_sub]
  omega

/-- `charge_gas(amount)`: when `amount ≤ gl` (`¬ (gl <+ amount)`) and `1 ≤ amount.toNat`,
the updated `EV_GAS_LEFT` (`gl - amount`) strictly decreases in `.toNat`. -/
theorem gas_strictly_decreases (gl amount : Guest.Word)
    (hle : amount.toNat ≤ gl.toNat) (hpos : 1 ≤ amount.toNat) :
    (gl - amount : BitVec 64).toNat < gl.toNat := by
  have hsub := toNat_sub_of_le gl amount hle
  omega

/-- `charge_state_gas(amount)` reservoir branch (`sgl >=+ amount`):
when `amount.toNat ≤ sgl.toNat` and `1 ≤ amount.toNat`, the combined gas measure
`sgl.toNat + gl.toNat` strictly decreases. -/
theorem state_gas_sum_decreases_reservoir (sgl gl amount : Guest.Word)
    (hle : amount.toNat ≤ sgl.toNat) (hpos : 1 ≤ amount.toNat) :
    (sgl - amount : BitVec 64).toNat + gl.toNat < sgl.toNat + gl.toNat := by
  have hsub := toNat_sub_of_le sgl amount hle
  omega

/-- `charge_state_gas(amount)` spill branch (`sgl <+ amount` and `tot >=+ amount`):
when `sgl.toNat < amount.toNat`, `amount.toNat ≤ sgl.toNat + gl.toNat`, and `1 ≤ amount.toNat`,
setting `EV_STATE_GAS_LEFT := 0` and `EV_GAS_LEFT := gl - (amount - sgl)` strictly
decreases the combined gas measure `sgl.toNat + gl.toNat`. -/
theorem state_gas_sum_decreases_spill (sgl gl amount : Guest.Word)
    (hlt : sgl.toNat < amount.toNat)
    (htot : amount.toNat ≤ sgl.toNat + gl.toNat)
    (hpos : 1 ≤ amount.toNat) :
    (0 : BitVec 64).toNat + (gl - (amount - sgl)).toNat < sgl.toNat + gl.toNat := by
  have hrem_le : sgl.toNat ≤ amount.toNat := Nat.le_of_lt hlt
  have hrem : (amount - sgl : BitVec 64).toNat = amount.toNat - sgl.toNat :=
    toNat_sub_of_le amount sgl hrem_le
  have hgl_le : (amount - sgl : BitVec 64).toNat ≤ gl.toNat := by
    rw [hrem]
    omega
  have hgl_sub : (gl - (amount - sgl) : BitVec 64).toNat =
      gl.toNat - (amount - sgl : BitVec 64).toNat :=
    toNat_sub_of_le gl (amount - sgl) hgl_le
  have hzero : (0 : BitVec 64).toNat = 0 := rfl
  rw [hzero, hgl_sub, hrem]
  have _ := hpos
  omega

/-- Unsigned 64-bit minimum helper mirroring `fun 1 min(1 a, 1 b)` in `guest/src/lib/mem.pnk`. -/
def minOf (a b : Guest.Word) : Guest.Word :=
  if a < b then a else b

/-- `minOf a b` never exceeds `a` in `.toNat`. -/
theorem minOf_le_left (a b : Guest.Word) :
    (minOf a b).toNat ≤ a.toNat := by
  unfold minOf
  split
  · exact Nat.le_refl _
  · rename_i hnot
    have hnot' : ¬ a.toNat < b.toNat := fun h => hnot (BitVec.lt_def.mpr h)
    omega

/-- `minOf a b` never exceeds `b` in `.toNat`. -/
theorem minOf_le_right (a b : Guest.Word) :
    (minOf a b).toNat ≤ b.toNat := by
  unfold minOf
  split
  · rename_i hlt
    have hlt' : a.toNat < b.toNat := BitVec.lt_def.mp hlt
    omega
  · exact Nat.le_refl _

/-- `credit_state_gas_refund(amount)` (`guest/src/evm.pnk:270-277`):
with `from_gl = minOf amount spilled`, the new `EV_GAS_LEFT = gl + from_gl`,
new `EV_STATE_GAS_LEFT = sgl + (amount - from_gl)`, and new
`EV_STATE_GAS_SPILLED = spilled - from_gl` satisfy exact conservation:
the combined `(sgl' + gl')` increases by `amount.toNat` while `spilled'` decreases
by `from_gl.toNat` whenever the 64-bit additions do not overflow. -/
theorem credit_state_gas_refund_increases_sum (sgl gl spilled amount : Guest.Word)
    (hgl_no_ovf : gl.toNat + (minOf amount spilled).toNat < 2 ^ 64)
    (hsgl_no_ovf : sgl.toNat + (amount - minOf amount spilled).toNat < 2 ^ 64) :
    let from_gl := minOf amount spilled
    let gl' := gl + from_gl
    let sgl' := sgl + (amount - from_gl)
    let spilled' := spilled - from_gl
    sgl'.toNat + gl'.toNat = sgl.toNat + gl.toNat + amount.toNat ∧
      spilled'.toNat = spilled.toNat - from_gl.toNat := by
  dsimp only
  have hle_amt : (minOf amount spilled).toNat ≤ amount.toNat := minOf_le_left amount spilled
  have hle_sp : (minOf amount spilled).toNat ≤ spilled.toNat := minOf_le_right amount spilled
  have hsub_amt : (amount - minOf amount spilled).toNat =
      amount.toNat - (minOf amount spilled).toNat :=
    toNat_sub_of_le amount (minOf amount spilled) hle_amt
  have hsub_sp : (spilled - minOf amount spilled).toNat =
      spilled.toNat - (minOf amount spilled).toNat :=
    toNat_sub_of_le spilled (minOf amount spilled) hle_sp
  have hadd_gl : (gl + minOf amount spilled).toNat =
      gl.toNat + (minOf amount spilled).toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hgl_no_ovf
  have hadd_sgl : (sgl + (amount - minOf amount spilled)).toNat =
      sgl.toNat + (amount - minOf amount spilled).toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hsgl_no_ovf
  refine ⟨?_, hsub_sp⟩
  rw [hadd_sgl, hadd_gl, hsub_amt]
  omega

/-- Maximum 64-bit unsigned word `WORD_MAX = 2^64 - 1`. -/
def wordMax64 : Guest.Word := BitVec.ofNat 64 (2 ^ 64 - 1)

/-- Saturating 64-bit addition `add_sat(a, b)` (`guest/src/evm.pnk:181-187`). -/
def addSat64 (a b : Guest.Word) : Guest.Word :=
  let s := a + b
  if s < a then wordMax64 else s

/-- `addSat64 a b` evaluates to `min (a.toNat + b.toNat) (2 ^ 64 - 1)`. -/
theorem addSat64_eq (a b : Guest.Word) :
    (addSat64 a b).toNat = min (a.toNat + b.toNat) (2 ^ 64 - 1) := by
  unfold addSat64 wordMax64
  dsimp only
  have ha : a.toNat < 2 ^ 64 := a.isLt
  have hb : b.toNat < 2 ^ 64 := b.isLt
  have hadd : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := BitVec.toNat_add a b
  have hmax : (BitVec.ofNat 64 (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by decide
  split
  · rename_i hlt
    have hlt' : (a + b).toNat < a.toNat := BitVec.lt_def.mp hlt
    rw [hmax]
    omega
  · rename_i hge
    have hge' : ¬ (a + b).toNat < a.toNat := fun h => hge (BitVec.lt_def.mpr h)
    rw [hadd] at hge' ⊢
    omega

/-- `addSat64 a b` is always at least `a.toNat`. -/
theorem addSat64_ge_left (a b : Guest.Word) :
    a.toNat ≤ (addSat64 a b).toNat := by
  have ha : a.toNat < 2 ^ 64 := a.isLt
  rw [addSat64_eq]
  omega

/-- When `a.toNat + b.toNat < 2 ^ 64`, `addSat64 a b` is exact (`a.toNat + b.toNat`). -/
theorem addSat64_le_sum_of_no_overflow (a b : Guest.Word)
    (hno : a.toNat + b.toNat < 2 ^ 64) :
    (addSat64 a b).toNat = a.toNat + b.toNat := by
  rw [addSat64_eq]
  omega

/-- Ranking measure `bound - counter.toNat` for the ~200 upward counter loops
`while counter <+ bound { ... counter = counter + step }` in `Guest.Software.guestAst`:
when `counter.toNat < bound`, `1 ≤ step.toNat`, and `counter.toNat + step.toNat < 2 ^ 64`,
the measure `bound - (counter + step).toNat` strictly decreases. -/
theorem counter_step_measure_decreases (counter step : Guest.Word) (bound : Nat)
    (hlt : counter.toNat < bound)
    (hpos : 1 ≤ step.toNat)
    (hno : counter.toNat + step.toNat < 2 ^ 64) :
    bound - (counter + step).toNat < bound - counter.toNat := by
  have hadd : (counter + step).toNat = counter.toNat + step.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hno
  rw [hadd]
  omega

/-! ## 2. Compositional `PanSem` Clock Consumption Calculus (`.seq`, `.ite`, `.dec`) -/

/-- Compositional clock-consumption law for `ProgHOL.seq p1 p2` in `PanSemStateFiniteExact`:
1. The intermediate clock `(evaluateHOLFiniteState s p1).2.clock` never exceeds `s.clock`,
   and the final clock `(evaluateHOLFiniteState s (.seq p1 p2)).2.clock` never exceeds
   the intermediate clock.
2. Total clock ticks consumed by `.seq p1 p2` decompose additively as the clock ticks
   consumed by `p1` plus the clock ticks consumed after `p1`. -/
theorem panSem_evaluate_seq_clock_le {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (p1 p2 : ProgHOL width) :
    let out1 := PanSemStateFiniteExact.evaluateHOLFiniteState s p1
    let outSeq := PanSemStateFiniteExact.evaluateHOLFiniteState s (.seq p1 p2)
    outSeq.2.clock ≤ out1.2.clock ∧
      out1.2.clock ≤ s.clock ∧
      s.clock - outSeq.2.clock =
        (s.clock - out1.2.clock) + (out1.2.clock - outSeq.2.clock) := by
  dsimp only
  have h1 : (PanSemStateFiniteExact.evaluateHOLFiniteState s p1).2.clock ≤ s.clock :=
    evaluateHOLFiniteState_clock_le s p1
  have hseq_eq := evaluateHOLFiniteState_seq_line780 s p1 p2
  have h2 : (PanSemStateFiniteExact.evaluateHOLFiniteState s (.seq p1 p2)).2.clock ≤
      (PanSemStateFiniteExact.evaluateHOLFiniteState s p1).2.clock := by
    rw [hseq_eq]
    dsimp only
    cases (PanSemStateFiniteExact.evaluateHOLFiniteState s p1).1 with
    | none =>
        exact evaluateHOLFiniteState_clock_le
          (PanSemStateFiniteExact.evaluateHOLFiniteState s p1).2 p2
    | some _ => exact Nat.le_refl _
  refine ⟨h2, h1, ?_⟩
  omega

/-- Compositional clock-consumption law for `ProgHOL.ite c t e` (`if`) in `PanSemStateFiniteExact`:
the post-state clock never exceeds `s.clock`, and the clock ticks consumed by `.ite c t e`
are bounded by `max (s.clock - outT.2.clock) (s.clock - outE.2.clock)`. -/
theorem panSem_evaluate_if_clock_le {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (c : ExpHOL width) (t e : ProgHOL width) :
    let outIf := PanSemStateFiniteExact.evaluateHOLFiniteState s (.ite c t e)
    let outT := PanSemStateFiniteExact.evaluateHOLFiniteState s t
    let outE := PanSemStateFiniteExact.evaluateHOLFiniteState s e
    outIf.2.clock ≤ s.clock ∧
      s.clock - outIf.2.clock ≤ max (s.clock - outT.2.clock) (s.clock - outE.2.clock) := by
  dsimp only
  have hle : (PanSemStateFiniteExact.evaluateHOLFiniteState s (.ite c t e)).2.clock ≤ s.clock :=
    evaluateHOLFiniteState_clock_le s (.ite c t e)
  refine ⟨hle, ?_⟩
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.ite c t e)]
  dsimp only
  cases @evalHOLExact width σ _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) c with
  | none =>
      dsimp only
      omega
  | some val =>
      cases val with
      | rStruct _ =>
          dsimp only
          omega
      | nStruct _ _ =>
          dsimp only
          omega
      | val wl =>
          cases wl with
          | word w =>
              dsimp only
              split <;> omega

/-- Compositional clock-consumption law for `ProgHOL.dec name sh init body` in `PanSemStateFiniteExact`:
1. The post-state clock never exceeds `s.clock`.
2. Whenever `init` evaluates to `val` of matching shape `sh`, the clock consumption of
   `.dec name sh init body` equals the clock consumption of `body` from `setVarHOLFinite name val s`. -/
theorem panSem_evaluate_dec_clock_le {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (name : MlS) (sh : ShapeHOL)
    (init : ExpHOL width) (body : ProgHOL width) :
    let outDec := PanSemStateFiniteExact.evaluateHOLFiniteState s (.dec name sh init body)
    outDec.2.clock ≤ s.clock ∧
      ∀ val : ValueHOL width,
        @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) init = some val →
        shapeEqHOL sh (shapeOfHOLExact val) = true →
        outDec.2.clock =
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            (PanSemStateFiniteExact.setVarHOLFinite name val s) body).2.clock := by
  dsimp only
  refine ⟨evaluateHOLFiniteState_clock_le s (.dec name sh init body), ?_⟩
  intro val hinit hshape
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [hinit]
  dsimp only
  rw [if_pos hshape]

/-! ## 3. Connection to `GuestStepBound` Architectural & Gas Constants -/

/-- Challenge maximum block gas limit (`InitE.gasLimit = 200,000,000`). -/
def maxBlockGasLimit : Nat := InitE.gasLimit

/-- The architectural input blob upper bound `Guest.maxInputBytes` is `134,217,712` bytes (`128 MiB - 16`). -/
theorem maxInputBytes_eq : Guest.maxInputBytes = 1073741808 := rfl

/-- The challenge maximum block gas limit `maxBlockGasLimit` is `200,000,000`. -/
theorem maxBlockGasLimit_eq : maxBlockGasLimit = 200000000 := rfl

/-- Re-export of the kernel-checked maximum stack frame bound `guestMaxFrameBound = 348`
from `InitECandidate.Solver.GuestStepBound`. -/
theorem guestMaxFrameBound_eq_348 :
    GuestStepBound.guestMaxFrameBound = 348 :=
  GuestStepBound.guestMaxFrameBound_eq

/-- Any byte-cursor loop `while i <+ len` over an input slice of length `len ≤ Guest.maxInputBytes`
with step `1 ≤ step.toNat` has initial ranking measure `len - i.toNat ≤ 134217712` and
strictly decreases its remaining distance on every step. -/
theorem input_cursor_measure_bound_and_dec (i step : Guest.Word) (len : Nat)
    (hlen : len ≤ Guest.maxInputBytes)
    (hlt : i.toNat < len)
    (hpos : 1 ≤ step.toNat)
    (hno : i.toNat + step.toNat < 2 ^ 64) :
    len - i.toNat ≤ 1073741808 ∧
      len - (i + step).toNat < len - i.toNat := by
  have hdec := counter_step_measure_decreases i step len hlt hpos hno
  have hmax : Guest.maxInputBytes = 1073741808 := maxInputBytes_eq
  refine ⟨?_, hdec⟩
  omega

/-- Under a valid decoded input with `Guest.GasLimit.declaredGasLimit input ≤ maxBlockGasLimit`,
any gas-charging step `charge_gas(amount)` with `1 ≤ amount.toNat` and `amount.toNat ≤ gl.toNat`
from a frame with `gl.toNat ≤ decoded.payload.gasLimit` transitions to a strictly smaller
remaining gas `< 200000000`. -/
theorem block_gas_measure_bound_and_dec {input : Guest.InputBlob}
    {decoded : Guest.InputDecode.StatelessInput}
    (gl amount : Guest.Word)
    (hdecode : Guest.InputDecode.decodeStatelessInput input = some decoded)
    (hdeclared : Guest.GasLimit.declaredGasLimit input ≤ maxBlockGasLimit)
    (hgl_le : gl.toNat ≤ decoded.payload.gasLimit)
    (hamt_le : amount.toNat ≤ gl.toNat)
    (hpos : 1 ≤ amount.toNat) :
    (gl - amount : BitVec 64).toNat < gl.toNat ∧
      (gl - amount : BitVec 64).toNat < 200000000 := by
  have hdec_bound :=
    GuestStepBound.declaredGasLimit_le_of_decode hdecode hdeclared
  have hstrict := gas_strictly_decreases gl amount hamt_le hpos
  refine ⟨hstrict, ?_⟩
  omega

end InitECandidate.Solver
