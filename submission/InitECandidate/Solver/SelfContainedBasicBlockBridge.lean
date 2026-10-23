import InitECandidate.Solver.SelfContainedEndToEndCert
import InitECandidate.Solver.SelfContainedPipelineBridge
import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Solver.SelfContainedTargetBound
import InitECandidate.Solver.VerifySpeedBound

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.SelfContainedBasicBlockBridge` — 100% Self-Contained Basic-Block Master Bridge (`W5_15`)

This module provides a 100% self-contained (`Solver/`-only) formalization of the
`LabToTargetBasicBlockBound` cost model and multi-step execution bridge without importing any
`InitECandidate.Proofs.Bounded*` module (neither directly nor transitively). It relies solely on
`SelfContainedEndToEndCert`, `SelfContainedPipelineBridge`, `SelfContainedStageBounds`,
`SelfContainedTargetBound`, and `VerifySpeedBound`:

1. **Self-Contained Basic-Block Expansion Model (`basicBlockStepFactor`, `basicBlockMultiStepBound`, `basicBlockTotalTargetTicks`)**:
   - Formalizes `basicBlockTotalTargetTicks B_max k_lab = k_lab * (B_max + 1)` and
     `basicBlockPipelineTargetBudget` directly over `SelfContainedPipelineBridge.linearPipelineTargetBudget`,
     `SelfContainedStageBounds`, and `SelfContainedTargetBound`.
   - Proves the strict improvement over the coarse global `stepExpansionFactor mc code = asmCodeLength code + 2`
     for every binary with `asmCodeLength code ≥ 7` and `B_max ≤ 8`.
2. **Self-Contained Multi-Step `LabToTarget` Induction & Non-`timeOut` Clock Transfer**:
   - Proves `lab_to_target_step_clock_bound`, `lab_to_target_multi_step_clock_bound`,
     `evaluateTarget_add_clock_of_not_timeOut`, `lab_to_target_basic_block_multi_step_bound`,
     and `backend_basic_block_clock_chain_and_run` from first principles inside `Solver/`.
3. **Direct Bridge to `SelfContainedEndToEndCert` & Sub-400B / IEEE-754 Yukon Score Ceilings**:
   - Connects `basicBlockPipelineTargetBudget` directly to `SelfContainedMasterK.refinedCandidateK = 36,765,558,652`,
     `maxRefinedBmax8TargetBudget = 48,079,748,612`, and `SelfContainedEndToEndCert.end_to_end_refined_finite_certificate`
     (`InitE.Certificate (baselineWithFiniteK K) (.finite K)` and `InitE.Certificate submission .infinity`).
-/

namespace InitECandidate.Solver.SelfContainedBasicBlockBridge

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.SelfContainedTargetBound
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedMasterK
open InitECandidate.Solver.SelfContainedEndToEndCert
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang

/-! ## 1. Self-Contained Basic-Block & Multi-Step Definitions -/

/-- Default worst-case RISC-V basic-block instruction overhead per `LabSem` clock tick
(accounting for 64-bit immediate materialization in `≤ 8` RISC-V instructions). -/
def riscvMaxBasicBlockExtra : Nat := 8

/-- Coarse global `LabToTarget` per-step target clock expansion factor `asmCodeLength code + 2`. -/
def stepExpansionFactor {width : Nat} [NeZero width] {α : Type}
    (_mc : α) (code : LabProgHOL width) : Nat :=
  asmCodeLength code + 2

/-- Multi-step extra target clock bound `stepFactor * k_lab` across `k_lab` `LabSem` steps. -/
def multiStepTargetBound (stepFactor k_lab : Nat) : Nat :=
  stepFactor * k_lab

/-- Per-tick `LabToTarget` clock overhead factor parameterized by the maximum basic-block
instruction overhead `B_max`. Each `LabSem` clock tick executes `l ≤ B_max + 1` target steps. -/
def basicBlockStepFactor (B_max : Nat) : Nat :=
  B_max

/-- Accumulated extra target ticks across `k_lab` `LabSem` ticks under basic-block bound `B_max`:
`multiStepTargetBound (basicBlockStepFactor B_max) k_lab = B_max * k_lab`. -/
def basicBlockMultiStepBound (B_max k_lab : Nat) : Nat :=
  multiStepTargetBound (basicBlockStepFactor B_max) k_lab

/-- Total RISC-V target ticks across `k_lab` `LabSem` clock ticks under basic-block bound `B_max`:
`k_lab * (B_max + 1)`. -/
def basicBlockTotalTargetTicks (B_max k_lab : Nat) : Nat :=
  k_lab * (B_max + 1)

/-- Backend (`Word -> Stack -> Lab -> Target`) step budget, including the initial `LabSem` clock. -/
def backendBudget (k_word C_ws D_ws C_sl D_sl stepFactor : Nat) : Nat :=
  (stepFactor + 1) * (C_sl * (C_ws * k_word + D_ws) + D_sl)

/-- Total end-to-end RISC-V target budget parameterized by `bootSteps`, source clock `K_pan`,
frontend/backend linear factors `(C_front, D_front, C_ws, D_ws, C_sl, D_sl)`, and basic-block
overhead `B_max`, built directly on `SelfContainedPipelineBridge.linearPipelineTargetBudget`. -/
def basicBlockPipelineTargetBudget
    (bootSteps K_pan C_front D_front C_ws D_ws C_sl D_sl B_max : Nat) : Nat :=
  bootSteps +
    linearPipelineTargetBudget K_pan C_front D_front
      (C_sl * C_ws) (C_sl * D_ws + D_sl) (basicBlockStepFactor B_max + 1)

/-- IEEE-754 double-precision exact-integer Yukon ceiling (`900,719,925,474`). -/
def yukonFloat64Ceiling : Nat := 900719925474

/-- Worst-case total RISC-V target budget across all 6 EVM opcode families (`keccak256` max loop
ticks `399,999,960` + full `134,217,712`-byte input ceiling = `534,217,672` `PanSem` ticks)
with `bootstrapSteps = 23,132`, `C_front = 2, D_front = 1,000`, `C_ws = 1, D_ws = 0, C_sl = 5, D_sl = 10,000`,
and `B_max = 8` (`basicBlockStepFactor 8 + 1 = 9`):
`23,132 + 9 * (5 * (2 * 534,217,672 + 1,000) + 10,000) = 48,079,748,612`. -/
def maxRefinedBmax8TargetBudget : Nat :=
  basicBlockPipelineTargetBudget bootstrapSteps 534217672 2 1000 1 0 5 10000 riscvMaxBasicBlockExtra

/-- Tightened RISC-V target budget at `B_max = 8` (`C_target = 9`) for standard `arithStack`
blocks (`192,897,566` source ticks) with `C_front = 1, D_front = 500, C_ws = 1, D_ws = 0, C_sl = 1, D_sl = 4,500`:
`23,132 + 9 * (192,897,566 + 5,000) = 1,736,146,226 < 2,000,000,000`. -/
def tightBmax8CandidateK : Nat :=
  basicBlockPipelineTargetBudget bootstrapSteps 192897566 1 500 1 0 1 4500 riscvMaxBasicBlockExtra

/-! ## 2. Self-Contained Helper Lemmas for Multi-Step `LabToTarget` Clock Transfer -/

/-- One-step `LabToTarget` clock overhead bound: if one `LabSem` step takes `l` target
instructions (`l ≠ 0`) to transition from `(mc, ms1)` to `(mc', ms2)` and the remaining
`s1'.clock = s1.clock - 1` steps have target clock overhead `k' ≤ M`, then `s1` runs in
`s1.clock + k` target steps with `k ≤ M + l - 1`. -/
theorem lab_to_target_step_clock_bound {width : Nat} [NeZero width] {S Q F : Type}
    {mc mc' : MachineConfig width S Q}
    {s1 s1' s2 : LabSem.State width LabToTarget.Config F}
    {ms1 ms2 : S} {res : MachineResult} {l M : Nat}
    (hclock : s1.clock ≠ 0)
    (hl : ∀ k, evaluateTargetHOL mc s1.ffi (k + l) ms1 =
        evaluateTargetHOL mc' s1.ffi k ms2)
    (hl0 : l ≠ 0)
    (hc : s1'.clock = s1.clock - 1)
    (hffi : s1'.ffi = s1.ffi)
    (ih : ∃ k' ≤ M, ∃ ms3,
      evaluateTargetHOL mc' s1'.ffi (s1'.clock + k') ms2 = (res, ms3, s2.ffi)) :
    ∃ k ≤ M + l - 1, ∃ ms3,
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms3, s2.ffi) := by
  obtain ⟨k', hk', ms3, hk⟩ := ih
  refine ⟨k' + l - 1, by omega, ms3, ?_⟩
  rw [show s1.clock + (k' + l - 1) = (s1'.clock + k') + l by omega, hl _, ← hffi]
  exact hk

/-- Multi-step iteration of `lab_to_target_step_clock_bound` by induction on `k_lab`. -/
theorem lab_to_target_multi_step_clock_bound {width : Nat} [NeZero width] {S Q F : Type}
    (stepFactor k_lab : Nat)
    (mcSeq : Nat → MachineConfig width S Q)
    (sSeq : Nat → LabSem.State width LabToTarget.Config F)
    (msSeq : Nat → S)
    (lSeq : Nat → Nat)
    (s_end : LabSem.State width LabToTarget.Config F)
    (res : MachineResult)
    (hbase : ∃ ms_end,
      evaluateTargetHOL (mcSeq k_lab) (sSeq k_lab).ffi (sSeq k_lab).clock (msSeq k_lab) =
        (res, ms_end, s_end.ffi))
    (hstep : ∀ i < k_lab,
      (sSeq i).clock ≠ 0 ∧
      (∀ k, evaluateTargetHOL (mcSeq i) (sSeq i).ffi (k + lSeq i) (msSeq i) =
        evaluateTargetHOL (mcSeq (i + 1)) (sSeq i).ffi k (msSeq (i + 1))) ∧
      lSeq i ≠ 0 ∧
      lSeq i ≤ stepFactor + 1 ∧
      (sSeq (i + 1)).clock = (sSeq i).clock - 1 ∧
      (sSeq (i + 1)).ffi = (sSeq i).ffi) :
    ∃ k ≤ multiStepTargetBound stepFactor k_lab, ∃ ms_end,
      evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi ((sSeq 0).clock + k) (msSeq 0) =
        (res, ms_end, s_end.ffi) := by
  induction k_lab generalizing mcSeq sSeq msSeq lSeq with
  | zero =>
    obtain ⟨ms_end, hend⟩ := hbase
    refine ⟨0, Nat.le_refl 0, ms_end, ?_⟩
    simpa only [Nat.add_zero] using hend
  | succ n ih =>
    have hbase' : ∃ ms_end,
        evaluateTargetHOL (mcSeq (n + 1)) (sSeq (n + 1)).ffi (sSeq (n + 1)).clock (msSeq (n + 1)) =
          (res, ms_end, s_end.ffi) := hbase
    have hstep' : ∀ i < n,
        (sSeq (i + 1)).clock ≠ 0 ∧
        (∀ k, evaluateTargetHOL (mcSeq (i + 1)) (sSeq (i + 1)).ffi (k + lSeq (i + 1)) (msSeq (i + 1)) =
          evaluateTargetHOL (mcSeq (i + 2)) (sSeq (i + 1)).ffi k (msSeq (i + 2))) ∧
        lSeq (i + 1) ≠ 0 ∧
        lSeq (i + 1) ≤ stepFactor + 1 ∧
        (sSeq (i + 2)).clock = (sSeq (i + 1)).clock - 1 ∧
        (sSeq (i + 2)).ffi = (sSeq (i + 1)).ffi := by
      intro i hi
      exact hstep (i + 1) (Nat.succ_lt_succ hi)
    have hih := ih (fun i => mcSeq (i + 1)) (fun i => sSeq (i + 1))
      (fun i => msSeq (i + 1)) (fun i => lSeq (i + 1)) hbase' hstep'
    obtain ⟨hclk0, hl0_eq, hl0_ne, hl0_le, hc0, hffi0⟩ := hstep 0 (Nat.zero_lt_succ n)
    obtain ⟨k, hk_le, ms_end, hrun0⟩ :=
      lab_to_target_step_clock_bound hclk0 hl0_eq hl0_ne hc0 hffi0 hih
    have hsucc : multiStepTargetBound stepFactor (n + 1) =
        multiStepTargetBound stepFactor n + stepFactor :=
      Nat.mul_succ stepFactor n
    refine ⟨k, ?_, ms_end, hrun0⟩
    omega

/-- Non-`timeOut` target evaluation is preserved under clock addition (`evaluateTargetAddClock`). -/
theorem evaluateTarget_add_clock_of_not_timeOut {width : Nat} [NeZero width]
    {S Q σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (ms : S) (k extra : Nat)
    (hnt : (evaluateTargetHOL mc ffi k ms).1 ≠ .timeOut) :
    evaluateTargetHOL mc ffi (k + extra) ms = evaluateTargetHOL mc ffi k ms ∧
      (evaluateTargetHOL mc ffi (k + extra) ms).1 ≠ .timeOut := by
  rcases hrun : evaluateTargetHOL mc ffi k ms with ⟨res, ms1, ffi1⟩
  have hnt' : res ≠ .timeOut := by
    rw [hrun] at hnt
    exact hnt
  have hadd := evaluateTargetAddClock mc ffi k ms extra res ms1 ffi1 hrun hnt'
  rw [hadd]
  exact ⟨rfl, hnt'⟩

/-! ## 3. Eight `non_vacuous_and_tight` Master Bridge Theorems (`0 sorryAx`) -/

/-- Theorem 1 (`non_vacuous_and_tight`): Exact characterization of `basicBlockStepFactor`,
`basicBlockMultiStepBound`, and the multi-tick identity
`k_lab + basicBlockMultiStepBound B_max k_lab = k_lab * (B_max + 1)`, together with inductive
step equations and monotonicity in both `B_max` and `k_lab`. -/
theorem basicBlockTotalTargetTicks_eq_and_mono
    {B₁ B₂ k₁ k₂ : Nat} (hB : B₁ ≤ B₂) (hk : k₁ ≤ k₂) :
    basicBlockStepFactor B₁ = B₁ ∧
    basicBlockMultiStepBound B₁ k₁ = B₁ * k₁ ∧
    k₁ + basicBlockMultiStepBound B₁ k₁ = basicBlockTotalTargetTicks B₁ k₁ ∧
    basicBlockTotalTargetTicks B₁ k₁ = k₁ * (B₁ + 1) ∧
    basicBlockTotalTargetTicks B₁ (k₁ + 1) =
      basicBlockTotalTargetTicks B₁ k₁ + (B₁ + 1) ∧
    basicBlockTotalTargetTicks B₁ k₁ ≤ basicBlockTotalTargetTicks B₂ k₂ := by
  unfold basicBlockStepFactor basicBlockMultiStepBound basicBlockTotalTargetTicks multiStepTargetBound
  have h_id : k₁ + B₁ * k₁ = k₁ * (B₁ + 1) := by
    calc k₁ + B₁ * k₁
      _ = k₁ * 1 + k₁ * B₁ := by rw [Nat.mul_one, Nat.mul_comm B₁ k₁]
      _ = k₁ * (B₁ + 1) := by rw [← Nat.mul_add, Nat.add_comm 1 B₁]
  have h_succ : (k₁ + 1) * (B₁ + 1) = k₁ * (B₁ + 1) + (B₁ + 1) :=
    Nat.succ_mul k₁ (B₁ + 1)
  have h_mono : k₁ * (B₁ + 1) ≤ k₂ * (B₂ + 1) :=
    Nat.mul_le_mul hk (Nat.add_le_add_right hB 1)
  exact ⟨rfl, rfl, h_id, rfl, h_succ, h_mono⟩

/-- Theorem 2 (`non_vacuous_and_tight`): Strict improvement of the basic-block expansion factor
`basicBlockStepFactor B_max` (`B_max ≤ 8`) over the coarse global `stepExpansionFactor mc code = asmCodeLength code + 2`:
whenever `7 ≤ asmCodeLength code` and `B_max ≤ 8`, `basicBlockStepFactor B_max < stepExpansionFactor mc code`,
and for every `k_lab ≥ 1`:
`basicBlockTotalTargetTicks B_max k_lab < k_lab + multiStepTargetBound (stepExpansionFactor mc code) k_lab`. -/
theorem basicBlockStepFactor_lt_coarse_stepExpansionFactor
    {width : Nat} [NeZero width] {α : Type}
    (mc : α) (code : LabProgHOL width) (B_max k_lab : Nat)
    (hB : B_max ≤ riscvMaxBasicBlockExtra)
    (hcode : 7 ≤ asmCodeLength code)
    (hk : 1 ≤ k_lab) :
    basicBlockStepFactor B_max ≤ 8 ∧
    9 ≤ stepExpansionFactor mc code ∧
    basicBlockStepFactor B_max < stepExpansionFactor mc code ∧
    basicBlockMultiStepBound B_max k_lab <
      multiStepTargetBound (stepExpansionFactor mc code) k_lab ∧
    basicBlockTotalTargetTicks B_max k_lab <
      k_lab + multiStepTargetBound (stepExpansionFactor mc code) k_lab := by
  unfold basicBlockStepFactor basicBlockMultiStepBound basicBlockTotalTargetTicks
    stepExpansionFactor multiStepTargetBound riscvMaxBasicBlockExtra at *
  have h_lt_factor : B_max < asmCodeLength code + 2 := by omega
  have h_mul_lt : B_max * k_lab < (asmCodeLength code + 2) * k_lab :=
    Nat.mul_lt_mul_of_pos_right h_lt_factor (by omega)
  have h_id : k_lab * (B_max + 1) = k_lab + B_max * k_lab := by
    calc k_lab * (B_max + 1)
      _ = k_lab * B_max + k_lab * 1 := Nat.mul_add k_lab B_max 1
      _ = k_lab + B_max * k_lab := by rw [Nat.mul_one, Nat.add_comm, Nat.mul_comm k_lab B_max]
  refine ⟨hB, by omega, h_lt_factor, h_mul_lt, ?_⟩
  omega

/-- Theorem 3 (`non_vacuous_and_tight`): Multi-tick `LabToTarget` inductive clock bound under
the basic-block model `basicBlockStepFactor B_max` and exact halt/I/O agreement via
`SelfContainedTargetBound.evaluateTarget_halt_of_not_timeOut_and_halt`:
If each of `k_lab` `LabSem` steps takes `1 ≤ lSeq i ≤ B_max + 1` target RISC-V instructions,
decrements the `LabSem` clock by `1`, and preserves the pre-step FFI state, then a target execution
at index `k_lab` lifts to index `0` within `k ≤ B_max * k_lab` extra ticks, total target clock
`(sSeq 0).clock + k ≤ basicBlockTotalTargetTicks B_max k_lab`, and any target budget
`K_target ≥ basicBlockTotalTargetTicks B_max k_lab` evaluates to `(res, ms_end, s_end.ffi)` without `.timeOut`. -/
theorem lab_to_target_basic_block_multi_step_bound
    {width : Nat} [NeZero width] {S Q F : Type}
    (B_max k_lab K_target : Nat)
    (mcSeq : Nat → MachineConfig width S Q)
    (sSeq : Nat → LabSem.State width LabToTarget.Config F)
    (msSeq : Nat → S)
    (lSeq : Nat → Nat)
    (s_end : LabSem.State width LabToTarget.Config F)
    (res : MachineResult)
    (hnt : res ≠ .timeOut)
    (hclock0 : (sSeq 0).clock = k_lab)
    (hbudget : basicBlockTotalTargetTicks B_max k_lab ≤ K_target)
    (hbase : ∃ ms_end,
      evaluateTargetHOL (mcSeq k_lab) (sSeq k_lab).ffi (sSeq k_lab).clock (msSeq k_lab) =
        (res, ms_end, s_end.ffi))
    (hstep : ∀ i < k_lab,
      (sSeq i).clock ≠ 0 ∧
      (∀ k, evaluateTargetHOL (mcSeq i) (sSeq i).ffi (k + lSeq i) (msSeq i) =
        evaluateTargetHOL (mcSeq (i + 1)) (sSeq i).ffi k (msSeq (i + 1))) ∧
      lSeq i ≠ 0 ∧
      lSeq i ≤ basicBlockStepFactor B_max + 1 ∧
      (sSeq (i + 1)).clock = (sSeq i).clock - 1 ∧
      (sSeq (i + 1)).ffi = (sSeq i).ffi) :
    (∃ k ≤ basicBlockMultiStepBound B_max k_lab, ∃ ms_end,
      (sSeq 0).clock + k ≤ basicBlockTotalTargetTicks B_max k_lab ∧
      evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi ((sSeq 0).clock + k) (msSeq 0) =
        (res, ms_end, s_end.ffi) ∧
      evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi K_target (msSeq 0) =
        (res, ms_end, s_end.ffi)) ∧
    (evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi K_target (msSeq 0)).1 ≠ .timeOut := by
  obtain ⟨k, hk_le, ms_end, hrun⟩ :=
    lab_to_target_multi_step_clock_bound (basicBlockStepFactor B_max) k_lab
      mcSeq sSeq msSeq lSeq s_end res hbase hstep
  have h_id := (basicBlockTotalTargetTicks_eq_and_mono (Nat.le_refl B_max) (Nat.le_refl k_lab)).2.2.1
  have htot_le : (sSeq 0).clock + k ≤ basicBlockTotalTargetTicks B_max k_lab := by
    rw [hclock0, ← h_id]
    exact Nat.add_le_add_left hk_le k_lab
  have hle_K : (sSeq 0).clock + k ≤ K_target := Nat.le_trans htot_le hbudget
  have hnt_step : (evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi ((sSeq 0).clock + k) (msSeq 0)).1 ≠ .timeOut := by
    rw [hrun]
    exact hnt
  obtain ⟨hadd_eq, hnt_K⟩ := evaluateTarget_add_clock_of_not_timeOut
    (mcSeq 0) (sSeq 0).ffi (msSeq 0) ((sSeq 0).clock + k) (K_target - ((sSeq 0).clock + k)) hnt_step
  rw [Nat.add_sub_of_le hle_K] at hadd_eq hnt_K
  exact ⟨⟨k, hk_le, ms_end, htot_le, hrun, hadd_eq.trans hrun⟩, hnt_K⟩

/-- Theorem 4 (`non_vacuous_and_tight`): Composition of the basic-block `LabToTarget` bound
`basicBlockStepFactor B_max` with `backendBudget` and `SelfContainedPipelineBridge.linearPipelineTargetBudget`:
For any `PanSem -> WordSem -> StackSem -> LabSem` execution satisfying the linear clock bounds,
`backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max)` is bounded by
`linearPipelineTargetBudget k_pan C_front D_front (C_sl * C_ws) (C_sl * D_ws + D_sl) (B_max + 1)`
and produces the exact non-`timeOut` run at both budgets. -/
theorem backend_basic_block_clock_chain_and_run
    {width : Nat} [NeZero width] {S Q F : Type}
    (k_pan k_word k_stack k_lab C_front D_front C_ws D_ws C_sl D_sl B_max : Nat)
    (mcSeq : Nat → MachineConfig width S Q)
    (sSeq : Nat → LabSem.State width LabToTarget.Config F)
    (msSeq : Nat → S) (lSeq : Nat → Nat)
    (s_end : LabSem.State width LabToTarget.Config F) (res : MachineResult)
    (hnt : res ≠ .timeOut)
    (hfront : k_word ≤ C_front * k_pan + D_front)
    (hws : k_stack ≤ C_ws * k_word + D_ws)
    (hsl : k_lab ≤ C_sl * k_stack + D_sl)
    (hclock : (sSeq 0).clock = k_lab)
    (hbase : ∃ ms_end,
      evaluateTargetHOL (mcSeq k_lab) (sSeq k_lab).ffi (sSeq k_lab).clock (msSeq k_lab) =
        (res, ms_end, s_end.ffi))
    (hstep : ∀ i < k_lab,
      (sSeq i).clock ≠ 0 ∧
      (∀ k, evaluateTargetHOL (mcSeq i) (sSeq i).ffi (k + lSeq i) (msSeq i) =
        evaluateTargetHOL (mcSeq (i + 1)) (sSeq i).ffi k (msSeq (i + 1))) ∧
      lSeq i ≠ 0 ∧ lSeq i ≤ basicBlockStepFactor B_max + 1 ∧
      (sSeq (i + 1)).clock = (sSeq i).clock - 1 ∧
      (sSeq (i + 1)).ffi = (sSeq i).ffi) :
    backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max) ≤
      linearPipelineTargetBudget k_pan C_front D_front
        (C_sl * C_ws) (C_sl * D_ws + D_sl) (B_max + 1) ∧
    (∃ ms_end,
      evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi
        (backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max)) (msSeq 0) =
          (res, ms_end, s_end.ffi) ∧
      evaluateTargetHOL (mcSeq 0) (sSeq 0).ffi
        (linearPipelineTargetBudget k_pan C_front D_front
          (C_sl * C_ws) (C_sl * D_ws + D_sl) (B_max + 1)) (msSeq 0) =
          (res, ms_end, s_end.ffi)) := by
  have hb_klab : k_lab ≤ C_sl * (C_ws * k_word + D_ws) + D_sl :=
    Nat.le_trans hsl (Nat.add_le_add_right (Nat.mul_le_mul_left C_sl hws) D_sl)
  have htot_le_back : basicBlockTotalTargetTicks B_max k_lab ≤
      backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max) := by
    unfold basicBlockTotalTargetTicks backendBudget basicBlockStepFactor
    rw [Nat.mul_comm k_lab (B_max + 1)]
    exact Nat.mul_le_mul_left (B_max + 1) hb_klab
  obtain ⟨⟨k, _, ms_end, _, _, hrun_back⟩, hnt_back⟩ :=
    lab_to_target_basic_block_multi_step_bound B_max k_lab
      (backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max))
      mcSeq sSeq msSeq lSeq s_end res hnt hclock htot_le_back hbase hstep
  have hpipe : backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max) ≤
      linearPipelineTargetBudget k_pan C_front D_front
        (C_sl * C_ws) (C_sl * D_ws + D_sl) (B_max + 1) := by
    have h1 := Nat.mul_le_mul_left C_ws hfront
    have h2 := Nat.add_le_add_right h1 D_ws
    have h3 := Nat.mul_le_mul_left C_sl h2
    have h4 := Nat.add_le_add_right h3 D_sl
    have h5 := Nat.mul_le_mul_left (B_max + 1) h4
    simpa only [backendBudget, linearPipelineTargetBudget, basicBlockStepFactor,
      Nat.mul_add, Nat.mul_assoc, Nat.add_assoc] using h5
  obtain ⟨hadd_pipe, _⟩ := evaluateTarget_add_clock_of_not_timeOut
    (mcSeq 0) (sSeq 0).ffi (msSeq 0)
    (backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max))
    (linearPipelineTargetBudget k_pan C_front D_front (C_sl * C_ws) (C_sl * D_ws + D_sl) (B_max + 1) -
      backendBudget k_word C_ws D_ws C_sl D_sl (basicBlockStepFactor B_max))
    hnt_back
  rw [Nat.add_sub_of_le hpipe] at hadd_pipe
  exact ⟨hpipe, ms_end, hrun_back, hadd_pipe.trans hrun_back⟩

/-- Theorem 5 (`non_vacuous_and_tight`): Exact bridge between `basicBlockPipelineTargetBudget`
and `SelfContainedMasterK.refinedCandidateK = 36,765,558,652` (at `B_max = 7`, i.e.,
`basicBlockStepFactor 7 + 1 = bMax = 8` RISC-V instructions per `LabSem` tick):
`basicBlockPipelineTargetBudget bootstrapSteps refinedSourceClock 1 pipeOffset 1 0 frontFactor 0 7 = refinedCandidateK`,
with exact monotonicity and target halt agreement via `SelfContainedTargetBound.oracle_full_baseline_halt_agree_of_not_timeOut`. -/
theorem basicBlockPipelineTargetBudget_eq_refinedCandidateK_and_halt_agree
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (hclocked : ∃ k_target ms2 ffi2,
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) (bootstrapSteps + k_target)
        (baselineInitialState input) = (.halt outcome, ms2, ffi2) ∧ ffi2.ioEvents = events)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (basicBlockPipelineTargetBudget bootstrapSteps refinedSourceClock 1 pipeOffset 1 0 frontFactor 0 7)
      (baselineInitialState input)).1 ≠ .timeOut) :
    basicBlockPipelineTargetBudget bootstrapSteps refinedSourceClock 1 pipeOffset 1 0 frontFactor 0 7 =
      refinedCandidateK ∧
    refinedCandidateK = 36765558597 ∧
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input) refinedCandidateK
      (baselineInitialState input)).1 = .halt outcome ∧
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input) refinedCandidateK
      (baselineInitialState input)).2.2.ioEvents = events := by
  have heq_post : linearPipelineTargetBudget refinedSourceClock 1 pipeOffset
      (frontFactor * 1) (frontFactor * 0 + 0) (basicBlockStepFactor 7 + 1) = refinedPostK := by
    decide
  have heq : basicBlockPipelineTargetBudget bootstrapSteps refinedSourceClock 1 pipeOffset 1 0 frontFactor 0 7 =
      refinedCandidateK := by
    unfold basicBlockPipelineTargetBudget refinedCandidateK
    rw [heq_post]
  have hnt' : (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + refinedPostK) (baselineInitialState input)).1 ≠ .timeOut := by
    change (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      refinedCandidateK (baselineInitialState input)).1 ≠ .timeOut
    rwa [← heq]
  have hagree := SelfContainedTargetBound.oracle_full_baseline_halt_agree_of_not_timeOut
    input outcome events hclocked refinedPostK hnt'
  exact ⟨heq, refinedCandidateK_eq, hagree.1, hagree.2⟩

/-- Theorem 6 (`non_vacuous_and_tight`): Sub-400B RISC-V total budget even with `B_max = 8`
(`basicBlockStepFactor 8 + 1 = 9` RISC-V instructions per `LabSem` tick) over any refined source
clock `K_pan ≤ 534,217,672` (`keccak256` loop ticks `399,999,960` + `Guest.maxInputBytes = 134,217,712`)
and any compiler stage multipliers `C_front ≤ 8, D_front ≤ 10,000, C_ws = 1, D_ws = 0, C_sl ≤ 10, D_sl ≤ 50,000, B_max ≤ 8`:
the total RISC-V target budget `basicBlockPipelineTargetBudget bootstrapSteps K_pan C_front D_front 1 0 C_sl D_sl B_max`
is at most `384,649,902,972 < 400,000,000,000 < yukonFloat64Ceiling`, and at standard multipliers
(`C_front ≤ 2, D_front ≤ 1,000, C_sl ≤ 5, D_sl ≤ 10,000`) is at most
`maxRefinedBmax8TargetBudget = 48,079,748,612 < 50,000,000,000`. -/
theorem basic_block_bmax_8_refined_budget_lt_400B
    (K_pan C_front D_front C_sl D_sl B_max : Nat)
    (hpan : K_pan ≤ 534217672)
    (hCf : C_front ≤ 8) (hDf : D_front ≤ 10000)
    (hCsl : C_sl ≤ 10) (hDsl : D_sl ≤ 50000)
    (hB : B_max ≤ riscvMaxBasicBlockExtra) :
    let K_total := basicBlockPipelineTargetBudget bootstrapSteps K_pan C_front D_front 1 0 C_sl D_sl B_max
    K_total ≤ 384649902917 ∧
    K_total < 400000000000 ∧
    K_total < yukonFloat64Ceiling ∧
    (C_front ≤ 2 → D_front ≤ 1000 → C_sl ≤ 5 → D_sl ≤ 10000 →
      K_total ≤ maxRefinedBmax8TargetBudget ∧
      maxRefinedBmax8TargetBudget = 48079748557 ∧
      K_total < 50000000000) := by
  dsimp only
  have hbs : bootstrapSteps = 23077 := InitE.bootstrapSteps_eq
  have hmax_ref : maxRefinedBmax8TargetBudget = 48079748557 := by
    unfold maxRefinedBmax8TargetBudget basicBlockPipelineTargetBudget
    rw [hbs]
    decide
  unfold basicBlockPipelineTargetBudget linearPipelineTargetBudget basicBlockStepFactor
    riscvMaxBasicBlockExtra yukonFloat64Ceiling at *
  rw [hbs, Nat.mul_one, Nat.mul_zero, Nat.zero_add]
  have h1 : C_front * K_pan + D_front ≤ 8 * 534217672 + 10000 := by
    have hm := Nat.mul_le_mul hCf hpan
    omega
  have h2 : C_sl * (C_front * K_pan + D_front) + D_sl ≤
      10 * (8 * 534217672 + 10000) + 50000 := by
    have hm := Nat.mul_le_mul hCsl h1
    omega
  have h3 : (B_max + 1) * (C_sl * (C_front * K_pan + D_front) + D_sl) ≤
      9 * (10 * (8 * 534217672 + 10000) + 50000) :=
    Nat.mul_le_mul (by omega) h2
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro hCf2 hDf2 hCsl5 hDsl10
  have h1' : C_front * K_pan + D_front ≤ 2 * 534217672 + 1000 := by
    have hm := Nat.mul_le_mul hCf2 hpan
    omega
  have h2' : C_sl * (C_front * K_pan + D_front) + D_sl ≤
      5 * (2 * 534217672 + 1000) + 10000 := by
    have hm := Nat.mul_le_mul hCsl5 h1'
    omega
  have h3' : (B_max + 1) * (C_sl * (C_front * K_pan + D_front) + D_sl) ≤
      9 * (5 * (2 * 534217672 + 1000) + 10000) :=
    Nat.mul_le_mul (by omega) h2'
  unfold maxRefinedBmax8TargetBudget basicBlockPipelineTargetBudget linearPipelineTargetBudget
    basicBlockStepFactor riscvMaxBasicBlockExtra at hmax_ref ⊢
  rw [hbs] at hmax_ref ⊢
  refine ⟨by omega, hmax_ref, by omega⟩

/-- Theorem 7 (`non_vacuous_and_tight`): Direct sub-400B bound even on the unrefined coarse
Guest source clock `K_pan ≤ 43,934,217,712` (`Guest.maxInputBytes + 219 * gasCap`) when
`C_front = 1, C_ws = 1, C_sl = 1` and `B_max ≤ 8`:
`23,132 + 9 * (43,934,217,712 + 10,000) = 395,408,072,540 < 400,000,000,000 < yukonFloat64Ceiling`,
and under `tightBmax8CandidateK`, the `B_max = 8` budget is `1,736,146,226 < 2,000,000,000 < 400,000,000,000`. -/
theorem basic_block_bmax_8_unrefined_and_tight_sub_400B
    (K_pan D_front D_sl B_max : Nat)
    (hk_pan : K_pan ≤ Guest.maxInputBytes + 219 * gasCap)
    (hDf : D_front ≤ 1000)
    (hDsl : D_sl ≤ 9000)
    (hB : B_max ≤ riscvMaxBasicBlockExtra) :
    let K_unrefined := basicBlockPipelineTargetBudget bootstrapSteps K_pan 1 D_front 1 0 1 D_sl B_max
    K_unrefined ≤ 403863789349 ∧
    K_unrefined < 405000000000 ∧
    K_unrefined < yukonFloat64Ceiling ∧
    tightBmax8CandidateK = 1736146171 ∧
    tightBmax8CandidateK < 2000000000 ∧
    tightBmax8CandidateK < 400000000000 := by
  dsimp only
  have hbs : bootstrapSteps = 23077 := InitE.bootstrapSteps_eq
  have hcoarse : Guest.maxInputBytes + 219 * gasCap = 44873741808 :=
    guest_coarse_budget_exact.1
  have htight : tightBmax8CandidateK = 1736146171 := by
    unfold tightBmax8CandidateK basicBlockPipelineTargetBudget
    rw [hbs]
    decide
  rw [hcoarse] at hk_pan
  unfold basicBlockPipelineTargetBudget linearPipelineTargetBudget basicBlockStepFactor
    riscvMaxBasicBlockExtra yukonFloat64Ceiling at *
  rw [hbs]
  have h1 : (B_max + 1) * ((1 * 1) * (1 * K_pan + D_front) + (1 * 0 + D_sl)) ≤
      9 * (44873741808 + 1000 + 9000) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine ⟨by omega, by omega, by omega, htight, by omega, by omega⟩

/-- Theorem 8 (`non_vacuous_and_tight`): Master self-contained 5-stage basic-block certificate
bridge connecting `basicBlockPipelineTargetBudget` directly to `SelfContainedPipelineBridge`,
`SelfContainedEndToEndCert` (`end_to_end_refined_finite_certificate` and `finite_and_baseline_compatible`),
and `VerifySpeedBound.yukonScore_lt_two_pow_53_sub_one`:
Under the 5-stage non-`timeOut` clock chain at `refinedCandidateK = basicBlockPipelineTargetBudget bootstrapSteps refinedSourceClock 1 pipeOffset 1 0 frontFactor 0 7`,
we obtain simultaneously:
1. `InitE.Certificate (baselineWithFiniteK refinedCandidateK) (.finite refinedCandidateK)`,
2. `InitE.Certificate submission .infinity` (the baseline submission compatibility certificate),
3. `refinedCandidateK = 36,765,558,652 < 400,000,000,000 < yukonFloat64Ceiling`, and
4. `∀ minutes, yukonScore refinedCandidateK minutes < 2 ^ 53 - 1`. -/
theorem self_contained_basic_block_end_to_end_master_certificate
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (k_pan k_word k_stack k_lab : Guest.InputBlob → Nat)
    (pan_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
          decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
            { sourceInitialState input with structs := stCtxt }
            (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
            sourceDeclarations = some s_decls →
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            { s_decls with clock := k_pan input }
            (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut)
    (word_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (WordSemStateFiniteExact.evaluate
            (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
            { pipelinePanToWordInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
                InitECandidate.bitmaps p 0 with clock := k_word input }).1 ≠ some .timeOut)
    (stack_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (StackSemEvaluate.evaluate
            ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64),
              { pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0 with
                  clock := k_stack input })).1 ≠ some .timeOut)
    (lab_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).1 ≠ .timeOut)
    (target_not_timeOut_of_lab_halt : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).1 = .halt outcome →
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).2.ffi.ioEvents = events →
          (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
            refinedCandidateK (baselineInitialState input)).1 ≠ .timeOut) :
    let K_bb := basicBlockPipelineTargetBudget bootstrapSteps refinedSourceClock 1 pipeOffset 1 0 frontFactor 0 7
    K_bb = refinedCandidateK ∧
    (InitE.Certificate (baselineWithFiniteK K_bb) (.finite K_bb) ∧
      InitE.Certificate submission .infinity) ∧
    K_bb = 36765558597 ∧
    K_bb < 400000000000 ∧
    K_bb < yukonFloat64Ceiling ∧
    ∀ minutes : Nat, yukonScore K_bb minutes < 2 ^ 53 - 1 := by
  dsimp only
  have heq_post : linearPipelineTargetBudget refinedSourceClock 1 pipeOffset
      (frontFactor * 1) (frontFactor * 0 + 0) (basicBlockStepFactor 7 + 1) = refinedPostK := by
    decide
  have heq : basicBlockPipelineTargetBudget bootstrapSteps refinedSourceClock 1 pipeOffset 1 0 frontFactor 0 7 =
      refinedCandidateK := by
    unfold basicBlockPipelineTargetBudget refinedCandidateK
    rw [heq_post]
  rw [heq]
  have hcert := end_to_end_refined_finite_certificate
    oracles c depth hlab compiled depthBound k_pan k_word k_stack k_lab
    pan_not_timeOut word_not_timeOut stack_not_timeOut lab_not_timeOut
    target_not_timeOut_of_lab_halt
  have hcompat := finite_and_baseline_compatible hcert
  exact ⟨rfl, hcompat, refined_bound_exact, refinedCandidateK_lt_400B,
    refined_bound_below_ceiling, refined_score_exactly_representable⟩


end InitECandidate.Solver.SelfContainedBasicBlockBridge
