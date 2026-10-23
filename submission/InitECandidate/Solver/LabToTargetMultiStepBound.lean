import InitECandidate.Solver.FastBoundedTarget
import InitECandidate.Solver.BoundedCertificate

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.LabToTargetMultiStepBound` — Multi-Step `LabToTarget` Clock Expansion & Non-`timeOut` Budget Transfer

This module establishes the multi-step inductive iteration of `InitE.lab_to_target_step_clock_bound`
from `InitECandidate.Proofs.BoundedTarget`:

1. **Per-Step Expansion Factor & Multi-Step Bound (`stepExpansionFactor`, `multiStepTargetBound`)**:
   - `stepExpansionFactor mc code := asmCodeLength code + 2`
   - `multiStepTargetBound stepFactor k_lab := stepFactor * k_lab`
   - Inductive step law `multiStepTargetBound_succ` and monotonicity in `k_lab`
     (`multiStepTargetBound_mono_right`, `multiStepTargetBound_mono`).
2. **Multi-Step Inductive Iteration (`lab_to_target_multi_step_clock_bound`)**:
   - Iterates `lab_to_target_step_clock_bound` by induction on `k_lab`, bounding the
     accumulated target clock overhead across `k_lab` `LabSem` steps by
     `multiStepTargetBound stepFactor k_lab`.
3. **Target Non-`timeOut` Budget Transfer (`evaluateTarget_add_clock_of_not_timeOut`, `target_not_timeOut_of_lab_step_factor_budget`)**:
   - Connects `lab_to_target_step_clock_bound` and `evaluateTarget_add_clock_of_not_timeOut`
     (`evaluateTargetAddClock`) to show that any target step budget
     `K_target ≥ s1.clock + multiStepTargetBound (stepExpansionFactor mc code) s1.clock`
     preserves non-`timeOut` target execution and its exact halt/FFI result.
-/

namespace InitECandidate.Solver

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.BoundedCertificate
open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget

/-- Per-step target clock expansion factor `asmCodeLength code + 2` for a `LabSem`
program `code` under machine configuration `_mc`. -/
def stepExpansionFactor {width : Nat} [NeZero width] {α : Type}
    (_mc : α) (code : LabProgHOL width) : Nat :=
  asmCodeLength code + 2

/-- Multi-step target clock bound `stepFactor * k_lab` across `k_lab` `LabSem` steps
with per-step expansion factor `stepFactor`. -/
def multiStepTargetBound (stepFactor k_lab : Nat) : Nat :=
  stepFactor * k_lab

/-- Unfolding and positivity characterization of `stepExpansionFactor mc code`. -/
theorem stepExpansionFactor_eq_and_ge_two {width : Nat} [NeZero width] {α : Type}
    (mc : α) (code : LabProgHOL width) :
    stepExpansionFactor mc code = asmCodeLength code + 2 ∧
      2 ≤ stepExpansionFactor mc code ∧
      1 ≤ stepExpansionFactor mc code := by
  unfold stepExpansionFactor
  omega

/-- Zero-step base case for `multiStepTargetBound`. -/
@[simp] theorem multiStepTargetBound_zero (stepFactor : Nat) :
    multiStepTargetBound stepFactor 0 = 0 :=
  Nat.mul_zero stepFactor

/-- Inductive step equation `multiStepTargetBound stepFactor (k_lab + 1) =
multiStepTargetBound stepFactor k_lab + stepFactor`. -/
theorem multiStepTargetBound_succ (stepFactor k_lab : Nat) :
    multiStepTargetBound stepFactor (k_lab + 1) =
      multiStepTargetBound stepFactor k_lab + stepFactor := by
  unfold multiStepTargetBound
  exact Nat.mul_succ stepFactor k_lab

/-- Monotonicity of `multiStepTargetBound stepFactor k_lab` in the `LabSem` step count `k_lab`. -/
theorem multiStepTargetBound_mono_right (stepFactor : Nat) {k₁ k₂ : Nat}
    (hle : k₁ ≤ k₂) :
    multiStepTargetBound stepFactor k₁ ≤ multiStepTargetBound stepFactor k₂ :=
  Nat.mul_le_mul_left stepFactor hle

/-- Joint monotonicity of `multiStepTargetBound` in both `stepFactor` and `k_lab`. -/
theorem multiStepTargetBound_mono {stepFactor₁ stepFactor₂ k₁ k₂ : Nat}
    (hsf : stepFactor₁ ≤ stepFactor₂) (hk : k₁ ≤ k₂) :
    multiStepTargetBound stepFactor₁ k₁ ≤ multiStepTargetBound stepFactor₂ k₂ :=
  Nat.mul_le_mul hsf hk

/-- Multi-step iteration of `lab_to_target_step_clock_bound` by induction on `k_lab`:
if each of the `k_lab` `LabSem` steps from index `i` to `i + 1` takes `lSeq i` target
instructions (`lSeq i ≠ 0` and `lSeq i ≤ stepFactor + 1`), decrements the `LabSem` clock
by `1`, and preserves the pre-step FFI state, then a target execution at index `k_lab`
with clock overhead `0` lifts to a target execution at index `0` with clock overhead
`k ≤ multiStepTargetBound stepFactor k_lab`. -/
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
    have hsucc := multiStepTargetBound_succ stepFactor n
    refine ⟨k, ?_, ms_end, hrun0⟩
    omega

/-- Non-`timeOut` target evaluation is preserved under clock addition (`evaluateTargetAddClock`):
if `(evaluateTargetHOL mc ffi k ms).1 ≠ .timeOut`, then adding `extra` clock ticks preserves
the full target evaluation triple and remains non-`timeOut`. -/
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

/-- Connecting `lab_to_target_step_clock_bound`, `stepExpansionFactor`, `multiStepTargetBound`,
and `evaluateTarget_add_clock_of_not_timeOut`: if one `LabSem` step from `s1` (`s1.clock ≠ 0`)
to `s1'` (`s1'.clock = s1.clock - 1`) takes `l` target steps (`l ≠ 0`,
`l ≤ stepExpansionFactor mc code + 1`) and the remaining `s1'.clock` steps complete with
non-`timeOut` result `res` within overhead `multiStepTargetBound (stepExpansionFactor mc code) s1'.clock`,
then any target clock budget `K_target` with
`s1.clock + multiStepTargetBound (stepExpansionFactor mc code) s1.clock ≤ K_target`
evaluates to `(res, ms3, s2.ffi)` and does not time out (`≠ .timeOut`). -/
theorem target_not_timeOut_of_lab_step_factor_budget {width : Nat} [NeZero width] {S Q F : Type}
    (mc mc' : MachineConfig width S Q)
    (code : LabProgHOL width)
    (s1 s1' s2 : LabSem.State width LabToTarget.Config F)
    (ms1 ms2 : S) (res : MachineResult) (l K_target : Nat)
    (hclock : s1.clock ≠ 0)
    (hl : ∀ k, evaluateTargetHOL mc s1.ffi (k + l) ms1 =
        evaluateTargetHOL mc' s1.ffi k ms2)
    (hl0 : l ≠ 0)
    (hl_bound : l ≤ stepExpansionFactor mc code + 1)
    (hc : s1'.clock = s1.clock - 1)
    (hffi : s1'.ffi = s1.ffi)
    (ih : ∃ k' ≤ multiStepTargetBound (stepExpansionFactor mc code) s1'.clock, ∃ ms3,
      evaluateTargetHOL mc' s1'.ffi (s1'.clock + k') ms2 = (res, ms3, s2.ffi))
    (hnt : res ≠ .timeOut)
    (hbudget : s1.clock + multiStepTargetBound (stepExpansionFactor mc code) s1.clock ≤ K_target) :
    (∃ k ≤ multiStepTargetBound (stepExpansionFactor mc code) s1.clock, ∃ ms3,
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms3, s2.ffi) ∧
      evaluateTargetHOL mc s1.ffi K_target ms1 = (res, ms3, s2.ffi)) ∧
    (evaluateTargetHOL mc s1.ffi K_target ms1).1 ≠ .timeOut := by
  obtain ⟨k, hk_le, ms3, hrun⟩ :=
    lab_to_target_step_clock_bound hclock hl hl0 hc hffi ih
  have hclk_eq : s1.clock = s1'.clock + 1 := by omega
  have hbound_succ :
      multiStepTargetBound (stepExpansionFactor mc code) s1.clock =
        multiStepTargetBound (stepExpansionFactor mc code) s1'.clock +
          stepExpansionFactor mc code := by
    rw [hclk_eq]
    exact multiStepTargetBound_succ (stepExpansionFactor mc code) s1'.clock
  have hk_bound : k ≤ multiStepTargetBound (stepExpansionFactor mc code) s1.clock := by
    omega
  have hle_target : s1.clock + k ≤ K_target := by
    omega
  have hnt_step : (evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1).1 ≠ .timeOut := by
    rw [hrun]
    exact hnt
  obtain ⟨hadd_eq, hnt_K⟩ := evaluateTarget_add_clock_of_not_timeOut
    mc s1.ffi ms1 (s1.clock + k) (K_target - (s1.clock + k)) hnt_step
  rw [Nat.add_sub_of_le hle_target] at hadd_eq hnt_K
  refine ⟨⟨k, hk_bound, ms3, hrun, ?_⟩, hnt_K⟩
  exact hadd_eq.trans hrun


end InitECandidate.Solver
