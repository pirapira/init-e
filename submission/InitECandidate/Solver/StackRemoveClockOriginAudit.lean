import InitECandidate.Solver.WordToStackSemanticMmioBound
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompileSemantics

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# StackRemove clock-origin audit

Facts established by reading Flapjack (`StackRemove/Proofs/CompCorrect/*`):
* the guest compiler config has `stackConf.jump = false` (checked below);
* in `CompCorrect`, the only constructor case that creates a nonzero allowance is
  `StoreConsts` (copy-loop allowance); `Seq`, `Loop`, `CallReturn*` only *sum* sub-run
  allowances; all other cases return the sub-run clock unchanged;
* `WordToStack` emits `.storeConsts` (`NativeCompile.lean:117`) and `.alloc`
  (`NativeCompile.lean:114`) from WordLang `storeConsts` / `alloc`, which the Pancake
  frontend never emits directly but `WordAlloc`/`WordSimp` passes do mention.
Only the first fact and the entry simulation at `jump = false` are machine-checked here.
-/

namespace InitECandidate.Solver.StackRemoveClockOriginAudit

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.RiscVConfig
open InitECandidate.Proofs
open InitE

/-- Guest StackRemove runs with `jump = false` for every oracle list. -/
theorem guest_stackRemove_jump_false (oracles : List (Option (Spt Nat))) :
    (oracleCompilerConfig oracles).stackConf.jump = false := by
  simp [oracleCompilerConfig, pancakeRiscVBackendConfig_eq]
  rfl

/-- StackRemove entry simulation specialised to the guest's `jump = false`. -/
theorem stackRemove_entry_jump_false {width : Nat} [NeZero width] {C F : Type}
    (bounds : BitVec width × BitVec width) (pointer start clock : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (relation : stateRelHOL false bounds pointer source target)
    (run : StackSemEvaluate.evaluate (.call none (.inl start) none, {source with clock := clock}) =
      (result, postSource))
    (nonError : result ≠ some .error) :
    ∃ extra postTarget,
      StackSemEvaluate.evaluate (.call none (.inl start) none, {target with clock := extra + clock}) =
        (result, postTarget) ∧ postTarget.ffi = postSource.ffi :=
  CompileSemantics.entrySimulation false bounds pointer start clock source target postSource
    result relation run nonError

/-! ## Allowance algebra mirroring the `CompCorrect` case structure -/

/-- Per-construct allowance: only `storeConsts` contributes, by its copy-loop allowance. -/
def caseAllowance (isStoreConsts : Bool) (copyAllowance : Nat) : Nat :=
  if isStoreConsts then copyAllowance else 0

/-- Total allowance of a run as the sum over executed constructs (Seq/Loop sum rule). -/
def runAllowance : List (Bool × Nat) → Nat
  | [] => 0
  | (b, a) :: rest => caseAllowance b a + runAllowance rest

theorem caseAllowance_non_storeConsts (a : Nat) : caseAllowance false a = 0 := rfl

theorem caseAllowance_storeConsts (a : Nat) : caseAllowance true a = a := rfl

theorem runAllowance_append (xs ys : List (Bool × Nat)) :
    runAllowance (xs ++ ys) = runAllowance xs + runAllowance ys := by
  induction xs with
  | nil => simp [runAllowance]
  | cons x xs ih => obtain ⟨b, a⟩ := x; simp [runAllowance, ih]; omega

/-- A run with no executed `storeConsts` has zero StackRemove allowance. -/
theorem runAllowance_zero_of_no_storeConsts (xs : List (Bool × Nat))
    (h : ∀ p ∈ xs, p.1 = false) : runAllowance xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨b, a⟩ := x
    have hb : b = false := h (b, a) (List.mem_cons_self ..)
    subst hb
    simp [runAllowance, caseAllowance, ih (fun p hp => h p (List.mem_cons_of_mem _ hp))]

/-- Allowance bound: `n` executed `storeConsts`, each with allowance `≤ A`, cost `≤ n * A`. -/
theorem runAllowance_le (xs : List (Bool × Nat)) (A : Nat) (h : ∀ p ∈ xs, p.2 ≤ A) :
    runAllowance xs ≤ (xs.filter (·.1)).length * A := by
  induction xs with
  | nil => simp [runAllowance]
  | cons x xs ih =>
    obtain ⟨b, a⟩ := x
    have ha : a ≤ A := h (b, a) (List.mem_cons_self ..)
    have ih' := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    cases b <;> simp [runAllowance, caseAllowance, List.filter] <;> [omega; (rw [Nat.succ_mul]; omega)]

/-- Tightness: one `storeConsts` with allowance `A` attains the bound. -/
theorem runAllowance_tight (A : Nat) : runAllowance [(true, A)] = 1 * A := by
  simp [runAllowance, caseAllowance]


end InitECandidate.Solver.StackRemoveClockOriginAudit
