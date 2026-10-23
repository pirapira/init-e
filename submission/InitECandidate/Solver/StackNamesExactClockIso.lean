import InitECandidate.Solver.SelfContainedStageBounds
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock


/-!
# `InitECandidate.Solver.StackNamesExactClockIso`

Exact clock isometry (`C_sn = 1, D_sn = 0`) for `StackNames` (`renameState`, `makeInit`,
`progCompHOL`, `compileHOL`) and composition with the zero-tick `StackRemove.initCode`
neutrality (`init_code_neutral`) without importing any `Proofs/Bounded*` module.
-/
namespace InitECandidate.Solver.StackNamesExactClockIso

open Flapjack Flapjack.Compiler.Backend
open StackLang StackProps StackRemove StackRemove.Proofs.InitClock
open StackNames
open InitECandidate.Solver.SelfContainedStageBounds

set_option autoImplicit false

/-- `StackNames` linear clock expansion slope (`C_sn = 1`). -/
def C_sn : Nat := 1

/-- `StackNames` linear clock expansion offset (`D_sn = 0`). -/
def D_sn : Nat := 0

/-- State relation for `StackNames` (`t = StackNames.renameState c f s`). -/
noncomputable def stateRel {width : Nat} [NeZero width] {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat) (s : StackSemStateFiniteExact width C F) :
    StackSemStateFiniteExact width C F :=
  StackNames.renameState c f s

/-- 1. `StackNames` state relation preserves the clock identically (`C_sn = 1, D_sn = 0`). -/
theorem stack_names_stateRel_clock_iso {width : Nat} [NeZero width] {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat) (s : StackSemStateFiniteExact width C F) :
    s.clock = (stateRel c f s).clock ∧
      (stateRel c f s).clock = C_sn * s.clock + D_sn := by
  simp [stateRel, StackNames.renameState, C_sn, D_sn]

/-- 2. `StackNames.makeInit` preserves the clock identically (`C_sn = 1, D_sn = 0`). -/
theorem stack_names_makeInit_clock_iso {width : Nat} [NeZero width] {C F : Type}
    (f : Spt Nat) (code : Spt (HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (s : StackSemStateFiniteExact width C F) :
    (StackNames.makeInit f code oracle s).clock = s.clock ∧
      (StackNames.makeInit f code oracle s).clock = C_sn * s.clock + D_sn := by
  simp [StackNames.makeInit, C_sn, D_sn]

/-- 3. `StackNames.compCorrect` induces an exact post-evaluation clock isometry (`C_sn = 1, D_sn = 0`)
and exact result agreement for every program `p`. -/
theorem stack_names_eval_post_clock_iso {width : Nat} [NeZero width] {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    (StackSemEvaluate.evaluate (StackNames.progCompHOL f p, stateRel c f s)).1 =
      (StackSemEvaluate.evaluate (p, s)).1 ∧
    (StackSemEvaluate.evaluate (StackNames.progCompHOL f p, stateRel c f s)).2.clock =
      (StackSemEvaluate.evaluate (p, s)).2.clock ∧
    (StackSemEvaluate.evaluate (StackNames.progCompHOL f p, stateRel c f s)).2.ffi =
      (StackSemEvaluate.evaluate (p, s)).2.ffi := by
  rcases hev : StackSemEvaluate.evaluate (p, s) with ⟨r, t⟩
  have hcomp := StackNames.compCorrect (c := c) (f := f) p s r t ⟨hev, hf, ha, hs, hk, hc⟩
  change StackSemEvaluate.evaluate (StackNames.progCompHOL f p, stateRel c f s) =
    (r, stateRel c f t) at hcomp
  rw [hcomp]
  exact ⟨rfl, rfl, rfl⟩

/-- 4. Non-timeout equivalence (`stack_names_not_timeOut`) across `StackNames` for any program `p`. -/
theorem stack_names_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat) (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    (StackSemEvaluate.evaluate (StackNames.progCompHOL f p, stateRel c f s)).1 ≠ some .timeOut ↔
      (StackSemEvaluate.evaluate (p, s)).1 ≠ some .timeOut := by
  have h := (stack_names_eval_post_clock_iso c f p s hf ha hs hk hc).1
  rw [h]

/-- 5. Entry-call non-timeout equivalence and exact clock isometry at explicit clock `k`. -/
theorem stack_names_entry_not_timeOut_and_clock_iso {width : Nat} [NeZero width] {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat) (s : StackSemStateFiniteExact width C F) (start k : Nat)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    ((StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { stateRel c f s with clock := k })).1 ≠ some .timeOut ↔
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k })).1 ≠ some .timeOut) ∧
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { stateRel c f s with clock := k })).2.clock =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k })).2.clock := by
  have h := StackNames.CompileSemantics.evaluate_entry_renameState
    (c := c) (f := f) (s := s) hf ha hs hk hc start k
  change StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { stateRel c f s with clock := k }) =
    ((StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k })).1,
      StackNames.renameState c f
        (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
          { s with clock := k })).2) at h
  rw [h]
  exact ⟨Iff.rfl, rfl⟩

/-- 6. All branches of the complete `StackRemove.initCode` initializer are `clockNeutralHOL`
(`0` StackSem ticks consumed), self-contained without `Proofs/Bounded*`. -/
theorem init_code_neutral {width : Nat} [NeZero width]
    (generateGc : Bool) (maximumHeap pointer : Nat) :
    clockNeutralHOL (initCode (width := width) generateGc maximumHeap pointer) :=
  initCodeClockNeutral generateGc maximumHeap pointer

/-- 7. Exact post-clock of `StackRemove.initCode` on both `s` and `stateRel c f s` (`0` ticks consumed). -/
theorem init_code_post_clock_and_consumed_ticks {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maximumHeap pointer : Nat)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s)).2.clock = s.clock ∧
    s.clock - (StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s)).2.clock = 0 := by
  have ht : (StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s)).2.clock = s.clock := by
    rcases he : StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) with ⟨r, t⟩
    have hx := EvaluateNeutral.evaluateClockNeutral
      (initCode generateGc maximumHeap pointer) s t r s.clock
      ⟨he, init_code_neutral generateGc maximumHeap pointer⟩
    have hs : { s with clock := s.clock } = s := rfl
    rw [hs, he] at hx
    exact congrArg (fun x => x.2.clock) hx
  exact ⟨ht, by omega⟩

/-- 8. Composition of `StackNames` exact clock isometry (`C_sn = 1, D_sn = 0`, `stack_names_not_timeOut`)
with `init_code_neutral` and `stack_remove_init_clocked_shift`:
`initCode` consumes `0` ticks, entry `0` consumes `1` call tick (`k_body + 1`), and `StackNames`
adds `0` extra ticks (`C_sn * (k_body + 1) + D_sn = k_body + 1`). -/
theorem stack_names_compose_init_code_neutral {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer start : Nat)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat)
    (s2 t : StackSemStateFiniteExact width C F) (k_body : Nat)
    (hentry : sptLookup 0 s2.code =
      some (.seq (StackRemove.initCode generateGc maxHeap pointer)
        (.call none (.inl start) none)))
    (hrun : StackSemEvaluate.evaluate (StackRemove.initCode generateGc maxHeap pointer, s2) =
      (none, t))
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s2.useAlloc) (hs : ¬s2.useStore) (hk : ¬s2.useStack)
    (hc : s2.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    clockNeutralHOL (StackRemove.initCode (width := width) generateGc maxHeap pointer) ∧
    t.clock = s2.clock ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { stateRel c f s2 with clock := C_sn * (k_body + 1) + D_sn })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_body })).1 ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { stateRel c f s2 with clock := C_sn * (k_body + 1) + D_sn })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_body })).2.ffi ∧
    ((StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
        { stateRel c f s2 with clock := C_sn * (k_body + 1) + D_sn })).1 ≠ some .timeOut ↔
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_body })).1 ≠ some .timeOut) := by
  have hneut := init_code_neutral (width := width) generateGc maxHeap pointer
  have hpost := (init_code_post_clock_and_consumed_ticks generateGc maxHeap pointer s2).1
  rw [hrun] at hpost
  have hshift := stack_remove_init_clocked_shift generateGc maxHeap pointer start s2 t k_body hentry hrun
  have hnames := stack_names_clocked_agree (c := c) (f := f) (s := s2) hf ha hs hk hc 0 (k_body + 1)
  have hclk : C_sn * (k_body + 1) + D_sn = k_body + 1 := by simp [C_sn, D_sn]
  change (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { stateRel c f s2 with clock := k_body + 1 })).1 = _ ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { stateRel c f s2 with clock := k_body + 1 })).2.ffi = _ at hnames
  rw [hclk]
  have hr_eq : (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { stateRel c f s2 with clock := k_body + 1 })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_body })).1 := hnames.1.trans hshift.1
  have hffi_eq : (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { stateRel c f s2 with clock := k_body + 1 })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k_body })).2.ffi := hnames.2.trans hshift.2
  refine ⟨hneut, hpost, hr_eq, hffi_eq, ?_⟩
  rw [hr_eq]

/-- 9. Sharp arithmetic boundary for the composed `StackRemove.initCode` + `StackNames` entry clock:
since `initCode` consumes `0` ticks, entry `0` takes `1` call tick, and `StackNames` has
`C_sn = 1, D_sn = 0`, the required target entry clock for body budget `k_body` is `k_body + 1`. -/
theorem stack_names_init_budget_non_vacuous_and_tight (k_entry k_body : Nat) :
    C_sn * (k_body + 1) + D_sn ≤ k_entry ↔ k_body < k_entry := by
  simp only [C_sn, D_sn]
  omega


end InitECandidate.Solver.StackNamesExactClockIso
