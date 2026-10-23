import InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock
import InitECandidate.Solver.WordToWordNoStubCall
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)

/-! ## `CodeNoSt`: every installed / installable code entry is `storeConsts`-free -/

/-- State invariant: every entry of the code table and of every future oracle batch
satisfies `StackNoSt`. -/
def CodeNoSt {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : Prop :=
  (∀ k p, sptLookup k s.code = some p → StackNoSt p = true) ∧
  (∀ i, ∀ e ∈ (s.compileOracle i).2.1, StackNoSt e.2 = true)

theorem lookup_foldl_sptUnion {α : Type} (k : Nat) (v : α) :
    ∀ (L : List (Spt α)) (init : Spt α),
      sptLookup k (L.foldl sptUnion init) = some v →
      sptLookup k init = some v ∨ ∃ t ∈ L, sptLookup k t = some v
  | [], init, h => Or.inl h
  | t :: L, init, h => by
      rcases lookup_foldl_sptUnion k v L (sptUnion init t) h with h1 | ⟨u, hu, hl⟩
      · rw [sptLookup_sptUnion] at h1
        cases hi : sptLookup k init with
        | some w => rw [hi] at h1; exact Or.inl h1
        | none => rw [hi] at h1; exact Or.inr ⟨t, List.mem_cons_self .., h1⟩
      · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, hl⟩

/-- `CodeNoSt` is preserved by every evaluation, including `install`
(derived from Flapjack's `evaluateCodeBitmaps` code/oracle evolution law). -/
theorem codeNoSt_evaluate {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (h : CodeNoSt source) : CodeNoSt post := by
  obtain ⟨count, hor, hcode, _⟩ :=
    StackProps.EvaluateCodeBitmaps.evaluateCodeBitmaps program source result post run
  refine ⟨fun k p hk => ?_, fun i e he => ?_⟩
  · rw [hcode] at hk
    rcases lookup_foldl_sptUnion k p _ _ hk with h0 | ⟨t, ht, hl⟩
    · exact h.1 k p h0
    · rcases List.mem_map.1 ht with ⟨idx, _, rfl⟩
      rw [sptLookup_sptFromAList] at hl
      exact h.2 idx (k, p) (sptAListLookup_mem _ _ _ hl)
  · rw [hor] at he
    exact h.2 (i + count) e he

/-! ## Clock outcome -/

/-- Allowed extra clock for one simulated run: zero, except a final `halt` (stack-overflow
`halt 2` of `stackAlloc`) may cost at most one tick. -/
def ClockOk {width : Nat} [NeZero width] (clock : Nat) (r : Option (StackSemResult width)) : Prop :=
  clock = 0 ∨ (clock ≤ 1 ∧ ∃ w, r = some (.halt w))


/-- A `ClockOk` run whose result is not a `halt` costs no extra clock. -/
theorem clockOk_zero_of_not_halt {width : Nat} [NeZero width] {c : Nat}
    {r : Option (StackSemResult width)} (h : ClockOk c r) (nh : ∀ w, r ≠ some (.halt w)) :
    c = 0 := by
  rcases h with h | ⟨_, w, hw⟩
  · exact h
  · exact absurd hw (nh w)

/-- Loop exit keeps a `halt` a `halt`, so `ClockOk` survives `exitLoop`. -/
theorem clockOk_exitLoop {width : Nat} [NeZero width] {c : Nat}
    {r : Option (StackSemResult width)} (h : ClockOk c r) :
    ClockOk c (StackSemControl.exitLoop r) := by
  rcases h with h | ⟨hc, w, hw⟩
  · exact Or.inl h
  · subst hw; exact Or.inr ⟨hc, w, rfl⟩

end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Seq
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.Seq
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemControl
/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-local Seq proof infrastructure: the reviewed unconditional clock
identity recovers the original rebound evaluator equation. No independent
HOL declaration is claimed. -/
theorem evaluateSeqUnclampedZ {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (source : StackSemStateFiniteExact width C F) :
    evaluate (.seq first second, source) =
      match evaluate (first, source) with
      | (none, middle) => evaluate (second, middle)
      | (some result, middle) => (some result, middle) := by
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases evaluate (first, source) with ⟨result, middle⟩
  cases result <;> rfl

/-- Source-local NONE branch equation, with the actual first run as its premise; no independent HOL declaration. -/
theorem evaluateSeqNoneZ {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (source middle : StackSemStateFiniteExact width C F)
    (execution : evaluate (first, source) = (none, middle)) :
    evaluate (.seq first second, source) = evaluate (second, middle) := by
  rw [evaluateSeqUnclampedZ, execution]

/-- Source-local SOME branch equation, with the actual first run as its premise; no independent HOL declaration. -/
theorem evaluateSeqSomeZ {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (source middle : StackSemStateFiniteExact width C F)
    (result : StackSemResult width)
    (execution : evaluate (first, source) = (some result, middle)) :
    evaluate (.seq first second, source) = (some result, middle) := by
  rw [evaluateSeqUnclampedZ, execution]

/-- Genuine original Seq induction case. Only the two source-shaped recursive
induction hypotheses augment the original four premises: the first is fixed
at the input source; the second is guarded by the actual first NONE run.
Target evaluation and extra clocks are derived, not assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectSeqZ {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (firstIH : ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
      (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (first, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound first k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k first, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (secondIH : ∀ (middle : StackSemStateFiniteExact width C F),
      evaluate (first, source) = (none, middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (second, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k middle t ∧ StackProps.regBound second k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k second, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.seq first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.seq first second) pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer (.seq first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  change StackProps.regBound first pointer ∧ StackProps.regBound second pointer at lower
  rcases firstRun : evaluate (first, source) with ⟨firstResult, middle⟩
  cases firstResult with
  | none =>
    rw [evaluateSeqNoneZ first second source middle firstRun] at sourceRun
    obtain ⟨firstClock, middleTarget, hck1, firstTargetRun, middleRelation⟩ :=
      firstIH none middle target pointer bounds jump ⟨firstRun, by simp, relation, lower.1⟩
    change stateRelHOL jump bounds pointer middle middleTarget at middleRelation
    obtain ⟨secondClock, postTarget, hck2, secondTargetRun, postRelation⟩ :=
      secondIH middle firstRun result postSource middleTarget pointer bounds jump
        ⟨sourceRun, notError, middleRelation, lower.2⟩
    have extraRun := StackProps.evaluateAddClock secondClock
      (comp jump bounds pointer first) {target with clock := firstClock + target.clock}
      none middleTarget ⟨firstTargetRun, by simp⟩
    have combinedRun :
        evaluate (comp jump bounds pointer first,
          {target with clock := (firstClock + secondClock) + target.clock}) =
          (none, {middleTarget with clock := secondClock + middleTarget.clock}) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extraRun
    refine ⟨firstClock + secondClock, postTarget, (by rw [clockOk_zero_of_not_halt hck1 (by intro w h; first | (simp at h; done) | (subst h; simp [StackSemControl.contLoop] at continues))]; simpa using hck2), ?_, ?_⟩
    · rw [comp, evaluateSeqNoneZ _ _ _ _ combinedRun]
      exact secondTargetRun
    · cases result with
      | none => exact postRelation
      | some value => cases value <;> exact postRelation
  | some firstResult =>
    rw [evaluateSeqSomeZ first second source middle firstResult firstRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
      firstIH (some firstResult) middle target pointer bounds jump
        ⟨firstRun, notError, relation, lower.1⟩
    refine ⟨clock, postTarget, hck, ?_, ?_⟩
    · rw [comp, evaluateSeqSomeZ _ _ _ _ _ targetRun]
    · cases firstResult <;> exact postRelation
end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Seq

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.If
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.If
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Seq
open Flapjack Compiler.Backend.StackLang Compiler.Encoders.Asm StackSemEvaluate StackSemStateOps
/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-local operand preservation infrastructure; no independent HOL declaration. -/
theorem operandLookupZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (operand : HolRegImm width)
    (relation : stateRelHOL jump bounds pointer source target)
    (lower : match operand with | .reg n => n < pointer | .imm _ => True) :
    StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source =
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
  cases operand with
  | reg n => exact RelationLaws.stateRelGetVar jump bounds pointer n source target ⟨relation, lower⟩
  | imm w => rfl

/-- Genuine original If induction case: original four premises and complete
existential target/result relation, augmented only by the original actual
lookup/comparison-guarded branch induction hypotheses. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectIfZ {width : Nat} [NeZero width] {C F : Type}
    (comparison : Cmp) (register : Nat) (operand : HolRegImm width)
    (first second : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (firstIH : ∀ (left right : WordLocW width),
      getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some true →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (first, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound first k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k first, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (secondIH : ∀ (left right : WordLocW width),
      getVar register source = some left →
      StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some right →
      wordSemWordCmp comparison left right = some false →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (second, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound second k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k second, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.ite comparison register operand first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.ite comparison register operand first second) pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer (.ite comparison register operand first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  simp only [StackProps.regBound] at lower
  have leftEq := RelationLaws.stateRelGetVar jump bounds pointer register source target ⟨relation, lower.1⟩
  have rightEq := operandLookupZ jump bounds pointer source target operand relation lower.2.1
  rw [evaluate_ite] at sourceRun
  cases leftLookup : getVar register source with
  | none =>
    rw [leftLookup] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some left =>
    rw [leftLookup] at sourceRun
    cases rightLookup : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source with
    | none =>
      rw [rightLookup] at sourceRun
      exact (notError (Prod.mk.inj sourceRun).1.symm).elim
    | some right =>
      rw [rightLookup] at sourceRun
      simp only [] at sourceRun
      cases compared : wordSemWordCmp comparison left right with
      | none =>
        rw [compared] at sourceRun
        exact (notError (Prod.mk.inj sourceRun).1.symm).elim
      | some truth =>
        cases truth with
        | false =>
          rw [compared] at sourceRun
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            secondIH left right leftLookup rightLookup compared result postSource target pointer bounds jump
              ⟨sourceRun, notError, relation, lower.2.2.2⟩
          have targetLeft : getVar register {target with clock := clock + target.clock} = some left :=
            leftEq.symm.trans leftLookup
          have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} = some right := by
            have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
                {target with clock := clock + target.clock} =
                StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
              cases operand <;> rfl
            exact same.trans (rightEq.symm.trans rightLookup)
          refine ⟨clock, postTarget, hck, ?_, ?_⟩
          · rw [comp, evaluate_ite, targetLeft, targetRight]
            simpa only [compared] using targetRun
          · cases result with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
        | true =>
          rw [compared] at sourceRun
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            firstIH left right leftLookup rightLookup compared result postSource target pointer bounds jump
              ⟨sourceRun, notError, relation, lower.2.2.1⟩
          have targetLeft : getVar register {target with clock := clock + target.clock} = some left :=
            leftEq.symm.trans leftLookup
          have targetRight : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
              {target with clock := clock + target.clock} = some right := by
            have same : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand)
                {target with clock := clock + target.clock} =
                StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) target := by
              cases operand <;> rfl
            exact same.trans (rightEq.symm.trans rightLookup)
          refine ⟨clock, postTarget, hck, ?_, ?_⟩
          · rw [comp, evaluate_ite, targetLeft, targetRight]
            simpa only [compared] using targetRun
          · cases result with
            | none => exact postRelation
            | some value => cases value <;> exact postRelation
end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.If

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Loop
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.Loop
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Seq InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.If
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemControl StackSemStateOps
/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Source-local Loop proof infrastructure: the reviewed unconditional clock
identity recovers the original rebound evaluator equation. No independent
HOL declaration is claimed. -/
theorem evaluateLoopUnclampedZ {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source : StackSemStateFiniteExact width C F) :
    evaluate (.loop body, source) =
      match evaluate (body, source) with
      | (result, middle) =>
          if StackSemControl.contLoop result then
            if middle.clock = 0 then (some .timeOut, emptyEnv middle)
            else evaluate (.loop body, decClock middle)
          else (StackSemControl.exitLoop result, middle) := by
  rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate]

/-- Actual exit branch equation; source-local infrastructure with no separate HOL original. -/
theorem evaluateLoopExitZ {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source middle : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : evaluate (body, source) = (result, middle))
    (exits : StackSemControl.contLoop result = false) :
    evaluate (.loop body, source) = (StackSemControl.exitLoop result, middle) := by
  rw [evaluateLoopUnclampedZ, execution]
  simp only [exits, Bool.false_eq_true, if_false]

/-- Actual zero-clock branch equation; source-local infrastructure, not a separate HOL port. -/
theorem evaluateLoopTimeOutZ {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source middle : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : evaluate (body, source) = (result, middle))
    (continues : StackSemControl.contLoop result = true) (zero : middle.clock = 0) :
    evaluate (.loop body, source) = (some .timeOut, emptyEnv middle) := by
  rw [evaluateLoopUnclampedZ, execution]
  simp only [continues, if_true, zero]

/-- Actual reentry equation; source-local infrastructure retaining both real guards. -/
theorem evaluateLoopReentryZ {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source middle : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (execution : evaluate (body, source) = (result, middle))
    (continues : StackSemControl.contLoop result = true) (nonzero : middle.clock ≠ 0) :
    evaluate (.loop body, source) = evaluate (.loop body, decClock middle) := by
  rw [evaluateLoopUnclampedZ, execution]
  simp only [continues, if_true, nonzero, if_false]

/-- The original non-Error whole-run premise excludes a body Error. This is
source-local case factoring, with no independent HOL declaration. -/
theorem loopBodyNotErrorZ {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (source middle post : StackSemStateFiniteExact width C F)
    (bodyResult result : Option (StackSemResult width))
    (bodyRun : evaluate (body, source) = (bodyResult, middle))
    (loopRun : evaluate (.loop body, source) = (result, post))
    (notError : result ≠ some .error) : bodyResult ≠ some .error := by
  intro eq
  subst bodyResult
  have exits : StackSemControl.contLoop (some (.error : StackSemResult width)) = false := rfl
  rw [evaluateLoopExitZ body source middle (some .error) bodyRun exits] at loopRun
  exact notError (Prod.mk.inj loopRun).1.symm

/-- Genuine full original Loop induction case, with only the original body and
actual body-run/continuation/nonzero-clock guarded reentry IHs augmenting the
four source premises. The native target run and added clock are derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectLoopZ {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (bodyIH : ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
      (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (body, source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k source t ∧ StackProps.regBound body k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (reentryIH : ∀ (bodyResult : Option (StackSemResult width)) (middle : StackSemStateFiniteExact width C F),
      evaluate (body, source) = (bodyResult, middle) →
      StackSemControl.contLoop bodyResult = true → middle.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (.loop body, decClock middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock middle) t ∧ StackProps.regBound (.loop body) k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k (.loop body), {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.loop body, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.loop body) pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer (.loop body),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, lower⟩
  rcases bodyRun : evaluate (body, source) with ⟨bodyResult, middle⟩
  have bodyNotError := loopBodyNotErrorZ body source middle postSource bodyResult result bodyRun sourceRun notError
  obtain ⟨firstClock, middleTarget, hck1, firstTargetRun, bodyPost⟩ :=
    bodyIH bodyResult middle target pointer bounds jump
      ⟨bodyRun, bodyNotError, relation, by simpa only [StackProps.regBound] using lower⟩
  by_cases continues : StackSemControl.contLoop bodyResult = true
  · have middleRelation : stateRelHOL jump bounds pointer middle middleTarget := by
      rcases StackProps.contLoopImp bodyResult continues with same | same
      · rw [same] at bodyPost; exact bodyPost
      · rw [same] at bodyPost; exact bodyPost
    have middleClocks : middleTarget.clock = middle.clock := middleRelation.2.2.2.2.2.2.2.2.1
    by_cases zero : middle.clock = 0
    · rw [evaluateLoopTimeOutZ body source middle bodyResult bodyRun continues zero] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      refine ⟨firstClock, emptyEnv middleTarget, Or.inl (clockOk_zero_of_not_halt hck1 (by intro w h; first | (simp at h; done) | (subst h; simp [StackSemControl.contLoop] at continues))), ?_, ?_⟩
      · simpa only [comp] using
          evaluateLoopTimeOutZ (comp jump bounds pointer body)
            {target with clock := firstClock + target.clock} middleTarget bodyResult
            firstTargetRun continues (middleClocks.trans zero)
      · change middleTarget.ffi = middle.ffi
        exact middleRelation.2.2.2.2.2.2.2.2.2.1
    · rw [evaluateLoopReentryZ body source middle bodyResult bodyRun continues zero] at sourceRun
      have decRelation := RelationLaws.stateRelDecClock jump bounds pointer middle middleTarget middleRelation
      obtain ⟨secondClock, postTarget, hck2, secondTargetRun, postRelation⟩ :=
        reentryIH bodyResult middle bodyRun continues zero result postSource
          (decClock middleTarget) pointer bounds jump ⟨sourceRun, notError, decRelation, lower⟩
      have notTimeout : bodyResult ≠ some .timeOut := by
        rcases StackProps.contLoopImp bodyResult continues with same | same <;> simp [same]
      have extraRun := StackProps.evaluateAddClock secondClock
        (comp jump bounds pointer body) {target with clock := firstClock + target.clock}
        bodyResult middleTarget ⟨firstTargetRun, notTimeout⟩
      have combinedRun :
          evaluate (comp jump bounds pointer body,
            {target with clock := (firstClock + secondClock) + target.clock}) =
            (bodyResult, {middleTarget with clock := secondClock + middleTarget.clock}) := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using extraRun
      have targetNonzero : middleTarget.clock ≠ 0 := by rw [middleClocks]; exact zero
      have boostedNonzero : ({middleTarget with clock := secondClock + middleTarget.clock}).clock ≠ 0 := by
        change secondClock + middleTarget.clock ≠ 0
        omega
      have decState : decClock {middleTarget with clock := secondClock + middleTarget.clock} =
          {decClock middleTarget with clock := secondClock + (decClock middleTarget).clock} := by
        change {middleTarget with clock := secondClock + middleTarget.clock - 1} =
          {middleTarget with clock := secondClock + (middleTarget.clock - 1)}
        have arithmetic : secondClock + middleTarget.clock - 1 = secondClock + (middleTarget.clock - 1) := by omega
        rw [arithmetic]
      refine ⟨firstClock + secondClock, postTarget, (by rw [clockOk_zero_of_not_halt hck1 (by intro w h; first | (simp at h; done) | (subst h; simp [StackSemControl.contLoop] at continues))]; simpa using hck2), ?_, ?_⟩
      · rw [comp, evaluateLoopReentryZ _ _ _ _ combinedRun continues boostedNonzero, decState]
        simpa only [comp] using secondTargetRun
      · cases result with
        | none => exact postRelation
        | some value => cases value <;> exact postRelation
  · have exits : StackSemControl.contLoop bodyResult = false := by
      cases equality : StackSemControl.contLoop bodyResult <;> simp_all
    rw [evaluateLoopExitZ body source middle bodyResult bodyRun exits] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨firstClock, middleTarget, clockOk_exitLoop hck1, ?_, ?_⟩
    · simpa only [comp] using
        evaluateLoopExitZ (comp jump bounds pointer body)
          {target with clock := firstClock + target.clock} middleTarget bodyResult firstTargetRun exits
    · cases bodyResult with
      | none => simp [StackSemControl.contLoop] at continues
      | some value =>
        cases value with
        | «break» label => cases label <;> exact bodyPost
        | _ => exact bodyPost
end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Loop

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallTail
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallTail
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Seq InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.If InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Loop
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Original ret=NONE Call case. Arbitrary handlers are retained; handler
SOME is excluded only by the original source non-Error premise. Only actual
source lookup/handler NONE/nonzero-clock guarded callee IHs are assumed.
Unconditional clock clamping is discharged for both faithful evaluators. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCallTailZ {width : Nat} [NeZero width] {C F : Type}
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (program : HolProg width),
      StackSemControl.findCode dest source.regs source.code = some program →
      handler = none → source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock source) t ∧ StackProps.regBound program k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.call none dest handler, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.call none dest handler : HolProg width) pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer (.call none dest handler),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_call] at sourceRun
  cases lookup : StackSemControl.findCode dest source.regs source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    cases handler with
    | some h =>
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | none =>
      obtain ⟨targetLookup, bodyBound⟩ := FindCode.findCodeLemma jump bounds pointer
        source target dest program ⟨relation, by
          simp only [StackProps.regBound] at bound
          cases dest <;> exact bound.1, lookup⟩
      by_cases zero : source.clock = 0
      · simp only [zero, if_true] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
        subst result
        subst postSource
        refine ⟨0, emptyEnv target, Or.inl rfl, ?_, ?_⟩
        · simpa only [comp, Nat.zero_add] using
            (evaluate_call none dest none target).trans (by
              simp only [targetLookup, clocks, zero, if_true])
        · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
      · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at sourceRun
        rcases bodyRun : evaluate (program, decClock source) with ⟨bodyResult, middle⟩
        rw [bodyRun] at sourceRun
        by_cases bad : StackSemControl.badFunReturn bodyResult = true
        · simp only [bad, if_true] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        · simp [bad] at sourceRun
          rcases sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            calleeIH program lookup rfl zero bodyResult middle (decClock target) pointer bounds jump
              ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, bodyBound⟩
          refine ⟨clock, postTarget, hck, ?_, ?_⟩
          swap
          · cases bodyResult with
            | none => exact postRelation
            | some r => cases r <;> exact postRelation
          have nonzero : clock + target.clock ≠ 0 := by omega
          have clockEq : decClock {target with clock := clock + target.clock} =
              {decClock target with clock := clock + (decClock target).clock} := by
            simp only [decClock]
            congr 1
            omega
          simp only [comp]
          rw [evaluate_call]
          simp only [targetLookup, nonzero, if_false, StackSemEvaluateClock.fixClockEvaluate]
          rw [clockEq, targetRun]
          simp [bad]
end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallTail

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnNone
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnNone
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Seq InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.If InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Loop InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallTail
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

/-- Flapjack proof infrastructure for the original returning Call case.
This removes the native clock clamp using the unconditional evaluator theorem;
it claims no independent HOL declaration. Every original result branch remains. -/
theorem evaluateCallReturnNoneUnclampedZ {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (source : StackSemStateFiniteExact width C F) :
    evaluate (.call (some (body, link, l1, l2)) dest none, source) =
      match StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
      | none => (some .error, source)
      | some program =>
        if source.clock = 0 then (some .timeOut, emptyEnv source)
        else
          match evaluate (program, decClock (setVar link (.loc l1 l2) source)) with
          | (some (.result value), middle) =>
            if value ≠ .loc l1 l2 then (some .error, middle)
            else evaluate (body, middle)
          | (some (.exception value), middle) => (some (.exception value), middle)
          | (none, middle) => (some .error, middle)
          | (some (.break _), middle) => (some .error, middle)
          | (some (.continue _), middle) => (some .error, middle)
          | (result, middle) => (result, middle) := by
  rw [evaluate_call]
  cases lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
  | none => simp only [lookup]
  | some program =>
    simp only [lookup]
    split
    · rfl
    · rw [StackSemEvaluateClock.fixClockEvaluate]
      rfl

/-- Flapjack proof infrastructure: assigning the return location and consuming
one tick preserves the complete relation. No separate HOL declaration. -/
theorem entryRelationZ {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer link l1 l2 : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) (below : link < pointer) :
    stateRelHOL jump bounds pointer
      (decClock (setVar link (.loc l1 l2) source))
      (decClock (setVar link (.loc l1 l2) target)) :=
  RelationLaws.stateRelDecClock jump bounds pointer _ _
    (StateUpdates.stateRelSetVar jump bounds pointer link (.loc l1 l2) source target
      ⟨relation, below⟩)

/-- Flapjack proof infrastructure for target callee entry with an existential
clock allowance. The nonzero premise is the actual source Call branch guard. -/
theorem entryClockZ {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (link l1 l2 extra : Nat)
    (nonzero : target.clock ≠ 0) :
    decClock (setVar link (.loc l1 l2) {target with clock := extra + target.clock}) =
      {decClock (setVar link (.loc l1 l2) target) with
        clock := extra + (decClock (setVar link (.loc l1 l2) target)).clock} := by
  simp only [setVar, decClock]
  congr 1
  omega

/-- Flapjack proof infrastructure for composing the callee and return-body
clock allowances. The run is the intermediate conclusion obtained from the
callee IH, not a premise of a tagged pass-correctness port. The actual return
result discharges the non-TimeOut condition of `evaluateAddClock`. -/
theorem calleeAllowanceZ {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (target post : StackSemStateFiniteExact width C F)
    (link l1 l2 first second : Nat) (nonzero : target.clock ≠ 0)
    (run : evaluate (program,
      {decClock (setVar link (.loc l1 l2) target) with
        clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}) =
      (some (.result (.loc l1 l2)), post)) :
    evaluate (program,
      decClock (setVar link (.loc l1 l2)
        {target with clock := (first + second) + target.clock})) =
      (some (.result (.loc l1 l2)), {post with clock := second + post.clock}) := by
  rw [entryClockZ target link l1 l2 (first + second) nonzero]
  have boosted := StackProps.evaluateAddClock second program
    {decClock (setVar link (.loc l1 l2) target) with
      clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}
    (some (.result (.loc l1 l2))) post ⟨run, by simp⟩
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using boosted

/-- Source-local actual successful-return branch equation, used for both
source and compiled target. This has no separate HOL declaration. -/
theorem evaluateCallReturnNoneResultZ {width : Nat} [NeZero width] {C F : Type}
    (body program : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (source middle : StackSemStateFiniteExact width C F)
    (lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (run : evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.result (.loc l1 l2)), middle)) :
    evaluate (.call (some (body, link, l1, l2)) dest none, source) =
      evaluate (body, middle) := by
  rw [evaluateCallReturnNoneUnclampedZ]
  simp only [lookup, nonzero, if_false, run, ne_eq, not_true_eq_false]

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Original returning Call with handler NONE, retaining every source result.
Only actual source lookup/nonzero-clock guarded callee and actual successful
return-location guarded continuation induction hypotheses are added to the
original four premises. Intermediate target runs and relations are derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCallReturnNoneZ {width : Nat} [NeZero width] {C F : Type}
    (body : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (program : HolProg width),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock (setVar link (.loc l1 l2) source)) t ∧ StackProps.regBound program k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (returnIH : ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (some (.result (.loc l1 l2)), middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (body, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (middle) t ∧ StackProps.regBound body k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.call (some (body, link, l1, l2)) dest none, source) =
        (result, postSource) ∧ result ≠ some .error ∧
      stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.call (some (body, link, l1, l2)) dest none) pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer (.call (some (body, link, l1, l2)) dest none),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluateCallReturnNoneUnclampedZ] at sourceRun
  cases lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    obtain ⟨targetLookup, programBound⟩ := FindCode.findCodeLemmaErased jump bounds pointer
      source target dest program link ⟨relation, by
        simp only [StackProps.regBound] at bound
        cases dest <;> exact bound.1, lookup⟩
    have bodyBound : StackProps.regBound body pointer := by
      simp only [StackProps.regBound] at bound
      exact bound.2.1
    have linkBound : link < pointer := by
      simp only [StackProps.regBound] at bound
      exact bound.2.2.1
    by_cases zero : source.clock = 0
    · simp only [zero, if_true] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
      subst result
      subst postSource
      refine ⟨0, emptyEnv target, Or.inl rfl, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluateCallReturnNoneUnclampedZ (comp jump bounds pointer body) link l1 l2 dest target).trans (by
            simp only [targetLookup, clocks, zero, if_true])
      · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
    · simp only [zero, if_false] at sourceRun
      have targetNonzero : target.clock ≠ 0 := by omega
      have entry := entryRelationZ jump bounds pointer link l1 l2 source target relation linkBound
      rcases bodyRun : evaluate (program, decClock (setVar link (.loc l1 l2) source)) with
        ⟨bodyResult, middle⟩
      rw [bodyRun] at sourceRun
      cases bodyResult with
      | none =>
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some value =>
        cases value with
        | error => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | «break» n => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | «continue» n => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | result value =>
          change (if value ≠ .loc l1 l2 then (some .error, middle)
            else evaluate (body, middle)) = (result, postSource) at sourceRun
          split at sourceRun
          · exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          · rename_i equal
            have correct : value = .loc l1 l2 := by simpa only [ne_eq, not_not] using equal
            subst value
            obtain ⟨first, middleTarget, hck1, calleeRun, middleRelation⟩ :=
              calleeIH program lookup zero (some (.result (.loc l1 l2))) middle
                (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
                ⟨bodyRun, by simp, entry, programBound⟩
            obtain ⟨second, postTarget, hck2, returnRun, postRelation⟩ :=
              returnIH program middle lookup zero bodyRun result postSource middleTarget pointer bounds jump
                ⟨sourceRun, notError, middleRelation, bodyBound⟩
            have boosted := calleeAllowanceZ (comp jump bounds pointer program) target middleTarget
              link l1 l2 first second targetNonzero calleeRun
            refine ⟨first + second, postTarget, (by rw [clockOk_zero_of_not_halt hck1 (by intro w h; first | (simp at h; done) | (subst h; simp [StackSemControl.contLoop] at continues))]; simpa using hck2), ?_, ?_⟩
            · have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
              simp only [comp]
              rw [evaluateCallReturnNoneResultZ (comp jump bounds pointer body)
                (comp jump bounds pointer program) link l1 l2 dest
                {target with clock := (first + second) + target.clock}
                {middleTarget with clock := second + middleTarget.clock}
                targetLookup totalNonzero boosted]
              exact returnRun
            · cases result with
              | none => exact postRelation
              | some r => cases r <;> exact postRelation
        | halt n =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            calleeIH program lookup zero (some (.halt n)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, hck, ?_, postRelation⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          simp only [comp]
          rw [evaluateCallReturnNoneUnclampedZ]
          simp only [targetLookup, nonzero, if_false]
          rw [entryClockZ target link l1 l2 clock targetNonzero, targetRun]
        | timeOut =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            calleeIH program lookup zero (some (.timeOut)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, hck, ?_, postRelation⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          simp only [comp]
          rw [evaluateCallReturnNoneUnclampedZ]
          simp only [targetLookup, nonzero, if_false]
          rw [entryClockZ target link l1 l2 clock targetNonzero, targetRun]
        | finalFFI event =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            calleeIH program lookup zero (some (.finalFFI event)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, hck, ?_, postRelation⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          simp only [comp]
          rw [evaluateCallReturnNoneUnclampedZ]
          simp only [targetLookup, nonzero, if_false]
          rw [entryClockZ target link l1 l2 clock targetNonzero, targetRun]
        | exception location =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            calleeIH program lookup zero (some (.exception location)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, hck, ?_, postRelation⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          simp only [comp]
          rw [evaluateCallReturnNoneUnclampedZ]
          simp only [targetLookup, nonzero, if_false]
          rw [entryClockZ target link l1 l2 clock targetNonzero, targetRun]
end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnNone

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnHandler
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallReturnHandler
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Seq InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.If InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Loop InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallTail InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnNone
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps
open CallReturnNone

/-- Flapjack proof infrastructure for the original returning Call case.
This removes the native clock clamp using the unconditional evaluator theorem;
it claims no independent HOL declaration. Every original result branch remains. -/
theorem evaluateCallReturnHandlerUnclampedZ {width : Nat} [NeZero width] {C F : Type}
    (body handler : HolProg width) (link l1 l2 hl1 hl2 : Nat) (dest : Sum Nat Nat)
    (source : StackSemStateFiniteExact width C F) :
    evaluate (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)), source) =
      match StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
      | none => (some .error, source)
      | some program =>
        if source.clock = 0 then (some .timeOut, emptyEnv source)
        else
          match evaluate (program, decClock (setVar link (.loc l1 l2) source)) with
          | (some (.result value), middle) =>
            if value ≠ .loc l1 l2 then (some .error, middle)
            else evaluate (body, middle)
          | (some (.exception value), middle) =>
            if value ≠ .loc hl1 hl2 then (some .error, middle)
            else evaluate (handler, middle)
          | (none, middle) => (some .error, middle)
          | (some (.break _), middle) => (some .error, middle)
          | (some (.continue _), middle) => (some .error, middle)
          | (result, middle) => (result, middle) := by
  rw [evaluate_call]
  cases lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
  | none => simp only [lookup]
  | some program =>
    simp only [lookup]
    split
    · rfl
    · rw [StackSemEvaluateClock.fixClockEvaluate]
      rfl

/-- Flapjack proof infrastructure for composing the callee and exception-body
clock allowances. The run is the intermediate conclusion obtained from the
callee IH, not a premise of a tagged pass-correctness port. The actual exception
result discharges the non-TimeOut condition of `evaluateAddClock`. -/
theorem exceptionAllowanceZ {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (target post : StackSemStateFiniteExact width C F)
    (link l1 l2 hl1 hl2 first second : Nat) (nonzero : target.clock ≠ 0)
    (run : evaluate (program,
      {decClock (setVar link (.loc l1 l2) target) with
        clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}) =
      (some (.exception (.loc hl1 hl2)), post)) :
    evaluate (program,
      decClock (setVar link (.loc l1 l2)
        {target with clock := (first + second) + target.clock})) =
      (some (.exception (.loc hl1 hl2)), {post with clock := second + post.clock}) := by
  rw [entryClockZ target link l1 l2 (first + second) nonzero]
  have boosted := StackProps.evaluateAddClock second program
    {decClock (setVar link (.loc l1 l2) target) with
      clock := first + (decClock (setVar link (.loc l1 l2) target)).clock}
    (some (.exception (.loc hl1 hl2))) post ⟨run, by simp⟩
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using boosted

/-- Source-local actual successful-return branch equation, used for both
source and compiled target. This has no separate HOL declaration. -/
theorem evaluateCallReturnHandlerResultZ {width : Nat} [NeZero width] {C F : Type}
    (body handler program : HolProg width) (link l1 l2 hl1 hl2 : Nat) (dest : Sum Nat Nat)
    (source middle : StackSemStateFiniteExact width C F)
    (lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (run : evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.result (.loc l1 l2)), middle)) :
    evaluate (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)), source) =
      evaluate (body, middle) := by
  rw [evaluateCallReturnHandlerUnclampedZ]
  simp only [lookup, nonzero, if_false, run, ne_eq, not_true_eq_false]

/-- Source-local actual successful-exception branch equation, used for both
source and compiled target. This has no separate HOL declaration. -/
theorem evaluateCallReturnHandlerExceptionZ {width : Nat} [NeZero width] {C F : Type}
    (body handler program : HolProg width) (link l1 l2 hl1 hl2 : Nat) (dest : Sum Nat Nat)
    (source middle : StackSemStateFiniteExact width C F)
    (lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program)
    (nonzero : source.clock ≠ 0)
    (run : evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
      (some (.exception (.loc hl1 hl2)), middle)) :
    evaluate (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)), source) =
      evaluate (handler, middle) := by
  rw [evaluateCallReturnHandlerUnclampedZ]
  simp only [lookup, nonzero, if_false, run, ne_eq, not_true_eq_false]

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Original returning Call with handler SOME, retaining every source result.
Only actual source lookup/nonzero-clock guarded callee and actual successful
return-location and exception-location guarded continuations induction hypotheses are added to the
original four premises. Intermediate target runs and relations are derived. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCallReturnHandlerZ {width : Nat} [NeZero width] {C F : Type}
    (body handler : HolProg width) (link l1 l2 hl1 hl2 : Nat) (dest : Sum Nat Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (program : HolProg width),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock (setVar link (.loc l1 l2) source)) t ∧ StackProps.regBound program k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (returnIH : ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (some (.result (.loc l1 l2)), middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (body, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (middle) t ∧ StackProps.regBound body k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (handlerIH : ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
      StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
      source.clock ≠ 0 →
      evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
        (some (.exception (.loc hl1 hl2)), middle) →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (handler, middle) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (middle) t ∧ StackProps.regBound handler k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k handler, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2)), source) =
        (result, postSource) ∧ result ≠ some .error ∧
      stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2))) pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer (.call (some (body, link, l1, l2)) dest (some (handler, hl1, hl2))),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluateCallReturnHandlerUnclampedZ] at sourceRun
  cases lookup : StackSemControl.findCode dest (source.regs.eraseEq link) source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    obtain ⟨targetLookup, programBound⟩ := FindCode.findCodeLemmaErased jump bounds pointer
      source target dest program link ⟨relation, by
        simp only [StackProps.regBound] at bound
        cases dest <;> exact bound.1, lookup⟩
    have bodyBound : StackProps.regBound body pointer := by
      simp only [StackProps.regBound] at bound
      exact bound.2.1
    have linkBound : link < pointer := by
      simp only [StackProps.regBound] at bound
      exact bound.2.2.1
    have handlerBound : StackProps.regBound handler pointer := by
      simp only [StackProps.regBound] at bound
      exact bound.2.2.2
    by_cases zero : source.clock = 0
    · simp only [zero, if_true] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
      subst result
      subst postSource
      refine ⟨0, emptyEnv target, Or.inl rfl, ?_, ?_⟩
      · simpa only [comp, Nat.zero_add] using
          (evaluateCallReturnHandlerUnclampedZ (comp jump bounds pointer body)
            (comp jump bounds pointer handler) link l1 l2 hl1 hl2 dest target).trans (by
            simp only [targetLookup, clocks, zero, if_true])
      · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
    · simp only [zero, if_false] at sourceRun
      have targetNonzero : target.clock ≠ 0 := by omega
      have entry := entryRelationZ jump bounds pointer link l1 l2 source target relation linkBound
      rcases bodyRun : evaluate (program, decClock (setVar link (.loc l1 l2) source)) with
        ⟨bodyResult, middle⟩
      rw [bodyRun] at sourceRun
      cases bodyResult with
      | none =>
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some value =>
        cases value with
        | error => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | «break» n => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | «continue» n => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | result value =>
          change (if value ≠ .loc l1 l2 then (some .error, middle)
            else evaluate (body, middle)) = (result, postSource) at sourceRun
          split at sourceRun
          · exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          · rename_i equal
            have correct : value = .loc l1 l2 := by simpa only [ne_eq, not_not] using equal
            subst value
            obtain ⟨first, middleTarget, hck1, calleeRun, middleRelation⟩ :=
              calleeIH program lookup zero (some (.result (.loc l1 l2))) middle
                (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
                ⟨bodyRun, by simp, entry, programBound⟩
            obtain ⟨second, postTarget, hck2, returnRun, postRelation⟩ :=
              returnIH program middle lookup zero bodyRun result postSource middleTarget pointer bounds jump
                ⟨sourceRun, notError, middleRelation, bodyBound⟩
            have boosted := calleeAllowanceZ (comp jump bounds pointer program) target middleTarget
              link l1 l2 first second targetNonzero calleeRun
            refine ⟨first + second, postTarget, (by rw [clockOk_zero_of_not_halt hck1 (by intro w h; first | (simp at h; done) | (subst h; simp [StackSemControl.contLoop] at continues))]; simpa using hck2), ?_, ?_⟩
            · have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
              simp only [comp]
              rw [evaluateCallReturnHandlerResultZ (comp jump bounds pointer body)
                (comp jump bounds pointer handler) (comp jump bounds pointer program) link l1 l2 hl1 hl2 dest
                {target with clock := (first + second) + target.clock}
                {middleTarget with clock := second + middleTarget.clock}
                targetLookup totalNonzero boosted]
              exact returnRun
            · cases result with
              | none => exact postRelation
              | some r => cases r <;> exact postRelation
        | halt n =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            calleeIH program lookup zero (some (.halt n)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, hck, ?_, postRelation⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          simp only [comp]
          rw [evaluateCallReturnHandlerUnclampedZ]
          simp only [targetLookup, nonzero, if_false]
          rw [entryClockZ target link l1 l2 clock targetNonzero, targetRun]
        | timeOut =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            calleeIH program lookup zero (some (.timeOut)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, hck, ?_, postRelation⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          simp only [comp]
          rw [evaluateCallReturnHandlerUnclampedZ]
          simp only [targetLookup, nonzero, if_false]
          rw [entryClockZ target link l1 l2 clock targetNonzero, targetRun]
        | finalFFI event =>
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            calleeIH program lookup zero (some (.finalFFI event)) middle
              (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
              ⟨bodyRun, by simp, entry, programBound⟩
          refine ⟨clock, postTarget, hck, ?_, postRelation⟩
          have nonzero : clock + target.clock ≠ 0 := by omega
          simp only [comp]
          rw [evaluateCallReturnHandlerUnclampedZ]
          simp only [targetLookup, nonzero, if_false]
          rw [entryClockZ target link l1 l2 clock targetNonzero, targetRun]
        | exception value =>
          change (if value ≠ .loc hl1 hl2 then (some .error, middle)
            else evaluate (handler, middle)) = (result, postSource) at sourceRun
          split at sourceRun
          · exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          · rename_i equal
            have correct : value = .loc hl1 hl2 := by simpa only [ne_eq, not_not] using equal
            subst value
            obtain ⟨first, middleTarget, hck1, calleeRun, middleRelation⟩ :=
              calleeIH program lookup zero (some (.exception (.loc hl1 hl2))) middle
                (decClock (setVar link (.loc l1 l2) target)) pointer bounds jump
                ⟨bodyRun, by simp, entry, programBound⟩
            obtain ⟨second, postTarget, hck2, returnRun, postRelation⟩ :=
              handlerIH program middle lookup zero bodyRun result postSource middleTarget pointer bounds jump
                ⟨sourceRun, notError, middleRelation, handlerBound⟩
            have boosted := exceptionAllowanceZ (comp jump bounds pointer program) target middleTarget
              link l1 l2 hl1 hl2 first second targetNonzero calleeRun
            refine ⟨first + second, postTarget, (by rw [clockOk_zero_of_not_halt hck1 (by intro w h; first | (simp at h; done) | (subst h; simp [StackSemControl.contLoop] at continues))]; simpa using hck2), ?_, ?_⟩
            · have totalNonzero : (first + second) + target.clock ≠ 0 := by omega
              simp only [comp]
              rw [evaluateCallReturnHandlerExceptionZ (comp jump bounds pointer body)
                (comp jump bounds pointer handler) (comp jump bounds pointer program) link l1 l2 hl1 hl2 dest
                {target with clock := (first + second) + target.clock}
                {middleTarget with clock := second + middleTarget.clock}
                targetLookup totalNonzero boosted]
              exact returnRun
            · cases result with
              | none => exact postRelation
              | some r => cases r <;> exact postRelation
end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnHandler

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.RawCall
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.RawCall
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Seq InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.If InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Loop InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallTail InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnNone InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnHandler
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine original RawCall induction case: the original four premises
and only the actual source Seq-code lookup/nonzero-clock guarded body IH.
The target callee lookup, body bound, clock allowance and all original
post-state/result alternatives are established here. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectRawCallZ {width : Nat} [NeZero width] {C F : Type}
    (label : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (frame body : HolProg width),
      sptLookup label source.code = some (.seq frame body) → source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (body, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock source) t ∧ StackProps.regBound body k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.rawCall label, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.rawCall label : HolProg width) pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer (.rawCall label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_rawCall] at sourceRun
  cases lookup : sptLookup label source.code with
  | none =>
    simp only [lookup] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some program =>
    simp only [lookup] at sourceRun
    cases shape : StackSemControl.destSeq program with
    | none =>
      simp only [shape] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | some pair =>
      rcases pair with ⟨frame, body⟩
      have programEq : program = .seq frame body := by
        cases program <;> simp [StackSemControl.destSeq] at shape ⊢
        exact ⟨shape.1, shape.2⟩
      subst program
      simp only [StackSemControl.destSeq] at sourceRun
      obtain ⟨targetLookup, programBound⟩ := FindCode.findCodeLemma jump bounds pointer
        source target (.inl label) (.seq frame body) ⟨relation, True.intro, lookup⟩
      change sptLookup label target.code = some (comp jump bounds pointer (.seq frame body)) at targetLookup
      simp only [comp] at targetLookup
      change StackProps.regBound frame pointer ∧ StackProps.regBound body pointer at programBound
      by_cases zero : source.clock = 0
      · simp only [zero, if_true] at sourceRun
        rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
        subst result
        subst postSource
        refine ⟨0, emptyEnv target, Or.inl rfl, ?_, ?_⟩
        · simpa only [comp, Nat.zero_add] using
            (evaluate_rawCall label target).trans (by
              simp only [targetLookup, StackSemControl.destSeq, clocks, zero, if_true])
        · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
      · simp only [zero, if_false] at sourceRun
        rcases bodyRun : evaluate (body, decClock source) with ⟨bodyResult, middle⟩
        rw [bodyRun] at sourceRun
        by_cases bad : StackSemControl.badFunReturn bodyResult = true
        · simp only [bad, if_true] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        · simp [bad] at sourceRun
          rcases sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
            calleeIH frame body lookup zero bodyResult middle (decClock target) pointer bounds jump
              ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, programBound.2⟩
          refine ⟨clock, postTarget, hck, ?_, ?_⟩
          swap
          · cases bodyResult with
            | none => exact postRelation
            | some r => cases r <;> exact postRelation
          have nonzero : clock + target.clock ≠ 0 := by omega
          have clockEq : decClock {target with clock := clock + target.clock} =
              {decClock target with clock := clock + (decClock target).clock} := by
            simp only [decClock]
            congr 1
            omega
          simp only [comp]
          rw [evaluate_rawCall]
          simp only [targetLookup, StackSemControl.destSeq, nonzero, if_false]
          rw [clockEq, targetRun]
          simp [bad]
end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.RawCall

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.JumpLower
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.JumpLower
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Seq InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.If InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Loop InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallTail InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnNone InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnHandler InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.RawCall
open Flapjack Compiler.Backend.StackLang Compiler.Encoders.Asm StackSemEvaluate StackSemStateOps

/-- Canonical owning-state roundtrip; Flapjack representation infrastructure. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Genuine original JumpLower case: original four premises and only the
actual source operand/comparison/code-lookup/nonzero-clock guarded callee IH.
Every original body-simulation quantifier and result alternative is retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectJumpLowerZ {width : Nat} [NeZero width] {C F : Type}
    (first second label : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : ∀ (left right : BitVec width) (program : HolProg width),
      getVar first source = some (.word left) → getVar second source = some (.word right) →
      wordCmpHOL .lower left right = true → sptLookup label source.code = some program →
      source.clock ≠ 0 →
      ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
        (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
      evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
        stateRelHOL j off k (decClock source) t ∧ StackProps.regBound program k →
      ∃ clock postTarget, ClockOk clock r ∧
        evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
        (match r with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
         | _ => stateRelHOL j off k post postTarget))
    (hypothesis : evaluate (.jumpLower first second label, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.jumpLower first second label : HolProg width) pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer (.jumpLower first second label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change first < pointer ∧ second < pointer at bound
  have readFirst := RelationLaws.stateRelGetVar jump bounds pointer first source target ⟨relation, bound.1⟩
  have readSecond := RelationLaws.stateRelGetVar jump bounds pointer second source target ⟨relation, bound.2⟩
  change source.regs.lookup first = target.regs.lookup first at readFirst
  change source.regs.lookup second = target.regs.lookup second at readSecond
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [evaluate_jumpLower] at sourceRun
  cases hFirst : getVar first source with
  | none =>
    simp only [hFirst] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some left =>
    cases left with
    | loc name offset =>
      simp only [hFirst] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word left =>
      cases hSecond : getVar second source with
      | none =>
        simp only [hFirst, hSecond] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some right =>
        cases right with
        | loc name offset =>
          simp only [hFirst, hSecond] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word right =>
          simp only [hFirst, hSecond] at sourceRun
          have targetFirst : target.regs.lookup first = some (.word left) := readFirst.symm.trans hFirst
          have targetSecond : target.regs.lookup second = some (.word right) := readSecond.symm.trans hSecond
          by_cases lower : wordCmpHOL .lower left right = true
          · simp only [lower, if_true, StackSemControl.findCode] at sourceRun
            cases lookup : sptLookup label source.code with
            | none =>
              simp only [lookup] at sourceRun
              exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
            | some program =>
              simp only [lookup] at sourceRun
              obtain ⟨targetLookup, bodyBound⟩ := FindCode.codeLookup jump bounds pointer label source target program relation lookup
              by_cases zero : source.clock = 0
              · simp only [zero, if_true] at sourceRun
                rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
                subst result
                subst postSource
                refine ⟨0, emptyEnv target, Or.inl rfl, ?_, ?_⟩
                · simpa only [comp, Nat.zero_add] using
                    (evaluate_jumpLower first second label target).trans (by
                      simp only [getVar, targetFirst, targetSecond, lower, if_true,
                        StackSemControl.findCode, targetLookup, clocks, zero])
                · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
              · simp only [zero, if_false] at sourceRun
                rcases bodyRun : evaluate (program, decClock source) with ⟨bodyResult, middle⟩
                rw [bodyRun] at sourceRun
                by_cases bad : StackSemControl.badFunReturn bodyResult = true
                · simp only [bad, if_true] at sourceRun
                  exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
                · simp [bad] at sourceRun
                  rcases sourceRun with ⟨resultEq, postEq⟩
                  subst result
                  subst postSource
                  obtain ⟨clock, postTarget, hck, targetRun, postRelation⟩ :=
                    calleeIH left right program hFirst hSecond lower lookup zero bodyResult middle
                      (decClock target) pointer bounds jump
                      ⟨bodyRun, notError, RelationLaws.stateRelDecClock jump bounds pointer source target relation, bodyBound⟩
                  refine ⟨clock, postTarget, hck, ?_, ?_⟩
                  swap
                  · cases bodyResult with
                    | none => exact postRelation
                    | some r => cases r <;> exact postRelation
                  have nonzero : clock + target.clock ≠ 0 := by omega
                  have clockEq : decClock {target with clock := clock + target.clock} =
                      {decClock target with clock := clock + (decClock target).clock} := by
                    simp only [decClock]
                    congr 1
                    omega
                  simp only [comp]
                  rw [evaluate_jumpLower]
                  simp only [getVar, targetFirst, targetSecond, StackSemControl.findCode,
                    targetLookup, lower, if_true, nonzero, if_false]
                  rw [clockEq, targetRun]
                  simp [bad]
          · simp [lower] at sourceRun
            rcases sourceRun with ⟨resultEq, postEq⟩
            subst result
            subst postSource
            refine ⟨0, target, Or.inl rfl, ?_, relation⟩
            simpa only [comp, Nat.zero_add] using
              (evaluate_jumpLower first second label target).trans (by
                simp [getVar, targetFirst, targetSecond, lower])
end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.JumpLower

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallAssembly
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.CompCorrect Flapjack.Compiler.Backend.StackRemove.CompCorrect.CallAssembly
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Seq InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.If InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Loop InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallTail InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnNone InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnHandler InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.RawCall InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.JumpLower
open Flapjack StackSemEvaluate StackSemStateOps Compiler.Backend.StackLang

/-- Actual imported canonical state codec, without a duplicate carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExactZ
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full Call constructor assembly across every return and handler AST option.
The three match-indexed induction hypotheses are precisely the actual source
branches already checked in the component cases: successful lookup/nonzero
callee entry, successful matching return continuation, and successful matching
exception handler. They retain the fixed original source state and all original
simulation quantifiers. No target execution or post-state fact is assumed.
The native evaluator closure inherits reals_as_rational_cuts (SOUNDNESS item 8),
including arbitrary callee programs; no evaluator-carrier independence is claimed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectCallZ {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (calleeIH : match ret with
      | none =>
          ∀ (program : HolProg width),
            StackSemControl.findCode dest source.regs source.code = some program →
            handler = none → source.clock ≠ 0 →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (program, decClock source) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (decClock source) t ∧ StackProps.regBound program k →
            ∃ clock postTarget, ClockOk clock r ∧
              evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget)
      | some (_body, link, l1, l2) =>
          ∀ (program : HolProg width),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (program, decClock (setVar link (.loc l1 l2) source)) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (decClock (setVar link (.loc l1 l2) source)) t ∧ StackProps.regBound program k →
            ∃ clock postTarget, ClockOk clock r ∧
              evaluate (comp j off k program, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget))
    (returnIH : match ret with
      | none => True
      | some (body, link, l1, l2) =>
          ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
            evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
              (some (.result (.loc l1 l2)), middle) →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (body, middle) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (middle) t ∧ StackProps.regBound body k →
            ∃ clock postTarget, ClockOk clock r ∧
              evaluate (comp j off k body, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget))
    (handlerIH : match ret, handler with
      | some (_body, link, l1, l2), some (handler, hl1, hl2) =>
          ∀ (program : HolProg width) (middle : StackSemStateFiniteExact width C F),
            StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some program →
            source.clock ≠ 0 →
            evaluate (program, decClock (setVar link (.loc l1 l2) source)) =
              (some (.exception (.loc hl1 hl2)), middle) →
            ∀ (r : Option (StackSemResult width)) (post t : StackSemStateFiniteExact width C F)
              (k : Nat) (off : BitVec width × BitVec width) (j : Bool),
            evaluate (handler, middle) = (r, post) ∧ r ≠ some .error ∧
              stateRelHOL j off k (middle) t ∧ StackProps.regBound handler k →
            ∃ clock postTarget, ClockOk clock r ∧
              evaluate (comp j off k handler, {t with clock := clock + t.clock}) = (r, postTarget) ∧
              (match r with
               | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = post.ffi
               | _ => stateRelHOL j off k post postTarget)
      | _, _ => True)
    (hypothesis : evaluate (.call ret dest handler, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.call ret dest handler : HolProg width) pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer (.call ret dest handler),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  cases ret with
  | none =>
    obtain ⟨clock, postTarget, hck, run, relation⟩ :=
      InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallTail.compCorrectCallTailZ dest handler source result postSource target
        pointer bounds jump calleeIH hypothesis
    refine ⟨clock, postTarget, hck, run, ?_⟩
    cases result with
    | none => exact relation
    | some value => cases value <;> exact relation
  | some returning =>
    rcases returning with ⟨body, link, l1, l2⟩
    cases handler with
    | none =>
      obtain ⟨clock, postTarget, hck, run, relation⟩ :=
        InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnNone.compCorrectCallReturnNoneZ body link l1 l2 dest source result
          postSource target pointer bounds jump calleeIH returnIH hypothesis
      refine ⟨clock, postTarget, hck, run, ?_⟩
      cases result with
      | none => exact relation
      | some value => cases value <;> exact relation
    | some exceptional =>
      rcases exceptional with ⟨handlerBody, hl1, hl2⟩
      obtain ⟨clock, postTarget, hck, run, relation⟩ :=
        InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallReturnHandler.compCorrectCallReturnHandlerZ body handlerBody link l1 l2 hl1 hl2
          dest source result postSource target pointer bounds jump calleeIH returnIH handlerIH hypothesis
      refine ⟨clock, postTarget, hck, run, ?_⟩
      cases result with
      | none => exact relation
      | some value => cases value <;> exact relation
end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.CallAssembly

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Assembly
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.CompCorrect
open Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps StackSemControl StackSemMeasure
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)

/-- Normalize a recursive `ClockOk` case result. -/
local macro "normZ" r:ident "using" proof:term : tactic =>
  `(tactic| (
    rcases ($proof:term) with ⟨clock, post, hc, run, relation⟩
    refine ⟨clock, post, hc, run, ?_⟩
    cases $r:ident with
    | none => exact relation
    | some returned => cases returned <;> exact relation))

/-- Lift a zero-clock base case (`∃ postTarget, evaluate (comp …, target) = …`). -/
local macro "baseZ" r:ident "using" proof:term : tactic =>
  `(tactic| (
    rcases ($proof:term) with ⟨post, run, relation⟩
    refine ⟨0, post, Or.inl rfl, by rw [Nat.zero_add]; exact run, ?_⟩
    cases $r:ident with
    | none => exact relation
    | some returned => cases returned <;> exact relation))

theorem codeNoSt_decClock {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} (h : CodeNoSt s) : CodeNoSt (decClock s) := h

theorem codeNoSt_setVar {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} (v : Nat) (x : WordLocW width) (h : CodeNoSt s) :
    CodeNoSt (setVar v x s) := h

/-- Any program reached by `findCode` comes from the code table. -/
theorem noSt_of_findCode {width : Nat} [NeZero width] {C F : Type} {κ : Type}
    {s : StackSemStateFiniteExact width C F} (h : CodeNoSt s)
    (dest : Sum Nat κ) (regs : HolFiniteMapExact κ (WordLocW width)) (p : HolProg width)
    (hf : StackSemControl.findCode dest regs s.code = some p) : StackNoSt p = true := by
  cases dest with
  | inl l => exact h.1 l p hf
  | inr r =>
      simp only [StackSemControl.findCode] at hf
      split at hf
      · exact h.1 _ p hf
      · exact absurd hf (by simp)

theorem noSt_call_ret {width : Nat} [NeZero width] {body : HolProg width} {link l1 l2 : Nat}
    {dest : Sum Nat Nat} {handler : Option (HolProg width × Nat × Nat)}
    (h : StackNoSt (.call (some (body, link, l1, l2)) dest handler) = true) :
    StackNoSt body = true := by
  rw [StackNoSt.eq_def] at h
  simp only [Bool.and_eq_true] at h; exact h.1

theorem noSt_call_handler {width : Nat} [NeZero width] {ret : Option (HolProg width × Nat × Nat × Nat)}
    {hb : HolProg width} {hl1 hl2 : Nat} {dest : Sum Nat Nat}
    (h : StackNoSt (.call ret dest (some (hb, hl1, hl2))) = true) :
    StackNoSt hb = true := by
  rw [StackNoSt.eq_def] at h
  simp only [Bool.and_eq_true] at h
  cases ret with
  | none => exact h.2
  | some x => obtain ⟨a, b, c, d⟩ := x; exact h.2

private theorem correctnessMeasureZ {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      StackNoSt program = true → CodeNoSt source →
      ∀ (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
      ∀ (_hypothesis : evaluate (program, source) = (result, postSource) ∧ result ≠ some .error ∧
        stateRelHOL jump bounds pointer source target ∧ StackProps.regBound program pointer),
      ∃ clock postTarget, ClockOk clock result ∧
        evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
          (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  intro measure
  induction measure using Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro program source hm hnost hcode result postSource target pointer bounds jump hypothesis
  subst hm
  cases program
  case storeConsts a b c => simp [StackNoSt] at hnost
  case stackAlloc count =>
    obtain ⟨clock, post, hc1, hc0, run, rel⟩ :=
      InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace.compCorrectStackAllocZ
        source result postSource target count pointer bounds jump hypothesis
    have hok : ClockOk clock result := by
      rcases hypothesis with ⟨sr, ne, _, _⟩
      cases result with
      | none => exact Or.inl (hc0 rfl)
      | some v =>
        refine Or.inr ⟨hc1, ?_⟩
        rw [StackSemEvaluate.evaluate_stackAlloc] at sr
        split at sr
        · exact absurd (Prod.mk.inj sr).1.symm ne
        · split at sr
          · exact ⟨_, (Prod.mk.inj sr).1.symm⟩
          · exact absurd (Prod.mk.inj sr).1 (by simp)
    refine ⟨clock, post, hok, run, ?_⟩
    cases result with
    | none => exact rel
    | some v => cases v <;> exact rel
  all_goals first
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.FFI.compCorrectFFIZ _ _ _ _ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StoreTransfers.compCorrectGetZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StoreTransfers.compCorrectSetZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Bitmap.compCorrectBitmapLoadZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Install.compCorrectInstallZ _ _ _ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.DataBufferWrite.compCorrectDataBufferWriteZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Atoms.compCorrectSkipZ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Atoms.compCorrectHaltZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Atoms.compCorrectAllocZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemoryAny.compCorrectStackLoadAnyZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemoryAny.compCorrectStackStoreAnyZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Locations.compCorrectLocValueZ _ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectTickZ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectReturnZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectRaiseZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectBreakZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Control.compCorrectContinueZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.ShMemOp.compCorrectShMemOpZ _ _ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSpace.compCorrectStackFreeZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.HeapOperation.compCorrectOpCurrHeapZ _ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemory.compCorrectStackLoadZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackMemory.compCorrectStackStoreZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.Instructions.compCorrectInstZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.CodeBufferWrite.compCorrectCodeBufferWriteZ _ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSize.compCorrectStackGetSizeZ _ _ _ _ _ _ _ _ hypothesis)
    | solve | baseZ result using (InitECandidate.Solver.StackRemoveAllocFreeAndBaseCasesZeroClock.StackSize.compCorrectStackSetSizeZ _ _ _ _ _ _ _ _ hypothesis)
    | skip
  case seq first second =>
    simp only [StackNoSt, Bool.and_eq_true] at hnost
    refine (by normZ result using (Seq.compCorrectSeqZ first second source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro r post t k off j h
      normZ r using (ih _ (seq_first_measure_lt first second source) first source rfl hnost.1 hcode r post t k off j h)
    · intro middle firstRun
      have hcm := codeNoSt_evaluate first source _ middle firstRun hcode
      have smaller := seq_second_measure_lt first second source ((none : Option (StackSemResult width)), middle)
      have unclamped := StackSemEvaluateClock.fixClockEvaluate first source
      rw [firstRun] at unclamped
      rw [unclamped] at smaller
      intro r post t k off j h
      normZ r using (ih _ smaller second middle rfl hnost.2 hcm r post t k off j h)
  case ite comparison register operand first second =>
    simp only [StackNoSt, Bool.and_eq_true] at hnost
    refine (by normZ result using (If.compCorrectIfZ comparison register operand first second source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro left right _ _ _ r post t k off j h
      normZ r using (ih _ (if_first_measure_lt comparison register operand first second source) first source rfl hnost.1 hcode r post t k off j h)
    · intro left right _ _ _ r post t k off j h
      normZ r using (ih _ (if_second_measure_lt comparison register operand first second source) second source rfl hnost.2 hcode r post t k off j h)
  case loop body =>
    have hb : StackNoSt body = true := by simpa only [StackNoSt] using hnost
    refine (by normZ result using (Loop.compCorrectLoopZ body source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro r post t k off j h
      normZ r using (ih _ (loop_body_measure_lt body source) body source rfl hb hcode r post t k off j h)
    · intro bodyResult middle bodyRun _ nonzero
      have hcm := codeNoSt_decClock (codeNoSt_evaluate body source _ middle bodyRun hcode)
      have unclamped := StackSemEvaluateClock.fixClockEvaluate body source
      rw [bodyRun] at unclamped
      have smaller := loop_reentry_measure_lt body source (bodyResult, middle)
        (by simpa only [unclamped] using nonzero)
      rw [unclamped] at smaller
      intro r post t k off j h
      normZ r using (ih _ smaller (.loop body) (decClock middle) rfl hnost hcm r post t k off j h)
  case jumpLower first second label =>
    refine (by normZ result using (JumpLower.compCorrectJumpLowerZ first second label source result postSource target pointer bounds jump ?_ hypothesis))
    · intro left right program _ _ _ hlk nonzero r post t k off j h
      normZ r using (ih _ (callee_measure_lt program (.jumpLower first second label) source nonzero) program (decClock source) rfl (hcode.1 _ _ hlk) (codeNoSt_decClock hcode) r post t k off j h)
  case rawCall label =>
    refine (by normZ result using (RawCall.compCorrectRawCallZ label source result postSource target pointer bounds jump ?_ hypothesis))
    · intro frame body hlk nonzero r post t k off j h
      have hfb := hcode.1 _ _ hlk
      simp only [StackNoSt, Bool.and_eq_true] at hfb
      normZ r using (ih _ (callee_measure_lt body (.rawCall label) source nonzero) body (decClock source) rfl hfb.2 (codeNoSt_decClock hcode) r post t k off j h)
  case call ret dest handler =>
    have hret := fun body link l1 l2 (e : ret = some (body, link, l1, l2)) =>
      noSt_call_ret (e ▸ hnost)
    have hhd := fun hb hl1 hl2 (e : handler = some (hb, hl1, hl2)) =>
      noSt_call_handler (e ▸ hnost)
    refine (by normZ result using (CallAssembly.compCorrectCallZ ret dest handler source result postSource target pointer bounds jump ?_ ?_ ?_ hypothesis))
    · cases ret with
      | none =>
        intro program hlk _ nonzero r post t k off j h
        normZ r using (ih _ (callee_measure_lt program (.call none dest handler) source nonzero) program (decClock source) rfl (noSt_of_findCode hcode dest _ program hlk) (codeNoSt_decClock hcode) r post t k off j h)
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        intro program hlk nonzero
        have smaller := callee_measure_lt program (.call (some (body, link, l1, l2)) dest handler)
          (setVar link (.loc l1 l2) source) nonzero
        intro r post t k off j h
        normZ r using (ih _ smaller program (decClock (setVar link (.loc l1 l2) source)) rfl (noSt_of_findCode hcode dest _ program hlk) (codeNoSt_decClock (codeNoSt_setVar _ _ hcode)) r post t k off j h)
    · cases ret with
      | none => trivial
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        intro program middle _ nonzero calleeRun
        have hcm := codeNoSt_evaluate program _ _ middle calleeRun (codeNoSt_decClock (codeNoSt_setVar link (.loc l1 l2) hcode))
        have unclamped := StackSemEvaluateClock.fixClockEvaluate program (decClock (setVar link (.loc l1 l2) source))
        rw [calleeRun] at unclamped
        have smaller := call_continuation_measure_lt body (.call (some (body, link, l1, l2)) dest handler)
          source link l1 l2 ((some (.result (.loc l1 l2)) : Option (StackSemResult width)), middle) nonzero
        rw [unclamped] at smaller
        intro r post t k off j h
        normZ r using (ih _ smaller body middle rfl (hret body link l1 l2 rfl) hcm r post t k off j h)
    · cases ret with
      | none => trivial
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        cases handler with
        | none => trivial
        | some handlerEntry =>
          rcases handlerEntry with ⟨handlerBody, hl1, hl2⟩
          intro program middle _ nonzero calleeRun
          have hcm := codeNoSt_evaluate program _ _ middle calleeRun (codeNoSt_decClock (codeNoSt_setVar link (.loc l1 l2) hcode))
          have unclamped := StackSemEvaluateClock.fixClockEvaluate program (decClock (setVar link (.loc l1 l2) source))
          rw [calleeRun] at unclamped
          have smaller := call_continuation_measure_lt handlerBody
            (.call (some (body, link, l1, l2)) dest (some (handlerBody, hl1, hl2)))
            source link l1 l2 ((some (.exception (.loc hl1 hl2)) : Option (StackSemResult width)), middle) nonzero
          rw [unclamped] at smaller
          intro r post t k off j h
          normZ r using (ih _ smaller handlerBody middle rfl (hhd handlerBody hl1 hl2 rfl) hcm r post t k off j h)

/-- **StackRemove `comp_correct` with exact clock accounting.** For a `storeConsts`-free
program run from a state whose code table and oracle are `storeConsts`-free, the compiled
program needs **zero** extra clock, except that a final `halt` (the `stackAlloc`
stack-overflow `halt 2`) may cost at most one tick. -/
theorem compCorrectZ {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hnost : StackNoSt program = true) (hcode : CodeNoSt source)
    (hypothesis : evaluate (program, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound program pointer) :
    ∃ clock postTarget, ClockOk clock result ∧
      evaluate (comp jump bounds pointer program,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) :=
  correctnessMeasureZ _ program source rfl hnost hcode result postSource target pointer bounds jump hypothesis

/-- Isometry form: a non-`halt` result is simulated at exactly the source clock. -/
theorem compCorrectZ_noHalt {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hnost : StackNoSt program = true) (hcode : CodeNoSt source)
    (noHalt : ∀ w, result ≠ some (.halt w))
    (hypothesis : evaluate (program, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound program pointer) :
    ∃ postTarget,
      evaluate (comp jump bounds pointer program, target) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  obtain ⟨clock, post, hc, run, rel⟩ :=
    compCorrectZ program source result postSource target pointer bounds jump hnost hcode hypothesis
  have h0 := clockOk_zero_of_not_halt hc noHalt
  subst h0
  refine ⟨post, by rw [Nat.zero_add] at run; exact run, ?_⟩
  cases result with
  | none => exact rel
  | some v => cases v <;> exact rel

end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Assembly

/-! ## Pancake link -/

namespace InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake
open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt panToWordToWord_NoSt)
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock

/-- Every non-stub body compiled from Pancake reaches `StackRemove.comp` `storeConsts`-free
(Pancake → LoopToWord → WordToWord → WordToStack → StackRawCall → StackAlloc),
unconditionally. Same `WordNoStubCall` discharge as
`panToStackNames_NoSt_and_NoStubCall_unconditional`. -/
theorem panToStackAlloc_bodies_StackNoSt {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 = true := by
  intro y hy
  rcases c_compileNative ac perf _
      (fun x hx => ⟨panToWordToWord_NoSt arch prog wc ac x hx,
        InitECandidate.Solver.WordToWordNoStubCall.panToWordToWord_NoStubCall arch prog wc ac x hx⟩) y hy with e | hc
  · exact Or.inl e
  · right
    unfold StackAlloc.progComp
    exact (of_clean (c_stackAllocComp _ _ _ (c_rawCallCompTop info _ hc))).1

/-- **End-to-end.** For every function body compiled from any Pancake program, except the
`storeConsts` stub (label `6`), the StackRemove simulation of that body from a
`CodeNoSt` state adds zero extra clock, except at most one tick on a final `halt`. -/
theorem panToStackRemove_body_zeroExtraClock {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
        CodeNoSt source →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL jump bounds pointer source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 pointer →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp jump bounds pointer
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget) := by
  intro y hy
  rcases panToStackAlloc_bodies_StackNoSt arch prog wc ac perf info y hy with e | hn
  · exact Or.inl e
  · right
    intro source result postSource target pointer bounds jump hcode hyp
    obtain ⟨clock, post, hc, run, _⟩ :=
      Assembly.compCorrectZ _ source result postSource target pointer bounds jump hn hcode hyp
    exact ⟨clock, post, hc, run⟩

/-! ## Witnesses (non-vacuity / tightness) -/

/-- `StackNoSt` really rejects `storeConsts`. -/
theorem stackNoSt_rejects_storeConsts {width : Nat} [NeZero width] (a b : Nat) (c : Option Nat) :
    StackNoSt (.storeConsts a b c : HolProg width) = false := rfl

/-- `StackNoSt` accepts a `storeConsts`-free program. -/
theorem stackNoSt_accepts_skip {width : Nat} [NeZero width] :
    StackNoSt (.seq .skip .skip : HolProg width) = true := rfl

/-- Tight: the one-tick `halt` allowance is attained by the bound. -/
theorem clockOk_halt_one {width : Nat} [NeZero width] (w : WordLocW width) :
    ClockOk 1 (some (.halt w)) := Or.inr ⟨le_refl 1, w, rfl⟩

/-- Tight: no tick is allowed on a non-`halt` result. -/
theorem clockOk_rejects_one_none {width : Nat} [NeZero width] :
    ¬ ClockOk (width := width) 1 none := by
  rintro (h | ⟨_, w, hw⟩)
  · exact absurd h (by decide)
  · exact absurd hw (by simp)

/-- Tight: two ticks are never allowed, even on `halt`. -/
theorem clockOk_rejects_two_halt {width : Nat} [NeZero width] (w : WordLocW width) :
    ¬ ClockOk 2 (some (.halt w)) := by
  rintro (h | ⟨h, _⟩)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- `CodeNoSt` is not vacuous: it fails as soon as a code entry contains `storeConsts`. -/
theorem codeNoSt_rejects {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (k a b : Nat) (c : Option Nat)
    (hk : sptLookup k s.code = some (.storeConsts a b c)) : ¬ CodeNoSt s := by
  intro h
  have := h.1 k _ hk
  simp [StackNoSt] at this

end InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.Pancake
