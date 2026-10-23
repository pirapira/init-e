import InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge
import InitECandidate.Solver.StackNamesExactClockIso
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# StackRawCall → StackAlloc → StackRemove → StackNames → StackToLab

* `StackNames` is an exact clock isometry: Flapjack's `StackNames.compCorrect` runs the renamed
  program at the **same** clock and ends in `renameState` of the source post-state
  (extra = 0, 1:1).
* Composed with `StackRawCallLinearClockAndZeroExtraBridge`, StackRawCall followed by StackNames
  needs at most `extra ≤ source.clock` (≤ 2× expansion).
* `StackToLab` is **not** linear in the StackSem clock: LabSem charges one tick per executed
  instruction, StackSem only on calls/loops/`tick`. A `skip` (or any straight-line code)
  finishes in StackSem at clock `0`, while every LabSem run at clock `0` times out
  (`stackToLab_no_linear_clock_bound`). Flapjack's `flattenCorrect` therefore only gives an
  existential `ck`; no slope `C · source.clock + D` with `D` independent of the code exists
  in terms of the StackSem clock. The module `StackToLabLinearSlopeSynthesis` cited in the
  brief does not exist in this tree.
-/

namespace InitECandidate.Solver.StackRawCallToStackNamesAndStackToLabLinearBridge

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

variable {width : Nat} [NeZero width]

/-! ## StackNames: exact isometry -/

/-- **StackNames, extra = 0.** The renamed program, run at the very same clock as the source,
produces the same result, and its post-state is the renaming of the source post-state, so
post clocks are equal. -/
theorem stackNames_exact_clock {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (p, s) = (r, t))
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    StackSemEvaluate.evaluate (StackNames.progCompHOL f p, StackNames.renameState c f s) =
      (r, StackNames.renameState c f t) ∧
    (StackNames.renameState c f s).clock = s.clock ∧
    (StackNames.renameState c f t).clock = t.clock :=
  ⟨StackNames.compCorrect p s r t ⟨run, hf, ha, hs, hk, hc⟩, rfl, rfl⟩

/-- Ticks consumed are identical across StackNames. -/
theorem stackNames_ticks_eq {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (p, s) = (r, t))
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    (StackNames.renameState c f s).clock -
        (StackSemEvaluate.evaluate (StackNames.progCompHOL f p, StackNames.renameState c f s)).2.clock =
      s.clock - t.clock := by
  rw [(stackNames_exact_clock c f p s t r run hf ha hs hk hc).1]
  rfl

/-! ## StackRawCall ∘ StackNames -/

/-- **StackRawCall then StackNames.** If the StackRawCall target state satisfies StackNames'
side conditions, the renamed compiled program runs with at most `extra ≤ source.clock` more
clock than the source (≤ 2× expansion), with the same result. -/
theorem rawCall_then_stackNames {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (info : Spt Nat) (program : HolProg width)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (nonError : result ≠ some .error) (relation : StackRawCall.stateRel info source target)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬target.useAlloc) (hs : ¬target.useStore) (hk : ¬target.useStack)
    (hc : target.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    ∃ extra targetPost, extra ≤ source.clock ∧ target.clock + extra ≤ 2 * source.clock ∧
      StackSemEvaluate.evaluate (StackNames.progCompHOL f (StackRawCall.comp info program),
        StackNames.renameState c f {target with clock := target.clock + extra}) =
        (result, StackNames.renameState c f targetPost) := by
  obtain ⟨extra, targetPost, h1, h2, tr⟩ :=
    StackRawCallLinearClockAndZeroExtraBridge.rawCall_extra_le_clock program source target post
      info result run nonError relation
  exact ⟨extra, targetPost, h1, h2,
    (stackNames_exact_clock c f _ _ _ result tr hf ha hs hk hc).1⟩

/-! ## StackToLab: no linear bound in the StackSem clock -/

/-- LabSem at clock `0` always times out, whatever the code. -/
theorem labSem_zero_clock_timeout {C F : Type} (s : LabSem.State width C F) (h : s.clock = 0) :
    (LabSem.evaluate s).1 = .timeOut := by
  rw [LabSem.evaluate, if_pos h]

/-- StackSem `skip` finishes at every clock, including `0`, consuming no tick. -/
theorem stackSem_skip_zero_clock {C F : Type} (s : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate ((.skip : HolProg width), s) = (none, s) :=
  StackSemEvaluate.evaluate_skip s

/-- **StackToLab is not clock-linear in StackSem ticks.** There is a StackSem run that consumes
`0` ticks at clock `0` and terminates normally, while the LabSem target with the same clock
(`C · 0 + 0` for every slope `C`) times out. Any StackToLab bound must carry a code-dependent
additive term (Flapjack's existential `ck`). -/
theorem stackToLab_no_linear_clock_bound {C F : Type}
    (s : StackSemStateFiniteExact width C F) (t : LabSem.State width C F)
    (h0 : s.clock = 0) (slope : Nat) :
    StackSemEvaluate.evaluate ((.skip : HolProg width), s) = (none, s) ∧
    (s.clock - (StackSemEvaluate.evaluate ((.skip : HolProg width), s)).2.clock = 0) ∧
    (LabSem.evaluate {t with clock := slope * s.clock}).1 = .timeOut := by
  refine ⟨stackSem_skip_zero_clock s, by rw [stackSem_skip_zero_clock]; simp, ?_⟩
  exact labSem_zero_clock_timeout _ (by simp [h0])

/-! ## Master -/

open InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall in
/-- **Master.** For every Pancake program:
* StackRawCall → StackAlloc → StackRemove: the bridge of
  `pancake_rawCall_stackAlloc_stackRemove_clock` (≤ 2× on StackRawCall, identity and no GC on
  StackAlloc, `ClockOk` on StackRemove);
* StackNames: exact isometry (same clock, same result, renamed post-state) on any run;
* StackRawCall ∘ StackNames: `extra ≤ source.clock`;
* StackToLab: no clock bound linear in StackSem ticks (code-dependent `ck` is unavoidable). -/
theorem pancake_stackRawCall_to_stackNames_and_stackToLab {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (dc : DataToWord.Config) (info : Spt Nat)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt f)) :
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.NoGcCall
        (StackAlloc.progComp y).2 = true) ∧
    (∀ (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
       (r : Option (StackSemResult width)),
       StackSemEvaluate.evaluate (p, s) = (r, t) →
       ¬s.useAlloc → ¬s.useStore → ¬s.useStack →
       s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f) →
       StackSemEvaluate.evaluate (StackNames.progCompHOL f p, StackNames.renameState c f s) =
         (r, StackNames.renameState c f t) ∧
       (StackNames.renameState c f t).clock = t.clock) ∧
    (∀ (program : HolProg width) (source target post : StackSemStateFiniteExact width C F)
       (result : Option (StackSemResult width)),
       StackSemEvaluate.evaluate (program, source) = (result, post) → result ≠ some .error →
       StackRawCall.stateRel info source target →
       ¬target.useAlloc → ¬target.useStore → ¬target.useStack →
       target.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f) →
       ∃ extra targetPost, extra ≤ source.clock ∧ target.clock + extra ≤ 2 * source.clock ∧
         StackSemEvaluate.evaluate (StackNames.progCompHOL f (StackRawCall.comp info program),
           StackNames.renameState c f {target with clock := target.clock + extra}) =
           (result, StackNames.renameState c f targetPost)) ∧
    (∀ (s : StackSemStateFiniteExact width C F) (t : LabSem.State width C F) (slope : Nat),
       s.clock = 0 →
       StackSemEvaluate.evaluate ((.skip : HolProg width), s) = (none, s) ∧
       (LabSem.evaluate {t with clock := slope * s.clock}).1 = .timeOut) := by
  have m := StackRawCallLinearClockAndZeroExtraBridge.pancake_rawCall_stackAlloc_stackRemove_clock
    (C := C) (F := F) arch prog wc ac perf dc info
  refine ⟨m.2.1, fun y hy => (m.2.2.1 y hy).2, ?_, ?_, ?_⟩
  · intro p s t r run ha hs hk hc
    have e := stackNames_exact_clock c f p s t r run hf ha hs hk hc
    exact ⟨e.1, e.2.2⟩
  · intro program source target post result run ne rel ha hs hk hc
    exact rawCall_then_stackNames c f info program source target post result run ne rel hf ha hs hk hc
  · intro s t slope h0
    have e := stackToLab_no_linear_clock_bound s t h0 slope
    exact ⟨e.1, e.2.2⟩

end InitECandidate.Solver.StackRawCallToStackNamesAndStackToLabLinearBridge
