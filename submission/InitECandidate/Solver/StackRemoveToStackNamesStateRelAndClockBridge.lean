import InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
import InitECandidate.Solver.StackRawCallToStackNamesAndStackToLabLinearBridge

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# StackRemove → StackNames: side conditions from `stateRelHOL` and clock composition

* `StackRemove.stateRelHOL` contains `target.useStack = false`, `target.useStore = false` and
  `target.useAlloc = false` as literal conjuncts, so StackNames' three flag conditions follow
  from the StackRemove relation alone (no `¬source.useAlloc` needed: the relation fixes
  `target.useAlloc = false` directly).
* The `compile` field does **not** follow: `stateRelHOL` constrains `source.compile` in terms
  of `target.compile` (`source.compile cfg p = target.compile cfg (p.map progComp)`), and says
  nothing about how `target.compile` factors through `StackNames.compileHOL f`. It is the
  StackNames installation interface and stays a hypothesis (`hc`).
* Composition: StackRemove (`compCorrectZ`, extra `+0`, `+1` only on a final `halt`) then
  StackNames (exact isometry): the renamed StackRemove output runs at
  `clock + target.clock` with `ClockOk clock result`, same result.
-/

namespace InitECandidate.Solver.StackRemoveToStackNamesStateRelAndClockBridge

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)

variable {width : Nat} [NeZero width]

/-- **1. Flags.** `stateRelHOL` forces the three StackNames flag conditions on the target, and
pins the source flags (`useStack`, `useStore` true; `useAlloc` false). -/
theorem stateRelHOL_target_flags {C F : Type} {jump : Bool}
    {bounds : BitVec width × BitVec width} {pointer : Nat}
    {source target : StackSemStateFiniteExact width C F}
    (h : stateRelHOL jump bounds pointer source target) :
    ¬target.useAlloc ∧ ¬target.useStore ∧ ¬target.useStack ∧
    source.useStack = true ∧ source.useStore = true ∧ source.useAlloc = false := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  simp [h1, h2, h3, h4, h5, h6]

/-- The flags survive the clock update used by the StackRemove simulation. -/
theorem stateRelHOL_target_flags_withClock {C F : Type} {jump : Bool}
    {bounds : BitVec width × BitVec width} {pointer : Nat}
    {source target : StackSemStateFiniteExact width C F}
    (h : stateRelHOL jump bounds pointer source target) (k : Nat) :
    ¬({target with clock := k}).useAlloc ∧ ¬({target with clock := k}).useStore ∧
    ¬({target with clock := k}).useStack ∧ ({target with clock := k}).clock = k := by
  obtain ⟨a, b, c, -⟩ := stateRelHOL_target_flags h
  exact ⟨a, b, c, rfl⟩

/-- **What the relation says about `compile`:** the source compiler factors through the target
compiler after `progComp`. Clock is equal as well. -/
theorem stateRelHOL_compile_and_clock {C F : Type} {jump : Bool}
    {bounds : BitVec width × BitVec width} {pointer : Nat}
    {source target : StackSemStateFiniteExact width C F}
    (h : stateRelHOL jump bounds pointer source target) :
    source.compile = (fun config program =>
      target.compile config (program.map (progComp jump bounds pointer))) ∧
    target.clock = source.clock := by
  obtain ⟨-, -, -, -, -, -, -, -, hc, -, -, -, -, -, hcomp, -⟩ := h
  exact ⟨hcomp, hc⟩

/-- **2. StackRemove → StackNames.** For a `StackNoSt` body under `CodeNoSt`, the StackNames
renaming of the StackRemove output runs at `clock + target.clock` with `ClockOk clock result`
(`clock = 0`, or `≤ 1` on `halt`), produces the source result, and ends in the renaming of the
StackRemove post-state, whose clock equals it. Only the StackNames installation of
`target.compile` (`hc`) and the bijectivity of the name map remain as hypotheses; the three
flags are derived from `stateRelHOL`. -/
theorem stackRemove_then_stackNames_clock {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hnost : StackNoSt program = true) (hcode : CodeNoSt source)
    (run : StackSemEvaluate.evaluate (program, source) = (result, postSource))
    (nonError : result ≠ some .error)
    (relation : stateRelHOL jump bounds pointer source target)
    (bound : StackProps.regBound program pointer)
    (hc : target.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    ∃ clock postTarget, ClockOk clock result ∧
      clock + target.clock ≤ source.clock + 1 ∧
      StackSemEvaluate.evaluate
        (StackNames.progCompHOL f (comp jump bounds pointer program),
          StackNames.renameState c f {target with clock := clock + target.clock}) =
        (result, StackNames.renameState c f postTarget) ∧
      (StackNames.renameState c f postTarget).clock = postTarget.clock := by
  obtain ⟨clock, postTarget, hok, tr, -⟩ :=
    Assembly.compCorrectZ program source result postSource target pointer bounds jump hnost hcode
      ⟨run, nonError, relation, bound⟩
  obtain ⟨ha, hs, hk, -⟩ := stateRelHOL_target_flags_withClock relation (clock + target.clock)
  have e := StackRawCallToStackNamesAndStackToLabLinearBridge.stackNames_exact_clock c f _ _ _ _
    tr hf ha hs hk hc
  have hclk := (stateRelHOL_compile_and_clock relation).2
  refine ⟨clock, postTarget, hok, ?_, e.1, e.2.2⟩
  rcases hok with h0 | ⟨h1, -⟩ <;> omega

/-- Non-`halt` case of the composition: exactly zero extra clock across StackRemove ∘ StackNames. -/
theorem stackRemove_then_stackNames_noHalt {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hnost : StackNoSt program = true) (hcode : CodeNoSt source)
    (run : StackSemEvaluate.evaluate (program, source) = (result, postSource))
    (nonError : result ≠ some .error)
    (relation : stateRelHOL jump bounds pointer source target)
    (bound : StackProps.regBound program pointer)
    (hc : target.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f))
    (noHalt : ∀ w, result ≠ some (.halt w)) :
    ∃ postTarget, StackSemEvaluate.evaluate
        (StackNames.progCompHOL f (comp jump bounds pointer program),
          StackNames.renameState c f {target with clock := source.clock}) =
        (result, StackNames.renameState c f postTarget) := by
  obtain ⟨clock, postTarget, hok, -, tr, -⟩ :=
    stackRemove_then_stackNames_clock c f hf program source result postSource target pointer
      bounds jump hnost hcode run nonError relation bound hc
  have h0 : clock = 0 := by
    rcases hok with h | ⟨-, w, hw⟩
    · exact h
    · exact absurd hw (noHalt w)
  have hclk := (stateRelHOL_compile_and_clock relation).2
  subst h0
  refine ⟨postTarget, ?_⟩
  simpa [hclk] using tr

end InitECandidate.Solver.StackRemoveToStackNamesStateRelAndClockBridge
