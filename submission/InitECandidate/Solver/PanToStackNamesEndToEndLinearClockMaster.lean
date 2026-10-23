import InitECandidate.Solver.StackRawCallLinearClockAndZeroExtraBridge
import InitECandidate.Solver.StackRemoveToStackNamesStateRelAndClockBridge

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# StackRawCall → StackAlloc → StackRemove → StackNames: end-to-end linear clock (StackSem level)

Scope: the imported modules prove clock bounds for the StackSem passes only. No imported module
relates `PanSem.evaluate` (or Crep/Loop/Word semantics) to StackSem clocks, so the chain here
starts at the StackSem source of StackRawCall. StackAlloc is the identity on the compiled
sections (module 151), so the StackRawCall output is the StackRemove input unchanged.

Bound: `final clock ≤ 2 * source.clock + 1`; outside `halt`, `final = target.clock + extra`
with `extra ≤ source.clock` (StackRemove and StackNames add 0).
-/

namespace InitECandidate.Solver.PanToStackNamesEndToEndLinearClockMaster

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)

variable {width : Nat} [NeZero width]

/-- **End-to-end, StackSem level.** A StackSem run of `program` from `source` is simulated by
`StackNames ∘ StackRemove ∘ StackRawCall` (StackAlloc = identity) with the same result, at a
final clock `≤ 2 * source.clock + 1`. Hypotheses: the StackRawCall relation, the StackRemove
relation on the StackRawCall target at every clock, the StackRemove side conditions
(`StackNoSt`, `CodeNoSt`, `regBound`) and the StackNames installation oracle. -/
theorem pancake_to_stackNames_end_to_end_linear_clock {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (info : Spt Nat) (program : HolProg width)
    (source mid post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (nonError : result ≠ some .error)
    (rawRel : StackRawCall.stateRel info source mid)
    (low : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (remRel : ∀ k, StackRemove.stateRelHOL jump bounds pointer
      {mid with clock := k} {low with clock := k})
    (hnost : StackNoSt (StackRawCall.comp info program) = true)
    (hcode : ∀ k, CodeNoSt {mid with clock := k})
    (bound : StackProps.regBound (StackRawCall.comp info program) pointer)
    (hc : low.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    ∃ extra clock final, extra ≤ source.clock ∧ ClockOk clock result ∧
      mid.clock + extra ≤ 2 * source.clock ∧
      clock + mid.clock + extra ≤ 2 * source.clock + 1 ∧
      StackSemEvaluate.evaluate
        (StackNames.progCompHOL f
          (StackRemove.comp jump bounds pointer (StackRawCall.comp info program)),
          StackNames.renameState c f {low with clock := clock + (mid.clock + extra)}) =
        (result, StackNames.renameState c f final) := by
  obtain ⟨extra, mpost, h1, h2, tr⟩ :=
    StackRawCallLinearClockAndZeroExtraBridge.rawCall_extra_le_clock program source mid post
      info result run nonError rawRel
  have rel := remRel (mid.clock + extra)
  have hlow : ({low with clock := mid.clock + extra} :
      StackSemStateFiniteExact width C F).compile = (fun cfg => c cfg ∘ StackNames.compileHOL f) := hc
  obtain ⟨clock, final, hok, -, e, -⟩ :=
    StackRemoveToStackNamesStateRelAndClockBridge.stackRemove_then_stackNames_clock c f hf
      _ _ result mpost _ pointer bounds jump hnost (hcode _) tr nonError rel bound hlow
  refine ⟨extra, clock, final, h1, hok, h2, ?_, by simpa using e⟩
  rcases hok with h | ⟨h, -⟩ <;> omega

/-- **Non-`halt`.** StackRemove and StackNames add exactly 0: the final clock is
`mid.clock + extra`, and all expansion comes from StackRawCall (`extra ≤ source.clock`). -/
theorem pancake_to_stackNames_noHalt_linear_clock {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (info : Spt Nat) (program : HolProg width)
    (source mid post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (nonError : result ≠ some .error) (noHalt : ∀ w, result ≠ some (.halt w))
    (rawRel : StackRawCall.stateRel info source mid)
    (low : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (remRel : ∀ k, StackRemove.stateRelHOL jump bounds pointer
      {mid with clock := k} {low with clock := k})
    (hnost : StackNoSt (StackRawCall.comp info program) = true)
    (hcode : ∀ k, CodeNoSt {mid with clock := k})
    (bound : StackProps.regBound (StackRawCall.comp info program) pointer)
    (hc : low.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f)) :
    ∃ extra final, extra ≤ source.clock ∧ mid.clock + extra ≤ 2 * source.clock ∧
      StackSemEvaluate.evaluate
        (StackNames.progCompHOL f
          (StackRemove.comp jump bounds pointer (StackRawCall.comp info program)),
          StackNames.renameState c f {low with clock := mid.clock + extra}) =
        (result, StackNames.renameState c f final) := by
  obtain ⟨extra, clock, final, h1, hok, h2, -, e⟩ :=
    pancake_to_stackNames_end_to_end_linear_clock c f hf info program source mid post result
      run nonError rawRel low pointer bounds jump remRel hnost hcode bound hc
  have h0 : clock = 0 := by
    rcases hok with h | ⟨-, w, hw⟩
    · exact h
    · exact absurd hw (noHalt w)
  subst h0
  exact ⟨extra, final, h1, h2, by simpa using e⟩

/-- **Clock accounting summary.**
* StackAlloc: identity on every compiled section `≠ 6`, no GC call (module 151);
* StackNames: exact isometry (same result, same clock) on any run;
* StackRawCall → StackRemove → StackNames: final clock `≤ 2 * source.clock + 1`;
* StackToLab: no bound linear in StackSem ticks (`skip` at clock 0 vs LabSem timeout). -/
theorem flapjack_nine_pass_clock_accounting_summary {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (dc : DataToWord.Config) (info : Spt Nat)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt f)) :
    (∀ y ∈ PanToStackAllocIdentityAndUnconditionalNoGcCall.rawCallSections arch prog wc ac perf,
      y.1 ≠ storeConstsStubLocation → StackAlloc.progComp y = y) ∧
    (∀ (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
       (r : Option (StackSemResult width)),
       StackSemEvaluate.evaluate (p, s) = (r, t) →
       ¬s.useAlloc → ¬s.useStore → ¬s.useStack →
       s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f) →
       StackSemEvaluate.evaluate (StackNames.progCompHOL f p, StackNames.renameState c f s) =
         (r, StackNames.renameState c f t) ∧
       (StackNames.renameState c f t).clock = t.clock) ∧
    (∀ (s : StackSemStateFiniteExact width C F) (t : LabSem.State width C F) (slope : Nat),
       s.clock = 0 →
       StackSemEvaluate.evaluate ((.skip : HolProg width), s) = (none, s) ∧
       (LabSem.evaluate {t with clock := slope * s.clock}).1 = .timeOut) := by
  have m := StackRawCallToStackNamesAndStackToLabLinearBridge.pancake_stackRawCall_to_stackNames_and_stackToLab
    (C := C) (F := F) arch prog wc ac perf dc info c f hf
  exact ⟨m.1, m.2.2.1, m.2.2.2.2⟩

end InitECandidate.Solver.PanToStackNamesEndToEndLinearClockMaster
