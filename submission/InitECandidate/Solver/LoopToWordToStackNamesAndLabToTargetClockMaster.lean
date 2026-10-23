import InitECandidate.Solver.PanToWordToStackNamesSimulationAndClockMaster
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Assembly

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# LoopSem → WordSem → StackSem → StackNames, and the LabToTarget simulation

* LoopToWord (`compileCorrect`) runs the Word program at the Loop source clock exactly.
* WordToStack (`compCorrect`) runs the Stack program at `clock + extraClock`, ∃ extraClock.
* The glue is run-level: LoopToWord produces the Word run; the WordToStack side conditions are
  static facts about the Word program and the Word start state, so they are assumed on that
  start state, and the WordToStack theorem is applied to the Word run that LoopToWord produced.
* LabToTarget (`LabToTarget.compileCorrect`, not under `Proofs/Bounded*`): the machine run uses
  `s1.clock + k`, ∃ k, same result and FFI.
-/

namespace InitECandidate.Solver.LoopToWordToStackNamesAndLabToTargetClockMaster

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

variable {width : Nat} [NeZero width]

/-- **LoopSem → WordSem → StackSem.** The Word run of the LoopToWord output starts at the Loop
clock `s.clock`; if it is non-error, the WordToStack output runs at `s.clock + extraClock`. -/
theorem loop_to_word_to_stack_clock {C F : Type} (ac : AsmConfigExact width)
    (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width (Nat × C) F)
    (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat)
    (run : LoopSemStateFiniteExact.evaluate prog s = (res, s1)) (ne : res ≠ some .error)
    (rel : loopToWordStateRelHOLExact s t) (loc : LoopToWord.localsRelHOL ctxt s.locals t.locals)
    (h0 : sptLookup 0 t.locals = some retv) (gd : goodDimindex width)
    (nw : ¬ wordSemIsWordLoc retv = true)
    (acc : ∀ k, sptMem k (accVarsHOL prog .ln) → sptMem k ctxt)
    (k f frame : Nat) (target : StackSemStateFiniteExact width C F)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (w2s : WordToStackProofs.stateRel ac k f frame t target lens 0 ∧
      postAllocConventionsHOL k (LoopToWord.compHOL ctxt prog l).1 = true ∧
      flatExpConventions (LoopToWord.compHOL ctxt prog l).1 = true ∧
      WordToStack.Native.compNative ac false (LoopToWord.compHOL ctxt prog l).1 (bs, n)
        (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (LoopToWord.compHOL ctxt prog l).1 < 2 * frame + 2 * k) :
    ∃ t1 res1, WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt prog l).1 t = (res1, t1) ∧
      t.clock = s.clock ∧ t1.ffi = s1.ffi ∧
      (res1 ≠ some .error → ∃ extraClock targetPost targetResult,
        StackSemEvaluate.evaluate (compiled, {target with clock := s.clock + extraClock}) =
          (targetResult, targetPost)) := by
  obtain ⟨t1, res1, e, hf, -⟩ :=
    compileCorrect (C := Nat × C) prog s res s1 t ctxt retv l ⟨run, ne, rel, loc, h0, gd, nw, acc⟩
  obtain ⟨_, -, -, -, hc, -⟩ := rel
  refine ⟨t1, res1, e, hc, hf, fun ne1 => ?_⟩
  obtain ⟨x, tp, tr, es⟩ :=
    PanToWordToStackNamesSimulationAndClockMaster.wordToStack_clock_plus_extra ac _ t k f frame
      t1 target res1 bs bsPost n nPost compiled lens ⟨e, ne1, w2s⟩
  exact ⟨x, tp, tr, by rw [← hc]; exact es⟩

/-- **LoopSem → WordSem → StackSem → StackNames.** Same glue, continued through
StackRawCall → StackAlloc → StackRemove → StackNames: the StackNames program reproduces the
Stack result at final clock `≤ 2 * (s.clock + extraClock) + 1`. The StackRawCall / StackRemove /
StackNames interfaces are assumed for every possible WordToStack overhead `x`. -/
theorem loop_to_stackNames_clock {C F : Type} (ac : AsmConfigExact width)
    (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width (Nat × C) F)
    (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat)
    (run : LoopSemStateFiniteExact.evaluate prog s = (res, s1)) (ne : res ≠ some .error)
    (rel : loopToWordStateRelHOLExact s t) (loc : LoopToWord.localsRelHOL ctxt s.locals t.locals)
    (h0 : sptLookup 0 t.locals = some retv) (gd : goodDimindex width)
    (nw : ¬ wordSemIsWordLoc retv = true)
    (acc : ∀ k, sptMem k (accVarsHOL prog .ln) → sptMem k ctxt)
    (k f frame : Nat) (target : StackSemStateFiniteExact width C F)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (w2s : WordToStackProofs.stateRel ac k f frame t target lens 0 ∧
      postAllocConventionsHOL k (LoopToWord.compHOL ctxt prog l).1 = true ∧
      flatExpConventions (LoopToWord.compHOL ctxt prog l).1 = true ∧
      WordToStack.Native.compNative ac false (LoopToWord.compHOL ctxt prog l).1 (bs, n)
        (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (LoopToWord.compHOL ctxt prog l).1 < 2 * frame + 2 * k)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (fn : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt fn)) (info : Spt Nat)
    (mid low : Nat → StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (rawRel : ∀ x, StackRawCall.stateRel info {target with clock := target.clock + x} (mid x))
    (remRel : ∀ x kk, StackRemove.stateRelHOL jump bounds pointer
      {mid x with clock := kk} {low x with clock := kk})
    (hnost : PanToStackNoStoreConsts.StackNoSt (StackRawCall.comp info compiled) = true)
    (hcode : ∀ x kk, StackRemoveNoStoreConstsZeroExtraClock.CodeNoSt {mid x with clock := kk})
    (bound : StackProps.regBound (StackRawCall.comp info compiled) pointer)
    (hc : ∀ x, (low x).compile = (fun cfg => c cfg ∘ StackNames.compileHOL fn)) :
    ∃ t1 res1, WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt prog l).1 t = (res1, t1) ∧
      t1.ffi = s1.ffi ∧
      (res1 ≠ some .error → ∃ x targetPost targetResult,
        StackSemEvaluate.evaluate (compiled, {target with clock := s.clock + x}) =
          (targetResult, targetPost) ∧
        (targetResult ≠ some .error → ∃ extra clock final, extra ≤ s.clock + x ∧
          clock + (mid x).clock + extra ≤ 2 * (s.clock + x) + 1 ∧
          StackSemEvaluate.evaluate
            (StackNames.progCompHOL fn
              (StackRemove.comp jump bounds pointer (StackRawCall.comp info compiled)),
              StackNames.renameState c fn {low x with clock := clock + ((mid x).clock + extra)}) =
            (targetResult, StackNames.renameState c fn final))) := by
  obtain ⟨t1, res1, e, htc, hff, hst⟩ :=
    loop_to_word_to_stack_clock ac prog s res s1 t ctxt retv l run ne rel loc h0 gd nw acc
      k f frame target bs bsPost n nPost compiled lens w2s
  have hct : t.clock = target.clock := w2s.1.1
  refine ⟨t1, res1, e, hff, fun ne1 => ?_⟩
  obtain ⟨x, tp, tr, es⟩ := hst ne1
  refine ⟨x, tp, tr, es, fun ne2 => ?_⟩
  have es' : StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + x}) =
      (tr, tp) := by rw [← hct, htc]; exact es
  obtain ⟨extra, clock, final, h1, h2, en⟩ :=
    PanToWordToStackNamesSimulationAndClockMaster.word_to_stackNames_clock c fn hf info compiled
      target x tp (mid x) (low x) tr es' ne2 (rawRel x) pointer bounds jump (remRel x) hnost
      (hcode x) bound (hc x)
  rw [← hct, htc] at h1 h2
  exact ⟨extra, clock, final, h1, h2, en⟩

section LabTarget
open Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget

/-- **LabToTarget.** Flapjack's `compileCorrect` (outside `Proofs/Bounded*`): a non-error LabSem
run is reproduced by the target machine at clock `s1.clock + k`, ∃ k, same result and FFI. -/
theorem labToTarget_clock_plus_k {S Q F : Type} (p : BitVec width)
    (s1 : Flapjack.Compiler.Backend.LabSem.State width LabToTarget.Config F) (res : MachineResult)
    (mc : MachineConfig width S Q) (s2 : Flapjack.Compiler.Backend.LabSem.State width LabToTarget.Config F)
    (code2 : Flapjack.Compiler.Backend.LabSem.LabProgHOL width) (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S)
    (tie : LabToTarget.oracleTie mc ms1 s1) (run : Flapjack.Compiler.Backend.LabSem.evaluate s1 = (res, s2))
    (ne : res ≠ .error) (enc : encoderCorrect mc.target)
    (rel : LabToTarget.stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ k ms2, evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms2, s2.ffi) := by
  obtain ⟨k, -, ms2, h⟩ := LabToTarget.compileCorrect (T := Unit) p s1 res mc s2 code2 labs t1 ms1
    ⟨tie, run, ne, enc, rel⟩
  exact ⟨k, ms2, h⟩

end LabTarget

end InitECandidate.Solver.LoopToWordToStackNamesAndLabToTargetClockMaster
