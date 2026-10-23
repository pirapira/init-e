import InitECandidate.Solver.PanToStackNamesEndToEndLinearClockMaster
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Assembly
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Assembly
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Assembly

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# Upstream simulation theorems and their clock behaviour, composed with StackRawCall → StackNames

Inventory of the dynamic (`evaluate`) simulation theorems in Flapjack (none under `Proofs/Bounded*`):

| pass        | theorem                                         | target clock at start          |
|-------------|-------------------------------------------------|--------------------------------|
| PanToCrep   | **none** (only syntactic bridges in `PanToCrep/`) | —                              |
| CrepToLoop  | `crepToLoop_ncompile_correct`                   | `source.clock + ck`, ∃ ck       |
| LoopToWord  | `compileCorrect`                                | `source.clock` (exact, no ck)   |
| WordToWord  | `compile_single_correct`                        | same state, post = source post  |
| WordToStack | `WordToStackProofs.CompCorrect.compCorrect`     | `source.clock + extraClock`, ∃  |

So the exact-clock passes are LoopToWord and WordToWord (not PanToCrep, which has no
simulation theorem at all, and not WordToStack, which has an existential `extraClock`).
-/

namespace InitECandidate.Solver.PanToWordToStackNamesSimulationAndClockMaster

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

variable {width : Nat} [NeZero width]

/-- **CrepToLoop.** Existential overhead: the Loop target runs at `source.clock + ck`. -/
theorem crepToLoop_clock_plus_ck {σ : Type}
    (v : CrepProgHOL width) (v1 : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet)
    (run : evalCrepSemHOLProgExact v1 v = (res, s1)) (ne : res ≠ some .error)
    (hs : crepToLoopStateRelExact v1 t)
    (hm : crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs)
    (hg : crepToLoopGlobalsRelHOLExact v1.globals t.globals)
    (hc : crepToLoopCodeRelExact ctxt v1.code t.code)
    (hl : crepToLoopLocalsRelExact ctxt l v1.locals t.locals) :
    ∃ ck res1 t1, LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l v)
        { t with clock := v1.clock + ck } = (res1, t1) ∧ res1 = resultToLoop res ∧
      s1.clock = t1.clock := by
  obtain ⟨ck, res1, t1, e, rel, -, -, -, hr, -⟩ :=
    crepToLoop_ncompile_correct v v1 res s1 t ctxt l ⟨run, ne, hs, hm, hg, hc, hl⟩
  have h0 : v1.clock = t.clock := hs.2.2.1
  exact ⟨ck, res1, t1, by rw [h0]; exact e, hr, rel.2.2.1⟩

/-- **LoopToWord.** Exact start clock: the Word target runs at the Loop source clock, no ck. -/
theorem loopToWord_exact_clock {C F : Type}
    (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat)
    (run : LoopSemStateFiniteExact.evaluate prog s = (res, s1)) (ne : res ≠ some .error)
    (rel : loopToWordStateRelHOLExact s t) (loc : LoopToWord.localsRelHOL ctxt s.locals t.locals)
    (h0 : sptLookup 0 t.locals = some retv) (gd : goodDimindex width)
    (nw : ¬ wordSemIsWordLoc retv = true)
    (acc : ∀ k, sptMem k (accVarsHOL prog .ln) → sptMem k ctxt) :
    ∃ t1 res1, WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt prog l).1
        { t with clock := s.clock } = (res1, t1) ∧ t1.ffi = s1.ffi := by
  obtain ⟨t1, res1, e, hf, -⟩ :=
    compileCorrect (C := C) prog s res s1 t ctxt retv l ⟨run, ne, rel, loc, h0, gd, nw, acc⟩
  obtain ⟨_, -, -, -, hc, -⟩ := rel
  have : ({ t with clock := s.clock } : WordSemStateFiniteExact width C F) = t := by
    rw [← hc]
  exact ⟨t1, res1, by rw [this]; exact e, hf⟩

/-- **WordToStack.** Existential overhead: the Stack target runs at `source.clock + extraClock`. -/
theorem wordToStack_clock_plus_extra {C F : Type} (ac : AsmConfigExact width)
    (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (k f frame : Nat)
    (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (h : WordSemStateFiniteExact.evaluate program source = (result, sourcePost) ∧
      result ≠ some .error ∧ WordToStackProofs.stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      WordToStack.Native.compNative ac false program (bs, n) (k, f, frame) =
        (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k) :
    ∃ extraClock targetPost targetResult,
      StackSemEvaluate.evaluate (compiled, {target with clock := source.clock + extraClock}) =
        (targetResult, targetPost) := by
  obtain ⟨x, tp, tr, e, -⟩ :=
    WordToStackProofs.CompCorrect.compCorrect ac program source k f frame sourcePost target
      result bs bsPost n nPost compiled lens h
  have hc : source.clock = target.clock := h.2.2.1.1
  exact ⟨x, tp, tr, by rw [hc]; exact e⟩

/-- **WordToStack → StackRawCall → StackAlloc → StackRemove → StackNames.** If the WordToStack
output run (at `source.clock + extraClock`, from `compCorrect`) is non-error and its StackSem
state satisfies the StackRawCall / StackRemove / StackNames interfaces, the StackNames program
reproduces its result at final clock `≤ 2 * (source.clock + extraClock) + 1`. -/
theorem word_to_stackNames_clock {C F : Type}
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (fn : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt fn)) (info : Spt Nat)
    (compiled : HolProg width) (start : StackSemStateFiniteExact width C F)
    (extraClock : Nat) (targetPost mid low : StackSemStateFiniteExact width C F)
    (targetResult : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (compiled, {start with clock := start.clock + extraClock}) =
      (targetResult, targetPost))
    (ne : targetResult ≠ some .error)
    (rawRel : StackRawCall.stateRel info {start with clock := start.clock + extraClock} mid)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (remRel : ∀ k, StackRemove.stateRelHOL jump bounds pointer
      {mid with clock := k} {low with clock := k})
    (hnost : PanToStackNoStoreConsts.StackNoSt (StackRawCall.comp info compiled) = true)
    (hcode : ∀ k, StackRemoveNoStoreConstsZeroExtraClock.CodeNoSt {mid with clock := k})
    (bound : StackProps.regBound (StackRawCall.comp info compiled) pointer)
    (hc : low.compile = (fun cfg => c cfg ∘ StackNames.compileHOL fn)) :
    ∃ extra clock final, extra ≤ start.clock + extraClock ∧
      clock + mid.clock + extra ≤ 2 * (start.clock + extraClock) + 1 ∧
      StackSemEvaluate.evaluate
        (StackNames.progCompHOL fn
          (StackRemove.comp jump bounds pointer (StackRawCall.comp info compiled)),
          StackNames.renameState c fn {low with clock := clock + (mid.clock + extra)}) =
        (targetResult, StackNames.renameState c fn final) := by
  obtain ⟨extra, clock, final, h1, -, -, h3, e⟩ :=
    PanToStackNamesEndToEndLinearClockMaster.pancake_to_stackNames_end_to_end_linear_clock
      c fn hf info compiled _ mid targetPost targetResult run ne rawRel low pointer bounds jump
      remRel hnost hcode bound hc
  exact ⟨extra, clock, final, h1, h3, e⟩

end InitECandidate.Solver.PanToWordToStackNamesSimulationAndClockMaster
