import InitECandidate.Solver.LoopToWordToStackNamesAndLabToTargetClockMaster

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# CrepSem → LoopSem → WordSem → StackSem → … → StackNames, with LabToTarget

CrepToLoop runs the Loop program at `v1.clock + ck` with `ck` existential. The Loop→Word and
Word→Stack interfaces are about the Loop start state of that run, so they are assumed for every
clock value `K` (families indexed by `K`); the theorem instantiates them at `K = v1.clock + ck`.
The non-error Loop result is derived (`resultToLoop` maps only `error` to `error`).
-/

namespace InitECandidate.Solver.CrepToStackNamesAndLabToTargetEndToEndClockMaster

open Flapjack Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

variable {width : Nat} [NeZero width]

theorem resultToLoop_ne_error (res : Option (CrepResultHOLExact width))
    (h : res ≠ some .error) : resultToLoop res ≠ some .error := by
  rcases res with _ | r
  · simp [resultToLoop]
  · cases r <;> simp_all [resultToLoop]

/-- **CrepSem → LoopSem → WordSem.** A non-error Crep run gives a Loop run of the CrepToLoop
output at `v1.clock + ck` with result `resultToLoop res`, and then a Word run of the LoopToWord
output starting at exactly that clock, with the same FFI as the Loop post-state. -/
theorem crep_to_loop_to_word_clock {C σ : Type}
    (v : CrepProgHOL width) (v1 : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet)
    (run : evalCrepSemHOLProgExact v1 v = (res, s1)) (ne : res ≠ some .error)
    (hs : crepToLoopStateRelExact v1 t)
    (hm : crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs)
    (hg : crepToLoopGlobalsRelHOLExact v1.globals t.globals)
    (hc : crepToLoopCodeRelExact ctxt v1.code t.code)
    (hl : crepToLoopLocalsRelExact ctxt l v1.locals t.locals)
    (wctx : Spt Nat) (retv : WordLocW width) (lw : Nat × Nat)
    (tw : Nat → WordSemStateFiniteExact width C σ)
    (rel : ∀ K, loopToWordStateRelHOLExact {t with clock := K} (tw K))
    (loc : ∀ K, LoopToWord.localsRelHOL wctx t.locals (tw K).locals)
    (h0 : ∀ K, sptLookup 0 (tw K).locals = some retv) (gd : goodDimindex width)
    (nw : ¬ wordSemIsWordLoc retv = true)
    (acc : ∀ k, sptMem k (accVarsHOL (compileHOLExact ctxt l v) .ln) → sptMem k wctx) :
    ∃ ck res1 t1 wres wpost,
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l v)
        {t with clock := v1.clock + ck} = (res1, t1) ∧ res1 = resultToLoop res ∧
      s1.clock = t1.clock ∧
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1
        (tw (v1.clock + ck)) = (wres, wpost) ∧
      (tw (v1.clock + ck)).clock = v1.clock + ck ∧ wpost.ffi = t1.ffi := by
  obtain ⟨ck, res1, t1, e, hr, hcl⟩ :=
    PanToWordToStackNamesSimulationAndClockMaster.crepToLoop_clock_plus_ck v v1 res s1 t ctxt l
      run ne hs hm hg hc hl
  have ne1 : res1 ≠ some .error := hr ▸ resultToLoop_ne_error res ne
  obtain ⟨wpost, wres, ew, hf⟩ :=
    PanToWordToStackNamesSimulationAndClockMaster.loopToWord_exact_clock
      (compileHOLExact ctxt l v) {t with clock := v1.clock + ck} res1 t1 (tw (v1.clock + ck))
      wctx retv lw e ne1 (rel _) (loc _) (h0 _) gd nw acc
  have htw : (tw (v1.clock + ck)).clock = v1.clock + ck := by
    obtain ⟨_, -, -, -, h, -⟩ := rel (v1.clock + ck); simpa using h
  have ew' : WordSemStateFiniteExact.evaluate
      (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 (tw (v1.clock + ck)) =
      (wres, wpost) := by
    have : ({tw (v1.clock + ck) with clock := v1.clock + ck} : WordSemStateFiniteExact width C σ) =
        tw (v1.clock + ck) := by
      generalize tw (v1.clock + ck) = w at htw ⊢
      rw [← htw]
    rw [this] at ew; exact ew
  exact ⟨ck, res1, t1, wres, wpost, e, hr, hcl, ew', htw, hf⟩

/-- **CrepSem → … → StackNames.** Continue the Word run of `crep_to_loop_to_word_clock` through
WordToStack, StackRawCall, StackAlloc, StackRemove and StackNames. For the existential CrepToLoop
overhead `ck` and WordToStack overhead `x`, StackNames reproduces the Stack result at final clock
`≤ 2 * (v1.clock + ck + x) + 1`. Interfaces are assumed as families over the existential clocks. -/
theorem crep_to_stackNames_clock {C σ : Type} (ac : AsmConfigExact width)
    (v : CrepProgHOL width) (v1 : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet)
    (run : evalCrepSemHOLProgExact v1 v = (res, s1)) (ne : res ≠ some .error)
    (hs : crepToLoopStateRelExact v1 t)
    (hm : crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs)
    (hg : crepToLoopGlobalsRelHOLExact v1.globals t.globals)
    (hc : crepToLoopCodeRelExact ctxt v1.code t.code)
    (hl : crepToLoopLocalsRelExact ctxt l v1.locals t.locals)
    (wctx : Spt Nat) (retv : WordLocW width) (lw : Nat × Nat)
    (tw : Nat → WordSemStateFiniteExact width (Nat × C) σ)
    (rel : ∀ K, loopToWordStateRelHOLExact {t with clock := K} (tw K))
    (loc : ∀ K, LoopToWord.localsRelHOL wctx t.locals (tw K).locals)
    (h0 : ∀ K, sptLookup 0 (tw K).locals = some retv) (gd : goodDimindex width)
    (nw : ¬ wordSemIsWordLoc retv = true)
    (acc : ∀ k, sptMem k (accVarsHOL (compileHOLExact ctxt l v) .ln) → sptMem k wctx)
    (k f frame : Nat) (target : Nat → StackSemStateFiniteExact width C σ)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (w2s : ∀ K, WordToStackProofs.stateRel ac k f frame (tw K) (target K) lens 0 ∧
      postAllocConventionsHOL k (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 = true ∧
      flatExpConventions (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 = true ∧
      WordToStack.Native.compNative ac false
        (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 (bs, n)
        (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ (target K).bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost)
        ((target K).bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact (target K).code loc) ∧
      maxVarHOL (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 < 2 * frame + 2 * k)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (fn : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt fn)) (info : Spt Nat)
    (mid low : Nat → Nat → StackSemStateFiniteExact width C σ)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (rawRel : ∀ K x, StackRawCall.stateRel info
      {target K with clock := (target K).clock + x} (mid K x))
    (remRel : ∀ K x kk, StackRemove.stateRelHOL jump bounds pointer
      {mid K x with clock := kk} {low K x with clock := kk})
    (hnost : PanToStackNoStoreConsts.StackNoSt (StackRawCall.comp info compiled) = true)
    (hcode : ∀ K x kk, StackRemoveNoStoreConstsZeroExtraClock.CodeNoSt {mid K x with clock := kk})
    (bound : StackProps.regBound (StackRawCall.comp info compiled) pointer)
    (hcomp : ∀ K x, (low K x).compile = (fun cfg => c cfg ∘ StackNames.compileHOL fn)) :
    ∃ ck res1 t1, LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l v)
        {t with clock := v1.clock + ck} = (res1, t1) ∧ res1 = resultToLoop res ∧
      ∃ wres wpost, WordSemStateFiniteExact.evaluate
          (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 (tw (v1.clock + ck)) =
          (wres, wpost) ∧ wpost.ffi = t1.ffi ∧
        (wres ≠ some .error → ∃ x targetPost targetResult,
          StackSemEvaluate.evaluate (compiled,
            {target (v1.clock + ck) with clock := v1.clock + ck + x}) =
            (targetResult, targetPost) ∧
          (targetResult ≠ some .error → ∃ extra clock final, extra ≤ v1.clock + ck + x ∧
            clock + (mid (v1.clock + ck) x).clock + extra ≤ 2 * (v1.clock + ck + x) + 1 ∧
            StackSemEvaluate.evaluate
              (StackNames.progCompHOL fn
                (StackRemove.comp jump bounds pointer (StackRawCall.comp info compiled)),
                StackNames.renameState c fn
                  {low (v1.clock + ck) x with clock := clock + ((mid (v1.clock + ck) x).clock + extra)}) =
              (targetResult, StackNames.renameState c fn final))) := by
  obtain ⟨ck, res1, t1, e, hr, -⟩ :=
    PanToWordToStackNamesSimulationAndClockMaster.crepToLoop_clock_plus_ck v v1 res s1 t ctxt l
      run ne hs hm hg hc hl
  have ne1 : res1 ≠ some .error := hr ▸ resultToLoop_ne_error res ne
  set K := v1.clock + ck with hK
  obtain ⟨wpost, wres, ew, hff, hrest⟩ :=
    LoopToWordToStackNamesAndLabToTargetClockMaster.loop_to_stackNames_clock ac
      (compileHOLExact ctxt l v) {t with clock := K} res1 t1 (tw K) wctx retv lw e ne1 (rel K)
      (loc K) (h0 K) gd nw acc k f frame (target K) bs bsPost n nPost compiled lens (w2s K)
      c fn hf info (mid K) (low K) pointer bounds jump (rawRel K) (remRel K) hnost (hcode K)
      bound (hcomp K)
  exact ⟨ck, res1, t1, e, hr, wres, wpost, ew, hff, hrest⟩

/-- **Summary.** The CrepSem → … → StackNames chain (`crep_to_stackNames_clock`) and the
LabToTarget simulation (`labToTarget_clock_plus_k`: target machine at `s1.clock + k`) hold
together. The StackNames → StackToLab link is the missing piece between them (no linear bound,
`stackToLab_no_linear_clock_bound`). -/
theorem crep_to_stackNames_and_labToTarget_summary {C σ S Q F : Type} (ac : AsmConfigExact width)
    (v : CrepProgHOL width) (v1 : CrepSemHOLState width σ)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet)
    (run : evalCrepSemHOLProgExact v1 v = (res, s1)) (ne : res ≠ some .error)
    (hs : crepToLoopStateRelExact v1 t)
    (hm : crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs)
    (hg : crepToLoopGlobalsRelHOLExact v1.globals t.globals)
    (hc : crepToLoopCodeRelExact ctxt v1.code t.code)
    (hl : crepToLoopLocalsRelExact ctxt l v1.locals t.locals)
    (wctx : Spt Nat) (retv : WordLocW width) (lw : Nat × Nat)
    (tw : Nat → WordSemStateFiniteExact width (Nat × C) σ)
    (rel : ∀ K, loopToWordStateRelHOLExact {t with clock := K} (tw K))
    (loc : ∀ K, LoopToWord.localsRelHOL wctx t.locals (tw K).locals)
    (h0 : ∀ K, sptLookup 0 (tw K).locals = some retv) (gd : goodDimindex width)
    (nw : ¬ wordSemIsWordLoc retv = true)
    (acc : ∀ k, sptMem k (accVarsHOL (compileHOLExact ctxt l v) .ln) → sptMem k wctx)
    (k f frame : Nat) (target : Nat → StackSemStateFiniteExact width C σ)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (w2s : ∀ K, WordToStackProofs.stateRel ac k f frame (tw K) (target K) lens 0 ∧
      postAllocConventionsHOL k (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 = true ∧
      flatExpConventions (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 = true ∧
      WordToStack.Native.compNative ac false
        (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 (bs, n)
        (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ (target K).bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost)
        ((target K).bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact (target K).code loc) ∧
      maxVarHOL (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 < 2 * frame + 2 * k)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (fn : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt fn)) (info : Spt Nat)
    (mid low : Nat → Nat → StackSemStateFiniteExact width C σ)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (rawRel : ∀ K x, StackRawCall.stateRel info
      {target K with clock := (target K).clock + x} (mid K x))
    (remRel : ∀ K x kk, StackRemove.stateRelHOL jump bounds pointer
      {mid K x with clock := kk} {low K x with clock := kk})
    (hnost : PanToStackNoStoreConsts.StackNoSt (StackRawCall.comp info compiled) = true)
    (hcode : ∀ K x kk, StackRemoveNoStoreConstsZeroExtraClock.CodeNoSt {mid K x with clock := kk})
    (bound : StackProps.regBound (StackRawCall.comp info compiled) pointer)
    (hcomp : ∀ K x, (low K x).compile = (fun cfg => c cfg ∘ StackNames.compileHOL fn))
    (p : BitVec width) (ls1 : Flapjack.Compiler.Backend.LabSem.State width LabToTarget.Config F)
    (lres : MachineResult) (mc : MachineConfig width S Q)
    (ls2 : Flapjack.Compiler.Backend.LabSem.State width LabToTarget.Config F)
    (code2 : Flapjack.Compiler.Backend.LabSem.LabProgHOL width) (labs : Spt (Spt Nat))
    (at1 : AsmState width) (ms1 : S)
    (tie : LabToTarget.oracleTie mc ms1 ls1)
    (lrun : Flapjack.Compiler.Backend.LabSem.evaluate ls1 = (lres, ls2))
    (lne : lres ≠ .error) (enc : Flapjack.Compiler.Encoders.AsmProps.encoderCorrect mc.target)
    (lrel : LabToTarget.stateRel (mc, code2, labs, p) ls1 at1 ms1) :
    (∃ ck res1 t1, LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l v)
        {t with clock := v1.clock + ck} = (res1, t1) ∧ res1 = resultToLoop res ∧
      ∃ wres wpost, WordSemStateFiniteExact.evaluate
          (LoopToWord.compHOL wctx (compileHOLExact ctxt l v) lw).1 (tw (v1.clock + ck)) =
          (wres, wpost) ∧ wpost.ffi = t1.ffi ∧
        (wres ≠ some .error → ∃ x targetPost targetResult,
          StackSemEvaluate.evaluate (compiled,
            {target (v1.clock + ck) with clock := v1.clock + ck + x}) =
            (targetResult, targetPost) ∧
          (targetResult ≠ some .error → ∃ extra clock final, extra ≤ v1.clock + ck + x ∧
            clock + (mid (v1.clock + ck) x).clock + extra ≤ 2 * (v1.clock + ck + x) + 1 ∧
            StackSemEvaluate.evaluate
              (StackNames.progCompHOL fn
                (StackRemove.comp jump bounds pointer (StackRawCall.comp info compiled)),
                StackNames.renameState c fn
                  {low (v1.clock + ck) x with clock := clock + ((mid (v1.clock + ck) x).clock + extra)}) =
              (targetResult, StackNames.renameState c fn final)))) ∧
    (∃ kk ms2, evaluateTargetHOL mc ls1.ffi (ls1.clock + kk) ms1 = (lres, ms2, ls2.ffi)) :=
  ⟨crep_to_stackNames_clock ac v v1 res s1 t ctxt l run ne hs hm hg hc hl wctx retv lw tw rel loc
      h0 gd nw acc k f frame target bs bsPost n nPost compiled lens w2s c fn hf info mid low
      pointer bounds jump rawRel remRel hnost hcode bound hcomp,
   LoopToWordToStackNamesAndLabToTargetClockMaster.labToTarget_clock_plus_k p ls1 lres mc ls2
      code2 labs at1 ms1 tie lrun lne enc lrel⟩

end InitECandidate.Solver.CrepToStackNamesAndLabToTargetEndToEndClockMaster
