import InitECandidate.Solver.FastBoundedTarget
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSemantics
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTopResource

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


namespace InitE
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Pancake.Proofs.PanToTarget

/-- Clock-preserving `WordToWord` simulation: at any clock `k`, a non-error entry call
on `s` (with `s.code = sptFromAList wprog0`) produces the exact same result and FFI state
on `{ s with code := sptFromAList wprog }` at the same clock `k`. -/
theorem word_to_word_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    (wconf : WordToWord.Config) (ac : AsmConfigExact width)
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : WordSemStateFiniteExact width C F) (start k : Nat)
    (hwtw : WordToWord.compile wconf ac wprog0 = (col, wprog))
    (hgc : WordSimp.gcFunConstOk s.gcFun)
    (hnic : WordProps.noInstallCode s.code)
    (hnac : WordProps.noAllocCode s.code)
    (hnmc : WordProps.noMtCode (sptFromAList wprog0))
    (hstack : s.stack = [])
    (hsc : s.code = sptFromAList wprog0)
    (hne : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k }).1 ≠ some .error) :
    (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k, code := sptFromAList wprog }).1 =
      (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        { s with clock := k }).1 ∧
    (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k, code := sptFromAList wprog }).2.ffi =
      (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        { s with clock := k }).2.ffi := by
  have hext := WordToWord.code_rel_ext_word_to_word ac wprog0 wconf col wprog hwtw
  have hrel0 := WordToWord.no_mt_code_rel_ext _ _ ⟨hnmc, hext⟩
  have hdom0 : sptDomain (sptFromAList wprog0) = sptDomain (sptFromAList wprog) := by
    simp only [WordToWord.compile, Prod.mk.injEq] at hwtw
    obtain ⟨-, rfl⟩ := hwtw
    funext n
    simp only [sptDomain, sptLookup_sptFromAList]
    rw [WordToWord.sptAListLookup_isSome_map_fullCompileSingle _ _ _ _ wprog0 _
      (WordToWord.compile_zip_length wconf wprog0)]
  rw [← hsc] at hrel0 hdom0 hnmc
  exact WordToWord.compile_runs_agree s (sptFromAList wprog) start k
    hrel0 hnic hnac hnmc hdom0 hgc hstack hne

/-- Clocked `WordToStack` simulation under `wordLangSafeForSpace`: a non-error `WordSem`
entry call at clock `k` yields a `StackSem` entry call at clock `k + ck` with the exact
compiled result (`res.map compileResult`) and identical FFI state. -/
theorem word_to_stack_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k_reg : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F)
    (start k : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (related : WordToStackProofs.stateRel ac k_reg 0 0 s t [] 0)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace s start)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k } = (res, s1))
    (hne : res ≠ some .error) :
    ∃ ck t1,
      StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k + ck }) =
        (res.map WordToStackProofs.CompCorrect.compileResult, t1) ∧
      s1.ffi = t1.ffi := by
  have sim := WordToStackProofs.StateRelSemantics.entrySimulationOfStateRel
    ac k_reg s t [] start related
  obtain ⟨ck, res1, t1, targetRun, outcome⟩ := sim k res s1 hrun hne
  rcases outcome with ⟨same, ffi⟩ | ⟨_, _, _, hover⟩
  · subst same
    exact ⟨ck, t1, targetRun, ffi⟩
  · obtain ⟨max, maxEq, maxLe⟩ := safe k res s1 hrun
    rw [maxEq] at hover
    simp only [Option.getD_some] at hover
    omega

/-- Clocked `StackRawCall` simulation: at any clock `k`, a non-error entry call on `source`
produces a target run on `{ source with code := sptFromAList (compile code), clock := k + extra }`
with the exact same result and FFI state. -/
theorem stack_rawcall_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { source with clock := clock }) =
      (result, post))
    (nonError : result ≠ some .error) :
    ∃ extra targetPost, StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        { source with code := sptFromAList (StackRawCall.compile code), clock := clock + extra }) =
      (result, targetPost) ∧ targetPost.ffi = post.ffi :=
  StackRawCall.CompileSemantics.entrySimulation code source start clock result post
    distinct sourceCode run nonError

/-- Clocked `StackAlloc` simulation: at any clock `k`, a non-error entry call on `s` produces
a target run at clock `k + ck` with the exact same result and FFI state. -/
theorem stack_alloc_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} {c : DataToWord.Config}
    {compile_rest : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)}
    {start : Nat} {anything : WordSemGcFun width}
    (hcode : ∀ k prog, sptLookup k s.code = some prog → k ≠ gcStubLocation ∧ StackProps.allocArg prog)
    (horacle : ∀ (i k : Nat) (q : HolProg width), (k, q) ∈ (s.compileOracle i).2.1 →
      k ≠ gcStubLocation ∧ StackProps.allocArg q)
    (hgc : s.gcFun = WordGcFunctions.wordGcFun c)
    (hbuf : s.bitmaps.length + s.dataBuffer.buffer.length + s.dataBuffer.spaceLeft < 2 ^ width - 1)
    (hst : s.stack.length * (width / 8) < 2 ^ width)
    (hK : s.useStack = true) (hA : s.useAlloc = true)
    (hC : s.compile = (fun cfg => compile_rest cfg ∘ List.map StackAlloc.progComp))
    (k : Nat) (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (he : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s with clock := k }) = (r, t))
    (hr : r ≠ some .error) :
    ∃ ck,
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with
          code := sptFromAList (StackAlloc.compile c (sptToAList s.code))
          gcFun := anything
          compile := compile_rest
          compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ s.compileOracle
          useStore := true, useStack := true, useAlloc := false, clock := k + ck })).1 = r ∧
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with
          code := sptFromAList (StackAlloc.compile c (sptToAList s.code))
          gcFun := anything
          compile := compile_rest
          compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ s.compileOracle
          useStore := true, useStack := true, useAlloc := false, clock := k + ck })).2.ffi = t.ffi := by
  obtain ⟨ck, regs1, he', -⟩ :=
    StackAlloc.comp_correct (anything := anything) (compile_rest := compile_rest)
      (.call none (.inl start) none) { s with clock := k } r t 0 0 c s.regs
      ⟨he, hr, ⟨trivial, trivial⟩, hcode, horacle, hgc, hA, hst, fun _ _ h => h, hK, hbuf, hC⟩
  exact ⟨ck, (congrArg Prod.fst he').trans rfl, (congrArg (fun p => p.2.ffi) he').trans rfl⟩

/-- Clocked `StackRemove` body simulation: at any clock `k`, a non-error entry call on `source`
produces a target run at clock `extra + k` with the exact same result and FFI state. -/
theorem stack_remove_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (relation : StackRemove.stateRelHOL jump bounds pointer source target)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { source with clock := clock }) =
      (result, postSource))
    (nonError : result ≠ some .error) :
    ∃ extra postTarget,
      StackSemEvaluate.evaluate
        ((.call none (.inl start) none : HolProg width), { target with clock := extra + clock }) =
        (result, postTarget) ∧ postTarget.ffi = postSource.ffi :=
  StackRemove.CompileSemantics.entrySimulation jump bounds pointer start clock
    source target postSource result relation run nonError

/-- Clock-preserving `StackRemove` initializer shift: if `initCode` finishes normally
(`(none, t)`) from `s2`, then for every clock `k`, calling procedure `0` on `s2` at clock
`k + 1` produces the exact same result and FFI state as calling `start` on `t` at clock `k`. -/
theorem stack_remove_init_clocked_shift {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer start : Nat)
    (s2 t : StackSemStateFiniteExact width C F) (k : Nat)
    (hentry : sptLookup 0 s2.code =
      some (.seq (StackRemove.initCode generateGc maxHeap pointer)
        (.call none (.inl start) none)))
    (hrun : StackSemEvaluate.evaluate (StackRemove.initCode generateGc maxHeap pointer, s2) =
      (none, t)) :
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { s2 with clock := k + 1 })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k })).1 ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { s2 with clock := k + 1 })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k })).2.ffi := by
  have clockRun := StackRemove.Proofs.InitClock.evaluateInitCodeClock
    generateGc maxHeap pointer s2 t none k hrun
  have body : StackSemEvaluate.evaluate
      (.seq (StackRemove.initCode generateGc maxHeap pointer) (.call none (.inl start) none),
        { s2 with clock := k }) =
      StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k }) := by
    rw [StackSemEvaluate.evaluate_seq, clockRun]
    simp [StackSemControl.fixClock]
  have notBad := StackRemove.Proofs.InitSemantics.callNotBad start { t with clock := k }
  rw [StackSemEvaluate.evaluate_call]
  simp only [StackSemControl.findCode, hentry, Nat.add_one_ne_zero, if_false,
    StackSemStateOps.decClock, Nat.add_sub_cancel]
  rw [show ({ ({ s2 with clock := k + 1 } : StackSemStateFiniteExact width C F) with
      clock := k } : StackSemStateFiniteExact width C F) = { s2 with clock := k } from rfl, body]
  simp only [StackSemControl.fixClock, notBad]
  exact ⟨rfl, rfl⟩

/-- Clock-preserving `StackNames` simulation: at any clock `k`, calling `start` on
`renameState c f s` produces the exact same result and FFI state as calling `start` on `s`
at the same clock `k`. -/
theorem stack_names_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F}
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f))
    (start k : Nat) :
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { StackNames.renameState c f s with clock := k })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k })).1 ∧
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { StackNames.renameState c f s with clock := k })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k })).2.ffi := by
  have h := StackNames.CompileSemantics.evaluate_entry_renameState
    (c := c) (f := f) (s := s) hf ha hs hk hc start k
  rw [h]
  exact ⟨rfl, rfl⟩

/-- Clocked `StackToLab` simulation: if a `StackSem` entry call at clock `k` finishes with
`FlattenSemantics.stackEntryClass res = .CompleteResult outcome`, then there exists `k'`
such that `LabSem.evaluate { s2 with clock := k + k' - 1 }` halts with `outcome` and the
same I/O events. -/
theorem stack_to_lab_clocked_halt {width : Nat} [NeZero width] {C F : Type}
    {start : Nat}
    {s1 : StackSemStateFiniteExact width C F}
    {s2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (halt : FlattenCallCorrect.haltAssum C F s1.code)
    (rel : StateRel.stateRel s1 s2)
    (hpc : LabSem.locToPc start 0 s2.code = some s2.pc)
    (k : Nat) (outcome : HolOutcome) (ev : List HolIoEvent)
    (hrun : FlattenSemantics.stackRuns start s1 k = (.CompleteResult outcome, ev)) :
    ∃ k',
      (LabSem.evaluate { s2 with clock := k + k' - 1 }).1 = .halt outcome ∧
      (LabSem.evaluate { s2 with clock := k + k' - 1 }).2.ffi.ioEvents = ev := by
  have hne : (CrepToLoopSemanticsRunRes.CompleteResult outcome :
      CrepToLoopSemanticsRunRes HolOutcome) ≠ .RunError := by
    intro h
    cases h
  obtain ⟨k', hlab⟩ := FlattenSemantics.stackRunsSim halt rel hpc k
    (.CompleteResult outcome) ev hrun hne
  refine ⟨k', ?_⟩
  simp only [FlattenSemantics.labRuns] at hlab
  rcases he : LabSem.evaluate { s2 with clock := k + k' - 1 } with ⟨m, next⟩
  rw [he] at hlab
  simp only [Prod.map, Prod.mk.injEq] at hlab
  obtain ⟨hm, rfl⟩ := hlab
  cases m with
  | halt o =>
    simp only [FlattenSemantics.labEntryClass,
      CrepToLoopSemanticsRunRes.CompleteResult.injEq] at hm
    subst hm
    exact ⟨rfl, rfl⟩
  | error => simp [FlattenSemantics.labEntryClass] at hm
  | timeOut => simp [FlattenSemantics.labEntryClass] at hm

/-- Clocked `fullMakeInit` simulation (`StackToLab` + `StackNames` + `StackRemove` +
`StackAlloc` + `StackRawCall`): if `fullMakeInit` succeeds (`= (s, opt)`) under `Assumptions`,
then any non-error `StackSem` entry call on `s` at clock `k` finishing with
`FlattenSemantics.stackEntryClass res = .CompleteResult outcome` produces a `LabSem.evaluate`
run on `t` at some clock `k_lab` that halts with `outcome` and the same I/O events! -/
theorem full_make_init_clocked_halt {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F}
    {opt : Option (StackSemStateFiniteExact width C F)}
    (hfm : FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t
      saveRegs dataSp coracle = (s, opt))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle)
    (k : Nat) (res : Option (StackSemResult width)) (s_post : StackSemStateFiniteExact width C F)
    (outcome : HolOutcome)
    (hrun : StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { s with clock := k }) = (res, s_post))
    (hclass : FlattenSemantics.stackEntryClass res = .CompleteResult outcome) :
    ∃ k_lab,
      (LabSem.evaluate { t with clock := k_lab }).1 = .halt outcome ∧
      (LabSem.evaluate { t with clock := k_lab }).2.ffi.ioEvents = s_post.ffi.ioEvents := by
  have hne : res ≠ some .error := by
    rintro rfl
    simp [FlattenSemantics.stackEntryClass] at hclass
  rw [fullMakeInit_eq] at hfm
  simp only [Prod.mk.injEq] at hfm
  obtain ⟨rfl, rfl⟩ := hfm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hgood, hgoodO, -, -, -, -, -, -, -, -⟩ := id hA
  have hdis := dischargeThese_s2 hA
  have hprop2 := propagateThese_s2 hA
  obtain ⟨⟨every, oracleBound, oracleEq, codeEq, k8, entry1, save, noStack, noStore, noAlloc,
    maxOk⟩, good, ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cbEmpty, le, al2, al4,
    albp, big, heap⟩ := And.intro hdis hprop2
  have codeRel : StackRemove.codeRelHOL stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).code :=
    StackRemove.Proofs.InitCodeRelation.impCodeRel stackConf.jump offset
      (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
      (code1 dataConf code) _ ⟨every, codeEq⟩
  have errLab : sptLookup StackRemove.stackErrLab
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).code =
      some (StackRemove.haltInst (BitVec.ofNat width 2)) := by
    rw [codeEq, sptLookup_sptFromAList]
    simp [StackRemove.compileHOL, StackRemove.initStubs, sptAListLookup, StackRemove.stackErrLab]
  have pre : StackRemove.Proofs.InitMake.initPre (StackToLab.isGenGc dataConf.gcKind) maxHeap
      bitmaps dataSp sp BvlToBvi.initGlobalsLocation
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) := by
    refine ⟨?_, ?_, maxOk⟩
    · rw [codeEq, sptLookup_sptFromAList]
      simp [StackRemove.compileHOL, StackRemove.initStubs, sptAListLookup]
    · have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
        rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
      rw [sub] at heap
      exact ⟨ptr2, ptr3, ptr4, bp, good, k8, entry1, save, noStack, noStore, noAlloc, r2, r3, r4,
        m0, m1, m2, m3, m4, le, big, al2, al4, albp, cbEmpty, heap⟩
  have hinit := StackRemove.Proofs.InitSemantics.evaluateInitCode
    (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp sp BvlToBvi.initGlobalsLocation
    (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
    stackConf.jump offset (coracle1 coracle) (sptFromAList (code1 dataConf code))
    ⟨pre, oracleEq, oracleBound, errLab, codeRel⟩
  revert hinit
  cases hinitRun : StackSemEvaluate.evaluate
      (StackRemove.initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp,
        s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) with
  | mk initRes t_rem =>
    cases initRes with
    | some _ => intro h; exact False.elim h
    | none =>
      rintro ⟨s1, hopt, rel_rem, _⟩
      have hs1 : StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind)
          maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
          (sptFromAList (code1 dataConf code))
          (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = s1 := by
        unfold StackRemove.Proofs.InitMake.makeInitAny
        rw [hopt]
      rw [hs1] at hrun
      obtain ⟨post, hpost, hprop⟩ := StackRemove.Proofs.InitAny.makeInitOpt_eq_some hopt
      -- Step 1: StackRawCall simulation from `s` (`makeInit dataConf (sptFromAList code) coracle s1`)
      obtain ⟨ck1, t_rc, hrun_rc, hffi_rc⟩ := stack_rawcall_clocked_sim code
        (StackAlloc.makeInit dataConf (sptFromAList code) coracle s1)
        BvlToBvi.initGlobalsLocation k res s_post hgood.1 rfl hrun hne
      have hm : { StackAlloc.makeInit dataConf (sptFromAList code) coracle s1 with
          code := sptFromAList (StackRawCall.compile code), clock := k + ck1 } =
          { StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1 with
            clock := k + ck1 } := by
        simp [StackAlloc.makeInit]
      rw [hm] at hrun_rc
      -- Step 2: StackAlloc simulation to `s1`
      have hu := StackRemove.Proofs.InitAny.makeInitAnyUseStack (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hus := StackRemove.Proofs.InitAny.makeInitAnyUseStore (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hua := StackRemove.Proofs.InitAny.makeInitAnyUseAlloc (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hcd := StackRemove.Proofs.InitAny.makeInitAnyCode (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hco := StackRemove.Proofs.InitAny.makeInitAnyCompileOracle
        (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      rw [hs1] at hu hus hua hcd hco
      have hcode_sa : ∀ k prog,
          sptLookup k (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).code = some prog →
          k ≠ gcStubLocation ∧ StackProps.allocArg prog := by
        intro k0 prog hk0
        simp only [StackAlloc.makeInit, sptLookup_sptFromAList] at hk0
        obtain ⟨⟨n0, p0⟩, hm0, he⟩ := List.mem_map.mp (sptAListLookup_mem hk0)
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨hst, hal⟩ := hgood.2.1 _ hm0
        exact ⟨by simp only [stackNumStubs, gcStubLocation] at hst ⊢; omega,
          (StackRawCall.callArgComp _ _).2.mpr hal⟩
      have horacle_sa : ∀ (i k : Nat) (q : HolProg width),
          (k, q) ∈ ((StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).compileOracle i).2.1 →
          k ≠ gcStubLocation ∧ StackProps.allocArg q := by
        intro i k0 q hq
        obtain ⟨hst, hal⟩ := (hgoodO i).2.1 _ hq
        exact ⟨by simp only [stackNumStubs, gcStubLocation] at hst ⊢; omega, hal⟩
      rcases hprop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hdb, _, _, _, hbl, _, _, _, _, _, hsb, _⟩
      have hbuf_sa : (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).bitmaps.length +
          (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).dataBuffer.buffer.length +
          (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).dataBuffer.spaceLeft <
          2 ^ width - 1 := by
        subst hpost
        simp only [StackAlloc.makeInit, StackRemove.Proofs.InitReduce.initReduce, List.length_nil, Nat.add_zero] at hbl hdb ⊢
        omega
      have hst_sa : (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).stack.length *
          (width / 8) < 2 ^ width := by
        subst hpost
        exact hsb
      have hnodup_rc : ((StackRawCall.compile code).map Prod.fst).Nodup := by
        rw [StackRawCall.mapFstCompile]; exact hgood.1
      obtain ⟨ck2, hrun_sa1, hffi_sa⟩ := stack_alloc_clocked_sim
        (s := StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1)
        (c := dataConf) (compile_rest := s1.compile) (start := BvlToBvi.initGlobalsLocation)
        (anything := s1.gcFun)
        hcode_sa horacle_sa rfl hbuf_sa hst_sa rfl rfl rfl (k + ck1) res t_rc hrun_rc hne
      let m_sa := StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1
      have hs1_eq : { m_sa with
          code := sptFromAList (StackAlloc.compile dataConf (sptToAList m_sa.code))
          gcFun := s1.gcFun
          compile := s1.compile
          compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ m_sa.compileOracle
          useStore := true, useStack := true, useAlloc := false, clock := k + ck1 + ck2 } =
          { s1 with clock := k + ck1 + ck2 } := by
        have hcc : sptFromAList (StackAlloc.compile dataConf
            (sptToAList (sptFromAList (StackRawCall.compile code)))) = s1.code := by
          rw [hcd, code1]
          refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
          rw [StackAlloc.CompCorrect.sptLookup_compile, StackAlloc.CompCorrect.sptLookup_compile,
            StackAlloc.ProgCompSupport.sptAListLookup_sptToAList, sptLookup_sptFromAList]
        cases s1
        simp only [m_sa, StackAlloc.makeInit, coracle1] at hcc hco hus hu hua ⊢
        simp only [Bool.not_eq_true] at hua
        subst hus hu hua
        rw [hcc, hco]
      change (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { m_sa with
            code := sptFromAList (StackAlloc.compile dataConf (sptToAList m_sa.code))
            gcFun := s1.gcFun
            compile := s1.compile
            compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ m_sa.compileOracle
            useStore := true, useStack := true, useAlloc := false, clock := k + ck1 + ck2 })).1 = res at hrun_sa1
      change (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { m_sa with
            code := sptFromAList (StackAlloc.compile dataConf (sptToAList m_sa.code))
            gcFun := s1.gcFun
            compile := s1.compile
            compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ m_sa.compileOracle
            useStore := true, useStack := true, useAlloc := false, clock := k + ck1 + ck2 })).2.ffi = t_rc.ffi at hffi_sa
      rw [hs1_eq] at hrun_sa1 hffi_sa
      rcases hrun_s1 : StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { s1 with clock := k + ck1 + ck2 }) with ⟨res_s1, post_s1⟩
      rw [hrun_s1] at hrun_sa1 hffi_sa
      simp only at hrun_sa1 hffi_sa
      subst res_s1
      -- Step 3: StackRemove body simulation from `s1` to `t_rem`
      obtain ⟨ck3, post_rem, hrun_rem, hffi_rem⟩ := stack_remove_clocked_sim
        stackConf.jump offset sp BvlToBvi.initGlobalsLocation (k + ck1 + ck2)
        s1 t_rem post_s1 res rel_rem hrun_s1 hne
      -- Step 4: StackRemove initCode shift (+1) from `t_rem` at `BvlToBvi.initGlobalsLocation` to `s2` at `0`
      have hshift := stack_remove_init_clocked_shift
        (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) t_rem
        (ck3 + (k + ck1 + ck2)) pre.1 hinitRun
      -- Step 5: StackNames agreement from `s2` to `s3` at `0`
      let s3_st := s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle
      let s2_st := s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle
      have hbij := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hnames := stack_names_clocked_agree
        (c := s3_st.compile)
        (f := stackConf.regNames)
        (s := s2_st)
        hbij
        (by simp [s2_st, noAlloc])
        (by simp [s2_st, noStore])
        (by simp [s2_st, noStack])
        rfl 0 (ck3 + (k + ck1 + ck2) + 1)
      have hs3_def : StackNames.renameState s3_st.compile stackConf.regNames s2_st = s3_st := by
        have hinv : ∀ y, StackNames.findNameSpt stackConf.regNames
            (holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) y) = y :=
          apply_holLinv_of_surjective hbij.2
        have hc : sptFromAList (StackNames.compileHOL stackConf.regNames
            (sptToAList (sptFromAList (code2 stackConf dataConf maxHeap sp offset code)))) =
            s3_st.code := by
          change _ = sptFromAList (StackNames.compileHOL stackConf.regNames
            (code2 stackConf dataConf maxHeap sp offset code))
          refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
          rw [sptLookup_sptFromAList, StackNames.sptAListLookup_compileHOL, ← sptLookup_sptFromAList,
            sptLookup_sptFromAList_sptToAList, sptLookup_sptFromAList, sptLookup_sptFromAList,
            StackNames.sptAListLookup_compileHOL]
        classical
        have hsave : (fun y => decide (∃ x, decide (∃ z, s3_st.ffiSaveRegs z = true ∧
            x = holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) z) = true ∧
            y = StackNames.findNameSpt stackConf.regNames x)) = s3_st.ffiSaveRegs := by
          funext y
          by_cases hy : s3_st.ffiSaveRegs y = true
          · rw [hy, decide_eq_true_iff]
            exact ⟨holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) y,
              decide_eq_true_iff.mpr ⟨y, hy, rfl⟩, (hinv y).symm⟩
          · rw [Bool.not_eq_true] at hy
            rw [hy, decide_eq_false_iff_not]
            rintro ⟨x, hx, rfl⟩
            obtain ⟨z, hz, rfl⟩ := decide_eq_true_iff.mp hx
            rw [hinv z, hz] at hy
            exact Bool.noConfusion hy
        have hor : s3_st.compileOracle =
            Prod.map id (Prod.map (StackNames.compileHOL stackConf.regNames) id) ∘
              coracle2 stackConf sp offset coracle := rfl
        simp only [s2_st, s2, StackNames.renameState, StackNames.makeInit,
          StackNames.MakeInit.mapKeys_mapKeys_linv hbij, hc, ← hor]
        refine Eq.trans ?_ (show { s3_st with ffiSaveRegs := s3_st.ffiSaveRegs } = s3_st from rfl)
        congr 1
      rw [hs3_def] at hnames
      -- Step 6: StackToLab simulation from `s3` at `0` to `t`
      have hruns_s3 : FlattenSemantics.stackRuns 0
          (s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
          (ck3 + (k + ck1 + ck2) + 1) =
          (.CompleteResult outcome, s_post.ffi.ioEvents) := by
        simp only [FlattenSemantics.stackRuns, Prod.map]
        rcases hev_s3 : StackSemEvaluate.evaluate
          ((.call none (.inl 0) none : HolProg width),
            { s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
              clock := ck3 + (k + ck1 + ck2) + 1 }) with ⟨r_s3, p_s3⟩
        have hnames1 := hnames.1
        change (StackSemEvaluate.evaluate
          ((.call none (.inl 0) none : HolProg width),
            { s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
              clock := ck3 + (k + ck1 + ck2) + 1 })).1 =
          (StackSemEvaluate.evaluate
            ((.call none (.inl 0) none : HolProg width),
              { s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
                clock := ck3 + (k + ck1 + ck2) + 1 })).1 at hnames1
        have hnames2 := hnames.2
        change (StackSemEvaluate.evaluate
          ((.call none (.inl 0) none : HolProg width),
            { s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
              clock := ck3 + (k + ck1 + ck2) + 1 })).2.ffi =
          (StackSemEvaluate.evaluate
            ((.call none (.inl 0) none : HolProg width),
              { s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
                clock := ck3 + (k + ck1 + ck2) + 1 })).2.ffi at hnames2
        have hr_eq : r_s3 = res := by
          rw [hev_s3, hshift.1, hrun_rem] at hnames1
          exact hnames1
        have hffi_eq : p_s3.ffi = s_post.ffi := by
          rw [hev_s3, hshift.2, hrun_rem] at hnames2
          exact hnames2.trans (hffi_rem.trans (hffi_sa.trans hffi_rc))
        rw [hr_eq, hclass, hffi_eq]
      obtain ⟨k', hhalt, hev_lab⟩ := stack_to_lab_clocked_halt
        MakeInit.haltAssumLemma (stateRel_s3 hA) (locToPc_start hA)
        (ck3 + (k + ck1 + ck2) + 1) outcome s_post.ffi.ioEvents hruns_s3
      exact ⟨(ck3 + (k + ck1 + ck2) + 1) + k' - 1, hhalt, hev_lab⟩

private theorem sptAListLookup_eq_local {α : Type} (key : Nat) :
    ∀ entries : List (Nat × α), sptAListLookup key entries = panPropsALookupEq key entries
  | [] => rfl
  | (other, value) :: entries => by
      simp only [sptAListLookup, panPropsALookupEq, sptAListLookup_eq_local key entries]
      by_cases h : key = other
      · subst h; simp
      · simp [h, Ne.symm h]

private theorem mem_of_lookup_local {α : Type} {key : Nat} {value : α} :
    ∀ {entries : List (Nat × α)}, panPropsALookupEq key entries = some value →
      (key, value) ∈ entries
  | [], h => by simp [panPropsALookupEq] at h
  | (other, v) :: entries, h => by
      simp only [panPropsALookupEq] at h
      by_cases ho : other = key
      · subst ho
        simp only [decide_true, if_true, Option.some.injEq] at h
        subst h
        exact List.mem_cons_self
      · simp only [ho, decide_false, Bool.false_eq_true, if_false] at h
        exact List.mem_cons_of_mem _ (mem_of_lookup_local h)

/-- Top-level `WordToStack.Native` clocked simulation under `wordLangSafeForSpace`:
from `initStateOk` and the `compileNative` conventions, a non-error `WordSem` entry call
on `makeInit asmConf k t (sptFromAList code) coracle` at clock `clk` yields a `StackSem`
entry call on `t` at clock `clk + ck` with mapped result and identical FFI state. -/
theorem word_to_stack_compile_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start clk : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (codeEq : t.code = sptFromAList (WordToStack.Native.compileNative asmConf false code).2.2.2)
    (kEq : k = asmConf.regCount - (5 + asmConf.avoidRegs.length))
    (ok : WordToStackProofs.InitializationStateRel.initStateOk asmConf k t coracle)
    (noRaise : panPropsALookupEq raiseStubLocation code = none)
    (noStore : panPropsALookupEq storeConstsStubLocation code = none)
    (bitmapsPrefix : (WordToStack.Native.compileNative asmConf false code).1 <+: t.bitmaps)
    (conventions : ∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
        entry.2.2 = true)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace
      (WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle) start)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
        clock := clk } = (res, s1))
    (hne : res ≠ some .error) :
    ∃ ck t1,
      StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := clk + ck }) =
        (res.map WordToStackProofs.CompCorrect.compileResult, t1) ∧
      s1.ffi = t1.ffi := by
  subst kEq
  rcases compiled : WordToStack.Native.compileWordToStackNative asmConf false
      (asmConf.regCount - (5 + asmConf.avoidRegs.length)) code (.list [4], 1) with
    ⟨bodies, frames, output, nextIndex⟩
  simp only [WordToStack.Native.compileNative, Bool.false_eq_true, if_false, compiled]
    at codeEq bitmapsPrefix
  have keys := Flapjack.WordToStackProofs.mapFstCompileWordToStack asmConf false _ code (.list [4], 1)
    bodies (frames, (output, nextIndex)) compiled
  have stubsDistinct : raiseStubLocation ≠ storeConstsStubLocation := by
    simp [raiseStubLocation, storeConstsStubLocation, wordNumStubs]
  have related : WordToStackProofs.stateRel asmConf
      (asmConf.regCount - (5 + asmConf.avoidRegs.length)) 0 0
      (WordToStack.Native.Initialization.makeInit asmConf
        (asmConf.regCount - (5 + asmConf.avoidRegs.length)) t (sptFromAList code)
        coracle : WordSemStateFiniteExact width (Nat × C) F)
      t [] 0 := by
    apply WordToStackProofs.InitializationStateRel.initStateOkImpliesStateRel
    refine ⟨?_, ?_, ?_, ?_, ok⟩
    · rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq_local]
      simp [panPropsALookupEq]
    · rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq_local]
      simp [panPropsALookupEq, stubsDistinct]
    · intro n wordProg argumentCount lookup
      rw [sptLookup_sptFromAList, sptAListLookup_eq_local] at lookup
      have member := mem_of_lookup_local lookup
      obtain ⟨flat, allocated⟩ := conventions _ member
      obtain ⟨bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, bodyLookup⟩ :=
        WordToStack.Native.compileWordToStackImpALookup asmConf false _ code (.list [4]) 1
          bodies frames output nextIndex n argumentCount wordProg t.bitmaps compiled lookup
          (by simp [appListAppend, appendAux]) (by simp [appListAppend, appendAux])
          (by simpa [appListAppend, appendAux] using bitmapsPrefix)
      refine ⟨allocated, flat, bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, ?_⟩
      have notRaise : n ≠ raiseStubLocation := by
        rintro rfl
        rw [noRaise] at lookup
        cases lookup
      have notStore : n ≠ storeConstsStubLocation := by
        rintro rfl
        rw [noStore] at lookup
        cases lookup
      rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq_local]
      simp [panPropsALookupEq, Ne.symm notRaise, Ne.symm notStore, bodyLookup]
    · rw [codeEq, sptDomainFromAList, sptDomainFromAList]
      funext x
      simp only [List.map_cons, List.mem_cons, keys]
  exact word_to_stack_clocked_sim asmConf (asmConf.regCount - (5 + asmConf.avoidRegs.length))
    _ t start clk res s1 related safe hrun hne

/-- Clocked backend chain (`WordToWord` + `WordToStack` + `FullMakeInit` + `LabToTarget`)
under the `optionLt stackMax (some (readLimits ...).1)` resource bound:
from a halting `WordSem` entry call on `wst0` (compiled from `panCode` by `PanToWord`) at
clock `k_word` with `semTermOutcome res outcome`, the initial `labst` halts at some clock `k_lab`
and the target machine halts at `k_lab + extra` with the same outcome and FFI state. -/
theorem pan_to_target_backend_clocked_halt {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapPtr : BitVec width) (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (panCode : List (Pancake.PanLang.DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (dataSp : Nat) (stackMax : Option Nat)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : LabToTarget.mcConfOk mc)
    (hinit : BackendProof.mcInitOk mc.target.config c mc) (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hlab : LabToTarget.compile mc.target.config c.labConf
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset p) = some (bytes, ltconf))
    (hmax : stackMax = WordDepth.maxDepth wconf.stackFrameSize
      (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wprog)))
    (hnodup : ((Pancake.PanLang.functionsHOL panCode).map Prod.fst).Nodup)
    (hffiOk : match c.labConf.ffiNames with
      | none => True
      | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s)
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapsDm w) sdm)
    (hffiN : ltconf.ffiNames = some mc.ffiNames)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      ltconf.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
        mc.mmioInfo = List.zip ((List.range ltconf.shmemExtra.length).map (fun index => index + i))
          (ltconf.shmemExtra.map fun rec => (rec.nbytes,
            HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff),
            rec.reg, BitVec.ofNat width rec.exitPc + mc.target.getPc ms)) ∧
        cbspace + bytes.length + LabToTarget.ffiOffset * (i + 3) < 2 ^ width)
    (hsource : pancakeGoodCodeHOL panCode = true)
    (hpi :
      let regNames := c.stackConf.regNames
      let r1 := StackNames.findNameSpt regNames 2
      let r2 := StackNames.findNameSpt regNames 4
      let biw := StackRemove.bytesInWord width
      let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
      holByteAligned (t.regs r1) = true ∧ holByteAligned (t.regs r2) = true ∧
      holByteAligned bitmapPtr = true ∧ t.regs r1 ≤ t.regs r2 ∧
      1024 * biw ≤ t.regs r2 - t.regs r1 ∧
      (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
      m (t.regs r1) = .word bitmapPtr ∧
      m (t.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width dataSp +
        biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
      m (t.regs r1 + 4 * biw) =
        .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
      SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
        (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) dataSp)
        (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)))
    (hlo : mc.target.getReg ms mc.lenReg +
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ≤
        mc.target.getReg ms mc.ptr2Reg)
    (hhi : mc.target.getReg ms mc.ptr2Reg ≤ mc.target.getReg ms mc.len2Reg -
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc)
    (hheap : (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1))
    (hheapLt : (StackRemove.bytesInWord width).toNat *
      (2 * DataToWord.maxHeapLimit width c.dataConf - 1) < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true)
    (hresLimit : optionLt stackMax
      (some (BackendProof.readLimits mc.target.config c mc ms).1) = true)
    (hsem : WordSemStateFiniteExact.semantics
      (let regNames := c.stackConf.regNames
       let r1 := StackNames.findNameSpt regNames 2
       let r2 := StackNames.findNameSpt regNames 4
       let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
       let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
       let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
       let labst := LabToTarget.makeInit (C := LabToTarget.Config) mc ffi t m
         (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
         (fun a => sdm a && holByteAligned a) ms
         (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
         (LabToTarget.compile mc.target.config)
         (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
         (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
           mc.target.config.addrOffset sp []))
       let sst := (FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
         mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
         dataSp (fun _ => (ltconf, [], []))).1
       WordToStack.Native.Initialization.makeInit mc.target.config
         (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
         (sptFromAList wprog)
         (fun _ => ((bitmaps.length, ltconf), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width))))))
      BvlToBvi.initGlobalsLocation ≠ .fail)
    (k_word : Nat) (res : Option (WordSemResult width)) (outcome : HolOutcome)
    (s_word_post : WordSemStateFiniteExact width (Nat × LabToTarget.Config) σ)
    (hres_ok : match res with
      | some (.finalFfi e) => outcome = .ffiOutcome e
      | some (.result (WordLocW.loc 1 0) _) => outcome = .success
      | some .notEnoughSpace => outcome = .resourceLimitHit
      | _ => False)
    (hrun_w0 : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { (let regNames := c.stackConf.regNames
         let r1 := StackNames.findNameSpt regNames 2
         let r2 := StackNames.findNameSpt regNames 4
         let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
         let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
         let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
         let labst := LabToTarget.makeInit (C := LabToTarget.Config) mc ffi t m
           (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
           (fun a => sdm a && holByteAligned a) ms
           (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
           (LabToTarget.compile mc.target.config)
           (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
           (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
             mc.target.config.addrOffset sp []))
         let sst := (FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
           mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
           dataSp (fun _ => (ltconf, [], []))).1
         let wst := WordToStack.Native.Initialization.makeInit mc.target.config
           (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
           (sptFromAList wprog)
           (fun _ => ((bitmaps.length, ltconf), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width)))))
         { wst with code := sptFromAList (panToWordCompileProgHOL mc.target.config.isa panCode) })
        with clock := k_word } = (res, s_word_post)) :
    ∃ k_target ms2 ffi2,
      evaluateTargetHOL mc ffi k_target ms = (.halt outcome, ms2, ffi2) ∧
      ffi2.ioEvents = s_word_post.ffi.ioEvents := by
  let regNames := c.stackConf.regNames
  let r1 := StackNames.findNameSpt regNames 2
  let r2 := StackNames.findNameSpt regNames 4
  let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
  let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
  let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
  let labst := LabToTarget.makeInit (C := LabToTarget.Config) mc ffi t m
    (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
    (fun a => sdm a && holByteAligned a) ms
    (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
    (LabToTarget.compile mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
    (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
      mc.target.config.addrOffset sp []))
  let sst := (FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
    mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
    dataSp (fun _ => (ltconf, [], []))).1
  let k_reg := mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)
  let worac : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
    fun _ => ((bitmaps.length, ltconf), [])
  let wst := WordToStack.Native.Initialization.makeInit mc.target.config k_reg sst
    (sptFromAList wprog) worac
  let wst0 := { wst with code := sptFromAList (panToWordCompileProgHOL mc.target.config.isa panCode) }
  have hA := Flapjack.Pancake.Proofs.PanToTarget.panToTargetFullMakeInitAssumptions
    (C := LabToTarget.Config) c mc ffi t m bitmapPtr bitmapsDm sdm ms
    (LabToTarget.compile mc.target.config) bytes cbspace ltconf panCode col wprog bitmaps wconf
    fs p dataSp hcfg hmc hinit hisa hwtw hwts hnodup hpi
  rcases hfm : FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
      mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
      dataSp (fun _ => (ltconf, [], [])) with ⟨sst', opt⟩
  have e_sst : sst = sst' := by simp only [sst, hfm]
  obtain ⟨hopt, -⟩ := fullMakeInitSemantics (s := sst') (opt := opt) ⟨hfm, hA⟩
  obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.mp hopt
  obtain ⟨hbmS, hcodeS⟩ := Flapjack.Pancake.Proofs.PanToTarget.fullMakeInit_bitmaps_code
    c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset bitmaps p labst _ dataSp _
    sst' x hfm
  have hinitS := Flapjack.Pancake.Proofs.PanToTarget.panToTargetInitStateOk mc.target.config
    wprog bitmaps wconf fs p ltconf c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset
    labst (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp sst' x hmc.1 hcfg.2.2.2.1 hwts hfm
  rw [Nat.add_comm mc.target.config.avoidRegs.length 5] at hinitS
  obtain ⟨hgc, -, -, -⟩ := Flapjack.Pancake.Proofs.PanToTarget.panToTargetWordStateFacts
    mc.target.config k_reg (sptFromAList wprog) worac c.stackConf c.dataConf maxHeap sp
    mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
    dataSp _ sst' x hfm
  obtain ⟨hraise, hstore⟩ := Flapjack.Pancake.Proofs.PanToTarget.panToTargetStubLocationsFree
    c.wordToWordConf mc.target.config panCode col wprog hisa hwtw
  have hconv := (BackendProof.compileToWordConventions2 c.wordToWordConf mc.target.config _ col
    wprog hwtw (fun _ _ => Or.inr hisa)).2.2
  have hsem' : (WordToStack.Native.Initialization.makeInit mc.target.config k_reg sst'
      (sptFromAList wprog) worac).semantics BvlToBvi.initGlobalsLocation ≠ .fail := by
    change wst.semantics BvlToBvi.initGlobalsLocation ≠ .fail at hsem
    simpa only [wst, e_sst] using hsem
  have hsafe := Flapjack.Pancake.Proofs.PanToTarget.panToTargetResourceLimitOfSemantics
    c mc ms panCode col wprog bitmaps wconf fs p stackMax worac hwtw hnodup hwts hmax hA hfm
    (Flapjack.Pancake.Proofs.PanToTarget.panToTargetLabRegWord mc ffi t _ _ _ ms _
      (LabToTarget.compile mc.target.config) _ cbspace _ hgi.1 _ hmc.2.2.2.1)
    (Flapjack.Pancake.Proofs.PanToTarget.panToTargetLabRegWord mc ffi t _ _ _ ms _
      (LabToTarget.compile mc.target.config) _ cbspace _ hgi.1 _ hmc.2.2.2.2.1)
    (Flapjack.Pancake.Proofs.PanToTarget.panToTargetLabRegWord mc ffi t _ _ _ ms _
      (LabToTarget.compile mc.target.config) _ cbspace _ hgi.1 _ hmc.2.2.2.2.2.1)
    hlo hhi hheap hheapLt halign hsem' hresLimit
  have hne0 : res ≠ some .error := by
    intro herr
    rw [herr] at hres_ok
    exact hres_ok
  have hrun_w0' : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { wst0 with clock := k_word }).1 ≠ some .error := by
    rw [hrun_w0]
    exact hne0
  have hww := word_to_word_clocked_agree c.wordToWordConf mc.target.config
    (panToWordCompileProgHOL mc.target.config.isa panCode) col wprog wst0
    BvlToBvi.initGlobalsLocation k_word hwtw
    (by simpa only [wst0, wst, e_sst] using hgc)
    (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_alloc_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl)
    (by simp [wst0, wst, WordToStack.Native.Initialization.makeInit])
    rfl hrun_w0'
  rcases hrun_w : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { wst with clock := k_word } with ⟨res_w, s_w_post⟩
  have hres_w : res_w = res := by
    have h1 := hww.1
    change (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { wst with clock := k_word }).1 =
      (WordSemStateFiniteExact.evaluate
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
        { wst0 with clock := k_word }).1 at h1
    rw [hrun_w, hrun_w0] at h1
    exact h1
  have hffi_w : s_w_post.ffi = s_word_post.ffi := by
    have h2 := hww.2
    change (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { wst with clock := k_word }).2.ffi =
      (WordSemStateFiniteExact.evaluate
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
        { wst0 with clock := k_word }).2.ffi at h2
    rw [hrun_w, hrun_w0] at h2
    exact h2
  rw [hres_w] at hrun_w
  obtain ⟨ck_wts, t_stack_post, hrun_stack, hffi_wts⟩ := word_to_stack_compile_clocked_sim
    mc.target.config wprog sst' k_reg worac BvlToBvi.initGlobalsLocation k_word res s_w_post
    (by rw [hwts, hcodeS]) rfl hinitS hraise hstore (by rw [hwts, hbmS])
    (fun entry he => ⟨(hconv entry he).1, (hconv entry he).2.1⟩)
    hsafe (by simpa only [wst, e_sst] using hrun_w) hne0
  have hclass_stack : FlattenSemantics.stackEntryClass
      (res.map WordToStackProofs.CompCorrect.compileResult) =
      CrepToLoopSemanticsRunRes.CompleteResult outcome := by
    rcases res with _ | r_val
    · cases hres_ok
    · cases r_val with
      | result ret_loc _ =>
        by_cases hloc : ret_loc = WordLocW.loc 1 0
        · subst hloc
          simp only at hres_ok
          subst hres_ok
          simp [FlattenSemantics.stackEntryClass, WordToStackProofs.CompCorrect.compileResult]
        · simp [hloc] at hres_ok
      | notEnoughSpace =>
        simp only at hres_ok
        subst hres_ok
        rcases hmc.1 with rfl | rfl <;>
          simp [FlattenSemantics.stackEntryClass, WordToStackProofs.CompCorrect.compileResult]
      | finalFfi e_ffi =>
        simp only at hres_ok
        subst hres_ok
        simp [FlattenSemantics.stackEntryClass, WordToStackProofs.CompCorrect.compileResult]
      | exception _ _ => cases hres_ok
      | timeOut => cases hres_ok
      | «break» _ => cases hres_ok
      | «continue» _ => cases hres_ok
      | error => cases hres_ok
  obtain ⟨k_lab, hhalt_lab, hev_lab⟩ := full_make_init_clocked_halt hfm hA (k_word + ck_wts)
    (res.map WordToStackProofs.CompCorrect.compileResult) t_stack_post outcome
    hrun_stack hclass_stack
  rcases hlab_ev : LabSem.evaluate { labst with clock := k_lab } with ⟨res_lab, next_lab⟩
  rw [hlab_ev] at hhalt_lab hev_lab
  obtain ⟨extra_t, ms2, htarget⟩ := pan_to_target_machine_lab_clocked_halt c mc ffi t m
    bitmapsDm sdm ms bytes cbspace panCode col wprog bitmaps wconf fs p ltconf
    hcfg hmc hisa hwtw hwts hlab hnodup hffiOk hgi hffiN hmmio hsource k_lab outcome next_lab
    (hlab_ev.trans (Prod.ext hhalt_lab rfl))
  refine ⟨k_lab + extra_t, ms2, next_lab.ffi, htarget, ?_⟩
  rw [hev_lab, ← hffi_wts, hffi_w]

/-- Two non-`.timeOut` `WordSemStateFiniteExact.evaluate` runs on the same program and state
(at clocks `k` and `k'`) produce the exact same result and FFI state (`evaluate_add_clock`). -/
theorem wordEvaluateIgnoreClocks {width : Nat} [NeZero width] {C F : Type}
    (prog : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (k k' : Nat) (r1 r2 : Option (WordSemResult width))
    (post1 post2 : WordSemStateFiniteExact width C F)
    (h1 : WordSemStateFiniteExact.evaluate prog { s with clock := k } = (r1, post1))
    (hnt1 : r1 ≠ some .timeOut)
    (h2 : WordSemStateFiniteExact.evaluate prog { s with clock := k' } = (r2, post2))
    (hnt2 : r2 ≠ some .timeOut) :
    r1 = r2 ∧ post1.ffi = post2.ffi := by
  have ha1 := WordSemStateFiniteExact.evaluate_add_clock k' prog { s with clock := k } r1 post1
    ⟨h1, hnt1⟩
  have ha2 := WordSemStateFiniteExact.evaluate_add_clock k prog { s with clock := k' } r2 post2
    ⟨h2, hnt2⟩
  simp only [Nat.add_comm k' k] at ha2
  rw [ha1] at ha2
  injection ha2 with hr hpost
  have hffi := congrArg WordSemStateFiniteExact.ffi hpost
  exact ⟨hr, hffi⟩

/-- Under `WordSemStateFiniteExact.semantics s start = .terminate outcome events`, any clock `k`
at which `(WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) { s with clock := k }).1 ≠ some .timeOut`
completes with `semTermOutcome res outcome` and `post.ffi.ioEvents = events`! -/
theorem word_halt_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (start : Nat)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hsem : WordSemStateFiniteExact.semantics s start = .terminate outcome events)
    (k : Nat) (res : Option (WordSemResult width))
    (post : WordSemStateFiniteExact width C F)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k } = (res, post))
    (hnt : res ≠ some .timeOut) :
    (match res with
      | some (.finalFfi e) => outcome = .ffiOutcome e
      | some (.result (WordLocW.loc 1 0) _) => outcome = .success
      | some .notEnoughSpace => outcome = .resourceLimitHit
      | _ => False) ∧
    post.ffi.ioEvents = events := by
  have hsem0 := hsem
  unfold WordSemStateFiniteExact.semantics at hsem
  dsimp only at hsem
  split at hsem
  · cases hsem
  · rename_i hnobad
    split at hsem
    · rename_i b hsome
      subst hsem
      obtain ⟨k0, post0, res0, out0, hrun0, hm0, heq⟩ := holOptionSome_some hsome
      injection heq with hout0 hev0
      subst hout0 hev0
      have hnt0 : res0 ≠ some .timeOut := by
        intro h; subst h; exact hm0
      obtain ⟨hr, hffi⟩ := wordEvaluateIgnoreClocks (.call none (some start) [0] none)
        s k k0 res res0 post post0 hrun hnt hrun0 hnt0
      subst hr
      refine ⟨?_, congrArg HolFfiState.ioEvents hffi⟩
      rcases res with _ | r_val
      · exact hm0
      · cases r_val with
        | result ret_loc ys =>
          by_cases hloc : ret_loc = WordLocW.loc 1 0
          · subst hloc; exact hm0
          · exfalso
            apply hnobad
            refine ⟨k, ?_⟩
            rw [hrun]
            exact hloc
        | _ => exact hm0
    · cases hsem

/-- Two non-`.timeOut` `StackSemEvaluate.evaluate` runs on the same program and state
(at clocks `k` and `k'`) produce the exact same result and FFI state (`StackProps.evaluateAddClock`). -/
theorem stackEvaluateIgnoreClocks {width : Nat} [NeZero width] {C F : Type}
    (prog : HolProg width)
    (s : StackSemStateFiniteExact width C F)
    (k k' : Nat) (r1 r2 : Option (StackSemResult width))
    (post1 post2 : StackSemStateFiniteExact width C F)
    (h1 : StackSemEvaluate.evaluate (prog, { s with clock := k }) = (r1, post1))
    (hnt1 : r1 ≠ some .timeOut)
    (h2 : StackSemEvaluate.evaluate (prog, { s with clock := k' }) = (r2, post2))
    (hnt2 : r2 ≠ some .timeOut) :
    r1 = r2 ∧ post1.ffi = post2.ffi := by
  have ha1 := StackProps.evaluateAddClock k' prog { s with clock := k } r1 post1 ⟨h1, hnt1⟩
  have ha2 := StackProps.evaluateAddClock k prog { s with clock := k' } r2 post2 ⟨h2, hnt2⟩
  simp only [Nat.add_comm k' k] at ha2
  rw [ha1] at ha2
  injection ha2 with hr hpost
  have hffi := congrArg StackSemStateFiniteExact.ffi hpost
  exact ⟨hr, hffi⟩

/-- Under `StackSemEvaluate.semantics start s = .terminate outcome events`, any clock `k`
at which `(StackSemEvaluate.evaluate ((.call none (.inl start) none), { s with clock := k })).1 ≠ some .timeOut`
completes with `FlattenSemantics.stackEntryClass res = .CompleteResult outcome` and
`post.ffi.ioEvents = events`! -/
theorem stack_halt_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (start : Nat)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hsem : StackSemEvaluate.semantics start s = .terminate outcome events)
    (k : Nat) (res : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (hrun : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s with clock := k }) = (res, post))
    (hnt : res ≠ some .timeOut) :
    FlattenSemantics.stackEntryClass res = .CompleteResult outcome ∧
    post.ffi.ioEvents = events := by
  rw [FlattenSemantics.stackSemIsWrapper] at hsem
  unfold crepToLoopSemanticsWrapper at hsem
  by_cases herr : ∃ k v, FlattenSemantics.stackRuns start s k = (.RunError, v)
  · rw [if_pos herr] at hsem; cases hsem
  · rw [if_neg herr] at hsem
    cases hsome : holOptionSome (fun res => ∃ k r ev,
        FlattenSemantics.stackRuns start s k = (.CompleteResult r, ev) ∧
        res = HolBehaviour.terminate r ev) with
    | none => rw [hsome] at hsem; cases hsem
    | some b =>
      rw [hsome] at hsem
      subst hsem
      obtain ⟨k0, out0, ev0, hk0, heq⟩ := holOptionSome_some hsome
      injection heq with hout0 hev0
      subst hout0 hev0
      simp only [FlattenSemantics.stackRuns] at hk0
      rcases hrun0 : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k0 }) with ⟨res0, post0⟩
      rw [hrun0] at hk0
      simp only [Prod.map, Prod.mk.injEq] at hk0
      obtain ⟨hclass0, rfl⟩ := hk0
      have hnt0 : res0 ≠ some .timeOut := by
        intro h; subst h; simp [FlattenSemantics.stackEntryClass] at hclass0
      obtain ⟨hr, hffi⟩ := stackEvaluateIgnoreClocks (.call none (.inl start) none)
        s k k0 res res0 post post0 hrun hnt hrun0 hnt0
      exact ⟨hr ▸ hclass0, congrArg HolFfiState.ioEvents hffi⟩

/-- Syntactic predicate characterizing `StackLang` programs that `StackAlloc.comp` leaves
completely unchanged (no `.alloc`, no `.storeConsts _ _ (some _)`, and no handler on tail calls). -/
def noAllocOrStoreConsts {width : Nat} [NeZero width] : HolProg width → Bool
  | .seq p1 p2 => noAllocOrStoreConsts p1 && noAllocOrStoreConsts p2
  | .ite _ _ _ p1 p2 => noAllocOrStoreConsts p1 && noAllocOrStoreConsts p2
  | .loop p1 => noAllocOrStoreConsts p1
  | .call none _ none => true
  | .call none _ (some _) => false
  | .call (some (p1, _, _, _)) _ none => noAllocOrStoreConsts p1
  | .call (some (p1, _, _, _)) _ (some (p2, _, _)) =>
      noAllocOrStoreConsts p1 && noAllocOrStoreConsts p2
  | .alloc _ => false
  | .storeConsts _ _ (some _) => false
  | _ => true

/-- When `noAllocOrStoreConsts p = true`, `StackAlloc.comp n m p` is the exact identity `(p, m)`. -/
theorem stack_alloc_comp_eq_self {width : Nat} [NeZero width] :
    ∀ (n m : Nat) (p : HolProg width),
      noAllocOrStoreConsts p = true → StackAlloc.comp n m p = (p, m)
  | n, m, .seq p1 p2, h => by
      simp only [noAllocOrStoreConsts, Bool.and_eq_true] at h
      simp only [StackAlloc.comp, stack_alloc_comp_eq_self n m p1 h.1,
        stack_alloc_comp_eq_self n m p2 h.2]
  | n, m, .ite c r ri p1 p2, h => by
      simp only [noAllocOrStoreConsts, Bool.and_eq_true] at h
      simp only [StackAlloc.comp, stack_alloc_comp_eq_self n m p1 h.1,
        stack_alloc_comp_eq_self n m p2 h.2]
  | n, m, .loop p1, h => by
      simp only [noAllocOrStoreConsts] at h
      simp only [StackAlloc.comp, stack_alloc_comp_eq_self n m p1 h]
  | n, m, .call none dest none, _ => rfl
  | _, _, .call none _ (some _), h => by simp [noAllocOrStoreConsts] at h
  | n, m, .call (some (p1, lr, l1, l2)) dest none, h => by
      simp only [noAllocOrStoreConsts] at h
      simp only [StackAlloc.comp, stack_alloc_comp_eq_self n m p1 h]
  | n, m, .call (some (p1, lr, l1, l2)) dest (some (p2, k1, k2)), h => by
      simp only [noAllocOrStoreConsts, Bool.and_eq_true] at h
      simp only [StackAlloc.comp, stack_alloc_comp_eq_self n m p1 h.1,
        stack_alloc_comp_eq_self n m p2 h.2]
  | _, _, .alloc _, h => by simp [noAllocOrStoreConsts] at h
  | _, _, .storeConsts _ _ (some _), h => by simp [noAllocOrStoreConsts] at h
  | _, _, .storeConsts _ _ none, _ | _, _, .skip, _ | _, _, .halt _, _ | _, _, .tick, _
  | _, _, .ret _, _ | _, _, .raise _, _ | _, _, .break _, _ | _, _, .continue _, _
  | _, _, .inst _, _ | _, _, .get _ _, _ | _, _, .set _ _, _ | _, _, .opCurrHeap _ _ _, _
  | _, _, .jumpLower _ _ _, _ | _, _, .rawCall _, _ | _, _, .install _ _ _ _ _, _
  | _, _, .shMemOp _ _ _, _ | _, _, .codeBufferWrite _ _, _ | _, _, .dataBufferWrite _ _, _
  | _, _, .ffi _ _ _ _ _ _, _ | _, _, .locValue _ _ _, _ | _, _, .stackAlloc _, _
  | _, _, .stackFree _, _ | _, _, .stackLoad _ _, _ | _, _, .stackLoadAny _ _, _
  | _, _, .stackStore _ _, _ | _, _, .stackStoreAny _ _, _ | _, _, .stackGetSize _, _
  | _, _, .stackSetSize _, _ | _, _, .bitmapLoad _ _, _ => rfl
termination_by _ _ p => sizeOf p
decreasing_by all_goals simp_wf <;> omega

/-- When `noAllocOrStoreConsts p = true`, `StackAlloc.progComp (n, p) = (n, p)`. -/
theorem stack_alloc_progComp_eq_self {width : Nat} [NeZero width]
    (n : Nat) (p : HolProg width) (h : noAllocOrStoreConsts p = true) :
    StackAlloc.progComp (n, p) = (n, p) := by
  simp [StackAlloc.progComp, stack_alloc_comp_eq_self n (StackAlloc.nextLabHOL p 2) p h]

/-- Same-clock `WordToStack` non-timeout run agreement: if the compiled `StackSem` entry call
does not time out at clock `k`, then its result and FFI state agree with the source `WordSem`
entry call at the exact same clock `k`! -/
theorem word_to_stack_run_agree_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k_reg : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F)
    (start k : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (res_t : Option (StackSemResult width))
    (t1 : StackSemStateFiniteExact width C F)
    (related : WordToStackProofs.stateRel ac k_reg 0 0 s t [] 0)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace s start)
    (hrun_s : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k } = (res, s1))
    (hne : res ≠ some .error)
    (hrun_t : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { t with clock := k }) = (res_t, t1))
    (hnt : res_t ≠ some .timeOut) :
    res_t = res.map WordToStackProofs.CompCorrect.compileResult ∧ t1.ffi = s1.ffi := by
  obtain ⟨ck, t_ck, hrun_ck, hffi_ck⟩ := word_to_stack_clocked_sim ac k_reg s t start k res s1
    related safe hrun_s hne
  have hadd := StackProps.evaluateAddClock ck (.call none (.inl start) none)
    { t with clock := k } res_t t1 ⟨hrun_t, hnt⟩
  rw [hadd] at hrun_ck
  injection hrun_ck with hr hpost
  exact ⟨hr, (congrArg StackSemStateFiniteExact.ffi hpost).trans hffi_ck.symm⟩

/-- Same-clock `StackRawCall` non-timeout run agreement: if the `StackRawCall`-compiled state
does not time out at `clock`, its result and FFI state agree with the source `StackSem` run at
the exact same `clock`! -/
theorem stack_rawcall_run_agree_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result targetResult : Option (StackSemResult width))
    (post targetPost : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { source with clock := clock }) =
      (result, post))
    (nonError : result ≠ some .error)
    (targetRun : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        { source with code := sptFromAList (StackRawCall.compile code), clock := clock }) =
      (targetResult, targetPost))
    (nonTimeout : targetResult ≠ some .timeOut) :
    targetResult = result ∧ targetPost.ffi = post.ffi := by
  obtain ⟨extra, post_ex, hrun_ex, hffi_ex⟩ := stack_rawcall_clocked_sim code source start clock
    result post distinct sourceCode run nonError
  have hadd := StackProps.evaluateAddClock extra (.call none (.inl start) none)
    { source with code := sptFromAList (StackRawCall.compile code), clock := clock }
    targetResult targetPost ⟨targetRun, nonTimeout⟩
  rw [hadd] at hrun_ex
  injection hrun_ex with hr hpost
  exact ⟨hr, (congrArg StackSemStateFiniteExact.ffi hpost).trans hffi_ex⟩

/-- Same-clock `StackAlloc` non-timeout run agreement: if the `StackAlloc`-compiled state
does not time out at clock `k`, its result and FFI state agree with the source `StackSem` run
at the exact same clock `k`! -/
theorem stack_alloc_run_agree_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} {c : DataToWord.Config}
    {compile_rest : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)}
    {start : Nat} {anything : WordSemGcFun width}
    (hcode : ∀ k prog, sptLookup k s.code = some prog → k ≠ gcStubLocation ∧ StackProps.allocArg prog)
    (horacle : ∀ (i k : Nat) (q : HolProg width), (k, q) ∈ (s.compileOracle i).2.1 →
      k ≠ gcStubLocation ∧ StackProps.allocArg q)
    (hgc : s.gcFun = WordGcFunctions.wordGcFun c)
    (hbuf : s.bitmaps.length + s.dataBuffer.buffer.length + s.dataBuffer.spaceLeft < 2 ^ width - 1)
    (hst : s.stack.length * (width / 8) < 2 ^ width)
    (hK : s.useStack = true) (hA : s.useAlloc = true)
    (hC : s.compile = (fun cfg => compile_rest cfg ∘ List.map StackAlloc.progComp))
    (k : Nat) (r r_t : Option (StackSemResult width))
    (t t_post : StackSemStateFiniteExact width C F)
    (he : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s with clock := k }) = (r, t))
    (hr : r ≠ some .error)
    (he_t : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s with
        code := sptFromAList (StackAlloc.compile c (sptToAList s.code))
        gcFun := anything
        compile := compile_rest
        compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ s.compileOracle
        useStore := true, useStack := true, useAlloc := false, clock := k }) = (r_t, t_post))
    (hnt : r_t ≠ some .timeOut) :
    r_t = r ∧ t_post.ffi = t.ffi := by
  obtain ⟨ck, hr_ck, hffi_ck⟩ := stack_alloc_clocked_sim (anything := anything)
    hcode horacle hgc hbuf hst hK hA hC k r t he hr
  have hadd := StackProps.evaluateAddClock ck (.call none (.inl start) none)
    { s with
      code := sptFromAList (StackAlloc.compile c (sptToAList s.code))
      gcFun := anything
      compile := compile_rest
      compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ s.compileOracle
      useStore := true, useStack := true, useAlloc := false, clock := k }
    r_t t_post ⟨he_t, hnt⟩
  rw [hadd] at hr_ck hffi_ck
  exact ⟨hr_ck, hffi_ck⟩

/-- Same-clock `StackRemove` non-timeout run agreement: if the `StackRemove`-compiled state
does not time out at `clock`, its result and FFI state agree with the source `StackSem` run
at the exact same `clock`! -/
theorem stack_remove_run_agree_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock : Nat)
    (source target postSource postTarget : StackSemStateFiniteExact width C F)
    (sourceResult targetResult : Option (StackSemResult width))
    (relation : StackRemove.stateRelHOL jump bounds pointer source target)
    (sourceRun : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { source with clock := clock }) =
      (sourceResult, postSource))
    (nonError : sourceResult ≠ some .error)
    (targetRun : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { target with clock := clock }) =
      (targetResult, postTarget))
    (nonTimeout : targetResult ≠ some .timeOut) :
    targetResult = sourceResult ∧ postTarget.ffi = postSource.ffi := by
  obtain ⟨extra, compiledPost, compiledRun, ffi⟩ :=
    stack_remove_clocked_sim jump bounds pointer start clock source target postSource sourceResult
      relation sourceRun nonError
  have boostedRun := StackProps.evaluateAddClock extra (.call none (.inl start) none)
    { target with clock := clock } targetResult postTarget ⟨targetRun, nonTimeout⟩
  have same : (targetResult, { postTarget with clock := postTarget.clock + extra }) =
      (sourceResult, compiledPost) := by
    rw [← boostedRun]
    simpa only [Nat.add_comm] using compiledRun
  rcases Prod.mk.inj same with ⟨resultEqual, postEqual⟩
  exact ⟨resultEqual, (congrArg StackSemStateFiniteExact.ffi postEqual).trans ffi⟩

/-- Same-clock `StackToLab` non-timeout run agreement: if `LabSem.evaluate` at clock `k - 1`
(`labRuns s2 k`) does not time out and `stackRuns start s1 k` does not produce `.RunError`,
then `stackRuns start s1 k` equals `labRuns s2 k` at the exact same clock `k`! -/
theorem stack_to_lab_run_agree_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    {start : Nat}
    {s1 : StackSemStateFiniteExact width C F}
    {s2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (halt : FlattenCallCorrect.haltAssum C F s1.code)
    (rel : StateRel.stateRel s1 s2)
    (hpc : LabSem.locToPc start 0 s2.code = some s2.pc)
    (k : Nat)
    (hne : (FlattenSemantics.stackRuns start s1 k).1 ≠ .RunError)
    (hnt : (FlattenSemantics.labRuns s2 k).1 ≠ .Incomplete) :
    FlattenSemantics.stackRuns start s1 k = FlattenSemantics.labRuns s2 k := by
  rcases hs : FlattenSemantics.stackRuns start s1 k with ⟨r_s, ev_s⟩
  have hr_ne : r_s ≠ .RunError := by
    rw [hs] at hne; exact hne
  obtain ⟨ck, hlab_ck⟩ := FlattenSemantics.stackRunsSim halt rel hpc k r_s ev_s hs hr_ne
  simp only [FlattenSemantics.labRuns] at hnt hlab_ck ⊢
  rcases he : LabSem.evaluate { s2 with clock := k - 1 } with ⟨m, next⟩
  rw [he] at hnt
  simp only [Prod.map] at hnt
  have hm_nt : m ≠ .timeOut := by
    rintro rfl
    exact hnt rfl
  have kpos : k ≠ 0 := by
    rintro rfl
    rw [LabSem.evaluate, if_pos rfl] at he
    exact hm_nt (Prod.mk.inj he).1.symm
  have hadd := LabProps.evaluateAddClock { s2 with clock := k - 1 } m next ck ⟨he, hm_nt⟩
  simp only at hadd
  rw [show k + ck - 1 = k - 1 + ck by omega, hadd] at hlab_ck
  exact hlab_ck.symm

/-- Same-clock `fullMakeInit` non-timeout run agreement (`StackRawCall` + `StackAlloc` +
`StackRemove` + `StackNames` + `StackToLab`): if `fullMakeInit` succeeds (`= (s, opt)`) under
`Assumptions` and `LabSem.evaluate` on `t` at clock `k` does not time out (`≠ .timeOut`),
and the intermediate `StackSem` runs at clock `k` do not error (`≠ some .error`), then
`FlattenSemantics.stackRuns BvlToBvi.initGlobalsLocation s k` agrees with
`FlattenSemantics.labRuns t (k + 1)` (`LabSem.evaluate { t with clock := k }`) at the exact
same clock `k`! -/
theorem full_make_init_run_agree_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F}
    {opt : Option (StackSemStateFiniteExact width C F)}
    (hfm : FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t
      saveRegs dataSp coracle = (s, opt))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle)
    (k : Nat) (res : Option (StackSemResult width)) (s_post : StackSemStateFiniteExact width C F)
    (hrun : StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { s with clock := k }) = (res, s_post))
    (hclass_ne : FlattenSemantics.stackEntryClass res ≠ .RunError)
    (hnt_lab : (LabSem.evaluate { t with clock := k }).1 ≠ .timeOut) :
    (FlattenSemantics.labEntryClass (LabSem.evaluate { t with clock := k }).1,
      (LabSem.evaluate { t with clock := k }).2.ffi.ioEvents) =
      (FlattenSemantics.stackEntryClass res, s_post.ffi.ioEvents) := by
  have hne : res ≠ some .error := by
    rintro rfl
    exact hclass_ne rfl
  rw [fullMakeInit_eq] at hfm
  simp only [Prod.mk.injEq] at hfm
  obtain ⟨rfl, rfl⟩ := hfm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hgood, hgoodO, -, -, -, -, -, -, -, -⟩ := id hA
  have hdis := dischargeThese_s2 hA
  have hprop2 := propagateThese_s2 hA
  obtain ⟨⟨every, oracleBound, oracleEq, codeEq, k8, entry1, save, noStack, noStore, noAlloc,
    maxOk⟩, good, ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cbEmpty, le, al2, al4,
    albp, big, heap⟩ := And.intro hdis hprop2
  have codeRel : StackRemove.codeRelHOL stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).code :=
    StackRemove.Proofs.InitCodeRelation.impCodeRel stackConf.jump offset
      (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
      (code1 dataConf code) _ ⟨every, codeEq⟩
  have errLab : sptLookup StackRemove.stackErrLab
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).code =
      some (StackRemove.haltInst (BitVec.ofNat width 2)) := by
    rw [codeEq, sptLookup_sptFromAList]
    simp [StackRemove.compileHOL, StackRemove.initStubs, sptAListLookup, StackRemove.stackErrLab]
  have pre : StackRemove.Proofs.InitMake.initPre (StackToLab.isGenGc dataConf.gcKind) maxHeap
      bitmaps dataSp sp BvlToBvi.initGlobalsLocation
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) := by
    refine ⟨?_, ?_, maxOk⟩
    · rw [codeEq, sptLookup_sptFromAList]
      simp [StackRemove.compileHOL, StackRemove.initStubs, sptAListLookup]
    · have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
        rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
      rw [sub] at heap
      exact ⟨ptr2, ptr3, ptr4, bp, good, k8, entry1, save, noStack, noStore, noAlloc, r2, r3, r4,
        m0, m1, m2, m3, m4, le, big, al2, al4, albp, cbEmpty, heap⟩
  have hinit := StackRemove.Proofs.InitSemantics.evaluateInitCode
    (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp sp BvlToBvi.initGlobalsLocation
    (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
    stackConf.jump offset (coracle1 coracle) (sptFromAList (code1 dataConf code))
    ⟨pre, oracleEq, oracleBound, errLab, codeRel⟩
  revert hinit
  cases hinitRun : StackSemEvaluate.evaluate
      (StackRemove.initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp,
        s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) with
  | mk initRes t_rem =>
    cases initRes with
    | some _ => intro h; exact False.elim h
    | none =>
      rintro ⟨s1, hopt, rel_rem, _⟩
      have hs1 : StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind)
          maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
          (sptFromAList (code1 dataConf code))
          (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = s1 := by
        unfold StackRemove.Proofs.InitMake.makeInitAny
        rw [hopt]
      rw [hs1] at hrun
      obtain ⟨post, hpost, hprop⟩ := StackRemove.Proofs.InitAny.makeInitOpt_eq_some hopt
      obtain ⟨ck1, t_rc, hrun_rc, hffi_rc⟩ := stack_rawcall_clocked_sim code
        (StackAlloc.makeInit dataConf (sptFromAList code) coracle s1)
        BvlToBvi.initGlobalsLocation k res s_post hgood.1 rfl hrun hne
      have hm : { StackAlloc.makeInit dataConf (sptFromAList code) coracle s1 with
          code := sptFromAList (StackRawCall.compile code), clock := k + ck1 } =
          { StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1 with
            clock := k + ck1 } := by
        simp [StackAlloc.makeInit]
      rw [hm] at hrun_rc
      have hu := StackRemove.Proofs.InitAny.makeInitAnyUseStack (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hus := StackRemove.Proofs.InitAny.makeInitAnyUseStore (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hua := StackRemove.Proofs.InitAny.makeInitAnyUseAlloc (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hcd := StackRemove.Proofs.InitAny.makeInitAnyCode (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hco := StackRemove.Proofs.InitAny.makeInitAnyCompileOracle
        (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      rw [hs1] at hu hus hua hcd hco
      have hcode_sa : ∀ k prog,
          sptLookup k (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).code = some prog →
          k ≠ gcStubLocation ∧ StackProps.allocArg prog := by
        intro k0 prog hk0
        simp only [StackAlloc.makeInit, sptLookup_sptFromAList] at hk0
        obtain ⟨⟨n0, p0⟩, hm0, he⟩ := List.mem_map.mp (sptAListLookup_mem hk0)
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨hst, hal⟩ := hgood.2.1 _ hm0
        exact ⟨by simp only [stackNumStubs, gcStubLocation] at hst ⊢; omega,
          (StackRawCall.callArgComp _ _).2.mpr hal⟩
      have horacle_sa : ∀ (i k : Nat) (q : HolProg width),
          (k, q) ∈ ((StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).compileOracle i).2.1 →
          k ≠ gcStubLocation ∧ StackProps.allocArg q := by
        intro i k0 q hq
        obtain ⟨hst, hal⟩ := (hgoodO i).2.1 _ hq
        exact ⟨by simp only [stackNumStubs, gcStubLocation] at hst ⊢; omega, hal⟩
      rcases hprop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        hdb, _, _, _, hbl, _, _, _, _, _, hsb, _⟩
      have hbuf_sa : (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).bitmaps.length +
          (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).dataBuffer.buffer.length +
          (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).dataBuffer.spaceLeft <
          2 ^ width - 1 := by
        subst hpost
        simp only [StackAlloc.makeInit, StackRemove.Proofs.InitReduce.initReduce, List.length_nil, Nat.add_zero] at hbl hdb ⊢
        omega
      have hst_sa : (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).stack.length *
          (width / 8) < 2 ^ width := by
        subst hpost
        exact hsb
      obtain ⟨ck2, hrun_sa1, hffi_sa⟩ := stack_alloc_clocked_sim
        (s := StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1)
        (c := dataConf) (compile_rest := s1.compile) (start := BvlToBvi.initGlobalsLocation)
        (anything := s1.gcFun)
        hcode_sa horacle_sa rfl hbuf_sa hst_sa rfl rfl rfl (k + ck1) res t_rc hrun_rc hne
      let m_sa := StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1
      have hs1_eq : { m_sa with
          code := sptFromAList (StackAlloc.compile dataConf (sptToAList m_sa.code))
          gcFun := s1.gcFun
          compile := s1.compile
          compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ m_sa.compileOracle
          useStore := true, useStack := true, useAlloc := false, clock := k + ck1 + ck2 } =
          { s1 with clock := k + ck1 + ck2 } := by
        have hcc : sptFromAList (StackAlloc.compile dataConf
            (sptToAList (sptFromAList (StackRawCall.compile code)))) = s1.code := by
          rw [hcd, code1]
          refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
          rw [StackAlloc.CompCorrect.sptLookup_compile, StackAlloc.CompCorrect.sptLookup_compile,
            StackAlloc.ProgCompSupport.sptAListLookup_sptToAList, sptLookup_sptFromAList]
        cases s1
        simp only [m_sa, StackAlloc.makeInit, coracle1] at hcc hco hus hu hua ⊢
        simp only [Bool.not_eq_true] at hua
        subst hus hu hua
        rw [hcc, hco]
      change (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { m_sa with
            code := sptFromAList (StackAlloc.compile dataConf (sptToAList m_sa.code))
            gcFun := s1.gcFun
            compile := s1.compile
            compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ m_sa.compileOracle
            useStore := true, useStack := true, useAlloc := false, clock := k + ck1 + ck2 })).1 = res at hrun_sa1
      change (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { m_sa with
            code := sptFromAList (StackAlloc.compile dataConf (sptToAList m_sa.code))
            gcFun := s1.gcFun
            compile := s1.compile
            compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ m_sa.compileOracle
            useStore := true, useStack := true, useAlloc := false, clock := k + ck1 + ck2 })).2.ffi = t_rc.ffi at hffi_sa
      rw [hs1_eq] at hrun_sa1 hffi_sa
      rcases hrun_s1 : StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { s1 with clock := k + ck1 + ck2 }) with ⟨res_s1, post_s1⟩
      rw [hrun_s1] at hrun_sa1 hffi_sa
      simp only at hrun_sa1 hffi_sa
      subst res_s1
      obtain ⟨ck3, post_rem, hrun_rem, hffi_rem⟩ := stack_remove_clocked_sim
        stackConf.jump offset sp BvlToBvi.initGlobalsLocation (k + ck1 + ck2)
        s1 t_rem post_s1 res rel_rem hrun_s1 hne
      have hshift := stack_remove_init_clocked_shift
        (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) t_rem
        (ck3 + (k + ck1 + ck2)) pre.1 hinitRun
      let s3_st := s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle
      let s2_st := s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle
      have hbij := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hnames := stack_names_clocked_agree
        (c := s3_st.compile)
        (f := stackConf.regNames)
        (s := s2_st)
        hbij
        (by simp [s2_st, noAlloc])
        (by simp [s2_st, noStore])
        (by simp [s2_st, noStack])
        rfl 0 (ck3 + (k + ck1 + ck2) + 1)
      have hs3_def : StackNames.renameState s3_st.compile stackConf.regNames s2_st = s3_st := by
        have hinv : ∀ y, StackNames.findNameSpt stackConf.regNames
            (holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) y) = y :=
          apply_holLinv_of_surjective hbij.2
        have hc : sptFromAList (StackNames.compileHOL stackConf.regNames
            (sptToAList (sptFromAList (code2 stackConf dataConf maxHeap sp offset code)))) =
            s3_st.code := by
          change _ = sptFromAList (StackNames.compileHOL stackConf.regNames
            (code2 stackConf dataConf maxHeap sp offset code))
          refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
          rw [sptLookup_sptFromAList, StackNames.sptAListLookup_compileHOL, ← sptLookup_sptFromAList,
            sptLookup_sptFromAList_sptToAList, sptLookup_sptFromAList, sptLookup_sptFromAList,
            StackNames.sptAListLookup_compileHOL]
        classical
        have hsave : (fun y => decide (∃ x, decide (∃ z, s3_st.ffiSaveRegs z = true ∧
            x = holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) z) = true ∧
            y = StackNames.findNameSpt stackConf.regNames x)) = s3_st.ffiSaveRegs := by
          funext y
          by_cases hy : s3_st.ffiSaveRegs y = true
          · rw [hy, decide_eq_true_iff]
            exact ⟨holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) y,
              decide_eq_true_iff.mpr ⟨y, hy, rfl⟩, (hinv y).symm⟩
          · rw [Bool.not_eq_true] at hy
            rw [hy, decide_eq_false_iff_not]
            rintro ⟨x, hx, rfl⟩
            obtain ⟨z, hz, rfl⟩ := decide_eq_true_iff.mp hx
            rw [hinv z, hz] at hy
            exact Bool.noConfusion hy
        have hor : s3_st.compileOracle =
            Prod.map id (Prod.map (StackNames.compileHOL stackConf.regNames) id) ∘
              coracle2 stackConf sp offset coracle := rfl
        simp only [s2_st, s2, StackNames.renameState, StackNames.makeInit,
          StackNames.MakeInit.mapKeys_mapKeys_linv hbij, hc, ← hor]
        refine Eq.trans ?_ (show { s3_st with ffiSaveRegs := s3_st.ffiSaveRegs } = s3_st from rfl)
        congr 1
      rw [hs3_def] at hnames
      have hruns_s3 : FlattenSemantics.stackRuns 0
          (s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
          (ck3 + (k + ck1 + ck2) + 1) =
          (FlattenSemantics.stackEntryClass res, s_post.ffi.ioEvents) := by
        simp only [FlattenSemantics.stackRuns, Prod.map]
        rcases hev_s3 : StackSemEvaluate.evaluate
          ((.call none (.inl 0) none : HolProg width),
            { s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
              clock := ck3 + (k + ck1 + ck2) + 1 }) with ⟨r_s3, p_s3⟩
        have hnames1 := hnames.1
        change (StackSemEvaluate.evaluate
          ((.call none (.inl 0) none : HolProg width),
            { s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
              clock := ck3 + (k + ck1 + ck2) + 1 })).1 =
          (StackSemEvaluate.evaluate
            ((.call none (.inl 0) none : HolProg width),
              { s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
                clock := ck3 + (k + ck1 + ck2) + 1 })).1 at hnames1
        have hnames2 := hnames.2
        change (StackSemEvaluate.evaluate
          ((.call none (.inl 0) none : HolProg width),
            { s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
              clock := ck3 + (k + ck1 + ck2) + 1 })).2.ffi =
          (StackSemEvaluate.evaluate
            ((.call none (.inl 0) none : HolProg width),
              { s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
                clock := ck3 + (k + ck1 + ck2) + 1 })).2.ffi at hnames2
        have hr_eq : r_s3 = res := by
          rw [hev_s3, hshift.1, hrun_rem] at hnames1
          exact hnames1
        have hffi_eq : p_s3.ffi = s_post.ffi := by
          rw [hev_s3, hshift.2, hrun_rem] at hnames2
          exact hnames2.trans (hffi_rem.trans (hffi_sa.trans hffi_rc))
        rw [hr_eq, hffi_eq]
      obtain ⟨ck4, hlab⟩ := FlattenSemantics.stackRunsSim
        MakeInit.haltAssumLemma (stateRel_s3 hA) (locToPc_start hA)
        (ck3 + (k + ck1 + ck2) + 1) (FlattenSemantics.stackEntryClass res) s_post.ffi.ioEvents
        hruns_s3 hclass_ne
      simp only [FlattenSemantics.labRuns] at hlab
      rcases he_k : LabSem.evaluate { t with clock := k } with ⟨m_k, next_k⟩
      rw [he_k] at hnt_lab
      have hadd := LabProps.evaluateAddClock { t with clock := k } m_k next_k
        (ck3 + ck1 + ck2 + ck4) ⟨he_k, hnt_lab⟩
      simp only at hadd
      rw [show ck3 + (k + ck1 + ck2) + 1 + ck4 - 1 = k + (ck3 + ck1 + ck2 + ck4) by omega,
        hadd] at hlab
      exact hlab

/-- Same-clock `WordToStack.Native` non-timeout run agreement under `wordLangSafeForSpace`:
if the compiled `StackSem` entry call on `t` does not time out at clock `clk`, then it produces
the exact mapped result `res.map compileResult` and identical FFI state as the source `WordSem`
entry call at the exact same clock `clk`! -/
theorem word_to_stack_compile_run_agree_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start clk : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (res_t : Option (StackSemResult width))
    (t1 : StackSemStateFiniteExact width C F)
    (codeEq : t.code = sptFromAList (WordToStack.Native.compileNative asmConf false code).2.2.2)
    (kEq : k = asmConf.regCount - (5 + asmConf.avoidRegs.length))
    (ok : WordToStackProofs.InitializationStateRel.initStateOk asmConf k t coracle)
    (noRaise : panPropsALookupEq raiseStubLocation code = none)
    (noStore : panPropsALookupEq storeConstsStubLocation code = none)
    (bitmapsPrefix : (WordToStack.Native.compileNative asmConf false code).1 <+: t.bitmaps)
    (conventions : ∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
        entry.2.2 = true)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace
      (WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle) start)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
        clock := clk } = (res, s1))
    (hne : res ≠ some .error)
    (hrun_t : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { t with clock := clk }) = (res_t, t1))
    (hnt : res_t ≠ some .timeOut) :
    res_t = res.map WordToStackProofs.CompCorrect.compileResult ∧ t1.ffi = s1.ffi := by
  obtain ⟨ck, t_post, hrun_post, hffi_post⟩ := word_to_stack_compile_clocked_sim asmConf code t k
    coracle start clk res s1 codeEq kEq ok noRaise noStore bitmapsPrefix conventions safe hrun hne
  have hadd := StackProps.evaluateAddClock ck (.call none (.inl start) none)
    { t with clock := clk } res_t t1 ⟨hrun_t, hnt⟩
  rw [hadd] at hrun_post
  injection hrun_post with hr hpost
  exact ⟨hr, (congrArg StackSemStateFiniteExact.ffi hpost).trans hffi_post.symm⟩

/-- Non-timeout target halt agreement for `pan_to_target_backend_clocked_halt`:
under the resource bound `optionLt stackMax (some (readLimits ...).1) = true`, if a `WordSem`
entry call on `wst0` (compiled from `panCode` by `PanToWord`) halts at clock `k_word` with
`semTermOutcome res outcome`, and `evaluateTargetHOL mc ffi K ms` does not time out at clock `K`,
then `evaluateTargetHOL mc ffi K ms` halts with `outcome` and the exact same FFI I/O events! -/
theorem pan_to_target_backend_halt_agree_of_not_timeOut {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapPtr : BitVec width) (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (panCode : List (Pancake.PanLang.DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (dataSp : Nat) (stackMax : Option Nat)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : LabToTarget.mcConfOk mc)
    (hinit : BackendProof.mcInitOk mc.target.config c mc) (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hlab : LabToTarget.compile mc.target.config c.labConf
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset p) = some (bytes, ltconf))
    (hmax : stackMax = WordDepth.maxDepth wconf.stackFrameSize
      (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wprog)))
    (hnodup : ((Pancake.PanLang.functionsHOL panCode).map Prod.fst).Nodup)
    (hffiOk : match c.labConf.ffiNames with
      | none => True
      | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s)
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapsDm w) sdm)
    (hffiN : ltconf.ffiNames = some mc.ffiNames)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      ltconf.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
        mc.mmioInfo = List.zip ((List.range ltconf.shmemExtra.length).map (fun index => index + i))
          (ltconf.shmemExtra.map fun rec => (rec.nbytes,
            HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff),
            rec.reg, BitVec.ofNat width rec.exitPc + mc.target.getPc ms)) ∧
        cbspace + bytes.length + LabToTarget.ffiOffset * (i + 3) < 2 ^ width)
    (hsource : pancakeGoodCodeHOL panCode = true)
    (hpi :
      let regNames := c.stackConf.regNames
      let r1 := StackNames.findNameSpt regNames 2
      let r2 := StackNames.findNameSpt regNames 4
      let biw := StackRemove.bytesInWord width
      let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
      holByteAligned (t.regs r1) = true ∧ holByteAligned (t.regs r2) = true ∧
      holByteAligned bitmapPtr = true ∧ t.regs r1 ≤ t.regs r2 ∧
      1024 * biw ≤ t.regs r2 - t.regs r1 ∧
      (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
      m (t.regs r1) = .word bitmapPtr ∧
      m (t.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width dataSp +
        biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
      m (t.regs r1 + 4 * biw) =
        .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
      SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
        (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) dataSp)
        (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)))
    (hlo : mc.target.getReg ms mc.lenReg +
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ≤
        mc.target.getReg ms mc.ptr2Reg)
    (hhi : mc.target.getReg ms mc.ptr2Reg ≤ mc.target.getReg ms mc.len2Reg -
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc)
    (hheap : (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1))
    (hheapLt : (StackRemove.bytesInWord width).toNat *
      (2 * DataToWord.maxHeapLimit width c.dataConf - 1) < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true)
    (hresLimit : optionLt stackMax
      (some (BackendProof.readLimits mc.target.config c mc ms).1) = true)
    (hsem : WordSemStateFiniteExact.semantics
      (let regNames := c.stackConf.regNames
       let r1 := StackNames.findNameSpt regNames 2
       let r2 := StackNames.findNameSpt regNames 4
       let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
       let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
       let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
       let labst := LabToTarget.makeInit (C := LabToTarget.Config) mc ffi t m
         (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
         (fun a => sdm a && holByteAligned a) ms
         (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
         (LabToTarget.compile mc.target.config)
         (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
         (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
           mc.target.config.addrOffset sp []))
       let sst := (FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
         mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
         dataSp (fun _ => (ltconf, [], []))).1
       WordToStack.Native.Initialization.makeInit mc.target.config
         (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
         (sptFromAList wprog)
         (fun _ => ((bitmaps.length, ltconf), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width))))))
      BvlToBvi.initGlobalsLocation ≠ .fail)
    (k_word : Nat) (res : Option (WordSemResult width)) (outcome : HolOutcome)
    (s_word_post : WordSemStateFiniteExact width (Nat × LabToTarget.Config) σ)
    (hres_ok : match res with
      | some (.finalFfi e) => outcome = .ffiOutcome e
      | some (.result (WordLocW.loc 1 0) _) => outcome = .success
      | some .notEnoughSpace => outcome = .resourceLimitHit
      | _ => False)
    (hrun_w0 : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { (let regNames := c.stackConf.regNames
         let r1 := StackNames.findNameSpt regNames 2
         let r2 := StackNames.findNameSpt regNames 4
         let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
         let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
         let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
         let labst := LabToTarget.makeInit (C := LabToTarget.Config) mc ffi t m
           (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
           (fun a => sdm a && holByteAligned a) ms
           (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
           (LabToTarget.compile mc.target.config)
           (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
           (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
             mc.target.config.addrOffset sp []))
         let sst := (FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
           mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
           dataSp (fun _ => (ltconf, [], []))).1
         let wst := WordToStack.Native.Initialization.makeInit mc.target.config
           (mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)) sst
           (sptFromAList wprog)
           (fun _ => ((bitmaps.length, ltconf), ([] : List (Nat × Nat × WordLangProgHOL (BitVec width)))))
         { wst with code := sptFromAList (panToWordCompileProgHOL mc.target.config.isa panCode) })
        with clock := k_word } = (res, s_word_post))
    (K : Nat)
    (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi K ms).1 = .halt outcome ∧
      (evaluateTargetHOL mc ffi K ms).2.2.ioEvents = s_word_post.ffi.ioEvents := by
  obtain ⟨k_target, ms2, ffi2, htarget, hio⟩ := pan_to_target_backend_clocked_halt
    c mc ffi t m bitmapPtr bitmapsDm sdm ms bytes cbspace ltconf panCode col wprog bitmaps wconf
    fs p dataSp stackMax hcfg hmc hinit hisa hwtw hwts hlab hmax hnodup hffiOk hgi hffiN hmmio
    hsource hpi hlo hhi hheap hheapLt halign hresLimit hsem k_word res outcome s_word_post
    hres_ok hrun_w0
  obtain ⟨ms1, hhaltK⟩ := evaluateTarget_halt_of_not_timeOut_and_halt
    mc ffi ms k_target K outcome ms2 ffi2 htarget hnt
  rw [hhaltK]
  exact ⟨rfl, hio⟩

/-- Arbitrary-clock `fullMakeInit` non-timeout halt agreement (`StackRawCall` + `StackAlloc` +
`StackRemove` + `StackNames` + `StackToLab`): if `fullMakeInit` succeeds (`= (s, opt)`) under
`Assumptions`, `StackSem` halts on `s` at clock `k` with `.CompleteResult outcome`, and
`LabSem.evaluate` on `t` at ANY clock `K_lab` does not time out (`≠ .timeOut`), then
`LabSem.evaluate { t with clock := K_lab }` halts with `.halt outcome` and identical I/O events! -/
theorem full_make_init_halt_of_lab_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F}
    {opt : Option (StackSemStateFiniteExact width C F)}
    (hfm : FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t
      saveRegs dataSp coracle = (s, opt))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle)
    (k : Nat) (res : Option (StackSemResult width)) (s_post : StackSemStateFiniteExact width C F)
    (outcome : HolOutcome)
    (hrun : StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { s with clock := k }) = (res, s_post))
    (hclass : FlattenSemantics.stackEntryClass res = .CompleteResult outcome)
    (K_lab : Nat)
    (hnt_lab : (LabSem.evaluate { t with clock := K_lab }).1 ≠ .timeOut) :
    (LabSem.evaluate { t with clock := K_lab }).1 = .halt outcome ∧
      (LabSem.evaluate { t with clock := K_lab }).2.ffi.ioEvents = s_post.ffi.ioEvents := by
  obtain ⟨k_lab, hhalt_lab, hio_lab⟩ := full_make_init_clocked_halt hfm hA k res s_post outcome
    hrun hclass
  rcases heK : LabSem.evaluate { t with clock := K_lab } with ⟨resK, nextK⟩
  rcases hek : LabSem.evaluate { t with clock := k_lab } with ⟨resk, nextk⟩
  rw [heK] at hnt_lab
  rw [hek] at hhalt_lab hio_lab
  simp only at hnt_lab hhalt_lab hio_lab
  subst hhalt_lab
  obtain ⟨hr, hffi⟩ := labEvaluateIgnoreClocks t K_lab k_lab resK (.halt outcome) nextK nextk
    heK hnt_lab hek (by rintro ⟨⟩)
  exact ⟨hr, (congrArg HolFfiState.ioEvents hffi).trans hio_lab⟩

/-- Arbitrary-clock `WordToStack.Native` non-timeout halt agreement under `wordLangSafeForSpace`:
if a `WordSem` entry call on `makeInit` at clock `clk` completes (`res ≠ some .error` and
`res ≠ some .timeOut`), and the compiled `StackSem` entry call on `t` at ANY clock `K_stack`
does not time out (`res_t ≠ some .timeOut`), then it produces the exact mapped result
`res.map compileResult` and identical FFI state! -/
theorem word_to_stack_compile_halt_of_stack_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start clk K_stack : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (res_t : Option (StackSemResult width))
    (t1 : StackSemStateFiniteExact width C F)
    (codeEq : t.code = sptFromAList (WordToStack.Native.compileNative asmConf false code).2.2.2)
    (kEq : k = asmConf.regCount - (5 + asmConf.avoidRegs.length))
    (ok : WordToStackProofs.InitializationStateRel.initStateOk asmConf k t coracle)
    (noRaise : panPropsALookupEq raiseStubLocation code = none)
    (noStore : panPropsALookupEq storeConstsStubLocation code = none)
    (bitmapsPrefix : (WordToStack.Native.compileNative asmConf false code).1 <+: t.bitmaps)
    (conventions : ∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
        entry.2.2 = true)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace
      (WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle) start)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
        clock := clk } = (res, s1))
    (hne : res ≠ some .error)
    (hnt_w : res ≠ some .timeOut)
    (hrun_t : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { t with clock := K_stack }) = (res_t, t1))
    (hnt : res_t ≠ some .timeOut) :
    res_t = res.map WordToStackProofs.CompCorrect.compileResult ∧ t1.ffi = s1.ffi := by
  obtain ⟨ck, t_post, hrun_post, hffi_post⟩ := word_to_stack_compile_clocked_sim asmConf code t k
    coracle start clk res s1 codeEq kEq ok noRaise noStore bitmapsPrefix conventions safe hrun hne
  have hnt_post : res.map WordToStackProofs.CompCorrect.compileResult ≠ some .timeOut := by
    cases res with
    | none => rintro ⟨⟩
    | some r =>
      cases r <;> simp [WordToStackProofs.CompCorrect.compileResult] at hnt_w ⊢
  obtain ⟨hr, hffi⟩ := stackEvaluateIgnoreClocks (.call none (.inl start) none) t K_stack (clk + ck)
    res_t (res.map WordToStackProofs.CompCorrect.compileResult) t1 t_post
    hrun_t hnt hrun_post hnt_post
  exact ⟨hr, hffi.trans hffi_post.symm⟩


end InitE
