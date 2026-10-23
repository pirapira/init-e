import InitECandidate.Proofs.CompilerOracles
import Flapjack.Compiler.Backend.LabToTarget.MachineSemantics
import Flapjack.Compiler.Backend.LabToTarget.SemanticsCompileFinal
import Flapjack.Compiler.Backend.LabFilter.Proofs.Semantics
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMachineToLab
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSemantics
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTopResource
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTop
import Flapjack.Pancake.LoopToWord.Proofs.StateRelImpSemantics
import Flapjack.Pancake.CrepToLoop.Proofs.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanToCrep.StateRelImpSemanticsTop
import Flapjack.Pancake.Proofs.PanToWord.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanSimp.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanStructs.SemanticsEq
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsDecls


/-! Clock agreement proofs kept in Solver so Yukon preserves them.
Only the fixed baseline CompilerOracles module is imported from InitECandidate.Proofs. -/

namespace InitECandidate.Solver.SelfContainedStageBounds
open InitE
set_option maxHeartbeats 800000

section LabAgreement
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget
theorem labEvaluateIgnoreClocks {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F)
    (k k' : Nat) (r1 r2 : MachineResult)
    (next1 next2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (h1 : LabSem.evaluate { s with clock := k } = (r1, next1))
    (hnt1 : r1 ≠ .timeOut)
    (h2 : LabSem.evaluate { s with clock := k' } = (r2, next2))
    (hnt2 : r2 ≠ .timeOut) :
    r1 = r2 ∧ next1.ffi = next2.ffi := by
  have ha1 := evaluateAddClock { s with clock := k } r1 next1 k' ⟨h1, hnt1⟩
  have ha2 := evaluateAddClock { s with clock := k' } r2 next2 k ⟨h2, hnt2⟩
  simp only [Nat.add_comm k' k] at ha2
  rw [ha1] at ha2
  injection ha2 with hr hnext
  have hffi := congrArg Flapjack.Compiler.Backend.LabSem.State.ffi hnext
  exact ⟨hr, hffi⟩

theorem lab_filter_align_clocked_halt {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width)
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hr : LabFilter.Proofs.stateRel s t)
    (k : Nat) (outcome : HolOutcome)
    (next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hhalt : LabSem.evaluate { alignDm (alignSdm t) with clock := k } = (.halt outcome, next)) :
    (LabSem.evaluate { s with clock := k }).1 = .halt outcome ∧
      (LabSem.evaluate { s with clock := k }).2.ffi = next.ffi := by
  have hdm : LabSem.evaluate { alignDm (alignSdm t) with clock := k } =
      ((LabSem.evaluate { alignSdm t with clock := k }).1,
        alignDm (LabSem.evaluate { alignSdm t with clock := k }).2) := by
    change LabSem.evaluate (alignDm { alignSdm t with clock := k }) = _
    have h := evaluateAlignDM hw { alignSdm t with clock := k }
    cases he : LabSem.evaluate { alignSdm t with clock := k }
    simpa only [he] using h
  have hsdm : LabSem.evaluate { alignSdm t with clock := k } =
      ((LabSem.evaluate { t with clock := k }).1,
        alignSdm (LabSem.evaluate { t with clock := k }).2) := by
    change LabSem.evaluate (alignSdm { t with clock := k }) = _
    have h := evaluateAlignSDM hw { t with clock := k }
    cases he : LabSem.evaluate { t with clock := k }
    simpa only [he] using h
  rw [hsdm] at hdm
  rw [hhalt] at hdm
  have hres_t : (LabSem.evaluate { t with clock := k }).1 = .halt outcome :=
    (congrArg Prod.fst hdm).symm
  have hffi_t : (LabSem.evaluate { t with clock := k }).2.ffi = next.ffi := by
    have h2 := congrArg Prod.snd hdm
    have hffi := congrArg Flapjack.Compiler.Backend.LabSem.State.ffi h2
    exact hffi.symm
  have hrc : LabFilter.Proofs.stateRel { s with clock := k } { t with clock := k } := by
    rcases hr with ⟨⟨compile, hs, hcomp⟩, hf⟩
    subst s
    exact ⟨⟨compile, rfl, hcomp⟩, hf⟩
  obtain ⟨extra, t2, he, hf⟩ := LabFilter.Proofs.filterCorrect
    { s with clock := k } { t with clock := k }
    (LabSem.evaluate { s with clock := k }).1
    (LabSem.evaluate { s with clock := k }).2
    ⟨rfl, hrc, hrc.2⟩
  have hnt : (LabSem.evaluate { t with clock := k }).1 ≠ .timeOut := by
    rw [hres_t]
    intro h
    cases h
  have hadd := evaluateAddClock { t with clock := k }
    (LabSem.evaluate { t with clock := k }).1
    (LabSem.evaluate { t with clock := k }).2 extra
    ⟨rfl, hnt⟩
  rw [hadd] at he
  constructor
  · exact (congrArg Prod.fst he).symm.trans hres_t
  · have ht2 : (LabSem.evaluate { t with clock := k }).2.ffi = t2.ffi :=
      congrArg (fun p => p.2.ffi) he
    rw [hf, ← ht2]
    exact hffi_t
end LabAgreement

section StackAgreement
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Pancake.Proofs.PanToTarget

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


end StackAgreement

section PanAgreement
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open Flapjack.LoopToWord.CompileCorrect

theorem loop_to_word_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (start k : Nat)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F)
    (hsr : loopToWordStateRelHOLExact s t)
    (hemp : sptIsEmpty s.locals = true)
    (hdim : goodDimindex width)
    (hret : sptLookup 0 t.locals = some (WordLocW.loc 1 0))
    (hev : LoopSemStateFiniteExact.evaluate
      (.call none (some start) [] none : HolLoopProg width) { s with clock := k } = (res, s1))
    (hne : res ≠ some .error) :
    ∃ t1 res1,
      WordSemStateFiniteExact.evaluate
        (.call none (some start) [0] none : WordLangProgHOL (BitVec width))
        { t with clock := k } = (res1, t1) ∧
      t1.ffi = s1.ffi ∧
      resultCase (makeCtxtHOL 2 [] .ln) (WordLocW.loc 1 0) { t with clock := k } res s1 res1 t1 := by
  have hloc : s.locals = .ln := by
    cases h : s.locals <;> simp_all [sptIsEmpty]
  have hlocals : LoopToWord.localsRelHOL (makeCtxtHOL 2 [] .ln)
      ({ s with clock := k } : LoopSemStateFiniteExact width F).locals
      ({ t with clock := k } : WordSemStateFiniteExact width C F).locals := by
    show LoopToWord.localsRelHOL _ s.locals t.locals
    rw [hloc]
    exact LoopToWord.localsRelHOLMkCtxtLn 2 [] _ ⟨by decide, by decide⟩
  obtain ⟨t1, res1, hrun, hffi, hrc⟩ :=
    compileCorrect (C := C) (.call none (some start) [] none) { s with clock := k } res s1
      { t with clock := k } (makeCtxtHOL 2 [] .ln) (WordLocW.loc 1 0) (0, 0)
      ⟨hev, hne, loopToWordStateRelWithClockHOLExact s t k hsr, hlocals, hret, hdim,
        by simp [wordSemIsWordLoc], by intro x hx; simp [accVarsHOL, sptMem, sptDomain] at hx⟩
  have hcomp : (LoopToWord.compHOL (makeCtxtHOL 2 [] .ln)
      (.call none (some start) [] none : HolLoopProg width) (0, 0)).1 =
      .call none (some start) [0] none := by simp [LoopToWord.compHOL]
  rw [hcomp] at hrun
  exact ⟨t1, res1, hrun, hffi, hrc⟩

theorem crep_to_loop_clocked_sim {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (t : LoopSemStateFiniteExact width σ)
    (crep_code : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (lc : Nat) (c : AsmArchitecture)
    (prog : CrepProgHOL width) (k : Nat)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (hmd : s.memaddrs = (fun address => t.mdomain address = true))
    (hbe : s.be = t.be)
    (hsh : s.shMemaddrs = (fun address => t.shMdomain address = true))
    (hffi : s.ffi = t.ffi)
    (hbase : s.baseAddr = t.baseAddr)
    (htop : s.topAddr = t.topAddr)
    (hmem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hglob : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hdist : (crep_code.map Prod.fst).Nodup)
    (hscode : s.code = alistToFmapCodeExact crep_code)
    (htcode : t.code = sptFromAList (compileProgHOLExact c crep_code))
    (hloc : s.locals = HolFiniteMapExact.empty)
    (hmf : (crepToLoopMakeFuncsExactHOL crep_code).lookup start = some (lc, 0))
    (hprog : holAlookup crep_code start = some ([], prog))
    (hev : evalCrepSemHOLProgExact { s with clock := k } (.call none start []) = (res, s1))
    (hne : res ≠ some .error) :
    ∃ k' t',
      LoopSemStateFiniteExact.evaluate
        (.call none (some lc) [] none : HolLoopProg width)
        { t with clock := k + k' } =
        (Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res, t') ∧
      s1.ffi = t'.ffi := by
  let nctxt : CrepToLoopContextExact :=
    mkCtxtExact c HolFiniteMapExact.empty (crepToLoopMakeFuncsExactHOL crep_code) 0
  have hcode2 : crepToLoopCodeRel2Exact nctxt s.code t.code := by
    rw [hscode, htcode]
    exact mkCtxtCodeImpCodeRel2Exact c crep_code start prog ⟨hdist, hprog⟩
  have hlc : findLabExact nctxt start = lc := by
    simp [findLabExact, nctxt, mkCtxtExact, hmf]
  have hdv : crepToLoopDistinctVarsExact nctxt.vars := by
    intro x y n m hx
    simp [nctxt, mkCtxtExact, HolFiniteMapExact.empty] at hx
  have hcm : crepToLoopCtxtMaxExact nctxt.vmax nctxt.vars := by
    intro v m hv
    simp [nctxt, mkCtxtExact, HolFiniteMapExact.empty] at hv
  have hmf' : (crepToLoopMakeFuncsExactHOL crep_code).lookup start =
      some (findLabExact nctxt start, 0) := by
    rw [hlc]; exact hmf
  obtain ⟨k', res', t', hrun, hsr, hres⟩ :=
    crepToLoopCodeRelEvaluateCallCorrect nctxt s.code t.code start
      { s with clock := k } res s1 { t with clock := k } crep_code lc prog hcode2 hev
      ⟨hbe, hsh, hmd, rfl, hffi, hbase, htop, hmem, hglob, hloc, rfl, rfl⟩ hmf'
      ⟨hlc, hscode, rfl, hprog, hdv, hcm⟩ hne
  rw [hlc] at hrun
  have hrun' : LoopSemStateFiniteExact.evaluate (.call none (some lc) [] none : HolLoopProg width)
      { t with clock := k + k' } = (res', t') := by
    have heq : ({ { t with clock := k } with clock := k + k' } :
        LoopSemStateFiniteExact width σ) = { t with clock := k + k' } := by
      cases t; rfl
    rw [← heq]
    exact hrun
  rw [hres] at hrun'
  exact ⟨k', t', hrun', hsr.2.2.2.2.1⟩

theorem crep_inline_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ)
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (start : MlString)
    (inl_fname : List CrepInlineMapHOLName)
    (k : Nat)
    (hsr : CrepInlineExact.crepInlineStateRelCodeExact s t)
    (hls : CrepInlineExact.crepInlineLocalsStrongRelExact s t)
    (hd : (crep_code.map Prod.fst).Nodup)
    (hs : s.code = alistToFmapCodeExact crep_code)
    (ht : t.code = alistToFmapCodeExact (CrepInlineCanonical.compileInlTopHOLExact inl_fname crep_code))
    (hne : (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1 ≠ some .error) :
    (evalCrepSemHOLProgExact { t with clock := k } (.call none start [])).1 =
      (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1 ∧
    (evalCrepSemHOLProgExact { t with clock := k } (.call none start [])).2.ffi =
      (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).2.ffi := by
  let inl_fs := CrepInlineCanonical.alistToFmapHOLExact
    (crep_code.filter fun triple => inl_fname.contains triple.1)
  have ht' : t.code = alistToFmapCodeExact
      (CrepInlineCanonical.compileInlProgHOLExact inl_fs crep_code) := by
    rw [ht, CrepInlineCanonical.compileInlTopHOLExact]
    rw [CrepInlineCanonical.compileInlProgHOLExactWithSupport_eq_compileInlProgHOLExact]
  have hsub : HolFiniteMapExact.submap inl_fs s.code := by
    intro key v h
    rw [hs]
    have hm := flookup_fupdateList_reverse_mem' _ key v h
    exact flookup_fupdateList_reverse_of_mem crep_code key v hd
      (List.mem_filter.mp hm).1
  have hci := CrepInlineStateRelImpSemantics.codeInl_of_alist s t crep_code inl_fs hd hs ht'
  exact CrepInlineStateRelImpSemantics.entry_agree s t start inl_fs hsr hls hsub hci k hne

theorem pan_to_crep_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
    (pan_code : List (DeclHOL width)) (start : MlS) (k : Nat)
    (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
    (hsr : panToCrepStateRelFiniteExact s t)
    (hdist : ((functionsHOL pan_code).map Prod.fst).Nodup)
    (hscode : s.code = HolFiniteMapExact.empty.updateList (functionsHOL pan_code).reverse)
    (htcode : t.code = HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse)
    (hloc : s.locals = HolFiniteMapExact.empty)
    (hlocal : ∀ entry ∈ functionsHOL pan_code, localisedProgHOL entry.2.2.1 = true)
    (hsize : sizeOfEidsHOL pan_code < 2 ^ width)
    (hdom : ∀ key, (s.eshapes.lookup key).isSome =
      ((getEidsFromDeclsHOL pan_code).lookup key).isSome)
    (hev : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none start [] : ProgHOL width) = (res, s1))
    (hne : res ≠ some .error) :
    ∃ res1 t1,
      evalCrepSemHOLProgExact { t with clock := k }
        (.call none start [] : CrepProgHOL width) = (res1, t1) ∧
      res1 ≠ some .error ∧
      t1.ffi = s1.ffi ∧
      (match res1 with
       | some .timeOut => .Incomplete
       | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
       | some (.return _) => .CompleteResult HolOutcome.success
       | _ => .RunError) = panEntryClass res := by
  let ctxt : PanToCrepContextExact width :=
    mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL pan_code)) 0
      (getEidsFromDeclsHOL pan_code)
  have hsr' : panToCrepStateRelFiniteExact ({ s with clock := k } : PanSemStateFiniteExact width σ)
      ({ t with clock := k } : CrepSemHOLState width σ) := by
    obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, h10⟩ := hsr
    exact ⟨h1, h2, h3, h4, h5, rfl, h7, h8, h9, h10⟩
  have hcode : codeRelExactHOLW ctxt ({ s with clock := k } : PanSemStateFiniteExact width σ).code
      ({ t with clock := k } : CrepSemHOLState width σ).code := by
    show codeRelExactHOLW ctxt s.code t.code
    rw [hscode, htcode]
    exact mkCtxtCodeImpCodeRelExactHOLW pan_code hdist hlocal
  have hexcp : panToCrepExcpRelFiniteExact ctxt.eids
      ({ s with clock := k } : PanSemStateFiniteExact width σ).eshapes :=
    getEidsImpExcpRelExact s.eshapes pan_code ⟨hsize, hdom⟩
  have hlocals : panToCrepLocalsRelFiniteExact ctxt
      ({ s with clock := k } : PanSemStateFiniteExact width σ).locals
      ({ t with clock := k } : CrepSemHOLState width σ).locals := by
    show panToCrepLocalsRelFiniteExact ctxt s.locals t.locals
    rw [hloc]
    exact mkCtxtImpLocalsRelExact _ _ _
  obtain ⟨res1, t1, hrun, hsr1, _, _, hres⟩ :=
    pcCompileCorrect (.call none start []) { s with clock := k } res s1 { t with clock := k } ctxt
      ⟨hev, hne, hsr', hcode, hexcp, hlocals, by simp [localisedProgHOL, everyExpListHOL]⟩
  have hcomp : compileProgExactHOLW ctxt (.call none start [] : ProgHOL width) =
      (.call none start [] : CrepProgHOL width) := by
    simp [compileProgExactHOLW, compileCallNoReturnExactHOLW, compileExpExactHOLWList]
  rw [hcomp] at hrun
  refine ⟨res1, t1, hrun, ?_, hsr1.2.2.2.2.2.2.2.1.symm, ?_⟩
  · rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only at hres <;>
      (try split at hres) <;> first | exact False.elim hres | exact hne rfl | (rcases hres with ⟨rfl, _⟩ | rfl; rintro ⟨⟩)
  · rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only [panEntryClass] at hres ⊢ <;>
      (try split at hres) <;> first | exact False.elim hres | exact hne rfl | (rcases hres with ⟨rfl, _⟩ | rfl; rfl)

theorem pan_simp_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (s t : PanSemStateFiniteExact width σ) (start : MlS) (k : Nat)
    (hrel : PanSimp.stateRel s t t.code)
    (hne : (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none start [] : ProgHOL width)).1 ≠ some .error) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState { t with clock := k }
      (.call none start [] : ProgHOL width)).1 =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
        (.call none start [] : ProgHOL width)).1 ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState { t with clock := k }
      (.call none start [] : ProgHOL width)).2.ffi =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
        (.call none start [] : ProgHOL width)).2.ffi := by
  obtain ⟨ht, hnone, hsome⟩ := hrel
  rcases hs : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none start [] : ProgHOL width) with ⟨result, sourcePost⟩
  have hne' : result ≠ some .error := by simpa only [hs] using hne
  obtain ⟨hsim, _⟩ := PanSimp.codeSimAll (.call none start []) { s with clock := k }
    result sourcePost t.code hs hne' ⟨hnone, hsome⟩
  have htk : ({ t with clock := k } : PanSemStateFiniteExact width σ) =
      { s with clock := k, code := t.code } := by
    rw [ht]
  rw [htk, hsim]
  exact ⟨rfl, rfl⟩

theorem pan_structs_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateFiniteExact width σ) (start : MlS)
    (context : Pancake.PanStructs.CompileShapeExact.ContextExact) (k : Nat)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (hstructs : context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)))
    (hlocals : source.locals = HolFiniteMapExact.empty)
    (hfields : feveryHOL
      (fun entry => valueFldsOkHOLExact source.structs entry.2)
      source.globals)
    (hwf : feveryHOL
      (fun entry => isWfShapeValueHOLExact source.structs entry.2)
      source.globals)
    (hclocals : context.locals = [])
    (hglobals : Pancake.Proofs.PanStructs.ShapeMap.shapeMap context.globals =
      source.globals.map2 (fun entry => shapeOfHOLExact entry.2))
    (hinfos : Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact source.structs)
    (hev : PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
      (.call none start [] : ProgHOL width) = (res, post))
    (hne : res ≠ some .error) :
    PanSemStateFiniteExact.evaluateHOLFiniteState
      { Pancake.Proofs.PanStructs.ConvertState.convertStateExact context source with clock := k }
      (.call none start [] : ProgHOL width) =
      (convertResHOL res,
        Pancake.Proofs.PanStructs.ConvertState.convertStateExact context post) := by
  have hlocalfields : feveryHOL
      (fun entry => valueFldsOkHOLExact source.structs entry.2)
      source.locals := by
    simp [hlocals, feveryHOL, HolFiniteMapExact.empty]
  have hlocalwf : feveryHOL
      (fun entry => isWfShapeValueHOLExact source.structs entry.2)
      source.locals := by
    simp [hlocals, feveryHOL, HolFiniteMapExact.empty]
  have hlocalmap : Pancake.Proofs.PanStructs.ShapeMap.shapeMap context.locals =
      source.locals.map2 (fun entry => shapeOfHOLExact entry.2) := by
    rw [hclocals, hlocals]
    apply HolFiniteMapExact.ext
    rfl
  obtain ⟨hrun, _⟩ := Pancake.Proofs.PanStructs.CompileCorrectExact.compileCorrectExact
    (.call none start []) { source with clock := k } post context res
    ⟨hev, hstructs, hlocalfields, hfields, hlocalwf, hwf, hinfos, hlocalmap, hglobals, hne⟩
  have hcomp : Pancake.PanStructs.CompileShapeExact.compileProgExact context
      (.call none start [] : ProgHOL width) = .call none start [] := by
    simp [Pancake.PanStructs.CompileShapeExact.compileProgExact,
      Pancake.PanStructs.CompileShapeExact.compileExpsExact]
  rw [hcomp] at hrun
  exact hrun

theorem pan_globals_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ) (start : MlS) (k : Nat)
    (hrel : panGlobalsStateRelHOLExact true context source target)
    (hne : (PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
      (.call none start [] : ProgHOL width)).1 ≠ some .error) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState { target with clock := k }
      (.call none start [] : ProgHOL width)).1 =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
        (.call none start [] : ProgHOL width)).1 ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState { target with clock := k }
      (.call none start [] : ProgHOL width)).2.ffi =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
        (.call none start [] : ProgHOL width)).2.ffi := by
  have hclock : panGlobalsStateRelHOLExact true context
      { source with clock := k } { target with clock := k } :=
    ⟨hrel.1, hrel.2.1, hrel.2.2.1, hrel.2.2.2.1, hrel.2.2.2.2.1, rfl, hrel.2.2.2.2.2.2⟩
  rcases hs : PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
      (.call none start [] : ProgHOL width) with ⟨result, sourcePost⟩
  have hne' : result ≠ some .error := by simpa only [hs, Prod.fst] using hne
  obtain ⟨targetPost, ht, hr⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (.call none start []) { source with clock := k } result context
    { target with clock := k } sourcePost ⟨hclock, hs, hne'⟩
  have compiledEntry : compileProgExactHOL context (.call none start [] : ProgHOL width) =
      .call none start [] := by simp [compileProgExactHOL, compileExpExactHOLList]
  rw [compiledEntry] at ht
  rcases hr with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hffi, _⟩
  rw [ht]
  exact ⟨rfl, hffi.symm⟩

theorem pan_globals_init_call_clocked_shift {width : Nat} [NeZero width] {σ : Type}
    (s s' : PanSemStateFiniteExact width σ) (start start' : MlS)
    (body body' : ProgHOL width) (args' : List (MlS × ShapeHOL)) (rshape : ShapeHOL)
    (h1 : s.code.lookup start = some ([], .seq body (.call none start' []), rshape))
    (h2 : s.code.lookup start' = some (args', body', rshape))
    (h3 : PanSemStateFiniteExact.evaluateHOLFiniteState
      { s with locals := HolFiniteMapExact.empty } body = (none, s'))
    (h4 : s'.clock = s.clock)
    (c : Nat) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := c + 1 }
      (.call none start [] : ProgHOL width)).1 =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { s' with clock := c }
        (.call none start' [] : ProgHOL width)).1 ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := c + 1 }
      (.call none start [] : ProgHOL width)).2.ffi =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { s' with clock := c }
        (.call none start' [] : ProgHOL width)).2.ffi := by
  let tin : PanSemStateFiniteExact width σ := { s with locals := HolFiniteMapExact.empty }
  have hcs : EvaluateClockSubCall.Mc tin body :=
    EvaluateClockSubCall.mc_of_pair tin body
      (evaluateClockSubHOLFinite body (PanPropsEvalStateFiniteExact.ofPanSemFinite tin))
  have hzero : PanSemStateFiniteExact.evaluateHOLFiniteState { tin with clock := 0 } body =
      (none, { s' with clock := 0 }) := by
    have hpre : PanSemStateFiniteExact.evaluateHOLFiniteState tin body =
        (none, { { s' with clock := 0 } with
          clock := ({ s' with clock := 0 }).clock + s.clock }) := by
      rw [show tin = { s with locals := HolFiniteMapExact.empty } from rfl, h3]
      congr 1
      simp only [Nat.zero_add]
      rw [← h4]
    have h := hcs none { s' with clock := 0 } s.clock hpre (by simp)
    simpa only [tin, Nat.sub_self] using h
  have hstep : ∀ k, PanSemStateFiniteExact.evaluateHOLFiniteState
      { s with locals := HolFiniteMapExact.empty, clock := k } body =
      (none, { s' with clock := k }) := by
    intro k
    have h := panPropsEvaluateAddClockEq body { tin with clock := 0 } none
      { s' with clock := 0 } k ⟨hzero, by simp⟩
    simpa only [tin, Nat.zero_add] using h
  exact SemInitSupport.step s s' start start' body body' args' rshape h1 h2 hstep c

private theorem bvSubZero_local {width : Nat} (x : BitVec width) : x - 0 = x := by
  apply BitVec.eq_of_toNat_eq
  simp

open PanGlobalsCompileDecsStructural PanGlobalsDeclListExact PanGlobalsCompileTopSemanticsDecls PanSemStateFiniteExact in

theorem pan_globals_compile_top_clocked_shift {width : Nat} [NeZero width] {σ : Type}
    (s t : PanSemStateFiniteExact width σ) (code : List (DeclHOL width)) (start : MlS)
    (mgs : BitVec width) (freeAddrs : BitVec width → Prop)
    (tmem : BitVec width → HolWordLab width)
    (tlocals : HolFiniteMapExact MlS (ValueHOL width))
    (h : ((functionsHOL code).map Prod.fst).Nodup ∧
      t = { s with
        topAddr := s.topAddr + mgs
        memaddrs := fun address => s.memaddrs address ∨ freeAddrs address
        memory := tmem
        locals := tlocals } ∧
      s.code = HolFiniteMapExact.empty ∧
      s.globals = HolFiniteMapExact.empty ∧
      panGlobalsByteAlignedHOL s.topAddr ∧
      goodDimindex width ∧
      mgs = panBytesInWord width *
        BitVec.ofNat width ((decShapesHOL code).map sizeOfShapeHOL).sum ∧
      freeAddrs = Flapjack.Compiler.Backend.StackRemove.addresses s.topAddr
        ((decShapesHOL code).map sizeOfShapeHOL).sum ∧
      (∀ address, s.memaddrs address → ¬ freeAddrs address) ∧
      (∀ address, s.memaddrs address → s.memory address = tmem address) ∧
      ¬ s.memaddrs (s.topAddr + mgs) ∧
      (panBytesInWord width).toNat * ((decShapesHOL code).map sizeOfShapeHOL).sum <
        2 ^ width ∧
      (∀ d ∈ code, isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) ∧
      PanSemStateFiniteExact.semanticsDecls s start code ≠ .fail)
    (s1 : PanSemStateFiniteExact width σ) (k : Nat)
    (hs1 : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := [] } (fun a => Classical.propDecidable (s.memaddrs a)) code = some s1)
    (hne : (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
      (.call none start [] : ProgHOL width)).1 ≠ some .error) :
    ∃ T,
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { t with structs := [] } (fun a => Classical.propDecidable (t.memaddrs a))
        (compileTopExactHOL code start) = some T ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
        (.call none start [] : ProgHOL width)).1 =
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
          (.call none start [] : ProgHOL width)).1 ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
        (.call none start [] : ProgHOL width)).2.ffi.ioEvents =
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
          (.call none start [] : ProgHOL width)).2.ffi.ioEvents := by
  classical
  obtain ⟨hdistinct, ht, hcode, hglobals, halign, hgood, rfl, rfl, hdisj, hmem,
    htopNot, hbound, hkinds, hnf⟩ := h
  obtain ⟨body, rshape, hmain⟩ := PanPropsHasMain.semanticsDeclsHasMainPrime s start code hnf
  have hkindsB : code.all (fun d => isFunctionHOL d || isDeclHOL d || isExnDeclHOL d) =
      true := by
    apply List.all_eq_true.mpr
    intro d hd
    rcases hkinds d hd with h | h | h <;> simp [h]
  have hstartLookup : (functionsHOL code).lookup start = some ([], body, rshape) := by
    rw [hcode, emptyUpdateListLookup _ _ hdistinct] at hmain; exact hmain
  have hevT := evaluateCompileTopOfSource _ s1 { t with structs := [] } code start _ hs1 hstartLookup
    hkinds rfl (by rw [ht])
  have hpart : resortDeclsHOL code = code.filter isExnDeclHOL ++ code.filter isDeclHOL ++
      code.filter isFunctionHOL := by
    have hnames : code.filter isNameHOL = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro d hd
      rcases hkinds d hd with h | h | h <;> cases d <;>
        first | exact Bool.noConfusion h | exact Bool.noConfusion
    simp [resortDeclsHOL, hnames]
  have hs1orig := hs1
  have hres := Flapjack.resortDeclsEvaluate { s with structs := [] } code hkindsB
  rw [← hres, hpart, Flapjack.evaluateDeclsHOLFinite_append,
    Flapjack.evaluateDeclsHOLFinite_append] at hs1
  cases hsE : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := [] } (fun a => Classical.propDecidable (s.memaddrs a))
      (code.filter isExnDeclHOL) with
  | none => simp [hsE] at hs1
  | some sE =>
  cases hsD : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      sE (fun a => Classical.propDecidable (sE.memaddrs a)) (code.filter isDeclHOL) with
  | none => simp [hsE, hsD] at hs1
  | some sD =>
  simp only [hsE, hsD, Option.bind_some] at hs1
  have hsEform := evalExnsForm _ _ sE (fun d hd => (List.mem_filter.mp hd).2) hsE
  have hs1form := evalFunsForm _ _ s1 (fun d hd => (List.mem_filter.mp hd).2) hs1
  have hsDcode : sD.code = sE.code := by
    have := evaluateDeclsHOLFinite_functions sE _ sD hsD
    rw [this, functionsHOL_filter_isDecl]
    rfl
  rcases hc : compileDecsExactHOL
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width
           ((decShapesHOL code).map sizeOfShapeHOL).sum } : PanGlobalsContextExact width)
      (fpermDecsHOL start (newMainNameHOL code) (resortDeclsHOL code)) with
    ⟨inits, funsC, exnsC, ctx⟩
  have hexplicit := PanGlobalsCompileTopSemanticsExact.evaluateDeclsCompileTopHOLFinite
    _ s1 code start [] body rshape inits funsC exnsC ctx ⟨hs1orig, hstartLookup, hkinds, hc⟩
  have hgeneric := evaluateCompileTopOfSource _ s1 { s with structs := [] } code start _ hs1orig
    hstartLookup hkinds rfl rfl
  rw [hgeneric] at hexplicit
  have htable := congrArg PanSemStateFiniteExact.code (Option.some.inj hexplicit)
  simp only at htable
  clear hexplicit hgeneric hres
  subst hsEform
  clear hsE hs1orig hpart hmain
  simp only at hsD hsDcode
  obtain ⟨N, hNdef⟩ : ∃ N, N = ((decShapesHOL code).map sizeOfShapeHOL).sum := ⟨_, rfl⟩
  obtain ⟨nm, hnm⟩ : ∃ nm, nm = newMainNameHOL code := ⟨_, rfl⟩
  rw [← hNdef] at ht hdisj htopNot hbound hc
  rw [← hnm] at hc htable
  obtain ⟨T, hT⟩ : ∃ T : PanSemStateFiniteExact width σ, T = { t with
    structs := []
    code := t.code.updateList (functionsHOL (compileTopExactHOL code start))
    eshapes := t.eshapes.updateList (exceptionsHOL (compileTopExactHOL code start)) } :=
    ⟨_, rfl⟩
  have hTcode : T.code = (HolFiniteMapExact.empty.update
      (start, [], .seq (nestedSeqHOL inits) (.call none nm []), rshape)).updateList
      ((functionsHOL (fpermDecsHOL start nm code)).map (fun entry =>
        (entry.1, entry.2.1, compileProgExactHOL ctx entry.2.2.1, entry.2.2.2))) := by
    rw [hT]; simp only; rw [ht]; simp only; rw [htable, hcode]; rfl
  have hcD : compileDecsExactHOL
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width N } :
         PanGlobalsContextExact width) (code.filter isDeclHOL) = (inits, [], [], ctx) := by
    have := compile_decs_FILTER_declsHOL _ _ _ _ _ _ hc
    rwa [filterDeclFperm, filterDeclResort] at this
  have hND : ((decShapesHOL (code.filter isDeclHOL)).map sizeOfShapeHOL).sum = N := by
    rw [(dec_shapes_FILTERHOL code).2.2.1]; exact hNdef.symm
  obtain ⟨t', hrun, hrel', hclk, hffi, hloc, -⟩ :=
    PanGlobalsInitGlobalsAssembly.initGlobalsAll _ (code.filter isDeclHOL) _ sD
      inits [] [] ctx { T with locals := HolFiniteMapExact.empty } _
      ⟨hsD, fun d hd => (List.mem_filter.mp hd).2, hcD, by
        unfold panGlobalsStateRelHOLExact
        subst hT ht
        refine ⟨?_, fun h => absurd h (by decide), rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_,
          fun a h => Or.inl h, rfl, hmem, rfl, ?_, ?_, ?_, ?_, hgood⟩
        · change s.topAddr = s.topAddr + panBytesInWord width * BitVec.ofNat width N -
            panBytesInWord width * BitVec.ofNat width N
          rw [BitVec.add_sub_cancel]
        · rw [exceptionsFilterExn, exceptions_compile_topHOL code start _ hstartLookup]
        · intro name value h
          rw [hglobals] at h
          cases h
        · intro name shape address h
          cases h
        · intro f ps p rs h
          rw [hcode] at h
          cases h
        · intro _ _ _ _ _ _ _ h
          exact absurd (by rw [hglobals]; rfl) h
        · rintro (h | h)
          · exact htopNot h
          · exact topNotInAddresses hgood _ _ hbound h
        · exact alignedAdd hgood _ _ halign
            (PanGlobalsInitGlobalsAlignment.byteAlignedBytesInWordMulHOL _ hgood), rfl, by
      intro a h
      rw [hND]
      subst hT ht
      change ¬ Flapjack.Compiler.Backend.StackRemove.addresses
        (s.topAddr + panBytesInWord width * BitVec.ofNat width N -
          panBytesInWord width * BitVec.ofNat width N - 0) N a
      rw [bvSubZero_local, BitVec.add_sub_cancel]
      exact hdisj a h, by
      intro a h
      rw [hND] at h
      subst hT ht
      change Flapjack.Compiler.Backend.StackRemove.addresses
        (s.topAddr + panBytesInWord width * BitVec.ofNat width N -
          panBytesInWord width * BitVec.ofNat width N - 0) N a at h
      rw [bvSubZero_local, BitVec.add_sub_cancel] at h
      exact Or.inr h,
      alignedZero, hcode, by
      rintro v sh addr ⟨h1, -⟩
      change (s.globals.lookup v).isSome = true at h1
      rw [hglobals] at h1
      (cases h1), by rw [hND]; exact hbound⟩
  have hnmFresh : nm ∉ (functionsHOL code).map Prod.fst := by
    rw [hnm]; exact new_main_name_correctHOL code
  have hstartMem : start ∈ (functionsHOL code).map Prod.fst :=
    List.mem_map.mpr ⟨_, lookupMem _ _ _ hstartLookup, rfl⟩
  have hnmStart : nm ≠ start := fun h => hnmFresh (h ▸ hstartMem)
  have hfpNodup := ALL_DISTINCT_fperm_decsHOL start nm code hdistinct
  have hLkeys : ((functionsHOL (fpermDecsHOL start nm code)).map (fun entry =>
      (entry.1, entry.2.1, compileProgExactHOL ctx entry.2.2.1, entry.2.2.2))).map Prod.fst =
      (functionsHOL (fpermDecsHOL start nm code)).map Prod.fst := by
    rw [List.map_map]; rfl
  have hLNodup := hLkeys ▸ hfpNodup
  have hTlookup : ∀ f entry, (f, entry) ∈ functionsHOL (fpermDecsHOL start nm code) →
      T.code.lookup f = some (entry.1, compileProgExactHOL ctx entry.2.1, entry.2.2) := by
    intro f entry hmem'
    rw [hTcode, HolFiniteMapExact.lookup_updateList, fupdateListLookup,
      lookupReverseOfNodup _ _ hLNodup,
      lookupOfMemNodup _ f (entry.1, compileProgExactHOL ctx entry.2.1, entry.2.2)
        (List.mem_map.mpr ⟨(f, entry), hmem', rfl⟩) hLNodup]
  have hstartNotRenamed : start ∉ (functionsHOL (fpermDecsHOL start nm code)).map Prod.fst := by
    rw [functionsFpermDecsHOL, List.map_map]
    intro hmem'
    obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem'
    simp only [Function.comp, fpermName] at heq
    by_cases h1 : start = entry.1
    · rw [if_pos h1] at heq; exact hnmStart heq
    · rw [if_neg h1] at heq
      by_cases h2 : nm = entry.1
      · exact hnmFresh (List.mem_map.mpr ⟨entry, hentry, h2.symm⟩)
      · rw [if_neg h2] at heq; exact h1 heq.symm
  have hL1 : T.code.lookup start =
      some ([], .seq (nestedSeqHOL inits) (.call none nm []), rshape) := by
    rw [hTcode, HolFiniteMapExact.lookup_updateList, fupdateListLookup,
      lookupNoneOfNotMem _ _ (by
        rw [List.map_reverse, List.mem_reverse, hLkeys]; exact hstartNotRenamed)]
    simp [HolFiniteMapExact.update, FUPDATE]
  have hbodyMem : (nm, ([] : List (MlS × ShapeHOL)), fpermHOL start nm body, rshape) ∈
      functionsHOL (fpermDecsHOL start nm code) := by
    rw [functionsFpermDecsHOL]
    refine List.mem_map.mpr ⟨(start, [], body, rshape), lookupMem _ _ _ hstartLookup, ?_⟩
    simp [fpermName]
  have hL2 := hTlookup nm _ hbodyMem
  have hsDempty : sD.code = HolFiniteMapExact.empty := hsDcode.trans hcode
  have hupd : ∀ (m : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
      (l : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)),
      m.updateList l = m.updateListEq l := by
    intro m l
    apply HolFiniteMapExact.ext
    funext k'
    simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_updateListEq]
    rw [FUPDATE_LIST_HOL_eq_FUPDATE_LIST]
  have hC2 : fpermCodeHOL start nm s1.code =
      HolFiniteMapExact.empty.updateList (functionsHOL (fpermDecsHOL start nm code)) := by
    rw [hs1form]
    simp only
    rw [hsDempty, functionsHOL_filter_isFunction, hupd, hupd,
      fpermCodeHOL_updateList_functions, fpermCodeHOL_empty]
  have hinv := Flapjack.evaluateInvariantsHOLFinite (nestedSeqHOL inits)
    (PanPropsEvalStateFiniteExact.ofPanSemFinite { T with locals := HolFiniteMapExact.empty })
    none (PanPropsEvalStateFiniteExact.ofPanSemFinite t') (by
      simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite, hrun])
  have htcode : t'.code = T.code := hinv.2.2.2.2.2.2.1
  have hrelT : panGlobalsStateRelHOLExact true ctx
      (emptyLocalsHOLFinite { s1 with code := (HolFiniteMapExact.empty.updateList
        (functionsHOL (fpermDecsHOL start nm code))) }) t' := by
    subst hs1form
    obtain ⟨h1, -, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, h16, h17, h18,
      h19⟩ := hrel'
    refine ⟨h1, fun _ => ?_, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ?_, h16,
      h17, h18, h19⟩
    · rw [hloc]; rfl
    · intro f ps p rs hlk
      change (HolFiniteMapExact.empty.updateList
        (functionsHOL (fpermDecsHOL start nm code))).lookup f = _ at hlk
      rw [emptyUpdateListLookup _ _ hfpNodup] at hlk
      rw [htcode]
      exact hTlookup f (ps, p, rs) (lookupMem _ _ _ hlk)
  
  have hshift := pan_globals_init_call_clocked_shift T t' start nm
    (nestedSeqHOL inits) (compileProgExactHOL ctx (fpermHOL start nm body)) [] rshape
    hL1 hL2 hrun hclk k
  have hfperm_k : PanSemStateFiniteExact.evaluateHOLFiniteState
      { s1 with code := fpermCodeHOL start nm s1.code, clock := k }
      (.call none (fpermName start nm start) [] : ProgHOL width) =
      (fun outcome : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ =>
        (outcome.1, { outcome.2 with code := fpermCodeHOL start nm outcome.2.code }))
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
          (.call none start [] : ProgHOL width)) := by
    simpa [fpermHOL] using evaluateFpermPrimeHOL start nm (.call none start []) s1 k
  have hname : fpermName start nm start = nm := by simp [fpermName]
  rw [hname, hC2] at hfperm_k
  let fpermCode := HolFiniteMapExact.empty.updateList (functionsHOL (fpermDecsHOL start nm code))
  have hempty_obs := Flapjack.panGlobals_call_emptyLocals_observation
    { s1 with code := fpermCode, clock := k } nm
  have hempty_eq : ({ emptyLocalsHOLFinite { s1 with code := fpermCode } with clock := k } :
      PanSemStateFiniteExact width σ) =
      emptyLocalsHOLFinite { s1 with code := fpermCode, clock := k } := rfl
  have hne_empty : (PanSemStateFiniteExact.evaluateHOLFiniteState
      { emptyLocalsHOLFinite { s1 with code := fpermCode } with clock := k }
      (.call none nm [] : ProgHOL width)).1 ≠ some .error := by
    rw [hempty_eq, ← (Prod.mk.inj hempty_obs).1, show fpermCode = _ from rfl, hfperm_k]
    exact hne
  have hglob_k := pan_globals_clocked_agree ctx
    (emptyLocalsHOLFinite { s1 with code := fpermCode }) t' nm k hrelT hne_empty
  refine ⟨T, ?_, ?_, ?_⟩
  · rw [hT]
    exact hevT
  · rw [hshift.1, hglob_k.1, hempty_eq, ← (Prod.mk.inj hempty_obs).1, show fpermCode = _ from rfl,
      hfperm_k]
  · rw [hshift.2, hglob_k.2, hempty_eq, ← (Prod.mk.inj hempty_obs).2, show fpermCode = _ from rfl,
      hfperm_k]

open Pancake.PanStructs.CompileShapeExact
open Pancake.Proofs.PanStructs.ConvertState
open Pancake.Proofs.PanStructs.ShapeMap
open Pancake.Proofs.PanStructs.StructInfosOkExact
open Pancake.Proofs.PanToWord.InitialComposition in

theorem pan_simp_structs_globals_clocked_sim {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (code : List (DeclHOL width)) (start : MlS) (globalsSize : Nat)
    (hfail : PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (hdist : ((functionsHOL code).map Prod.fst).Nodup)
    (hcode : source.code = HolFiniteMapExact.empty)
    (hlocals : source.locals = HolFiniteMapExact.empty)
    (hglobals : source.globals = HolFiniteMapExact.empty)
    (heshapes : source.eshapes = HolFiniteMapExact.empty)
    (hsize : globalsSize = ((decShapesHOL code).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum)
    (halloc : globalsAllocatableHOL source code)
    (halign : panGlobalsByteAlignedHOL source.topAddr) (hdim : goodDimindex width)
    (hmem : ∀ address, source.memaddrs address →
      target.memory address = wlabWlocExact (source.memory address))
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : res_src ≠ some .error) :
    let globalState : PanSemStateFiniteExact width σ :=
      { source with
        topAddr := source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize
        memaddrs := fun address => source.memaddrs address ∨
          Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
        memory := wlocWlabHOL ∘ target.memory
        locals := source.locals }
    ∃ T,
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { globalState with structs := [] }
        (fun a => Classical.propDecidable (globalState.memaddrs a))
        (compileTopExactHOL (compileTopExact (panSimpDeclsHOL code)) start) = some T ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
        (.call none start [] : ProgHOL width)).1 = convertResHOL res_src ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
        (.call none start [] : ProgHOL width)).2.ffi.ioEvents = s_src_post.ffi.ioEvents := by
  classical
  intro globalState
  
  have hrel0 : PanSimp.stateRel { source with structs := stCtxt }
      { source with structs := stCtxt } { source with structs := stCtxt }.code := by
    refine ⟨rfl, fun _ h => h, ?_⟩
    intro f vs p sh he
    simp [hcode, HolFiniteMapExact.empty] at he
  obtain ⟨s_simp, hev_simp, hrel_simp⟩ := PanSimp.stateRelImpEvaluateDeclsHOL
    { source with structs := stCtxt } code { source with structs := stCtxt } s_decls start
    ⟨hrel0, hdist, hev_decls⟩
  have hsimp_agree := pan_simp_clocked_agree s_decls s_simp start k hrel_simp
    (by rw [hev_call]; exact hne_src)
  rcases hev_simp_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_simp with clock := k }
      (.call none start [] : ProgHOL width) with ⟨res_simp, s_simp_post⟩
  have hres_simp : res_simp = res_src := by
    have h1 := hsimp_agree.1
    rw [hev_simp_call, hev_call] at h1
    exact h1
  have hffi_simp : s_simp_post.ffi = s_src_post.ffi := by
    have h2 := hsimp_agree.2
    rw [hev_simp_call, hev_call] at h2
    exact h2
  rw [hres_simp] at hev_simp_call
  
  let code1 := panSimpDeclsHOL code
  have hnames1 : decsStcnamesHOLExact [] code1 = some stCtxt := by
    rw [decsStcnamesHOLExact_panSimpDeclsHOL_eq]
    exact hst
  let context := getNamesExact { structs := [], locals := [], globals := [] } code1
  have hctx := decsStcnamesToGetNames [] code1 stCtxt
    ({ structs := [], locals := [], globals := [] } : ContextExact) ⟨hnames1, rfl⟩
  have hctxstructs : context.structs = stCtxt.map (fun entry => (entry.1, entry.2.fields)) := by
    simp [context, hctx]
  have hctxlocals : context.locals = [] := by simp [context, hctx]
  have hctxglobals : context.globals = [] := by simp [context, hctx]
  have hinfos := decsStcnamesInfosOk [] code1 stCtxt ()
    ⟨hnames1, by simp [structInfosOkHOLExact]⟩
  have hmapempty : ∀ {α β γ : Type} (f : α × β → γ),
      HolFiniteMapExact.map2 f (HolFiniteMapExact.empty : HolFiniteMapExact α β) =
        HolFiniteMapExact.empty := by
    intro α β γ f
    apply HolFiniteMapExact.ext
    rfl
  have hfields : feveryHOL (fun entry => valueFldsOkHOLExact stCtxt entry.2) source.globals := by
    simp [hglobals, feveryHOL, HolFiniteMapExact.empty]
  have hwf : feveryHOL (fun entry => isWfShapeValueHOLExact stCtxt entry.2) source.globals := by
    simp [hglobals, feveryHOL, HolFiniteMapExact.empty]
  have hshapes : shapeMap context.globals =
      source.globals.map2 (fun entry => shapeOfHOLExact entry.2) := by
    rw [hctxglobals, hglobals, hmapempty]
    rfl
  rcases hcompile : compileDeclsExact context code1 with ⟨compiled, finalContext⟩
  have hsim := Pancake.Proofs.PanStructs.CompileDeclsCorrectExact.compileDeclsCorrectExact
    { source with structs := stCtxt } code1 s_simp context finalContext compiled
    ⟨hev_simp, hctxstructs, hctxlocals, hinfos, hfields, hwf, hshapes, hcompile⟩
  obtain ⟨hrun_decls, _, hfinal, hpostfields, hpostwf, hpoststructs, hpostlocals, hpostshapes⟩ := hsim
  have htop_eq : compileTopExact code1 = compiled := by
    change (compileDeclsExact context code1).1 = compiled
    rw [hcompile]
  have hboot : convertStateExact finalContext { source with structs := stCtxt } =
      { source with structs := [] } := by
    simp [convertStateExact, convertCodeExact, convertEshapesExact,
      hlocals, hglobals, hcode, heshapes, hmapempty, hfinal]
  have hs1 : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := [] }
      (fun address => Classical.propDecidable (source.memaddrs address))
      (compileTopExact code1) = some (convertStateExact finalContext s_simp) := by
    rw [htop_eq]
    exact (congrArg (fun state : PanSemStateFiniteExact width σ =>
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
        (fun address => Classical.propDecidable (state.memaddrs address)) compiled)
      hboot).symm.trans hrun_decls
  have hstruct_call := pan_structs_clocked_agree s_simp start finalContext k res_src s_simp_post
    (by simpa [hfinal, hpoststructs] using hctxstructs)
    (by simpa [hpostlocals] using hlocals)
    (by simpa [hpoststructs] using hpostfields)
    (by simpa [hpoststructs] using hpostwf)
    (by simpa [hfinal] using hctxlocals)
    (by simpa [hfinal] using hpostshapes)
    (by simpa [hpoststructs] using hinfos)
    hev_simp_call hne_src
  
  have hrel0_src : PanSimp.stateRel source source source.code := by
    refine ⟨by cases source; rfl, fun _ h => h, ?_⟩
    intro f vs p sh he
    simp [hcode, HolFiniteMapExact.empty] at he
  have hsimp_sem := PanSimp.stateRelImpSemanticsDeclsHOL source source code start
    ⟨hrel0_src, hdist, hcode, hcode, hfail⟩
  have hsimpnf : PanSemStateFiniteExact.semanticsDecls source start code1 ≠ .fail := by
    rw [← hsimp_sem]; exact hfail
  have hstruct_sem := Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact.compileTopSemanticsDeclsExact
    source start code1 ⟨hsimpnf, hlocals, hcode, hglobals⟩
  have hboot_esh : { source with eshapes := source.eshapes.map2 (fun entry =>
      compileShapeExact (getNamesExact { structs := [], locals := [], globals := [] } code1).structs
        entry.2) } = source := by
    have hm : source.eshapes.map2 (fun entry =>
        compileShapeExact (getNamesExact { structs := [], locals := [], globals := [] } code1).structs
          entry.2) = source.eshapes := by
      rw [heshapes, hmapempty]
    rw [hm]
  rw [hboot_esh] at hstruct_sem
  have hstructnf : PanSemStateFiniteExact.semanticsDecls source start (compileTopExact code1) ≠ .fail := by
    rw [← hstruct_sem]; exact hsimpnf
  let structCode := compileTopExact code1
  have hdiststruct : ((functionsHOL structCode).map Prod.fst).Nodup := by
    dsimp only [structCode, code1]
    rw [functionNamesStructsCompileTopHOL, functionNamesCompileProgHOL]
    exact hdist
  have hsizelist := semanticsSizeDecsStcnamesCompileStructsHOL source start code1
    ⟨hsimpnf, hglobals⟩
  have hsizecompiled : ((decShapesHOL structCode).map sizeOfShapeHOL).sum = globalsSize := by
    dsimp only [structCode, code1]
    rw [hsizelist, decShapesCompileProgHOL, decsStcnamesHOLExact_panSimpDeclsHOL_eq]
    exact hsize.symm
  have halloc' := halloc
  dsimp only [globalsAllocatableHOL] at halloc'
  rw [← hsize] at halloc'
  obtain ⟨_, hdisjoint, htopnot, hbound⟩ := halloc'
  have hmemory : ∀ address, source.memaddrs address →
      source.memory address = (wlocWlabHOL ∘ target.memory) address := by
    intro address ha
    simp only [Function.comp_apply, hmem address ha, wlocWlabWlabWlocHOL]
  have hne_struct : (PanSemStateFiniteExact.evaluateHOLFiniteState
      { convertStateExact finalContext s_simp with clock := k }
      (.call none start [] : ProgHOL width)).1 ≠ some .error := by
    rw [hstruct_call]
    rcases res_src with _ | r_val
    · intro h; cases h
    · cases r_val <;> intro h <;> first | exact hne_src rfl | cases h
  obtain ⟨T, hevT, hresT, hev_ioT⟩ := pan_globals_compile_top_clocked_shift
    source globalState structCode start
    (panBytesInWord width * BitVec.ofNat width globalsSize)
    (Compiler.Backend.StackRemove.addresses source.topAddr globalsSize)
    (wlocWlabHOL ∘ target.memory) source.locals
    ⟨hdiststruct, rfl, hcode, hglobals, halign, hdim,
      (by rw [hsizecompiled]), (by rw [hsizecompiled]),
      (fun address hs hf => hdisjoint address ⟨hs, hf⟩), hmemory,
      htopnot, (by simpa [hsizecompiled, panBytesInWord,
        Compiler.Backend.StackRemove.bytesInWord, Nat.mul_comm] using hbound),
      compileTopNoNames _, hstructnf⟩
    (convertStateExact finalContext s_simp) k hs1 hne_struct
  refine ⟨T, hevT, ?_, ?_⟩
  · rw [hresT, hstruct_call]
  · rw [hev_ioT, hstruct_call]
    show (convertStateExact finalContext s_simp_post).ffi.ioEvents = s_src_post.ffi.ioEvents
    have hffi_conv : (convertStateExact finalContext s_simp_post).ffi = s_simp_post.ffi := rfl
    rw [hffi_conv, hffi_simp]

open PanToCrepStateRelImpSemanticsTop
open LoopToWordStateRelImpSemanticsSupport in
private theorem list_lookup_isSome_iff_local {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) : (List.lookup k l).isSome = true ↔ k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp only [List.lookup, Option.isSome, List.map_nil, List.not_mem_nil, reduceCtorEq]
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    by_cases h : k = a
    · subst h; simp only [List.lookup_cons, beq_self_eq_true, Option.isSome_some, List.map_cons, List.mem_cons, true_or]
    · have hbeq : (k == a) = false := beq_false_of_ne h
      simp only [List.lookup_cons, hbeq, ih, List.map_cons, List.mem_cons, h, false_or]

private theorem fupdateList_empty_eq_lookup_local {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) :
    FUPDATE_LIST FEMPTY l k = List.lookup k l.reverse := by
  have := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup l.reverse k
  simpa [FLOOKUP] using this

private theorem alistToFmap_eq_lookup_local {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) : FLOOKUP (alistToFmap l) k = List.lookup k l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    change FLOOKUP (FUPDATE (alistToFmap l) (a, b)) k = _
    rw [FLOOKUP_update, ih, List.lookup_cons]
    by_cases hk : k = a
    · subst hk; simp
    · have h1 : (a == k) = false := by simp [Ne.symm hk]
      have h2 : (k == a) = false := by simp [hk]
      simp [h1, h2]

open PanToCrepStateRelImpSemanticsTop
open LoopToWordStateRelImpSemanticsSupport in

theorem pan_to_crep_to_word_clocked_sim {width : Nat} [NeZero width] {C σ : Type}
    (globalState T : PanSemStateFiniteExact width σ)
    (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS)
    (heapLen : BitVec width)
    (hnolabels : noLabelsHOL target.memory (fun address => target.mdomain address = true))
    (_hstart : start = ofString "main")
    (hmdomain : (fun address => target.mdomain address = true) = globalState.memaddrs)
    (hshdomain : (fun address => target.shMdomain address = true) = globalState.shMemaddrs)
    (hbe : target.be = globalState.be)
    (hffi : target.ffi = globalState.ffi)
    (hcurrheap : target.store.lookup .currHeap = some (.word globalState.baseAddr))
    (hheaplen : target.store.lookup .heapLength = some (.word heapLen))
    (htop' : globalState.topAddr = globalState.baseAddr + (2 : BitVec width) * heapLen)
    (hmem_glob : globalState.memory = wlocWlabHOL ∘ target.memory)
    (hcode : globalState.code = HolFiniteMapExact.empty)
    (hglobals : globalState.globals = HolFiniteMapExact.empty)
    (hlocals : globalState.locals = HolFiniteMapExact.empty)
    (heshapes : globalState.eshapes = HolFiniteMapExact.empty)
    (htcode : target.code = sptFromAList
      (loopToWordCompileProgHOL (compileProgHOLExact arch (compileProgDeclsHOLW panCode))))
    (hloc0 : sptLookup 0 target.locals = some (WordLocW.loc 1 0))
    (hdim : goodDimindex width)
    (hdist_pan : ((functionsHOL panCode).map Prod.fst).Nodup)
    (hlocal_pan : ∀ entry ∈ functionsHOL panCode, localisedProgHOL entry.2.2.1 = true)
    (hall_pan : panCode.all (fun x => isFunctionHOL x || isExnDeclHOL x) = true)
    (hpanSize : sizeOfEidsHOL panCode < 2 ^ width)
    (hmf : (crepToLoopMakeFuncsExactHOL (compileProgDeclsHOLW panCode)).lookup start =
      some (firstLoopName, 0))
    (hglobalnf : PanSemStateFiniteExact.semanticsDecls globalState start panCode ≠ .fail)
    (hevT : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { globalState with structs := [] }
      (fun a => Classical.propDecidable (globalState.memaddrs a)) panCode = some T)
    (c : Nat) (res_pan : Option (PanSemResultExact width))
    (s_pan_post : PanSemStateFiniteExact width σ)
    (hev_pan : PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := c }
      (.call none start [] : ProgHOL width) = (res_pan, s_pan_post))
    (hne_pan : panEntryClass res_pan ≠ .RunError) :
    ∃ k' t_word res_word,
      WordSemStateFiniteExact.evaluate
        (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
        { target with clock := c + k' } = (res_word, t_word) ∧
      t_word.ffi.ioEvents = s_pan_post.ffi.ioEvents ∧
      wordEntryClass res_word = panEntryClass res_pan := by
  classical
  have hne_pan_err : res_pan ≠ some .error := by
    intro h; subst h; exact hne_pan rfl
  
  let s0 : PanSemStateFiniteExact width σ := { globalState with structs := [] }
  let p0 := PanPropsEvalStateFiniteExact.ofPanSemFinite s0
  let hdec : DecidablePred p0.memaddrs := fun a => Classical.propDecidable _
  have hcanon : PanPropsEvalStateFiniteExact.evaluateDeclsPanPropsCanonical p0 panCode =
      some (PanPropsEvalStateFiniteExact.ofPanSemFinite T) := by
    unfold PanPropsEvalStateFiniteExact.evaluateDeclsPanPropsCanonical
    have key : ∀ (st : PanSemStateFiniteExact width σ) (h1 h2 : DecidablePred st.memaddrs),
        @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ st h1 panCode =
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ st h2 panCode := by
      intro st h1 h2
      rw [Subsingleton.elim h1 h2]
    have hE := (key p0.toPanSemFinite inferInstance hdec).trans hevT
    rw [hE]
    rfl
  have hshape := PanPropsEvalStateFiniteExact.evaluateDeclsOnlyFunsAndExnDeclsHOLFinite p0 panCode
    (PanPropsEvalStateFiniteExact.ofPanSemFinite T) hall_pan hcanon
  have hT_eq : T = { s0 with
      code := HolFiniteMapExact.empty.updateList (functionsHOL panCode)
      eshapes := HolFiniteMapExact.empty.updateList (exceptionsHOL panCode) } := by
    have h := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hshape
    simp only [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] at h
    rw [h]
    simp [PanPropsEvalStateFiniteExact.toPanSemFinite, p0,
      PanPropsEvalStateFiniteExact.ofPanSemFinite, s0, hcode, heshapes]
  
  let crepState := crepStateHOL globalState panCode globalState.memory
  let crepStatePre := { crepState with
    code := HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW panCode).reverse }
  have hsr_crep : panToCrepStateRelFiniteExact T crepStatePre := by
    rw [hT_eq]
    simp [panToCrepStateRelFiniteExact, s0, crepStatePre, crepState, crepStateHOL,
      hglobals, HolFiniteMapExact.empty]
  have hscode_T : T.code = HolFiniteMapExact.empty.updateList (functionsHOL panCode).reverse := by
    rw [hT_eq]
    apply HolFiniteMapExact.ext
    funext k
    simp only [HolFiniteMapExact.lookup_updateList]
    change FUPDATE_LIST FEMPTY _ k = FUPDATE_LIST FEMPTY _ k
    rw [fupdateList_empty_eq_lookup_local, fupdateList_empty_eq_lookup_local, List.reverse_reverse,
      PanGlobalsCompileTopSemanticsDecls.lookupReverseOfNodup _ _ hdist_pan]
  have hdom_T : ∀ key, (T.eshapes.lookup key).isSome =
      ((getEidsFromDeclsHOL panCode).lookup key).isSome := by
    intro key
    rw [hT_eq]
    show ((HolFiniteMapExact.empty.updateList (exceptionsHOL panCode)).lookup key).isSome =
      ((getEidsFromDeclsHOL panCode).lookup key).isSome
    rw [HolFiniteMapExact.lookup_updateList, holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL,
      alistToFmap_eq_lookup_local]
    change (FUPDATE_LIST FEMPTY _ key).isSome = _
    rw [fupdateList_empty_eq_lookup_local]
    apply Bool.eq_iff_iff.mpr
    rw [list_lookup_isSome_iff_local, list_lookup_isSome_iff_local, List.map_reverse,
      List.mem_reverse, getEidsEntriesHOL_eq_lengthBased]
    simp only
    rw [List.map_fst_zip (by simp)]
  have hloc_T : T.locals = HolFiniteMapExact.empty := by
    rw [hT_eq]; exact hlocals
  obtain ⟨res_crep1, t_crep1, hrun_crep1, hne_crep1_val, hffi_crep1, hclass_crep1⟩ :=
    pan_to_crep_clocked_agree T crepStatePre panCode start c res_pan s_pan_post
      hsr_crep hdist_pan hscode_T rfl hloc_T hlocal_pan hpanSize hdom_T hev_pan hne_pan_err
  
  have hne_crep1 : (evalCrepSemHOLProgExact { crepStatePre with clock := c }
      (.call none start [])).1 ≠ some .error := by
    rw [hrun_crep1]
    exact hne_crep1_val
  have hinl := crep_inline_clocked_agree crepStatePre crepState
    (compileToCrepExactHOLW panCode) start
    ((functionsHOL (panCode.filter inlinableHOL)).map Prod.fst) c
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
    (firstCompileToCrepAllDistinctExact panCode hdist_pan) rfl
    (by simp [crepState, crepStateHOL, compileProgDeclsHOLW, alistToFmapCodeExact])
    hne_crep1
  rcases hrun_crep : evalCrepSemHOLProgExact { crepState with clock := c }
      (.call none start []) with ⟨res_crep, t_crep⟩
  have hres_crep : res_crep = res_crep1 := by
    have h1 := hinl.1
    rw [hrun_crep, hrun_crep1] at h1
    exact h1
  have hffi_crep : t_crep.ffi = t_crep1.ffi := by
    have h2 := hinl.2
    rw [hrun_crep, hrun_crep1] at h2
    exact h2
  
  let crepCode := compileProgDeclsHOLW panCode
  let loopState := loopStateHOL crepState arch crepCode target.clock target.memory
  have hcrep_sem := stateRelImpSemanticsDeclsPanToCrep globalState crepState panCode start
    ⟨(by simp [panToCrepStateRelFiniteExact, crepState, crepStateHOL,
          hglobals, HolFiniteMapExact.empty]),
      hdist_pan, hcode, rfl, hlocals, heshapes, hlocal_pan, hall_pan, hpanSize, hglobalnf⟩
  have hcrepnf : crepSemantics crepState start ≠ .fail := by
    rw [hcrep_sem]; exact hglobalnf
  have hdist_crep : (crepCode.map Prod.fst).Nodup :=
    panToCrepFirstCompileProgAllDistinctExact panCode hdist_pan
  obtain ⟨prog_crep, hprog_crep⟩ :=
    crepSemantics_ne_fail_imp_holAlookup crepState crepCode start rfl rfl hdist_crep hcrepnf
  have hne_crep : res_crep ≠ some .error := by
    rw [hres_crep]
    intro h
    subst h
    rw [hrun_crep1] at hne_crep1
    exact hne_crep1 rfl
  obtain ⟨k', t_loop, hrun_loop, hffi_loop⟩ :=
    crep_to_loop_clocked_sim crepState loopState crepCode start firstLoopName arch
      prog_crep c res_crep t_crep
      (by simp [loopState, loopStateHOL]) rfl
      (by simp [loopState, loopStateHOL]) rfl rfl rfl
      (by intro address ha
          have ha' : target.mdomain address = true := (congrFun hmdomain address).symm ▸ ha
          obtain ⟨w, hw⟩ := hnolabels address ha'
          simp [crepState, crepStateHOL, loopState, loopStateHOL, hmem_glob,
            wlocWlabHOL, wlabWlocExact, hw])
      (by intro address value he
          simp [crepState, crepStateHOL, HolFiniteMapExact.empty] at he)
      hdist_crep rfl rfl rfl hmf hprog_crep hrun_crep hne_crep
  
  have hdm : loopState.mdomain = target.mdomain := by
    funext address
    have hd := congrFun hmdomain address
    apply Bool.eq_iff_iff.mpr
    simpa [loopState, loopStateHOL, crepState, crepStateHOL] using Iff.of_eq hd.symm
  have hsh : loopState.shMdomain = target.shMdomain := by
    funext address
    have hd := congrFun hshdomain address
    simp [loopState, loopStateHOL, crepState, crepStateHOL, ← hd]
  have hparamsLoop := crepToLoopCompileProgDistinctParamsHOLExact crepCode arch
    (compileProgDeclsHOLW_params_nodup panCode)
  have hrel_word : loopToWordStateRelHOLExact loopState target := by
    refine ⟨heapLen, rfl, hdm.symm, hsh.symm, rfl, hbe, hffi, hcurrheap, hheaplen, htop', ?_, ?_⟩
    · intro name value hl
      simp [loopState, loopStateHOL, HolFiniteMapExact.empty] at hl
    · intro name params body hl
      constructor
      · rw [htcode]
        exact loopToWordLookupProgSomeLookupCompileProg _ name params body hl
      · apply of_decide_eq_true
        apply (List.all_eq_true.mp hparamsLoop) (name, params, body)
        apply sptAListLookup_mem name (compileProgHOLExact arch crepCode) (params, body)
        simpa only [loopState, loopStateHOL, sptLookup_sptFromAList] using hl
  have hne_loop : Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res_crep ≠ some .error := by
    rcases res_crep with _ | r_val
    · intro h; cases h
    · cases r_val <;> intro h <;> first | exact hne_crep rfl | cases h
  obtain ⟨t_word, res_word, hrun_word, hffi_word, hrc_word⟩ :=
    loop_to_word_clocked_agree loopState target firstLoopName (c + k')
      (Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res_crep) t_loop
      hrel_word rfl hdim hloc0 hrun_loop hne_loop
  refine ⟨k', t_word, res_word, hrun_word, ?_, ?_⟩
  · rw [hffi_word, ← hffi_loop, hffi_crep, hffi_crep1]
  · rw [← hclass_crep1, ← hres_crep] at hne_pan ⊢
    rcases res_crep with _ | (_ | _ | _ | _ | _ | _) <;>
      dsimp only [Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop, resultCase] at hne_pan hrc_word ⊢ <;>
      first | exact False.elim hrc_word | exact False.elim (hne_pan rfl) |
        (rcases hrc_word with ⟨rfl, _⟩; rfl) |
        (rcases hrc_word with ⟨_, rfl, _⟩; rfl) |
        (rcases hrc_word with ⟨_, _, rfl, _⟩; rfl) |
        (subst hrc_word; rfl)

open LoopToWordStateRelImpSemanticsSupport in

theorem pan_to_word_clocked_sim {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (h : (∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
      noLabelsHOL target.memory (fun address => target.mdomain address = true) ∧
      start = ofString "main" ∧
      globalsSize = ((decShapesHOL code).map
        (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum ∧
      distinctParamsHOL (functionsHOL code) ∧
      (fun address => target.mdomain address = true) =
        (fun address => source.memaddrs address ∨ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (fun address => target.shMdomain address = true) = source.shMemaddrs ∧
      target.be = source.be ∧ target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      target.store.lookup .heapLength = some (.word heapLen) ∧
      source.topAddr = source.baseAddr + (2 : BitVec width) * heapLen - panBytesInWord width * BitVec.ofNat width globalsSize ∧
      ((functionsHOL code).map Prod.fst).Nodup ∧ panGlobalsByteAlignedHOL source.topAddr ∧
      globalsAllocatableHOL source code ∧ source.code = HolFiniteMapExact.empty ∧
      target.code = sptFromAList (panToWordCompileProgHOL arch code) ∧
      source.globals = HolFiniteMapExact.empty ∧ source.locals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL code < 2 ^ width ∧ source.eshapes = HolFiniteMapExact.empty ∧
      sptLookup 0 target.locals = some (WordLocW.loc 1 0) ∧ goodDimindex width ∧
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError) :
    ∃ k' t_word res_word,
      WordSemStateFiniteExact.evaluate
        (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
        { target with clock := (k + 1) + k' } = (res_word, t_word) ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents ∧
      wordEntryClass res_word = panEntryClass res_src := by
  classical
  have hne_src_err : res_src ≠ some .error := by
    intro herr; subst herr; exact hne_src rfl
  obtain ⟨hmem, hnolabels, hstart, hsize, _hparams, hmdomain, hshdomain, hbe, hffi,
    hcurrheap, hheaplen, htop, hdist, halign, halloc, hcode, htcode, hglobals,
    hlocals, heids, heshapes, hloc0, hdim, hfail⟩ := h
  have hglobalsSem := Pancake.Proofs.PanToWord.InitialComposition.initialToGlobalsSemantics
    source target code start globalsSize hfail hdist hcode hlocals hglobals heshapes
    hsize halloc halign hdim hmem
  let structCode := Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code)
  let panCode := compileTopExactHOL structCode start
  let globalState : PanSemStateFiniteExact width σ :=
    { source with
      topAddr := source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize
      memaddrs := fun address => source.memaddrs address ∨
        Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
      memory := wlocWlabHOL ∘ target.memory
      locals := source.locals }
  have hglobalnf : PanSemStateFiniteExact.semanticsDecls globalState start panCode ≠ .fail := by
    rw [← hglobalsSem]; exact hfail
  have hstructnf : PanSemStateFiniteExact.semanticsDecls source start structCode ≠ .fail := by
    have h1 := Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact.compileTopSemanticsDeclsExact
      source start (panSimpDeclsHOL code)
    have hs := PanSimp.stateRelImpSemanticsDeclsHOL source source code start
      ⟨(by refine ⟨?_, (fun _ h => h), ?_⟩
           · cases source; rfl
           · intro f vs p sh he; simp [hcode, HolFiniteMapExact.empty] at he),
        hdist, hcode, hcode, hfail⟩
    have he := h1 ⟨(by rw [← hs]; exact hfail), hlocals, hcode, hglobals⟩
    have hm : source.eshapes.map2 (fun entry =>
        Pancake.PanStructs.CompileShapeExact.compileShapeExact
          (Pancake.PanStructs.CompileShapeExact.getNamesExact
            { structs := [], locals := [], globals := [] } (panSimpDeclsHOL code)).structs
          entry.2) = source.eshapes := by
      rw [heshapes]; apply HolFiniteMapExact.ext; rfl
    rw [hm] at he
    rw [← he, ← hs]; exact hfail
  have hdiststruct : ((functionsHOL structCode).map Prod.fst).Nodup := by
    dsimp only [structCode]
    rw [functionNamesStructsCompileTopHOL, functionNamesCompileProgHOL]; exact hdist
  obtain ⟨mainBody, mainShape, hmain⟩ := semanticsDeclsHasMainPanToWordHOL source start structCode
    ⟨hcode, hdiststruct, hstructnf⟩
  have hpanSize : sizeOfEidsHOL panCode < 2 ^ width := by
    dsimp only [panCode]
    rw [sizeOfEidsCompileTopHOL structCode start [] mainBody mainShape hmain]
    dsimp only [structCode]
    rw [sizeOfEidsStructsCompileEqHOL, sizeOfEidsHOL_panSimpDeclsHOL_eq]
    exact heids
  have hmf : (crepToLoopMakeFuncsExactHOL (compileProgDeclsHOLW panCode)).lookup start =
      some (firstLoopName, 0) :=
    flookupMakeFuncsMainHOL structCode start mainBody mainShape hmain
  have htop' : globalState.topAddr = globalState.baseAddr + (2 : BitVec width) * heapLen := by
    change source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize = _
    rw [htop]
    exact BitVec.sub_add_cancel _ _
  have hcodeWord : target.code = sptFromAList
      (loopToWordCompileProgHOL (compileProgHOLExact arch (compileProgDeclsHOLW panCode))) := by
    simpa [panToWordCompileProgHOL, panCode, structCode, hstart, loopToWordCompileHOL] using htcode
  obtain ⟨T, hevT, hresT, hioT⟩ := pan_simp_structs_globals_clocked_sim
    source target code start globalsSize hfail hdist hcode hlocals hglobals heshapes
    hsize halloc halign hdim hmem stCtxt s_decls hst hev_decls k res_src s_src_post hev_call hne_src_err
  rcases hev_pan : PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
      (.call none start [] : ProgHOL width) with ⟨res_pan, s_pan_post⟩
  have hres_pan : res_pan = convertResHOL res_src := by
    rw [hev_pan] at hresT; exact hresT
  have hio_pan : s_pan_post.ffi.ioEvents = s_src_post.ffi.ioEvents := by
    rw [hev_pan] at hioT; exact hioT
  have hclass_conv : panEntryClass (convertResHOL res_src) = panEntryClass res_src := by
    rcases res_src with _ | (_ | _ | _ | _ | _ | _ | _) <;>
      simp [convertResHOL, panEntryClass]
  have hne_pan : panEntryClass res_pan ≠ .RunError := by
    rw [hres_pan, hclass_conv]
    exact hne_src
  obtain ⟨k', t_word, res_word, hrun_word, hio_word, hclass_word⟩ :=
    pan_to_crep_to_word_clocked_sim globalState T target arch panCode start heapLen
      hnolabels hstart hmdomain hshdomain hbe hffi hcurrheap hheaplen htop' rfl
      hcode hglobals hlocals heshapes hcodeWord hloc0 hdim
      (allDistinctCompileTopHOL start structCode hdiststruct)
      (compileTopLocalisedHOL structCode start)
      (by apply List.all_eq_true.mpr
          intro d hd
          rcases PanGlobalsCompileDecsStructural.compile_top_only_functions_or_exnsHOL structCode start d hd with h | h <;> simp [h])
      hpanSize hmf hglobalnf hevT (k + 1) res_pan s_pan_post hev_pan hne_pan
  refine ⟨k', t_word, res_word, hrun_word, ?_, ?_⟩
  · rw [hio_word, hio_pan]
  · rw [hclass_word, hres_pan, hclass_conv]

open Classical in

theorem semanticsDecls_terminate_extract {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (start : MlS) (decls : List (DeclHOL width))
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hterm : PanSemStateFiniteExact.semanticsDecls s start decls = .terminate outcome events) :
    ∃ stCtxt s_decls,
      decsStcnamesHOLExact [] decls = some stCtxt ∧
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
        decls = some s_decls ∧
      (∀ k, panEntryClass (PanSemStateFiniteExact.evaluateHOLFiniteState
        { s_decls with clock := k } (.call none start [] : ProgHOL width)).1 ≠ .RunError) ∧
      ∃ k_pan res_src s_src_post,
        PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
          (.call none start [] : ProgHOL width) = (res_src, s_src_post) ∧
        panEntryClass res_src = .CompleteResult outcome ∧
        s_src_post.ffi.ioEvents = events := by
  unfold PanSemStateFiniteExact.semanticsDecls at hterm
  cases hst : decsStcnamesHOLExact [] decls with
  | none => rw [hst] at hterm; cases hterm
  | some stCtxt =>
    rw [hst] at hterm
    dsimp only at hterm
    have hdec_eq : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { s with structs := stCtxt } (Classical.decPred _) decls =
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a)) decls := by
      congr
    rw [hdec_eq] at hterm
    cases hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a)) decls with
    | none => rw [hev_decls] at hterm; cases hterm
    | some s_decls =>
      rw [hev_decls] at hterm
      dsimp only at hterm
      rw [panSemIsWrapper] at hterm
      unfold crepToLoopSemanticsWrapper at hterm
      by_cases herr : ∃ k v,
          (Prod.map panEntryClass (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘
            fun k => PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
              (.call none start [] : ProgHOL width)) k = (.RunError, v)
      · rw [if_pos herr] at hterm; cases hterm
      · rw [if_neg herr] at hterm
        cases hsome : holOptionSome (fun res => ∃ k r ev,
            (Prod.map panEntryClass (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘
              fun k => PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
                (.call none start [] : ProgHOL width)) k = (.CompleteResult r, ev) ∧
            res = HolBehaviour.terminate r ev) with
        | none => rw [hsome] at hterm; cases hterm
        | some res =>
          rw [hsome] at hterm
          subst hterm
          obtain ⟨k_pan, r, ev, hk, heq⟩ := holOptionSome_some hsome
          injection heq with hr hev
          subst hr hev
          refine ⟨stCtxt, s_decls, rfl, hev_decls, ?_, ?_⟩
          · intro k hk_err
            apply herr
            exact ⟨k, (PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
              (.call none start [])).2.ffi.ioEvents, Prod.ext hk_err rfl⟩
          · rcases hrun : PanSemStateFiniteExact.evaluateHOLFiniteState
              { s_decls with clock := k_pan } (.call none start []) with ⟨res_src, s_src_post⟩
            simp only [Function.comp_apply, Prod.map, hrun, Prod.mk.injEq] at hk
            exact ⟨k_pan, res_src, s_src_post, hrun, hk.1, hk.2⟩

open Classical in

theorem semanticsDecls_terminate_at_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (start : MlS) (decls : List (DeclHOL width))
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hterm : PanSemStateFiniteExact.semanticsDecls s start decls = .terminate outcome events)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] decls = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
      decls = some s_decls)
    (K_pan : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := K_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hnt : res_src ≠ some .timeOut) :
    panEntryClass res_src = .CompleteResult outcome ∧
    s_src_post.ffi.ioEvents = events := by
  obtain ⟨stCtxt', s_decls', hst', hev_decls', _, k_pan, res0, post0, hev0, hclass0, hio0⟩ :=
    semanticsDecls_terminate_extract s start decls outcome events hterm
  rw [hst] at hst'; cases hst'
  rw [hev_decls] at hev_decls'; cases hev_decls'
  have hnt0 : res0 ≠ some .timeOut := by
    intro h; subst h; cases hclass0
  have hadd0 := panPropsEvaluateAddClockEq (.call none start [])
    { s_decls with clock := k_pan } res0 post0 K_pan ⟨hev0, hnt0⟩
  have haddK := panPropsEvaluateAddClockEq (.call none start [])
    { s_decls with clock := K_pan } res_src s_src_post k_pan ⟨hev_call, hnt⟩
  simp only [ Nat.add_comm K_pan k_pan ] at haddK
  rw [hadd0] at haddK
  injection haddK with hres hpost
  have hffi : s_src_post.ffi = post0.ffi := by
    have := congrArg PanSemStateFiniteExact.ffi hpost
    exact this.symm
  exact ⟨hres ▸ hclass0, (congrArg HolFfiState.ioEvents hffi).trans hio0⟩

open LoopToWordStateRelImpSemanticsSupport in

theorem pan_to_word_halt_of_word_not_timeOut {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (h : (∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
      noLabelsHOL target.memory (fun address => target.mdomain address = true) ∧
      start = ofString "main" ∧
      globalsSize = ((decShapesHOL code).map
        (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum ∧
      distinctParamsHOL (functionsHOL code) ∧
      (fun address => target.mdomain address = true) =
        (fun address => source.memaddrs address ∨ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (fun address => target.shMdomain address = true) = source.shMemaddrs ∧
      target.be = source.be ∧ target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      target.store.lookup .heapLength = some (.word heapLen) ∧
      source.topAddr = source.baseAddr + (2 : BitVec width) * heapLen - panBytesInWord width * BitVec.ofNat width globalsSize ∧
      ((functionsHOL code).map Prod.fst).Nodup ∧ panGlobalsByteAlignedHOL source.topAddr ∧
      globalsAllocatableHOL source code ∧ source.code = HolFiniteMapExact.empty ∧
      target.code = sptFromAList (panToWordCompileProgHOL arch code) ∧
      source.globals = HolFiniteMapExact.empty ∧ source.locals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL code < 2 ^ width ∧ source.eshapes = HolFiniteMapExact.empty ∧
      sptLookup 0 target.locals = some (WordLocW.loc 1 0) ∧ goodDimindex width ∧
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome)
    (K_word : Nat) (res_word : Option (WordSemResult width))
    (t_word : WordSemStateFiniteExact width C σ)
    (hrun_w : WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
      { target with clock := K_word } = (res_word, t_word))
    (hnt_w : res_word ≠ some .timeOut) :
    wordEntryClass res_word = .CompleteResult outcome ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents := by
  have hne_src : panEntryClass res_src ≠ .RunError := by
    rw [hclass_src]; intro herr; cases herr
  obtain ⟨k', t_word', res_word', hrun_w', hio_w', hclass_w'⟩ :=
    pan_to_word_clocked_sim source target arch code start globalsSize heapLen h stCtxt s_decls
      hst hev_decls k res_src s_src_post hev_call hne_src
  have hcw' : wordEntryClass res_word' = .CompleteResult outcome := hclass_w'.trans hclass_src
  have hnt_w' : res_word' ≠ some .timeOut := by
    intro ht; subst ht; cases hcw'
  obtain ⟨hr, hffi_eq⟩ := wordEvaluateIgnoreClocks
    (.call none (some firstLoopName) [0] none) target K_word ((k + 1) + k')
    res_word res_word' t_word t_word' hrun_w hnt_w hrun_w' hnt_w'
  subst hr
  exact ⟨hcw', (congrArg HolFfiState.ioEvents hffi_eq).trans hio_w'⟩
end PanAgreement


end InitECandidate.Solver.SelfContainedStageBounds
