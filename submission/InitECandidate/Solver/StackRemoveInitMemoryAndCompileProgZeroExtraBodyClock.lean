import InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitClock

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# StackRemove `compileHOL`: initializer + per-body zero extra clock

Flapjack has no `StackRemove/CompileProgCorrect.lean` nor `InitMemoryCorrect.lean`; the real
objects are `StackRemove.compileHOL` (`Compile.lean`) = `initStubs` (sections `0,1,2`, with
`initCode` / `initMemory` in section `0`) `++ program.map progComp`, `Proofs/InitClock.lean`
(clock neutrality of `initCode`) and `Proofs/InitCodeCorrect.lean` (`initCodeThm`).

Established here:
* `initCode` / `initMemory` / all three `initStubs` are `storeConsts`-free and `initCode`
  consumes **zero** clock ticks (`initCode_clock_preserved`);
* on the real pipeline `StackToLab.compile` (StackRawCall → StackAlloc → StackRemove), every
  section emitted by `StackRemove.compileHOL` other than label `storeConstsStubLocation = 6`
  is `storeConsts`-free, for every Pancake program — label `6` is exactly the exception;
* combined master with `panToStackRemove_body_zeroExtraClock`.
-/

namespace InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt panToWordToWord_NoSt)
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock

variable {width : Nat} [NeZero width]

/-! ## Initializer: structure -/

theorem noSt_listSeq : ∀ l : List (HolProg width), (∀ x ∈ l, StackNoSt x = true) →
    StackNoSt (listSeqHOL l) = true
  | [], _ => rfl
  | [x], h => h x (by simp)
  | x :: y :: xs, h => by
      rw [listSeqHOL, StackNoSt.eq_def]
      simp only [Bool.and_eq_true]
      exact ⟨h x (by simp), noSt_listSeq (y :: xs) (fun z hz => h z (List.mem_cons_of_mem _ hz))⟩

theorem noSt_storeListCode (address temporary : Nat) :
    ∀ values : List (Sum (BitVec width) Nat), StackNoSt (storeListCode address temporary values) = true
  | [] => rfl
  | .inl v :: rest => by
      rw [storeListCode, StackNoSt.eq_def]; simp only [Bool.and_eq_true]
      exact ⟨noSt_listSeq _ (by simp [StackNoSt, addBytesInWordInst]), noSt_storeListCode address temporary rest⟩
  | .inr r :: rest => by
      rw [storeListCode, StackNoSt.eq_def]; simp only [Bool.and_eq_true]
      exact ⟨noSt_listSeq _ (by simp [StackNoSt, addBytesInWordInst]), noSt_storeListCode address temporary rest⟩

theorem noSt_initMemory (pointer : Nat) (values : List (Sum (BitVec width) Nat)) :
    StackNoSt (initMemory pointer values) = true := by
  unfold initMemory
  apply noSt_listSeq
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact noSt_storeListCode _ _ _

theorem noSt_initCode (generateGc : Bool) (maximumHeap pointer : Nat) :
    StackNoSt (initCode (width := width) generateGc maximumHeap pointer) = true := by
  unfold initCode
  apply noSt_listSeq
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | (subst h; exact noSt_initMemory _ _)
    | (subst h; rfl)
    | (subst h; simp [StackNoSt, moveHOL, addInst, constInst])

/-- All three StackRemove initialization sections are `storeConsts`-free. -/
theorem noSt_initStubs (generateGc : Bool) (maximumHeap pointer start : Nat) :
    ∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true := by
  intro e he
  simp only [initStubs, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · rw [StackNoSt.eq_def]; simp only [Bool.and_eq_true]
    exact ⟨noSt_initCode _ _ _, rfl⟩
  · rfl
  · rfl

/-- Initialization sections are labels `0, 1, 2` — never the `storeConsts` stub `6`. -/
theorem initStubs_labels (generateGc : Bool) (maximumHeap pointer start : Nat) :
    (initStubs (width := width) generateGc maximumHeap pointer start).map Prod.fst = [0, 1, 2] := rfl

theorem storeConstsStubLocation_eq : storeConstsStubLocation = 6 := by decide

/-! ## Initializer: clock -/

/-- `initCode` (including `initMemory`) consumes **zero** clock ticks: whatever its result,
the post-state clock equals the input clock. -/
theorem initCode_clock_preserved {C F : Type}
    (generateGc : Bool) (maximumHeap pointer : Nat)
    (source post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (run : StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, source) = (result, post)) :
    post.clock = source.clock := by
  have h := Proofs.InitClock.evaluateInitCodeClock generateGc maximumHeap pointer source post result
    source.clock run
  have hs : ({source with clock := source.clock} : StackSemStateFiniteExact width C F) = source := rfl
  rw [hs, run] at h
  have := congrArg (fun p => (Prod.snd p).clock) h
  simpa using this

/-- And `initCode` runs identically at every clock. -/
theorem initCode_clock_independent {C F : Type}
    (generateGc : Bool) (maximumHeap pointer : Nat)
    (source post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (clock : Nat)
    (run : StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, source) = (result, post)) :
    StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, {source with clock := clock}) =
      (result, {post with clock := clock}) :=
  Proofs.InitClock.evaluateInitCodeClock generateGc maximumHeap pointer source post result clock run

/-! ## The real StackToLab stack-side pipeline -/

/-- The GC stub of StackAlloc is clean (no `storeConsts`, no call into the stub). -/
theorem clean_gcStub (conf : DataToWord.Config) :
    ∀ e ∈ StackAlloc.stubs (width := width) conf, Clean e.2 = true := by
  intro e he
  simp only [StackAlloc.stubs, List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  cases h : conf.gcKind with
  | generational sizes =>
    rcases sizes with _ | ⟨g, gs⟩ <;>
      simp [Clean, StackAlloc.memcpyCode, StackAlloc.clearTopInst, StackAlloc.wordGcMoveCode, StackAlloc.wordGcMoveListCode, StackAlloc.wordGcMoveLoopCode, StackAlloc.wordGcMoveBitmapCode, StackAlloc.wordGcMoveBitmapsCode, StackAlloc.wordGcMoveRootsBitmapsCode, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcPartialMoveCode, StackAlloc.wordGenGcMoveBitmapCode, StackAlloc.wordGenGcPartialMoveBitmapCode, StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcPartialMoveBitmapsCode, StackAlloc.wordGenGcMoveRootsBitmapsCode, StackAlloc.wordGenGcPartialMoveRootsBitmapsCode, StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcPartialMoveListCode, StackAlloc.wordGenGcMoveDataCode, StackAlloc.wordGenGcPartialMoveRefListCode, StackAlloc.wordGenGcPartialMoveDataCode, StackAlloc.wordGenGcMoveRefsCode, StackAlloc.wordGenGcMoveLoopCode, StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger, StackAlloc.wordGcCode,
      add1Inst, addBytesInWordInst, addInst, andInst, constInst, div2Inst, haltInst, leftShiftInst, listSeqHOL, loadInst, moveHOL, orInst, rightShiftInst, storeInst, sub1Inst, subInst, whileHOL, xorInst, h] <;>
      (try split) <;> simp [Clean, StackAlloc.memcpyCode, StackAlloc.clearTopInst, StackAlloc.wordGcMoveCode, StackAlloc.wordGcMoveListCode, StackAlloc.wordGcMoveLoopCode, StackAlloc.wordGcMoveBitmapCode, StackAlloc.wordGcMoveBitmapsCode, StackAlloc.wordGcMoveRootsBitmapsCode, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcPartialMoveCode, StackAlloc.wordGenGcMoveBitmapCode, StackAlloc.wordGenGcPartialMoveBitmapCode, StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcPartialMoveBitmapsCode, StackAlloc.wordGenGcMoveRootsBitmapsCode, StackAlloc.wordGenGcPartialMoveRootsBitmapsCode, StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcPartialMoveListCode, StackAlloc.wordGenGcMoveDataCode, StackAlloc.wordGenGcPartialMoveRefListCode, StackAlloc.wordGenGcPartialMoveDataCode, StackAlloc.wordGenGcMoveRefsCode, StackAlloc.wordGenGcMoveLoopCode, StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger, StackAlloc.wordGcCode,
      add1Inst, addBytesInWordInst, addInst, andInst, constInst, div2Inst, haltInst, leftShiftInst, listSeqHOL, loadInst, moveHOL, orInst, rightShiftInst, storeInst, sub1Inst, subInst, whileHOL, xorInst, h]
  | _ => simp [Clean, StackAlloc.memcpyCode, StackAlloc.clearTopInst, StackAlloc.wordGcMoveCode, StackAlloc.wordGcMoveListCode, StackAlloc.wordGcMoveLoopCode, StackAlloc.wordGcMoveBitmapCode, StackAlloc.wordGcMoveBitmapsCode, StackAlloc.wordGcMoveRootsBitmapsCode, StackAlloc.wordGenGcMoveCode, StackAlloc.wordGenGcPartialMoveCode, StackAlloc.wordGenGcMoveBitmapCode, StackAlloc.wordGenGcPartialMoveBitmapCode, StackAlloc.wordGenGcMoveBitmapsCode, StackAlloc.wordGenGcPartialMoveBitmapsCode, StackAlloc.wordGenGcMoveRootsBitmapsCode, StackAlloc.wordGenGcPartialMoveRootsBitmapsCode, StackAlloc.wordGenGcMoveListCode, StackAlloc.wordGenGcPartialMoveListCode, StackAlloc.wordGenGcMoveDataCode, StackAlloc.wordGenGcPartialMoveRefListCode, StackAlloc.wordGenGcPartialMoveDataCode, StackAlloc.wordGenGcMoveRefsCode, StackAlloc.wordGenGcMoveLoopCode, StackAlloc.wordGcPartialOrFull, StackAlloc.setNewTrigger, StackAlloc.wordGcCode,
      add1Inst, addBytesInWordInst, addInst, andInst, constInst, div2Inst, haltInst, leftShiftInst, listSeqHOL, loadInst, moveHOL, orInst, rightShiftInst, storeInst, sub1Inst, subInst, whileHOL, xorInst, h]

/-- **Real pipeline.** For any Pancake program, every section of
`StackRemove.compileHOL … (StackAlloc.compile dc (StackRawCall.compile (WordToStack output)))`
(exactly the stack-side of `StackToLab.compile`) other than label `6` is `storeConsts`-free. -/
theorem stackRemoveCompile_sections_noSt
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) :
    ∀ e ∈ StackRemove.compileHOL jump bounds generateGc maximumHeap pointer start
        (StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)),
      e.1 = storeConstsStubLocation ∨ StackNoSt e.2 = true := by
  intro e he
  simp only [StackRemove.compileHOL, List.mem_append] at he
  rcases he with hi | hm
  · exact Or.inr (noSt_initStubs generateGc maximumHeap pointer start e hi)
  · rcases List.mem_map.1 hm with ⟨a, ha, rfl⟩
    simp only [StackRemove.progComp]
    simp only [StackAlloc.compile, List.mem_append] at ha
    rcases ha with hg | hb
    · exact Or.inr (of_clean (c_stackRemoveComp jump bounds pointer _ (clean_gcStub dc a hg))).1
    · rcases List.mem_map.1 hb with ⟨b, hb', rfl⟩
      simp only [StackRawCall.compile] at hb'
      rcases List.mem_map.1 hb' with ⟨y, hy, rfl⟩
      rcases c_compileNative ac perf _
          (fun x hx => ⟨panToWordToWord_NoSt arch prog wc ac x hx,
            InitECandidate.Solver.WordToWordNoStubCall.panToWordToWord_NoStubCall arch prog wc ac x hx⟩)
          y hy with h6 | hc
      · exact Or.inl h6
      · right
        unfold StackAlloc.progComp
        exact (of_clean (c_stackRemoveComp jump bounds pointer _
          (c_stackAllocComp _ _ _ (c_rawCallCompTop _ _ hc)))).1

/-- Tight: the single exception is real — section `6` holds `storeConsts`. -/
theorem storeConstsStub_not_noSt (k : Nat) :
    StackNoSt (storeConstsStubNative (width := width) k) = false := rfl

/-- Tight: WordToStack really emits section `6` with that stub body. -/
theorem compileNative_has_stub6 (ac : AsmConfigExact width) (perf : Bool)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) :
    (storeConstsStubLocation, storeConstsStubNative (ac.regCount - (5 + ac.avoidRegs.length))) ∈
      (compileNative ac perf progs).2.2.2 := by
  simp [compileNative]

/-! ## Combined master -/

/-- **Master (W4_10).** For every Pancake program:
1. the three StackRemove initialization sections are `storeConsts`-free and the initializer
   `initCode` (with `initMemory`) costs zero clock ticks;
2. every section produced by the stack side of `StackToLab.compile` except the stub `6` is
   `storeConsts`-free;
3. every user body (≠ `6`) is simulated by `StackRemove.comp` with zero extra clock, except
   at most one tick on a final `halt`, from any `CodeNoSt` state. -/
theorem pancake_stackRemove_compileProg_zeroExtraBodyClock {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maximumHeap pointer start : Nat) :
    (∀ e ∈ initStubs (width := width) generateGc maximumHeap pointer start, StackNoSt e.2 = true) ∧
    (∀ (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (initCode generateGc maximumHeap pointer, s) = (r, t) →
      t.clock = s.clock) ∧
    (∀ e ∈ StackRemove.compileHOL jump bounds generateGc maximumHeap pointer start
        (StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)),
      e.1 = storeConstsStubLocation ∨ StackNoSt e.2 = true) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        CodeNoSt source →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget)) :=
  ⟨noSt_initStubs generateGc maximumHeap pointer start,
   fun s t r h => initCode_clock_preserved generateGc maximumHeap pointer s t r h,
   stackRemoveCompile_sections_noSt arch prog wc ac perf dc jump bounds generateGc maximumHeap pointer start,
   Pancake.panToStackRemove_body_zeroExtraClock arch prog wc ac perf info⟩

end InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock
