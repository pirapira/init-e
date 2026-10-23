import InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts
import Flapjack.Compiler.Backend.StackToLab.Compile

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.PanToLabSectionAndStackRemoveClock

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.PanToStackNoStoreConsts
open InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts

variable {width : Nat} [NeZero width]

/-- Labels of the stubs that `StackToLab.compile` adds or receives: StackRemove init
stubs (0,1,2), the StackAlloc GC stub, and the WordToStack `storeConsts` stub. -/
def IsStubLabel (n : Nat) : Bool :=
  n == 0 || n == 1 || n == 2 || n == gcStubLocation || n == storeConstsStubLocation

/-- A section is "clean": it is `progToSectionHOL` of a body with `StackNoSt` (hence
`flattenHOL` never visits a `storeConsts` node). -/
def CleanSection (s : LabSem.LabSectionHOL width) : Prop :=
  ∃ p : HolProg width, s = StackToLab.progToSectionHOL (s.sectionId, p) ∧
    StackNoSt p = true ∧ FlattenVisitsSt p = false

/-! ## Per-pass list lemmas (any input list) -/

theorem rawCall_compile_mem (L : List (Nat × HolProg width)) :
    ∀ y ∈ StackRawCall.compile L, ∃ x ∈ L, y.1 = x.1 ∧
      ∃ info, y.2 = StackRawCall.compTop info x.2 := by
  intro y hy
  unfold StackRawCall.compile at hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  exact ⟨x, hx, rfl, _, rfl⟩

theorem stackAlloc_compile_mem (dc : DataToWord.Config) (L : List (Nat × HolProg width)) :
    ∀ y ∈ StackAlloc.compile dc L, y.1 = gcStubLocation ∨ ∃ x ∈ L, y = StackAlloc.progComp x := by
  intro y hy
  unfold StackAlloc.compile StackAlloc.stubs at hy
  rcases List.mem_append.1 hy with h | h
  · left; simp at h; rw [h]
  · right; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h; exact ⟨x, hx, rfl⟩

theorem stackAlloc_progComp_fst (x : Nat × HolProg width) : (StackAlloc.progComp x).1 = x.1 := by
  obtain ⟨n, p⟩ := x; rfl

theorem stackRemove_compileHOL_mem (j : Bool) (bd : BitVec width × BitVec width) (g : Bool)
    (mh sp st : Nat) (L : List (Nat × HolProg width)) :
    ∀ y ∈ StackRemove.compileHOL j bd g mh sp st L,
      (y.1 = 0 ∨ y.1 = 1 ∨ y.1 = 2) ∨ ∃ x ∈ L, y = (x.1, StackRemove.comp j bd sp x.2) := by
  intro y hy
  unfold StackRemove.compileHOL StackRemove.initStubs at hy
  rcases List.mem_append.1 hy with h | h
  · left; simp at h; rcases h with rfl | rfl | rfl <;> simp
  · right; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h; exact ⟨x, hx, rfl⟩

theorem stackNames_compileHOL_mem (f : Spt Nat) (L : List (Nat × HolProg width)) :
    ∀ y ∈ StackNames.compileHOL f L, ∃ x ∈ L, y = (x.1, StackNames.progCompHOL f x.2) := by
  intro y hy
  unfold StackNames.compileHOL at hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
  exact ⟨x, hx, rfl⟩

theorem clean_progToSection (n : Nat) (p : HolProg width) (h : StackNoSt p = true) :
    CleanSection (StackToLab.progToSectionHOL (n, p)) :=
  ⟨p, rfl, h, not_visits_of_StackNoSt p h⟩

/-- Generic: if every non-stub input body is `StackNoSt`, every section of
`StackToLab.compile` is a stub section or a clean section. -/
theorem stackToLab_compile_sections (sc : StackToLab.Config) (dc : DataToWord.Config)
    (mh sp : Nat) (off : BitVec width × BitVec width) (L : List (Nat × HolProg width))
    (hL : ∀ x ∈ L, x.1 = storeConstsStubLocation ∨ StackNoSt x.2 = true) :
    ∀ s ∈ StackToLab.compile sc dc mh sp off L,
      IsStubLabel s.sectionId = true ∨ CleanSection s := by
  intro s hs
  unfold StackToLab.compile at hs
  obtain ⟨y4, hy4, rfl⟩ := List.mem_map.1 hs
  obtain ⟨y3, hy3, rfl⟩ := stackNames_compileHOL_mem _ _ y4 hy4
  have hid : (StackToLab.progToSectionHOL (y3.1, StackNames.progCompHOL sc.regNames y3.2)).sectionId
      = y3.1 := rfl
  rcases stackRemove_compileHOL_mem _ _ _ _ _ _ _ y3 hy3 with h0 | ⟨y2, hy2, rfl⟩
  · left; rw [hid]; rcases h0 with h | h | h <;> simp [IsStubLabel, h]
  rcases stackAlloc_compile_mem _ _ y2 hy2 with hg | ⟨y1, hy1, rfl⟩
  · left; rw [hid]; simp [IsStubLabel, hg]
  obtain ⟨x, hx, hfst, info, hsnd⟩ := rawCall_compile_mem _ y1 hy1
  rcases hL x hx with hst | hok
  · left; rw [hid]; simp only [stackAlloc_progComp_fst, hfst, hst]; simp [IsStubLabel]
  · right
    apply clean_progToSection
    apply u_stackNames; apply u_stackRemoveComp
    apply s_progComp; rw [hsnd]; exact u_rawCallCompTop info x.2 hok

/-- (a) Universal theorem on the LabLang sections of the whole Pancake pipeline:
every section of `StackToLab.compile` applied to the WordToStack output of any Pancake
program is a stub section (labels 0,1,2, GC stub, storeConsts stub) or the section of a
body with `StackNoSt` and `FlattenVisitsSt = false`. No premise on the program. -/
theorem panToLab_sections_unconditional (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    ∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
      IsStubLabel s.sectionId = true ∨ CleanSection s :=
  stackToLab_compile_sections sc dc mh sp off _
    (s_compileNative_bodies ac perf _ (panToWordToWord_NoSt arch prog wc ac))

/-- Section ids are exactly the input ids plus the added stubs (order preserved). -/
theorem stackToLab_compile_ids (sc : StackToLab.Config) (dc : DataToWord.Config)
    (mh sp : Nat) (off : BitVec width × BitVec width) (L : List (Nat × HolProg width)) :
    (StackToLab.compile sc dc mh sp off L).map (·.sectionId) =
      [0, 1, 2, gcStubLocation] ++ L.map Prod.fst := by
  unfold StackToLab.compile StackRemove.compileHOL StackRemove.initStubs StackNames.compileHOL
    StackAlloc.compile StackAlloc.stubs StackRawCall.compile
  simp only [List.map_map, List.map_cons, List.cons_append, List.nil_append, List.map_append]
  refine congrArg (fun t => _ :: _ :: _ :: _ :: t) ?_
  apply List.map_congr_left
  intro x _; obtain ⟨n, p⟩ := x; rfl

/-! ## (b) StackRemove: the storeConsts expansion is never produced -/

/-- `StackRemove.comp` on a `StackNoSt` tree returns a `StackNoSt` tree; in particular the
`storeConsts` clause (bitmap prelude + `copyLoop`) is never taken: its output would
otherwise be the non-trivial expansion of `stackRemove_storeConsts_not_skip`. -/
theorem stackRemove_no_storeConsts_branch (j : Bool) (bd : BitVec width × BitVec width)
    (ptr : Nat) (p : HolProg width) (h : StackNoSt p = true) :
    StackNoSt (StackRemove.comp j bd ptr p) = true ∧ FlattenVisitsSt p = false :=
  ⟨u_stackRemoveComp j bd ptr p h, not_visits_of_StackNoSt p h⟩

/-- The premise matters: a `storeConsts` leaf does visit the forbidden branch. -/
theorem stackRemove_branch_tight :
    StackNoSt (.storeConsts 3 4 none : HolProg width) = false ∧
      FlattenVisitsSt (.storeConsts 3 4 none : HolProg width) = true := ⟨rfl, rfl⟩

theorem isStubLabel_storeConsts : IsStubLabel storeConstsStubLocation = true := by
  simp [IsStubLabel]

theorem isStubLabel_tight : IsStubLabel 64 = false := by
  simp [IsStubLabel, gcStubLocation, storeConstsStubLocation, stackNumStubs, wordNumStubs]


end InitECandidate.Solver.PanToLabSectionAndStackRemoveClock
