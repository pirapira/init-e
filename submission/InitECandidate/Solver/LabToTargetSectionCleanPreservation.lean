import InitECandidate.Solver.PanToLabSectionAndStackRemoveClock
import Flapjack.Compiler.Backend.LabToTarget.Compile

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.LabToTargetSectionCleanPreservation

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts
open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock

variable {width : Nat} [NeZero width]

abbrev Sec (width : Nat) [NeZero width] :=
  Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString) (BitVec width))

def ids (L : List (Sec width)) : List Nat := L.map (·.sectionId)

/-! ## Every LabToTarget section-list pass preserves the exact id list -/

theorem ids_filterSkip : ∀ L : List (Sec width), ids (filterSkip L) = ids L
  | [] => rfl
  | ⟨n, xs⟩ :: rest => by
      rw [filterSkip]; simp only [ids, List.map_cons]
      exact congrArg (n :: ·) (ids_filterSkip rest)

theorem ids_encSecList (enc : HolAsm width → List (BitVec 8)) (L : List (Sec width)) :
    ids (encSecList enc L) = ids L := by
  simp [encSecList, ids, encSec, List.map_map, Function.comp_def]

theorem ids_encSecsAgain (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) :
    ∀ (L : List (Sec width)) (pos : Nat), ids (encSecsAgain pos labs ffis enc L).1 = ids L
  | [], _ => by rw [encSecsAgain]
  | ⟨s, lines⟩ :: rest, pos => by
      rw [encSecsAgain]; simp only [ids, List.map_cons]
      exact congrArg (s :: ·) (ids_encSecsAgain labs ffis enc rest _)

theorem ids_updLabLen : ∀ (L : List (Sec width)) (pos : Nat), ids (updLabLen pos L) = ids L
  | [], _ => by rw [updLabLen]
  | ⟨s, lines⟩ :: rest, pos => by
      rw [updLabLen]; simp only [ids, List.map_cons]
      exact congrArg (s :: ·) (ids_updLabLen rest _)

theorem ids_padCode (nop : List (BitVec 8)) : ∀ L : List (Sec width), ids (padCode nop L) = ids L
  | [] => by rw [padCode]
  | ⟨n, xs⟩ :: rest => by
      rw [padCode]; simp only [ids, List.map_cons]
      exact congrArg (n :: ·) (ids_padCode nop rest)

theorem ids_removeLabelsLoop (config : AsmConfigExact width) (pos : Nat)
    (initLabs : Spt (Spt Nat)) (ffis : List HolFfiName) :
    ∀ (clock : Nat) (L L' : List (Sec width)) (labs : Spt (Spt Nat)),
      removeLabelsLoop clock config pos initLabs ffis L = some (L', labs) → ids L' = ids L
  | clock, L, L', labs, h => by
      rw [removeLabelsLoop] at h
      dsimp only at h
      split at h
      · split at h
        · rename_i hd
          obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h).symm
          rw [ids_padCode, ids_encSecsAgain, ids_updLabLen, ids_encSecsAgain]
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · rw [ids_removeLabelsLoop config pos initLabs ffis (clock - 1) _ L' labs h,
            ids_encSecsAgain]
termination_by clock => clock
decreasing_by omega

theorem ids_removeLabels (ic : Nat) (config : AsmConfigExact width) (pos : Nat)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (L L' : List (Sec width))
    (labs' : Spt (Spt Nat)) (h : removeLabels ic config pos labs ffis L = some (L', labs')) :
    ids L' = ids L := by
  unfold removeLabels at h
  rw [ids_removeLabelsLoop config pos labs ffis ic _ L' labs' h, ids_encSecList]

/-- Membership transport along an id-preserving pass. -/
theorem mem_of_ids_eq {L L' : List (Sec width)} (h : ids L' = ids L) (s' : Sec width)
    (hs : s' ∈ L') : ∃ s ∈ L, s.sectionId = s'.sectionId := by
  have : s'.sectionId ∈ ids L := by rw [← h]; exact List.mem_map_of_mem hs
  obtain ⟨s, hs, he⟩ := List.mem_map.1 this
  exact ⟨s, hs, he⟩

theorem length_of_ids_eq {L L' : List (Sec width)} (h : ids L' = ids L) :
    L'.length = L.length := by
  have := congrArg List.length h; simpa [ids] using this

/-! ## End to end -/

/-- Section list actually encoded by `LabToTarget.compile`: `removeLabels` applied to
`filterSkip` of the StackToLab output. Whenever it succeeds, its ids are exactly
`[0,1,2,gc] ++` the WordToStack names, in order, and every section whose id is not a stub
id comes from a `CleanSection` of StackToLab with the same id. -/
theorem panToTarget_sections_clean (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) :
    ids L' = [0, 1, 2, gcStubLocation] ++ (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2.map Prod.fst ∧
    ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨
      ∃ s ∈ StackToLab.compile sc dc mh sp off
          (compileNative ac perf (WordToWord.compile wc ac
            (panToWordCompileProgHOL arch prog)).2).2.2.2,
        s.sectionId = s'.sectionId ∧ CleanSection s := by
  have hid : ids L' = ids (StackToLab.compile sc dc mh sp off
      (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2) := by
    rw [ids_removeLabels ic ac pos labs ffis _ L' labs' h, ids_filterSkip]
  refine ⟨?_, ?_⟩
  · rw [hid]; exact stackToLab_compile_ids sc dc mh sp off _
  · intro s' hs'
    obtain ⟨s, hs, he⟩ := mem_of_ids_eq hid s' hs'
    rcases panToLab_sections_unconditional arch prog wc ac perf sc dc mh sp off s hs with st | cl
    · left; rw [← he]; exact st
    · right; exact ⟨s, hs, he, cl⟩

theorem panToTarget_sections_length (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) :
    L'.length = 4 + ((compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2).length := by
  have := congrArg List.length (panToTarget_sections_clean arch prog wc ac perf sc dc mh sp off
    ic pos labs ffis L' labs' h).1
  simp only [ids, List.length_map, List.length_append, List.length_cons, List.length_nil] at this
  omega

/-! ## Witnesses -/

theorem filterSkip_changes_lines :
    filterSkip [(⟨7, [.asm (.asmi (.inst .skip)) [] 0]⟩ : Sec width)] = [⟨7, []⟩] := by
  rw [filterSkip, filterSkip]; rfl

theorem ids_distinguish_stub :
    IsStubLabel (ids [(⟨64, []⟩ : Sec width)]).head! = false ∧
      IsStubLabel (ids [(⟨0, []⟩ : Sec width)]).head! = true := by
  refine ⟨?_, ?_⟩ <;> simp [ids, IsStubLabel, gcStubLocation, storeConstsStubLocation,
    stackNumStubs, wordNumStubs]

theorem ids_not_trivial :
    ids [(⟨3, []⟩ : Sec width)] ≠ ids [(⟨4, []⟩ : Sec width)] := by simp [ids]


end InitECandidate.Solver.LabToTargetSectionCleanPreservation
