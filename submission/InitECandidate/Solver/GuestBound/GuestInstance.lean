import InitECandidate.Solver.GuestBound.GuestEnv
import Guest.Model

/-!
# The stepped guest run satisfies `GuestEnv`

The assumptions collected in `GuestEnv` hold for the environment that
`Guest.runGuestStepped` evaluates in, so a bound on `main` in every `GuestEnv`
bounds the whole stepped run of the guest.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- The guest's memory-access model has the standard word operations. -/
theorem guest_wordEnv (state : PanValueProgramState Word) :
    WordEnv (programEnv Guest.guestFfiContext Guest.guestPrimitiveHandler Guest.guestHostFfi
      (some Guest.guestMemoryAccess) (none : Option (PanValueMemoryFfiHandler Word Guest.HostMemory))
      state) where
  noMemoryHandler := rfl
  wordOp := by
    intro access h operator values
    simp only [programEnv, Option.some.injEq] at h
    subst h
    rfl
  shift := by
    intro access h operator a b
    simp only [programEnv, Option.some.injEq] at h
    subst h
    rfl
  access := by
    refine ⟨Guest.guestMemoryAccess, rfl, ?_, ?_, ?_⟩
    · intro a b
      simp [Guest.guestMemoryAccess, panValueMemoryAccessOfModel, RiscV.panRiscVMemoryModel,
        RiscV.panRiscVWordOp, wordOpHOL, wordOp]
    · intro a b
      simp [Guest.guestMemoryAccess, panValueMemoryAccessOfModel, RiscV.panRiscVMemoryModel,
        RiscV.panRiscVWordOp, wordOpHOL, wordOp]
    intro operator a b
    cases operator <;>
      simp [Guest.guestMemoryAccess, panValueMemoryAccessOfModel, RiscV.panRiscVMemoryModel,
        RiscV.panRiscVCmp, evalPanCmp] <;>
      split <;> simp_all

/-- The guest's memory-access model stores and loads single word cells. -/
theorem guest_memEnv (state : PanValueProgramState Word) :
    MemEnv (programEnv Guest.guestFfiContext Guest.guestPrimitiveHandler Guest.guestHostFfi
      (some Guest.guestMemoryAccess) (none : Option (PanValueMemoryFfiHandler Word Guest.HostMemory))
      state) where
  access := by
    refine ⟨Guest.guestMemoryAccess, rfl, ?_, ?_⟩
    · intro memory b address value memory' h
      simp only [Guest.guestMemoryAccess, panValueMemoryAccessOfModel] at h
      split at h
      · simp only [Option.some.injEq] at h
        rw [← h]
        rfl
      · cases h
    · intro memory b address v h
      simp only [Guest.guestMemoryAccess, panValueMemoryAccessOfModel] at h
      split at h
      · cases hm : memory address with
        | none => rw [hm] at h; simp at h
        | some value =>
          rw [hm] at h
          cases value with
          | word w =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq] at h
            rw [h]
          | _ => simp at h
      · simp at h
  byte := by
    refine ⟨Guest.guestMemoryAccess, rfl, ?_⟩
    intro memory b address v h
    simp only [Guest.guestMemoryAccess, panValueMemoryAccessOfModel, panModelReadByte] at h
    split at h
    · simp only [panValueWordMemory] at h
      cases hm : memory ((RiscV.panRiscVMemoryModel (width := 64)).byteAlign b address) with
      | none => rw [hm] at h; simp at h
      | some value =>
        rw [hm] at h
        cases value with
        | word w =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at h
          exact ⟨w, hm, h.symm⟩
        | _ => simp at h
    · cases h
  storeByte := by
    refine ⟨Guest.guestMemoryAccess, rfl, ?_⟩
    intro memory b address value memory' h
    simp only [Guest.guestMemoryAccess, panValueMemoryAccessOfModel] at h
    split at h
    · cases hm : memory ((RiscV.panRiscVMemoryModel (width := 64)).byteAlign b address) with
      | none => rw [hm] at h; simp at h
      | some cellv =>
        rw [hm] at h
        cases cellv with
        | word w =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq] at h
          exact ⟨w, hm, h.symm⟩
        | _ => simp at h
    · simp at h
  storeDom := by
    refine ⟨Guest.guestMemoryAccess, rfl, ?_⟩
    intro memory b address value memory' h
    simp only [Guest.guestMemoryAccess, panValueMemoryAccessOfModel] at h
    split at h
    · rename_i hd
      simp only [decide_eq_true_eq] at hd
      have := hd.2.1
      rw [BitVec.lt_def] at this
      exact this
    · cases h
  storeByteDom := by
    refine ⟨Guest.guestMemoryAccess, rfl, ?_⟩
    intro memory b address value memory' h
    simp only [Guest.guestMemoryAccess, panValueMemoryAccessOfModel] at h
    split at h
    · rename_i hd
      simp only [decide_eq_true_eq] at hd
      have := hd.2.1
      rw [BitVec.lt_def] at this
      exact this
    · simp at h

/-- The environment of a stepped guest run is a `GuestEnv`. -/
theorem guest_guestEnv (state : PanValueProgramState Word)
    (hdecl : evalPanValueDeclarations Guest.guestInitialState Guest.Software.guestAst
      (memoryAccess := some Guest.guestMemoryAccess) = some state) :
    GuestEnv (programEnv Guest.guestFfiContext Guest.guestPrimitiveHandler Guest.guestHostFfi
      (some Guest.guestMemoryAccess) (none : Option (PanValueMemoryFfiHandler Word Guest.HostMemory))
      state) where
  functions := functionsFrom_declarations Guest.guestInitialState state Guest.Software.guestAst
    (some Guest.guestMemoryAccess) rfl hdecl
  word := guest_wordEnv state
  mem := guest_memEnv state
  prim := ⟨fun _ _ _ => rfl⟩
  bytes := (layout_declarations Guest.guestInitialState state Guest.Software.guestAst
    (some Guest.guestMemoryAccess) hdecl).1
  base := (layout_declarations Guest.guestInitialState state Guest.Software.guestAst
    (some Guest.guestMemoryAccess) hdecl).2.2

/-- A bound on `main` in every guest environment bounds every stepped run of
the guest that does not end in `.error`. -/
theorem guest_steps_le_of_main (N : Nat)
    (hmain : ∀ {σ : Type} {E : Env σ}, GuestEnv E → FunCost E "main" N)
    (input : Guest.InputBlob) (fuel : Nat) (r : Result Guest.HostMemory) (n : Nat)
    (hrun : Guest.runGuestStepped input fuel = some (r, n)) (hne : r.isError = false) :
    n ≤ N := by
  have h := programStepped_le Guest.guestFfiContext
    { source := Guest.guestInitialState, ffi := Guest.guestFfiState input }
    Guest.guestPrimitiveHandler Guest.guestHostFfi fuel Guest.Software.guestAst Guest.guestEntry []
    (some Guest.guestMemoryAccess) none N
    (fun state hdecl => hmain (guest_guestEnv state hdecl)) r n hrun hne
  simpa [panValueExpsStepCost, panValueExpStepCost.panValueExpsStepCost] using h

end InitECandidate.Solver.GuestBound
