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
