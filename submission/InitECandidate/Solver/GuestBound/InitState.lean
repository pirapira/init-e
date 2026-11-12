import InitECandidate.Solver.GuestBound.GuestInstance
import InitECandidate.Solver.GuestBound.ProgramAt
import InitECandidate.Solver.GuestBound.HeapKeep

/-!
# The state `main` starts in

After the declarations, `heap_ptr` is 0 and the memory is the guest's initial
memory. `guest_steps_le_of_main_at` turns a bound on `main` from such states
into a bound on every stepped run of the guest.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- After the guest's declarations the heap pointer is 0. -/
theorem guest_initial_heapOk (state : PanValueProgramState Word)
    (hdecl : evalPanValueDeclarations Guest.guestInitialState Guest.Software.guestAst
      (memoryAccess := some Guest.guestMemoryAccess) = some state) :
    HeapOk state.globals :=
  ⟨0#64, globals_declarations Guest.guestInitialState state Guest.Software.guestAst
    (some Guest.guestMemoryAccess) "heap_ptr" 0#64 hdecl (by decide +kernel), by decide⟩

/-- A bound on `main` from states with the heap pointer in the heap and the
initial memory bounds every stepped run of the guest that does not end in `.error`. -/
theorem guest_steps_le_of_main_at (N : Nat)
    (hmain : ∀ {σ : Type} {E : Env σ}, GuestEnv E →
      ∀ parameters body, lookupPanFunction "main" E.functions = some (parameters, body) →
      ∀ fuel (s : St σ) r n, HeapOk s.globals → s.memory = Guest.guestInitialMemory →
        E.run fuel s body = some (r, n) → r.isError = false → n ≤ N)
    (input : Guest.InputBlob) (fuel : Nat) (r : Result Guest.HostMemory) (n : Nat)
    (hrun : Guest.runGuestStepped input fuel = some (r, n)) (hne : r.isError = false) :
    n ≤ N := by
  have h := programStepped_le_at Guest.guestFfiContext
    { source := Guest.guestInitialState, ffi := Guest.guestFfiState input }
    Guest.guestPrimitiveHandler Guest.guestHostFfi fuel Guest.Software.guestAst Guest.guestEntry []
    (some Guest.guestMemoryAccess) none N
    (fun state hdecl parameters body cl hl fuel' rb nb hb hrb =>
      hmain (guest_guestEnv state hdecl) parameters body hl fuel' _ rb nb
        (guest_initial_heapOk state hdecl)
        (layout_declarations Guest.guestInitialState state Guest.Software.guestAst
          (some Guest.guestMemoryAccess) hdecl).2.1 hb hrb) r n hrun hne
  simpa [panValueExpsStepCost, panValueExpStepCost.panValueExpsStepCost] using h

end InitECandidate.Solver.GuestBound
