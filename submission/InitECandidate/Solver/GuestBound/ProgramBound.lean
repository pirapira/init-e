import InitECandidate.Solver.GuestBound.StaticCost

/-!
# From a bound on the entry function to a bound on the program run

`evalPanValueFfiProgramStepped` evaluates the declarations (uncounted) and
calls the entry function; its count is the count of that call.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type}

/-- The evaluator environment a program run uses after its declarations. -/
def programEnv (context : PanValueFfiContext Word) (primitive : PanPrimitiveHandler Word)
    (handler : PanValueStatefulFfiHandler Word σ)
    (memoryAccess : Option (PanValueMemoryAccess Word))
    (memoryHandler : Option (PanValueMemoryFfiHandler Word σ))
    (state : PanValueProgramState Word) : Env σ where
  context := context
  primitive := primitive
  handler := handler
  structs := state.structs
  functions := state.functions
  baseAddress := state.baseAddress
  topAddress := state.topAddress
  bytesInWord := state.bytesInWord
  memoryAccess := memoryAccess
  contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
    state.parameterShapes)
  memoryHandler := memoryHandler

/-- A program run costs at most the entry call's arguments plus the entry function. -/
theorem programStepped_le (context : PanValueFfiContext Word)
    (initial : PanValueFfiProgramState Word σ) (primitive : PanPrimitiveHandler Word)
    (handler : PanValueStatefulFfiHandler Word σ) (fuel : Nat)
    (declarations : List (Decl Word)) (entry : FunName) (arguments : List (Exp Word))
    (memoryAccess : Option (PanValueMemoryAccess Word))
    (memoryHandler : Option (PanValueMemoryFfiHandler Word σ)) (B : Nat)
    (hentry : ∀ state,
      evalPanValueDeclarations initial.source declarations (memoryAccess := memoryAccess) =
        some state →
      FunCost (programEnv context primitive handler memoryAccess memoryHandler state) entry B)
    (r : Result σ) (n : Nat)
    (hrun : evalPanValueFfiProgramStepped context initial primitive handler fuel declarations
      entry arguments (memoryAccess := memoryAccess) (memoryHandler := memoryHandler) =
        some (r, n)) :
    n ≤ panValueExpsStepCost arguments + B := by
  unfold evalPanValueFfiProgramStepped at hrun
  cases hdecl : evalPanValueDeclarations initial.source declarations
      (memoryAccess := memoryAccess) with
  | none => rw [hdecl] at hrun; simp at hrun
  | some state =>
    rw [hdecl] at hrun
    simp only [Option.bind_eq_bind, Option.bind_some] at hrun
    cases hcall : evalPanValueFfiCallSteps context primitive handler state.structs
        state.functions state.baseAddress state.topAddress state.bytesInWord fuel
        (fun _ => none) state.globals state.memory initial.ffi none entry arguments
        (memoryAccess := memoryAccess)
        (contracts := some (PanValueCallContracts.mk state.returnShapes state.exceptions
          state.parameterShapes))
        (memoryHandler := memoryHandler) with
    | none => rw [hcall] at hrun; simp at hrun
    | some callPair =>
      obtain ⟨rc, nc⟩ := callPair
      rw [hcall] at hrun
      have hnc : nc ≤ panValueExpsStepCost arguments + B + 0 :=
        callSteps_le (E := programEnv context primitive handler memoryAccess memoryHandler state)
          (info := none) (H := 0) (hentry state hdecl) trivial fuel
          ⟨fun _ => none, state.globals, state.memory, initial.ffi⟩ arguments false rc nc hcall
      simp only [Option.bind_some] at hrun
      repeat' split at hrun
      all_goals first
        | (simp at hrun; done)
        | (simp only [Option.some.injEq, Prod.mk.injEq] at *; omega)

end InitECandidate.Solver.GuestBound
