import InitE.SourceWitness.Initialization

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

abbrev arithmeticInitialState (input : Guest.InputBlob) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  { sourceInitialState input with
    memaddrs := arithmeticOrdinaryDomain
    shMemaddrs := arithmeticSharedDomain }

def entryState (input : Guest.InputBlob) := state0890 (arithmeticInitialState input)

theorem initialized (input : Guest.InputBlob) :
    evaluateDeclsHOLFinite (arithmeticInitialState input)
      (Guest.Software.guestAst.map declToHOL) = some (entryState input) := by
  rw [source_declarations_eq_suffix]
  exact suffix000_run (arithmeticInitialState input)

def execution (input : Guest.InputBlob) (clock : Nat) :=
  evaluateHOLFiniteStateWithDeciders
    { entryState input with
      memaddrs := arithmeticOrdinaryDomain
      shMemaddrs := arithmeticSharedDomain
      clock := clock }
    (.call none (Basis.Pure.MlString.ofString "main") [])

theorem sourceRunArithmetic_execution (input : Guest.InputBlob) (clock : Nat) :
    sourceRunArithmetic input clock = some (execution input clock) := by
  unfold sourceRunArithmetic
  rw [source_structures_empty]
  dsimp only
  change (match evaluateDeclsHOLFinite (arithmeticInitialState input)
      (Guest.Software.guestAst.map declToHOL) with
    | none => none
    | some entry => some (evaluateHOLFiniteStateWithDeciders
        { entry with
          memaddrs := arithmeticOrdinaryDomain
          shMemaddrs := arithmeticSharedDomain
          clock := clock }
        (.call none (Basis.Pure.MlString.ofString "main") []))) = _
  rw [initialized]
  rfl

end InitE.SourceWitness
