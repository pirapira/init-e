import InitE.ScoreLowerBound
import InitE.SourceWitness.Entry
import InitE.SourceWitness.Input

namespace InitE.SourceWitness
open Flapjack

def haltEvent : HolFinalEvent :=
  ⟨.extCall (Basis.Pure.MlString.ofString "halt"), [], [], .failed⟩

theorem halt_covered : coveredOutcome (.ffiOutcome haltEvent) := by
  exact ⟨rfl, .inr ⟨by decide, by decide, by decide⟩⟩

theorem source_of_execution (clock : Nat)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : execution input clock = (some (.finalFfi haltEvent), post)) :
    sourceBehaviour input = .terminate (.ffiOutcome haltEvent) post.ffi.ioEvents := by
  apply sourceBehaviour_of_sourceRun input clock haltEvent post
  rw [← sourceRunArithmetic_eq, sourceRunArithmetic_execution, run]

theorem score_from_execution {submission : Submission} {claimed : NatE}
    (certificate : Certificate submission claimed) (clock : Nat)
    (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : execution input clock = (some (.finalFfi haltEvent), post))
    (success : outputByte input post.ffi.ioEvents ⟨32, by decide⟩ = 1) :
    claimed.Allows 3 := by
  apply certificate.score_at_least_three_of_accepted input input_gas input_initially_clear
    (.ffiOutcome haltEvent) post.ffi.ioEvents (source_of_execution clock post run) halt_covered
  exact ⟨⟨rfl, rfl⟩, success⟩

end InitE.SourceWitness
