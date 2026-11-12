import InitECandidate.Solver.GuestBound.PairingAst
import InitECandidate.Solver.GuestBound.Fns.L9

/-! Unconditional costs of the loop-free and counter-loop parts of `bn254_pairing_check`. -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem pc_loop_cost (hE : GuestEnv E) : ∃ B, Costs E PC_LOOP B ∧ B ≤ 10 ^ 200 :=
  ⟨_, by cost_derive [], by decide +kernel⟩

end InitECandidate.Solver.GuestBound
