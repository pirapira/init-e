import InitECandidate.Solver.GuestBound.GuestEnv

/-!
# Example of a hand-proved loop

The loop of `rlp_be_len` (position 118 in the AST, loop 0) is accepted
automatically by `walkMLoop`; this module proves it in the form the
hand-proved hook expects, to show the statement shape and to test the hook.
It is used only when `manual-loops.txt` contains the line

    rlp_be_len 0 340282366920938463537161583726606417924 InitECandidate.Solver.GuestBound.Manual.Example
-/

namespace InitECandidate.Solver.GuestBound.Manual
open Flapjack

theorem rlp_be_len.loop0 {σ : Type} {E : Env σ} (hE : GuestEnv E) (b : Nat)
    (hbody : Costs E (loopBody 118 0) b) :
    Costs E (.while (loopGuard 118 0) (loopBody 118 0))
      (340282366920938463537161583726606417924 * (expCost (loopGuard 118 0) + b + 1)) := by
  have h := walkMLoop_costs hE.word (loopGuard 118 0) (loopBody 118 0) b (by decide +kernel) hbody
  have hiters : walkIters (assignedLocals (loopBody 118 0)).length = 340282366920938463537161583726606417924 := by decide +kernel
  rw [hiters] at h
  exact h

end InitECandidate.Solver.GuestBound.Manual
