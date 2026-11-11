import InitECandidate.Solver.GuestBound.StepRules

/-!
# The loop of `_rlp_validate_items_body`

Each iteration pops a record, advances `pos`, or pushes a record after
`scratch_alloc(24)`. Pops and advances change only the locals `go`, `pos`,
`end`, `top`; a push decreases the scratch rank. So the loop is a ranked walk.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

theorem scratchRank_lt (g : VarName → Option (PanValue Word)) : scratchRank g < 2 ^ 65 := by
  unfold scratchRank
  split
  · rename_i p fmp _ _
    have := p.isLt
    split <;> omega
  · omega

namespace Manual

theorem «_rlp_validate_items_body».loop0 {σ : Type} {E : Env σ} (hE : GuestEnv E) (b : Nat)
    (hbody : Costs E (loopBody 110 0) b) :
    Costs E (.while (loopGuard 110 0) (loopBody 110 0))
      (4271974071841820168495390267933222483964884098185561298029418866064329946018268565607043563520000 * (expCost (loopGuard 110 0) + b + 1)) := by
  revert hbody
  loop_reduce 110 0
  intro hbody
  have hq := keepFn_sound (quietKeeper E) hE.functions calmDepth
  have hN : 2 ^ 65 * walkIters ["go", "pos", "end", "top"].length = 4271974071841820168495390267933222483964884098185561298029418866064329946018268565607043563520000 := by decide +kernel
  rw [← hN]
  exact rankedWalk_costs (E := E) ["go", "pos", "end", "top"] scratchRank (2 ^ 65)
    scratchRank_lt _ _ b
    (fun fuel s r n hrun =>
      (StepOk.ite (D := [])
        (StepOk.ite
          (StepOk.of_walk hE.word (quietFn Guest.Software.guestAst) hq (by decide +kernel))
          (StepOk.of_walk hE.word (quietFn Guest.Software.guestAst) hq (by decide +kernel)))
        (StepOk.decCall_quiet
          (hq "rlp_item_header"
            (show keepFn quietLeaf Guest.Software.guestAst calmDepth "rlp_item_header" = true by
              decide +kernel))
          (by decide) (by simp)
          (StepOk.dec_word (by decide)
            (StepOk.dec_word (by decide)
              (StepOk.ite
                (StepOk.alloc_push hE (by decide) (by decide +kernel))
                (StepOk.assign_word (by simp) (by simp)))))))
        fuel s r n (by intro y hy; cases hy) hrun)
    hbody

end Manual
end InitECandidate.Solver.GuestBound
