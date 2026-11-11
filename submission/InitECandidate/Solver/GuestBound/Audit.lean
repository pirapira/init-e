import InitECandidate.Solver.GuestBound.ProgramBound

/-! Axiom audit for the guest-bound modules: each line must report only
`propext`, `Classical.choice` and `Quot.sound` (or no axioms). -/

open InitECandidate.Solver.GuestBound

#print axioms Triple.consequence
#print axioms Triple.skip
#print axioms Triple.seq
#print axioms Triple.ite
#print axioms while_steps
#print axioms Triple.while
#print axioms Triple.while_word
#print axioms condCost
#print axioms Costs.assignLocal
#print axioms callSteps_le
#print axioms Costs.call
#print axioms Costs.assignGlobal
#print axioms Costs.return
#print axioms Costs.raise
#print axioms Costs.store
#print axioms Costs.store32
#print axioms Costs.storeByte
#print axioms Costs.skip
#print axioms Costs.break
#print axioms Costs.continue
#print axioms Costs.seq
#print axioms Costs.ite
#print axioms Costs.dec
#print axioms Costs.decCall
#print axioms Costs.tick
#print axioms Costs.annot
#print axioms Costs.primitive
#print axioms Costs.shMemLoad
#print axioms Costs.shMemStore
#print axioms Costs.extCall
#print axioms staticCost_sound
#print axioms programStepped_le
