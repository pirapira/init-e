import InitECandidate.Solver.GuestBound.ExpCost

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
