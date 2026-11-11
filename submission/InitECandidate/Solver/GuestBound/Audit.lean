import InitECandidate.Solver.GuestBound.Fns.L10
import InitECandidate.Solver.GuestBound.GuestInstance

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
#print axioms funCost_of_index
#print axioms functionsFrom_declarations
#print axioms stepCost_eq
#print axioms Fn.alloc
#print axioms effect_sound
#print axioms counterLoop_costs
#print axioms straight_sound
#print axioms offsetLoop_costs
#print axioms loop_costs
#print axioms Fn.memcpy
#print axioms pureLoop_costs
#print axioms constLoop_costs
#print axioms walkLoop_costs
#print axioms calmFn_sound
#print axioms orbit_bound
#print axioms Fn.keccak256
#print axioms Fn.memeq
#print axioms stepLoop_costs
#print axioms lowerLoop_costs
#print axioms guest_guestEnv
#print axioms guest_steps_le_of_main
#print axioms walkMLoop_costs
#print axioms wordExp_eval
#print axioms Fn.divmnu
#print axioms Fn.htab_set
