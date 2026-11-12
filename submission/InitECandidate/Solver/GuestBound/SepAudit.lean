import InitECandidate.Solver.GuestBound.SepStack

/-!
# Axiom audit of the framed specifications

Building this file prints the axioms each result depends on.
-/

open InitECandidate.Solver.GuestBound

#print axioms WPF.frame
#print axioms WPFr.frame
#print axioms raiseFn_sound
#print axioms charge_gas_framed
#print axioms refill_framed
#print axioms credit_framed
#print axioms charge_state_framed
#print axioms frame_halt_framed
#print axioms incorporate_error_framed
#print axioms pc_add_framed
#print axioms op_jumpdest_framed
#print axioms stack_pop_framed
#print axioms op_pop_framed
#print axioms scratch_alloc_framed
#print axioms stack_push_framed
