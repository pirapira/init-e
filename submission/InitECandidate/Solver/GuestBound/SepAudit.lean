import InitECandidate.Solver.GuestBound.SepBinops
import InitECandidate.Solver.GuestBound.SepPushWords

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
#print axioms binop_framed
#print axioms pushLoad_framed
#print axioms «op_add_framed»
#print axioms «op_mul_framed»
#print axioms «op_sub_framed»
#print axioms «op_pc_framed»
#print axioms «op_gas_framed»
#print axioms «op_msize_framed»
#print axioms «op_calldatasize_framed»
#print axioms «op_codesize_framed»
#print axioms «op_returndatasize_framed»
#print axioms «op_eq_framed»
#print axioms «op_gt_framed»
#print axioms «op_lt_framed»
#print axioms «op_sgt_framed»
#print axioms «op_slt_framed»
