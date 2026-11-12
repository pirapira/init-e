import InitECandidate.Solver.GuestBound.SepBinops
import InitECandidate.Solver.GuestBound.SepPushWords
import InitECandidate.Solver.GuestBound.SepFrameOps
import InitECandidate.Solver.GuestBound.RunFramesLoop
import InitECandidate.Solver.GuestBound.DispatchOps
import InitECandidate.Solver.GuestBound.RfInstance
import InitECandidate.Solver.GuestBound.RfInstanceM
import InitECandidate.Solver.GuestBound.SepFinish
import InitECandidate.Solver.GuestBound.SepDom

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
#print axioms «op_timestamp_framed»
#print axioms «op_number_framed»
#print axioms «op_gaslimit_framed»
#print axioms «op_chainid_framed»
#print axioms «op_slotnum_framed»
#print axioms «op_add_frame»
#print axioms «op_mul_frame»
#print axioms «op_sub_frame»
#print axioms «op_signextend_frame»
#print axioms «op_lt_frame»
#print axioms «op_gt_frame»
#print axioms «op_slt_frame»
#print axioms «op_sgt_frame»
#print axioms «op_eq_frame»
#print axioms «op_iszero_frame»
#print axioms «op_shl_frame»
#print axioms «op_shr_frame»
#print axioms «op_sar_frame»
#print axioms «op_pc_frame»
#print axioms «op_gas_frame»
#print axioms «op_jumpdest_frame»
#print axioms «op_msize_frame»
#print axioms «op_pop_frame»
#print axioms «op_address_frame»
#print axioms «op_origin_frame»
#print axioms «op_caller_frame»
#print axioms «op_callvalue_frame»
#print axioms «op_calldatasize_frame»
#print axioms «op_codesize_frame»
#print axioms «op_gasprice_frame»
#print axioms «op_returndatasize_frame»
#print axioms «op_basefee_frame»
#print axioms «op_coinbase_frame»
#print axioms «op_timestamp_frame»
#print axioms «op_number_frame»
#print axioms «op_gaslimit_frame»
#print axioms «op_chainid_frame»
#print axioms «op_prevrandao_frame»
#print axioms «op_slotnum_frame»
#print axioms «op_and_frame»
#print axioms «op_or_frame»
#print axioms «op_xor_frame»
#print axioms «op_not_frame»
#print axioms «op_byte_frame»
#print axioms «op_jump_frame»
#print axioms «op_jumpi_frame»
#print axioms «op_dup_frame»
#print axioms «op_dupn_frame»
#print axioms rf_body_wps
#print axioms rf_loop
#print axioms run_frames_bound
#print axioms tree_sound
#print axioms handler_leaf
#print axioms handlers_proved
#print axioms op_dispatch_frame
#print axioms frame_exception_framed
#print axioms rfDispatch_step
#print axioms rfSpec
#print axioms run_frames_bound_frame
#print axioms frame_mem_alloc_framed
#print axioms extend_memory_framed
#print axioms add_sat_exact
#print axioms ceil32_runs
#print axioms m64_nat
#print axioms mul64x64_runs
#print axioms sat_word_runs
#print axioms u256_is_zero_runs
#print axioms words_of_runs
#print axioms memory_gas_cost_runs
#print axioms extend_memory_cost1_runs
#print axioms charge_with_memory_framed
#print axioms op_charge_mem
#print axioms op_mload_frameM
#print axioms op_dispatch_frameM
#print axioms rfDispatch_stepM
#print axioms run_frames_bound_frameM
#print axioms st_be32_framed
#print axioms st_be64_framed
#print axioms u256_to_be32_framed
#print axioms op_mstore_frameM
#print axioms op_mstore8_frameM
#print axioms op_stop_frameM
#print axioms op_return_frameM
#print axioms op_revert_frameM
#print axioms run_frames_bound_ghost
#print axioms run_frames_bound_chain
#print axioms frame_epilogue_seq
#print axioms finish_chain
#print axioms run_frames_bound_world
#print axioms Fr.reclaim
#print axioms op_swap_frame
#print axioms op_swapn_frame
#print axioms op_exchange_frame
