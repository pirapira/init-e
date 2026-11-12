import InitECandidate.Solver.GuestBound.FnsH
import InitECandidate.Solver.GuestBound.HeapFloor
import InitECandidate.Solver.GuestBound.Gas
import InitECandidate.Solver.GuestBound.MemKeep
import InitECandidate.Solver.GuestBound.HtabSet
import InitECandidate.Solver.GuestBound.HtabDelAny
import InitECandidate.Solver.GuestBound.HtabTruncate

/-! Axiom audit for the conditional results (not part of the generated
per-function chain): each line must report only `propext`,
`Classical.choice` and `Quot.sound` (or no axioms). -/

open InitECandidate.Solver.GuestBound

#print axioms htab_truncate_cost
#print axioms htab_set_exec
#print axioms htab_del_any_exec
#print axioms fq12_inv_cost
#print axioms fq_neg_canon
#print axioms fq_mul_small_canon
#print axioms fq12_reduce_canon
#print axioms fq12_mul_canon
#print axioms fq12_sqr_canon
#print axioms fe_add_canon
#print axioms fe_sub_canon
#print axioms fe_neg_canon
#print axioms fe_mul_small_canon
#print axioms fe_mul12_canon
#print axioms fe_sqr12_canon
#print axioms fe_set_zero12_canon
#print axioms fe_set_one12_canon
#print axioms ecp_set_inf12_bufs
#print axioms ecp_double12_bufs
#print axioms ecp_linefunc12_bufs
#print axioms ecp_add12_bufs
#print axioms memcpy_self
#print axioms fq12_frob_canon
#print axioms bn254_init_noop
#print axioms fq12_cast_canon
#print axioms fq12_twist_canon
#print axioms bn254_miller_raw_bufs
#print axioms fq2_mul_canon
#print axioms fe_mul1_canon
#print axioms fe_mul2_canon
#print axioms fe_sqr_small_canon
#print axioms fe_set_zeroK_canon
#print axioms fe_set_oneK_canon
#print axioms ecp_set_infK_bufs
#print axioms ecp_doubleK_bufs
#print axioms ecp_addK_bufs
#print axioms ecp_mulK_bufs
#print axioms fq_to_mont_canon
#print axioms bn254_parse_g1_bufs
#print axioms bn254_parse_g2_bufs
#print axioms call_cost_at
#print axioms WPc.ite_both
#print axioms pc_round
#print axioms bn254_pairing_check_cost
#print axioms fq_mul_spec1
#print axioms fun_heap_keep
#print axioms fun_floor_keep
#print axioms H.«bn254_pairing_check»
#print axioms H.«pre_alt_bn128_pairing_check»
#print axioms H.«run_precompile»
#print axioms H.«frame_prologue»
#print axioms H.«frame_start»
#print axioms H.«start_child»
#print axioms H.«generic_create»
#print axioms H.«op_create»
#print axioms H.«op_create2»
#print axioms H.«generic_call»
#print axioms H.«op_call»
#print axioms H.«op_callcode»
#print axioms H.«op_delegatecall»
#print axioms H.«op_staticcall»
#print axioms charge_gas_spec
#print axioms WPr.ite_both
#print axioms noStore_sound
#print axioms htab_get_mem
#print axioms nodedb_lookup_mem
