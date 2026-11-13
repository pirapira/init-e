import InitECandidate.Solver.GuestBound.WorldRestore
import InitECandidate.Solver.GuestBound.WorldAssn
import InitECandidate.Solver.GuestBound.WorldRollback
import InitECandidate.Solver.GuestBound.WorldBlob
import InitECandidate.Solver.GuestBound.WorldJset
import InitECandidate.Solver.GuestBound.TrieNew
import InitECandidate.Solver.GuestBound.WorldNode
import InitECandidate.Solver.GuestBound.TrieFreeze
import InitECandidate.Solver.GuestBound.TrieKey
import InitECandidate.Solver.GuestBound.TrieWalkFillCost
import InitECandidate.Solver.GuestBound.TrieDecLoop
import InitECandidate.Solver.GuestBound.TrieFrozen
import InitECandidate.Solver.GuestBound.TrieResolve
import InitECandidate.Solver.GuestBound.TrieCompact
import InitECandidate.Solver.GuestBound.TrieDecFinal
import InitECandidate.Solver.GuestBound.TrieDecWrap
import InitECandidate.Solver.GuestBound.TrieMptNew
import InitECandidate.Solver.GuestBound.TrieNibKey
import InitECandidate.Solver.GuestBound.TrieBranch
import InitECandidate.Solver.GuestBound.TrieIns
import InitECandidate.Solver.GuestBound.TrieLeafIns
import InitECandidate.Solver.GuestBound.TrieSplit
import InitECandidate.Solver.GuestBound.TrieLoop
import InitECandidate.Solver.GuestBound.TrieHandle
import InitECandidate.Solver.GuestBound.TrieLoopCost
import InitECandidate.Solver.GuestBound.TrieConcat
import InitECandidate.Solver.GuestBound.TrieDelExt
import InitECandidate.Solver.GuestBound.TrieCollapse
import InitECandidate.Solver.GuestBound.TrieDelete
import InitECandidate.Solver.GuestBound.TrieDelNode
import InitECandidate.Solver.GuestBound.TrieSet

/-! Axioms of the world-state layer results. -/

open InitECandidate.Solver.GuestBound

#print axioms HtabOK.frame
#print axioms TabsOK.update
#print axioms TabStep.of_set
#print axioms TabStep.of_del
#print axioms JournalOK.step
#print axioms htab_set_only
#print axioms state_restore_world
#print axioms Assn.region_changeV
#print axioms restore_spec
#print axioms HeapW.tab_step
#print axioms HeapW.node_child
#print axioms HeapW.node_add
#print axioms NodesOK.store_child
#print axioms rollback_world
#print axioms WorldTJ.alloc
#print axioms WorldTJ.write_free
#print axioms WorldTJ.release
#print axioms HeapW.jpush
#print axioms jset_world
#print axioms node_new_ext_world
#print axioms WorldTJ.node_child
#print axioms node_invalidate_world
#print axioms ImOK.tab_step
#print axioms ImOK.node_add
#print axioms ImOK.store_node
#print axioms SegsOK.frame
#print axioms WorldTJ.freeze
#print axioms WorldTJ.seg
#print axioms key_to_nibbles_world
#print axioms node_new_leaf_world
#print axioms node_new_branch_world
#print axioms WorldTJ.im_nibs
#print axioms WorldTJ.kd
#print axioms create_branch_world
#print axioms common_prefix_spec
#print axioms insert_leaf_world
#print axioms WorldTJ.ext
#print axioms WorldTJ.slot
#print axioms split_ext_world
#print axioms ins_step
#print axioms mpt_insert_node_world
#print axioms WorldTJ.root
#print axioms WorldTJ.set_root
#print axioms WorldTJ.add_handle
#print axioms ins_body
#print axioms mpt_insert_node_cost
#print axioms WorldTJ.ext_lv
#print axioms WorldTJ.slot_lv
#print axioms WorldTJ.cv_ext
#print axioms ImOK.store_child
#print axioms WorldTJ.fresh_nibs
#print axioms nibbles_concat_world
#print axioms delete_ext_finish_world
#print axioms collapse_branch_world
#print axioms uw_body
#print axioms dl_body
#print axioms delete_body_world
#print axioms delete_body_cost
#print axioms delete_node_world
#print axioms delete_node_cost
#print axioms mpt_set_world
#print axioms mpt_set_cost
#print axioms keccak_f1600_frame
#print axioms keccak_absorb_frame
#print axioms keccak256_frame
#print axioms mpt_nibble_key_world
#print axioms nibKeySpec
#print axioms localOnly_sound
#print axioms wk_scan
#print axioms wk_body
#print axioms node_rlp_fill_world
#print axioms wk_body_cost
#print axioms node_rlp_fill_cost
#print axioms dc_mode1
#print axioms dc_mode2
#print axioms dc_ext
#print axioms dc_br
#print axioms dc_body
#print axioms decode_body_world
#print axioms decode_body_cost
#print axioms WorldTJ.fresh_cn
#print axioms node_new_hashed_world
#print axioms resolve_step_world
#print axioms resolve_spec
#print axioms WorldTJ.grow
#print axioms key_to_nibbles_nib2
#print axioms compact_to_nibbles_nib
#print axioms ds_branch
#print axioms ds_ext
#print axioms decode_step_world
#print axioms decode_witness_body_world
#print axioms decode_witness_body_cost
#print axioms decode_mpt_world
#print axioms decode_node_world
#print axioms decode_mpt_cost
#print axioms decode_node_cost
#print axioms WorldTJ.fresh_handle
#print axioms mpt_new_world
#print axioms decode_witness_to_mpt_world
#print axioms mpt_from_witness_world
