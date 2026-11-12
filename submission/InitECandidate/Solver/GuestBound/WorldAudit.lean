import InitECandidate.Solver.GuestBound.WorldRestore
import InitECandidate.Solver.GuestBound.WorldAssn
import InitECandidate.Solver.GuestBound.WorldRollback
import InitECandidate.Solver.GuestBound.WorldBlob
import InitECandidate.Solver.GuestBound.WorldJset
import InitECandidate.Solver.GuestBound.TrieNew
import InitECandidate.Solver.GuestBound.WorldNode
import InitECandidate.Solver.GuestBound.TrieFreeze

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
