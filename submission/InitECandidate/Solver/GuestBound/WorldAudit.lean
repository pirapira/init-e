import InitECandidate.Solver.GuestBound.WorldRestore
import InitECandidate.Solver.GuestBound.WorldAssn
import InitECandidate.Solver.GuestBound.WorldRollback
import InitECandidate.Solver.GuestBound.WorldBlob

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
