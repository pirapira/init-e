import InitECandidate.Solver.GuestBound.TrieDecStep4
import InitECandidate.Solver.GuestBound.TrieLoopCost
import InitECandidate.Solver.GuestBound.Fns.L9C0
import InitECandidate.Solver.GuestBound.Fns.L8C1
import InitECandidate.Solver.GuestBound.Fns.L7C0
import InitECandidate.Solver.GuestBound.Fns.L2C7
import InitECandidate.Solver.GuestBound.Fns.L0C10

/-!
# The witness decoder: the loop of `_decode_witness_node_body`

One iteration (`dc_body`) dispatches on `mode`; with its step cost this gives
the world theorem and the step bound of `_decode_witness_node_body`, both
conditional on the interface `DecIface` of `_decode_step` and `_resolve_step`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

local notation "DGUARD" => ((Exp.cmp Cmp.notEqual (Exp.var VarKind.local "go") (Exp.const (BitVec.ofNat 64 0))) : Exp Word)

local notation "M0PROG" => ((Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "top") (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.dec "hash" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 80))]))
                                  (Prog.seq
                                    (Prog.ite (Exp.op BinOp.and [(Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "hash") (Exp.const (BitVec.ofNat 64 0)))), (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "result") (Exp.const (BitVec.ofNat 64 0))))])
                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "result"), (Exp.const (BitVec.ofNat 64 24))]) (Exp.var VarKind.local "hash"))
                                      Prog.skip)
                                    (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 8))])) (Exp.const (BitVec.ofNat 64 1)))
                                      (Prog.seq
                                        (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "result") (Exp.const (BitVec.ofNat 64 0)))
                                          (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 8))])
                                          Prog.skip)
                                        (Prog.dec "ck" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "result"), (Exp.const (BitVec.ofNat 64 0))]))
                                          (Prog.seq
                                            (Prog.ite (Exp.op BinOp.and [(Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "ck") (Exp.const (BitVec.ofNat 64 3)))), (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "ck") (Exp.const (BitVec.ofNat 64 0))))])
                                              (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 8))])
                                              Prog.skip)
                                            (Prog.decCall "ex" Shape.one "node_new_ext" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 64))])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 72))])), (Exp.var VarKind.local "result")]
                                              (Prog.seq
                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "ex"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 48))])))
                                                (Prog.seq
                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "ex"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 56))])))
                                                (Prog.seq
                                                (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))])))
                                                (Prog.assign VarKind.local "result" (Exp.var VarKind.local "ex")))))))))
                                      (Prog.dec "br" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]))
                                        (Prog.dec "i" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 32))]))
                                          (Prog.seq
                                            (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "result"))
                                            (Prog.seq
                                            (Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "result") (Exp.const (BitVec.ofNat 64 0)))
                                              (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 40))]) (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 40))])), (Exp.const (BitVec.ofNat 64 1))]))
                                              Prog.skip)
                                            (Prog.seq
                                            (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))
                                            (Prog.ite (Exp.cmp Cmp.less (Exp.var VarKind.local "i") (Exp.const (BitVec.ofNat 64 16)))
                                              (Prog.seq
                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 32))]) (Exp.var VarKind.local "i"))
                                                (Prog.seq
                                                (Prog.assign VarKind.local "slot" (Exp.var VarKind.local "i"))
                                                (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 2)))))
                                              (Prog.dec "arr2" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 24))]))
                                                (Prog.decCall "bv" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) "rlp_item" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr2"), (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 16)), (Exp.const (BitVec.ofNat 64 16))])])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr2"), (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 16)), (Exp.const (BitVec.ofNat 64 16))]), (Exp.const (BitVec.ofNat 64 8))]))]
                                                  (Prog.dec "occ" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 40))]))
                                                    (Prog.seq
                                                      (Prog.ite (Exp.cmp Cmp.equal (Exp.rField 0 (Exp.var VarKind.local "bv")) (Exp.const (BitVec.ofNat 64 0)))
                                                        (Prog.seq
                                                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 160))]) (Exp.rField 1 (Exp.var VarKind.local "bv")))
                                                          (Prog.seq
                                                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 168))]) (Exp.rField 2 (Exp.var VarKind.local "bv")))
                                                          (Prog.ite (Exp.cmp Cmp.notEqual (Exp.rField 2 (Exp.var VarKind.local "bv")) (Exp.const (BitVec.ofNat 64 0)))
                                                            (Prog.assign VarKind.local "occ" (Exp.op BinOp.add [(Exp.var VarKind.local "occ"), (Exp.const (BitVec.ofNat 64 1))]))
                                                            Prog.skip)))
                                                        Prog.skip)
                                                      (Prog.seq
                                                      (Prog.ite (Exp.cmp Cmp.lower (Exp.var VarKind.local "occ") (Exp.const (BitVec.ofNat 64 2)))
                                                        (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 9))])
                                                        Prog.skip)
                                                      (Prog.seq
                                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 48))])))
                                                      (Prog.seq
                                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 56))])))
                                                      (Prog.seq
                                                      (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))])))
                                                      (Prog.assign VarKind.local "result" (Exp.var VarKind.local "br")))))))))))))))))))) : Prog Word)

local notation "DBODY" => ((Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "mode") (Exp.const (BitVec.ofNat 64 1)))
                            (Prog.decCall "d" (Shape.comb [Shape.one, Shape.one]) "_decode_step" [(Exp.var VarKind.local "db"), (Exp.var VarKind.local "cur_p"), (Exp.var VarKind.local "cur_n")]
                              (Prog.ite (Exp.cmp Cmp.equal (Exp.rField 0 (Exp.var VarKind.local "d")) (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.seq
                                  (Prog.assign VarKind.local "result" (Exp.rField 1 (Exp.var VarKind.local "d")))
                                  (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 0))))
                                (Prog.seq
                                  (Prog.store (Exp.op BinOp.add [(Exp.rField 1 (Exp.var VarKind.local "d")), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "top"))
                                  (Prog.seq
                                  (Prog.assign VarKind.local "top" (Exp.rField 1 (Exp.var VarKind.local "d")))
                                  (Prog.seq
                                  (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 8))])) (Exp.const (BitVec.ofNat 64 1)))
                                    (Prog.assign VarKind.local "slot" (Exp.const (BitVec.ofNat 64 1)))
                                    (Prog.assign VarKind.local "slot" (Exp.const (BitVec.ofNat 64 0))))
                                  (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 2))))))))
                            (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "mode") (Exp.const (BitVec.ofNat 64 2)))
                              (Prog.dec "arr" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 24))]))
                                (Prog.decCall "r" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) "_resolve_step" [(Exp.var VarKind.local "db"), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "slot"), (Exp.const (BitVec.ofNat 64 16))])])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "slot"), (Exp.const (BitVec.ofNat 64 16))]), (Exp.const (BitVec.ofNat 64 8))]))]
                                  (Prog.ite (Exp.cmp Cmp.equal (Exp.rField 0 (Exp.var VarKind.local "r")) (Exp.const (BitVec.ofNat 64 0)))
                                    (Prog.seq
                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 80))]) (Exp.const (BitVec.ofNat 64 0)))
                                      (Prog.seq
                                      (Prog.assign VarKind.local "result" (Exp.rField 1 (Exp.var VarKind.local "r")))
                                      (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 0)))))
                                    (Prog.seq
                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 80))]) (Exp.rField 3 (Exp.var VarKind.local "r")))
                                      (Prog.seq
                                      (Prog.assign VarKind.local "cur_p" (Exp.rField 1 (Exp.var VarKind.local "r")))
                                      (Prog.seq
                                      (Prog.assign VarKind.local "cur_n" (Exp.rField 2 (Exp.var VarKind.local "r")))
                                      (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 1)))))))))
                              (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "top") (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.dec "hash" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 80))]))
                                  (Prog.seq
                                    (Prog.ite (Exp.op BinOp.and [(Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "hash") (Exp.const (BitVec.ofNat 64 0)))), (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "result") (Exp.const (BitVec.ofNat 64 0))))])
                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "result"), (Exp.const (BitVec.ofNat 64 24))]) (Exp.var VarKind.local "hash"))
                                      Prog.skip)
                                    (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 8))])) (Exp.const (BitVec.ofNat 64 1)))
                                      (Prog.seq
                                        (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "result") (Exp.const (BitVec.ofNat 64 0)))
                                          (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 8))])
                                          Prog.skip)
                                        (Prog.dec "ck" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "result"), (Exp.const (BitVec.ofNat 64 0))]))
                                          (Prog.seq
                                            (Prog.ite (Exp.op BinOp.and [(Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "ck") (Exp.const (BitVec.ofNat 64 3)))), (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "ck") (Exp.const (BitVec.ofNat 64 0))))])
                                              (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 8))])
                                              Prog.skip)
                                            (Prog.decCall "ex" Shape.one "node_new_ext" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 64))])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 72))])), (Exp.var VarKind.local "result")]
                                              (Prog.seq
                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "ex"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 48))])))
                                                (Prog.seq
                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "ex"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 56))])))
                                                (Prog.seq
                                                (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))])))
                                                (Prog.assign VarKind.local "result" (Exp.var VarKind.local "ex")))))))))
                                      (Prog.dec "br" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]))
                                        (Prog.dec "i" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 32))]))
                                          (Prog.seq
                                            (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "result"))
                                            (Prog.seq
                                            (Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "result") (Exp.const (BitVec.ofNat 64 0)))
                                              (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 40))]) (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 40))])), (Exp.const (BitVec.ofNat 64 1))]))
                                              Prog.skip)
                                            (Prog.seq
                                            (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))
                                            (Prog.ite (Exp.cmp Cmp.less (Exp.var VarKind.local "i") (Exp.const (BitVec.ofNat 64 16)))
                                              (Prog.seq
                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 32))]) (Exp.var VarKind.local "i"))
                                                (Prog.seq
                                                (Prog.assign VarKind.local "slot" (Exp.var VarKind.local "i"))
                                                (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 2)))))
                                              (Prog.dec "arr2" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 24))]))
                                                (Prog.decCall "bv" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) "rlp_item" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr2"), (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 16)), (Exp.const (BitVec.ofNat 64 16))])])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr2"), (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 16)), (Exp.const (BitVec.ofNat 64 16))]), (Exp.const (BitVec.ofNat 64 8))]))]
                                                  (Prog.dec "occ" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 40))]))
                                                    (Prog.seq
                                                      (Prog.ite (Exp.cmp Cmp.equal (Exp.rField 0 (Exp.var VarKind.local "bv")) (Exp.const (BitVec.ofNat 64 0)))
                                                        (Prog.seq
                                                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 160))]) (Exp.rField 1 (Exp.var VarKind.local "bv")))
                                                          (Prog.seq
                                                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 168))]) (Exp.rField 2 (Exp.var VarKind.local "bv")))
                                                          (Prog.ite (Exp.cmp Cmp.notEqual (Exp.rField 2 (Exp.var VarKind.local "bv")) (Exp.const (BitVec.ofNat 64 0)))
                                                            (Prog.assign VarKind.local "occ" (Exp.op BinOp.add [(Exp.var VarKind.local "occ"), (Exp.const (BitVec.ofNat 64 1))]))
                                                            Prog.skip)))
                                                        Prog.skip)
                                                      (Prog.seq
                                                      (Prog.ite (Exp.cmp Cmp.lower (Exp.var VarKind.local "occ") (Exp.const (BitVec.ofNat 64 2)))
                                                        (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 9))])
                                                        Prog.skip)
                                                      (Prog.seq
                                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 48))])))
                                                      (Prog.seq
                                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 56))])))
                                                      (Prog.seq
                                                      (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))])))
                                                      (Prog.assign VarKind.local "result" (Exp.var VarKind.local "br")))))))))))))))))))))) : Prog Word)

set_option maxHeartbeats 16000000 in
/-- Mode 0: the finished node goes to the top record, or the loop ends. -/
theorem dc_mode0 (hE : GuestEnv E) (I : DecIface E) {R0 : Reg}
    {G : VarName → Option (PanValue Word)} {M : Word → Option (PanValue Word)}
    {F : FfiState σ} {fv lim dbv : Word} {L0 : Nat}
    (hGfv : G "frame_mem_ptr" = some (.word fv)) (hFv : 2952790016 ≤ fv.toNat) {a : St σ}
    (hI : DcI I R0 G M F fv lim dbv L0 a) {md0 : Word}
    (hmd : a.locals "mode" = some (.word md0)) (hn1 : md0 ≠ 1#64) (hn2 : md0 ≠ 2#64)
    (hgo : ∀ gv, a.locals "go" = some (.word gv) → gv ≠ 0#64) :
    WPs E a M0PROG (DcPost I R0 G M F fv lim dbv L0 a) := by
  obtain ⟨la, ga, ma, fa⟩ := a
  obtain ⟨R, sp, topv, resv, cp, cn, md, sl, gv, ℓ, hle, hW, hf, hg, hgs, hfs, hsl, hPre, qdb,
    qtop, qres, qcp, qcn, qmode, qslot, qgo, hst, hres, hfin, hm2t, hM⟩ := hI
  dsimp only at hW hf hg hgs hPre qdb qtop qres qcp qcn qmode qslot qgo hst hM hmd hgo
  have hmde : md = md0 := by
    rw [qmode] at hmd
    simpa using hmd
  subst hmde
  have hgv := hgo gv qgo
  have hres' := hres hn1 hn2
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hlim := lim.isLt
  have hgfv : ga "frame_mem_ptr" = some (.word fv) :=
    (hg _ (by decide) (by decide)).trans hGfv
  have hmu0 := dcMu_eq (a := (⟨la, ga, ma, fa⟩ : St σ)) hgs qtop qmode qgo
  dsimp only at hmu0
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  simp only [evalF_local, qtop, eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · rename_i hw0
    have ht0 : topv ≠ 0#64 := by
      rintro rfl
      rw [hwv] at hw0
      simp [evalPanCmp] at hw0
    obtain ⟨htsp, htlim⟩ : sp.toNat ≤ topv.toNat ∧ topv.toNat + 88 ≤ lim.toNat := by
      rcases hst.top_in with h0 | h
      · exact absurd h0 ht0
      · exact h
    have e8 : (topv + 8#64).toNat = topv.toNat + 8 := by bv_omega
    have e16 : (topv + 16#64).toNat = topv.toNat + 16 := by bv_omega
    have e32 : (topv + 32#64).toNat = topv.toNat + 32 := by bv_omega
    have e64 : (topv + 64#64).toNat = topv.toNat + 64 := by bv_omega
    have e72 : (topv + 72#64).toNat = topv.toNat + 72 := by bv_omega
    refine WPs.dec_w (fun hashv => WPs.conseq (Q' := DcPost I R0 G M F fv lim dbv L0
      (⟨la, ga, ma, fa⟩ : St σ)) ?_
      (fun r h => h.restore (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)))
    refine WPs.seq (fun a' => ∃ m', a' = ⟨updatePanValueMap la "hash" (.word hashv), ga, m', fa⟩ ∧
        WorldTJ R ga m' ∧
        ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) → m' x = ma x)
      ((dc_hash hE (s := (⟨updatePanValueMap la "hash" (.word hashv), ga, ma, fa⟩ : St σ))
        (resv := resv) (hashv := hashv) hW hres' (by lk [qres]) (by lk [])).conseq
        (fun r hr => by
          obtain ⟨m', hr, hw', hm'⟩ := hr
          exact ⟨_, _, _, _, hr, m', rfl, hw', hm'⟩)) ?_
    rintro _ ⟨m', rfl, hW', hm'⟩
    have tr : ∀ {x w : Word}, 2952790016 ≤ x.toNat → Rd ma x w → Rd m' x w := by
      intro x w hx hr
      unfold Rd at hr ⊢
      rw [hm' x (Or.inr hx)]
      exact hr
    have hic : icOf m' topv = icOf ma topv :=
      icOf_congr (fun _ => hm' _ (Or.inr (by omega)))
    have ctx : D0Ctx I R0 R G M fa fv lim dbv (⟨la, ga, ma, fa⟩ : St σ)
        (⟨updatePanValueMap la "hash" (.word hashv), ga, m', fa⟩ : St σ) sp topv resv cp cn md
        sl gv :=
      { le := hle, w := hW', ffi := rfl, glob := hg, gs := hgs, gfv := hgfv, fs := hfs,
        spl := hsl, hF := hFv, pre := hPre, qdb := by lk [qdb], qtop := by lk [qtop],
        qres := by lk [qres], qcp := by lk [qcp], qcn := by lk [qcn], qmode := by lk [qmode],
        qslot := by lk [qslot], qgo := by lk [qgo], m1 := hn1, m2 := hn2, gv0 := hgv,
        mem := fun addr ha => (hm' addr (by omega)).trans (hM addr ha),
        mu := by rw [hmu0, hic] }
    subst hf
    cases hst with
    | nil => exact absurd rfl ht0
    | @ext _ _ prev seg sgl ℓt h1 h2 h3 h4 r0 r1 r64 r72 hs1 himm htail =>
      refine WPs.ite (w := 1#64) (fun x hx => by
        have := eval_cmp_inv hE (op := .equal)
          (eval_load_rd hE (eval_addc hE 8#64 ctx.qtop) (tr (by omega) r1))
          (of_eval (eval_const _ 1#64)) _ hx
        rw [this]
        rfl) ?_
      rw [if_neg (by decide)]
      exact dc_ext hE I ctx h1 htsp htlim (tr (by omega) r0) (tr (by omega) r64)
        (tr (by omega) r72) hs1 himm
        (htail.frame hlim (fun x hx _ => hm' x (Or.inr (by omega)))) hres'
    | @br _ _ prev kd b iw ℓt h1 h2 h3 h4 r0 r1 hkd r16 r32 hi hKb hLb htail =>
      refine WPs.ite (w := 0#64) (fun x hx => by
        have := eval_cmp_inv hE (op := .equal)
          (eval_load_rd hE (eval_addc hE 8#64 ctx.qtop) (tr (by omega) r1))
          (of_eval (eval_const _ 1#64)) _ hx
        rw [this]
        simp [evalPanCmp, hkd]) ?_
      rw [if_pos (show (0#64 : Word) = 0 from rfl)]
      exact dc_br hE I ctx h1 h2 htsp htlim (tr (by omega) r0) (tr (by omega) r1) hkd
        (tr (by omega) r16) (tr (by omega) r32) hi hKb hLb
        (htail.frame hlim (fun x hx _ => hm' x (Or.inr (by omega)))) hres'
  · rename_i hw0
    have ht0 : topv = 0#64 := by
      by_contra hne
      apply hw0
      rw [hwv]
      simp [evalPanCmp, hne]
    subst ht0
    refine WPs.assign (old := gv) (w := 0#64) qgo (of_eval (eval_const _ _)) ?_
    refine ⟨_, _, _, _, rfl, ⟨R, sp, 0#64, resv, cp, cn, md, sl, 0#64, ℓ, hle, hW, hf, hg, hgs, hfs,
      hsl, hPre, by lk [qdb], by lk [qtop], by lk [qres], by lk [qcp], by lk [qcn],
      by lk [qmode], by lk [qslot], by lk [], hst, fun _ _ => hres', fun _ => ⟨hn1, hn2, rfl⟩,
      fun h => absurd h hn2, hM⟩, ?_⟩
    rw [hmu0, dcMu_eq (sp := sp) (t := 0#64) (md := md) (gv := 0#64) hgs (by lk [qtop])
      (by lk [qmode]) (by lk [])]
    have h1 : goOf gv = 1 := by
      unfold goOf
      rw [if_neg hgv]
    have h0 : goOf (0#64 : Word) = 0 := by decide
    rw [h1, h0]
    dsimp only
    omega

set_option maxHeartbeats 8000000 in
/-- One iteration of the decoder loop. -/
theorem dc_body (hE : GuestEnv E) (I : DecIface E) {R0 : Reg}
    {G : VarName → Option (PanValue Word)} {M : Word → Option (PanValue Word)}
    {F : FfiState σ} {fv lim dbv : Word} {L0 : Nat}
    (hGfv : G "frame_mem_ptr" = some (.word fv)) (hFv : 2952790016 ≤ fv.toNat) {a : St σ}
    (hI : DcI I R0 G M F fv lim dbv L0 a) (hct : CondTrue E a DGUARD) :
    WPs E a DBODY (DcPost I R0 G M F fv lim dbv L0 a) := by
  have hI0 := hI
  obtain ⟨R, sp, topv, resv, cp, cn, md, sl, gv, ℓ, hle, hW, hf, hg, hgs, hfs, hsl, hPre, qdb,
    qtop, qres, qcp, qcn, qmode, qslot, qgo, -⟩ := hI0
  obtain ⟨w, cc, hcond, hw⟩ := hct
  have hgo : ∀ gv', a.locals "go" = some (.word gv') → gv' ≠ 0#64 := by
    intro gv' hq
    have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := gv') (by lk [hq]))
      (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    rintro rfl
    rw [hcv] at hw
    simp [evalPanCmp] at hw
  refine WPs.ite_both (fun w1 hw1 => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw1
  simp only [evalF_local, qmode, eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · rename_i h10
    have hn1 : md ≠ 1#64 := by
      rintro rfl
      rw [hwv] at h10
      simp [evalPanCmp] at h10
    refine WPs.ite_both (fun w2 hw2 => ?_)
    obtain ⟨x, y, hx, hy, hwv2⟩ := cmp_word_inv hE hw2
    simp only [evalF_local, qmode, eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i h20
      have hn2 : md ≠ 2#64 := by
        rintro rfl
        rw [hwv2] at h20
        simp [evalPanCmp] at h20
      exact dc_mode0 hE I hGfv hFv hI qmode hn1 hn2 hgo
    · rename_i h20
      have h2 : md = 2#64 := by
        by_contra hne
        apply h20
        rw [hwv2]
        simp [evalPanCmp, hne]
      subst h2
      exact dc_mode2 hE I hGfv hFv hI qmode hgo
  · rename_i h10
    have h1 : md = 1#64 := by
      by_contra hne
      apply h10
      rw [hwv]
      simp [evalPanCmp, hne]
    subst h1
    exact dc_mode1 hE I hGfv hFv hI qmode hgo

theorem dc_body_cost (hE : GuestEnv E) : Costs E DBODY (10 ^ 139) := by
  have h : ∃ B, Costs E DBODY B ∧ B ≤ 10 ^ 139 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem dc_loop_cost (hE : GuestEnv E) (I : DecIface E) {R0 : Reg}
    {G : VarName → Option (PanValue Word)} {M : Word → Option (PanValue Word)}
    {F : FfiState σ} {fv lim dbv : Word} {L0 : Nat}
    (hGfv : G "frame_mem_ptr" = some (.word fv)) (hFv : 2952790016 ≤ fv.toNat) :
    Triple E (fun a => DcI I R0 G M F fv lim dbv L0 a ∧ dcMu a ≤ 2 ^ 138)
      (.while DGUARD DBODY) ((2 ^ 138 + 1) * (expCost DGUARD + 10 ^ 139 + 1))
      (fun r => match r with
        | .normal _ _ _ _ => True
        | _ => True) := by
  refine (Triple.while_exit (I := DcI I R0 G M F fv lim dbv L0) (μ := dcMu)
    (Q := fun _ => True) (2 ^ 138) (condCost_exp _) (fun _ _ _ => trivial) ?_).consequence
    (fun _ h => h) (Nat.le_refl _) (fun r _ => by cases r <;> trivial)
  intro k
  refine Triple.of_costs (dc_body_cost hE) ?_
  rintro fuel' a r' n' ⟨hI, hk, hct⟩ hrun' hne'
  rcases dc_body hE I hGfv hFv hI hct r' (Runs.of_run hrun') with
    hst | ⟨l, g, m, f, rfl, hI', hlt⟩
  · cases r' with
    | error l g m f => cases hne'
    | raised l g m f ex val => trivial
    | finalFfi l g m f ev => trivial
    | _ => exact absurd hst (fun h => h)
  · exact ⟨hI', hk ▸ hlt⟩

/-- What `_decode_witness_node_body` guarantees: a node at level `L0` (or null). -/
def DecQ (I : DecIface E) (R0 : Reg) (s : St σ) (sp0 fv : Word) (L0 : Nat) (r : Result σ) : Prop :=
  ∃ l g m res R sp', r = .returned l g m s.ffi [.word res] ∧ R0.Le R ∧ WorldTJ R g m ∧
    DRes R L0 res ∧ I.Pre R g ∧
    (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = s.globals x) ∧
    g "scratch_ptr" = some (.word sp') ∧ fv.toNat ≤ sp'.toNat ∧ sp'.toNat ≤ sp0.toNat ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) → m addr = s.memory addr

set_option maxHeartbeats 8000000 in
theorem decode_body_world (hE : GuestEnv E) (I : DecIface E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "_decode_witness_node_body" E.functions =
      some (parameters, body))
    (R0 : Reg) (s : St σ) (r : Result σ) (dbv pw nw sp0 fv : Word) (L0 : Nat)
    (hdb : s.locals "db" = some (.word dbv)) (hp : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw)) (hW : WorldTJ R0 s.globals s.memory)
    (hPre : I.Pre R0 s.globals) (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ DecQ I R0 s sp0 fv L0 r := by
  have hbody := (fun_of_index 262 hE.functions (by guest_decl_at 262) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (DecQ I R0 s sp0 fv L0)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := pw) (of_eval (by lk [hp])) ?_
  refine WPs.dec (w := nw) (of_eval (by lk [hn])) ?_
  refine WPs.dec (w := 1#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 1#64) (of_eval (eval_const _ _)) ?_
  refine WPs.seqG (fun a => DcI I R0 s.globals s.memory s.ffi fv sp0 dbv L0 a ∧
      ∃ kk, E.cond a DGUARD = some (0, kk))
    (WPs.loopG (I := DcI I R0 s.globals s.memory s.ffi fv sp0 dbv L0)
      ⟨R0, sp0, 0#64, 0#64, pw, nw, 1#64, 0#64, 1#64, L0, Reg.Le.refl R0, hW, rfl,
        fun _ _ _ => rfl, hsp, hfs, Nat.le_refl _, hPre, by lk [hdb], by lk [], by lk [],
        by lk [], by lk [], by lk [], by lk [], by lk [], .nil, fun h _ => absurd rfl h,
        fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ _ => rfl⟩
      (fun a hI hct => (dc_body hE I hfv hF hI hct).conseq (by
        rintro r ⟨l, g, m, f, rfl, hI', -⟩
        exact hI'))
      (fun a kk hI hk => ⟨hI, kk, hk⟩)) ?_
  rintro ⟨la, ga, ma, fa⟩ ⟨⟨R, sp, topv, resv, cp, cn, md, sl, gv, ℓ, hle, hW', hf, hg, hgs, hfs',
    hsl, hPre', qdb, qtop, qres, qcp, qcn, qmode, qslot, qgo, hst, hres, hfin, hm2t, hM⟩, kk, hk⟩
  dsimp only at hW' hf hg hgs hPre' qdb qtop qres qcp qcn qmode qslot qgo hst hM
  subst hf
  have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := gv) (by lk [qgo]))
    (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hk)
  simp only [PanValue.word.injEq] at hcv
  have hg0 : gv = 0#64 := by
    by_contra hne
    simp [evalPanCmp, hne] at hcv
  obtain ⟨hn1, hn2, ht0⟩ := hfin hg0
  subst ht0
  have hℓ := hst.zero
  subst hℓ
  refine WPs.ret (w := resv) (of_eval (by lk [qres])) ?_
  simp only [restorePanValueFfiLocal]
  exact ⟨_, ga, ma, resv, R, sp, rfl, hle, hW', hres hn1 hn2, hPre', hg, hgs, hfs', hsl, hM⟩

theorem dec_ret_cost (hE : GuestEnv E) :
    Costs E (Prog.return (Exp.var VarKind.local "result") : Prog Word) 10 := ins_ret_cost hE

set_option maxHeartbeats 8000000 in
/-- Step bound of `_decode_witness_node_body`, given the decoder interface. -/
theorem decode_body_cost (hE : GuestEnv E) (I : DecIface E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "_decode_witness_node_body" E.functions =
      some (parameters, body))
    (R0 : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (dbv pw nw sp0 fv : Word)
    (L0 : Nat)
    (hdb : s.locals "db" = some (.word dbv)) (hp : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw)) (hW : WorldTJ R0 s.globals s.memory)
    (hPre : I.Pre R0 s.globals) (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 182 := by
  have hbody := (fun_of_index 262 hE.functions (by guest_decl_at 262) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hall := Triple.dec (E := E) (P := fun a => a = s)
    (P' := fun a => a = ⟨updatePanValueMap s.locals "top" (.word 0#64), s.globals, s.memory,
      s.ffi⟩) "top" Shape.one (Exp.const (BitVec.ofNat 64 0)) ?_
    (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap s.locals "top"
        (.word 0#64)) "result" (.word 0#64), s.globals, s.memory, s.ffi⟩) "result" Shape.one
      (Exp.const (BitVec.ofNat 64 0)) ?_
      (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
          s.locals "top" (.word 0#64)) "result" (.word 0#64)) "cur_p" (.word pw), s.globals,
          s.memory, s.ffi⟩) "cur_p" Shape.one (Exp.var VarKind.local "p") ?_
        (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
            (updatePanValueMap s.locals "top" (.word 0#64)) "result" (.word 0#64)) "cur_p"
            (.word pw)) "cur_n" (.word nw), s.globals, s.memory, s.ffi⟩) "cur_n" Shape.one
          (Exp.var VarKind.local "n") ?_
          (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap
              (updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "top"
              (.word 0#64)) "result" (.word 0#64)) "cur_p" (.word pw)) "cur_n" (.word nw))
              "mode" (.word 1#64), s.globals, s.memory, s.ffi⟩) "mode" Shape.one
            (Exp.const (BitVec.ofNat 64 1)) ?_
            (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap
                (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap
                s.locals "top" (.word 0#64)) "result" (.word 0#64)) "cur_p" (.word pw)) "cur_n"
                (.word nw)) "mode" (.word 1#64)) "slot" (.word 0#64), s.globals, s.memory,
                s.ffi⟩) "slot" Shape.one (Exp.const (BitVec.ofNat 64 0)) ?_
              (Triple.dec (P' := fun a => DcI I R0 s.globals s.memory s.ffi fv sp0 dbv L0 a ∧
                  dcMu a ≤ 2 ^ 138) "go" Shape.one (Exp.const (BitVec.ofNat 64 1)) ?_
                (Triple.seq (Mid := fun _ => True) (Q := fun _ => True)
                  (dc_loop_cost hE I hfv hF) (dec_ret_cost hE))))))))
  · have hn' := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq] at hn'
    refine Nat.le_trans hn' ?_
    decide +kernel
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) a 0#64) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 0#64) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (w := pw) (by lk [hp]) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (w := nw) (by lk [hn]) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 1#64) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 0#64) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 1#64) val hval
    subst this
    exact ⟨⟨R0, sp0, 0#64, 0#64, pw, nw, 1#64, 0#64, 1#64, L0, Reg.Le.refl R0, hW, rfl,
      fun _ _ _ => rfl, hsp, hfs, Nat.le_refl _, hPre, by lk [hdb], by lk [], by lk [],
      by lk [], by lk [], by lk [], by lk [], by lk [], .nil, fun h _ => absurd rfl h,
      fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ _ => rfl⟩,
      dcMu_le _⟩

end InitECandidate.Solver.GuestBound
