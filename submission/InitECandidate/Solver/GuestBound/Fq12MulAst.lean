import InitECandidate.Solver.GuestBound.Fq12Reduce

/-! The inner loop of `fq12_mul`, cut out of `Guest/SoftwareAst.lean` by `tools/gen-fq12mul-ast.py`. -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

notation "FQM_INNER" => ((Prog.while (Exp.cmp Cmp.notLower (Exp.var VarKind.local "iend") (Exp.var VarKind.local "i")) (Prog.dec "ai" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) (Exp.load (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) (Exp.op BinOp.add [(Exp.var VarKind.local "a"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 32))])])) (Prog.dec "bj" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) (Exp.load (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) (Exp.op BinOp.add [(Exp.var VarKind.local "b"), (Exp.panOp PanOp.mul [(Exp.op BinOp.sub [(Exp.var VarKind.local "k"), (Exp.var VarKind.local "i")]), (Exp.const (BitVec.ofNat 64 32))])])) (Prog.decCall "p" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) "fq_mul" [(Exp.var VarKind.local "ai"), (Exp.var VarKind.local "bj")] (Prog.seq (Prog.call (some ((some (VarKind.local, "acc")), none)) "fq_add" [(Exp.var VarKind.local "acc"), (Exp.var VarKind.local "p")]) (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))))))) : Prog Word)

end InitECandidate.Solver.GuestBound
