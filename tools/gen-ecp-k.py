#!/usr/bin/env python3
"""Regenerate GuestBound/EcpK.lean: ecp_set_inf and ecp_double for any field size. Run from the repository root."""
EZ="F * 32#64"
def c1(p): return f"{p} + {EZ}"
def c2(p): return f"{p} + 2#64 * ({EZ})"
val={"W":"hp","S":"q1","B":"q2","H":"q3","S2":"q4","T1":"q5","T2":"q6","x":"P","y":c1("P"),"z":c2("P")}
low={"W":"l0","S":"l1","B":"l2","H":"l3","S2":"l4","T1":"l5","T2":"l6"}
steps=[("sqr","T1",["x"]),("mul_small","W",["T1"]),("mul","S",["y","z"]),("mul","T1",["x","y"]),("mul","B",["T1","S"]),("sqr","T1",["W"]),("mul_small","T2",["B"]),("sub","H",["T1","T2"]),("sqr","S2",["S"]),("mul","T1",["H","S"]),("mul_small","T1",["T1"]),("mul_small","T2",["B"]),("sub","T2",["T2","H"]),("mul","T2",["W","T2"]),("sqr","W",["y"]),("mul","W",["W","S2"]),("mul_small","W",["W"]),("sub","T2",["T2","W"]),("mul","S",["S","S2"]),("mul_small","S",["S"])]
body=""
for op,d,args in steps:
    evs=" ".join("(by lk [hpt])" for _ in args)
    extra=" (eval_const _ _)" if op=="mul_small" else ""
    heavy=op in("mul","sqr")
    hk="hK" if heavy else "hK12"
    hg=" hgq" if heavy else ""
    mems=" ".join("(by simp [hP0, hP1, hP2])" for _ in args)
    names=f"(A := {val[args[0]]})"+(f" (B := {val[args[1]]})" if len(args)>1 else "")
    body+=f"  refine WPs.fe_{op}_stepK hE hF {hk} (D := {val[d]}) {names} (by lk [hfld]) (by lk []) {evs}{extra}{hg} hB\n    (by simp) (Or.inl {low[d]}) {mems} (fun m hB => ?_)\n  try dsimp only\n"
src=open('tools/ecp-k.template').read()
src=src.replace("STEPS\n",body).replace("C1(P)",c1("P")).replace("C2(P)",c2("P")).replace("C1(O)",c1("O")).replace("C2(O)",c2("O")).replace("EZ",EZ)
open('submission/InitECandidate/Solver/GuestBound/EcpK.lean','w').write(src)
