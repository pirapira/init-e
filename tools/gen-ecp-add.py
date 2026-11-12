#!/usr/bin/env python3
"""Regenerate GuestBound/EcpAdd.lean (the step lists of ecp_add). Run from the repository root."""
val={"U1":"hp","U2":"q1","V1":"q2","V2":"q3","U":"q4","V":"q5","Vsq":"q6","VsqV2":"q7","Vcu":"q8","W":"q9","A":"q10","T":"q11",
     "x1":"P1","y1":"P1 + 384#64","z1":"P1 + 768#64","x2":"P2","y2":"P2 + 384#64","z2":"P2 + 768#64"}
order=["U1","U2","V1","V2","U","V","Vsq","VsqV2","Vcu","W","A","T"]
low={n:f"(Or.inl l{i})" for i,n in enumerate(order)}
MEM="(by simp [m1a, m1b, m1c, m2a, m2b, m2c])"
def step(op,d,args,L,hg,ind="  "):
    evs=" ".join(f"(by lk [{L}_{a}])" for a in args)
    extra=" (eval_const _ _)" if op=="mul_small" else ""
    g=f" {hg}" if op in("mul","sqr") else ""
    mems=" ".join(MEM for _ in args)
    names=f"(A := {val[args[0]]})"+(f" (B := {val[args[1]]})" if len(args)>1 else "")
    return f"{ind}refine WPs.fe_{op}_step hE (D := {val[d]}) {names} (by lk [{L}_fld]) (by lk [{L}_{d}]) {evs}{extra}{g} hB\n{ind}  (by simp) {low[d]} {mems} (fun m hB => ?_)\n{ind}try dsimp only\n"
S1=[("mul","U1",["y2","z1"]),("mul","U2",["y1","z2"]),("mul","V1",["x2","z1"]),("mul","V2",["x1","z2"])]
S2=[("sub","U",["U1","U2"]),("sub","V",["V1","V2"]),("sqr","Vsq",["V"]),("mul","VsqV2",["Vsq","V2"]),("mul","Vcu",["V","Vsq"]),("mul","W",["z1","z2"]),("sqr","A",["U"]),("mul","A",["A","W"]),("sub","A",["A","Vcu"]),("mul_small","T",["VsqV2"]),("sub","A",["A","T"]),("mul","T",["V","A"]),("sub","V",["VsqV2","A"]),("mul","V",["U","V"]),("mul","U1",["Vcu","U2"]),("sub","V",["V","U1"]),("mul","W",["Vcu","W"])]
n1=["fld","out","p1","p2","mark","x1","y1","z1","x2","y2","z2","U1","U2","V1","V2"]
n2=n1+["U","V","Vsq","VsqV2","Vcu","W","A","T"]
lv=dict(val); lv.update({"fld":"12#64","out":"O","p1":"P1","p2":"P2","mark":"hp"})
base="hfld, hout, hp1, hp2"
def lookups(L,hL,names,using,ind="  "):
    return "".join(f"{ind}have {L}_{n} : {L} \"{n}\" = some (.word ({lv[n]})) := by rw [← {hL}]; lk [{using}]\n" for n in names)
src=open('tools/ecp-add.template').read()
src=src.replace("LOOKUPS_A\n",lookups("La","hLa",["fld","out","p1","p2"],base))
src=src.replace("LOOKUPS_B\n",lookups("Lb","hLb",["fld","out","p1","p2"],"La_fld, La_out, La_p1, La_p2"))
src=src.replace("LOOKUPS_1\n",lookups("L1","hL1",n1,"Lb_fld, Lb_out, Lb_p1, Lb_p2"))
src=src.replace("LOOKUPS_C\n",lookups("Lc","hLc",["fld","out","p1","p2"],"L1_fld, L1_out, L1_p1, L1_p2","      "))
src=src.replace("LOOKUPS_2\n",lookups("L2","hL2",n2,", ".join("L1_"+n for n in n1)))
src=src.replace("STEPS_1\n","".join(step(*s,"L1","hG1q") for s in S1))
src=src.replace("STEPS_2\n","".join(step(*s,"L2","hG2q") for s in S2))
open('submission/InitECandidate/Solver/GuestBound/EcpAdd.lean','w').write(src)
