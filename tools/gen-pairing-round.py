#!/usr/bin/env python3
"""Regenerate GuestBound/PairingRound.lean from tools/pairing-round.template. Run from the repository root."""
g1b="g1 + 1#64 * 32#64"; g1c="g1 + 2#64 * (1#64 * 32#64)"; t1b="t1 + 1#64 * 32#64"; t1c="t1 + 2#64 * (1#64 * 32#64)"
g2b="g2 + 2#64 * 32#64"; g2c="g2 + 2#64 * (2#64 * 32#64)"; t2b="t2 + 2#64 * 32#64"; t2c="t2 + 2#64 * (2#64 * 32#64)"
Q1="Qb + 384#64"; Q2="Qb + 768#64"; P1="Pb + 384#64"; P2="Pb + 768#64"
ALL1=f"[{t1c}, {t1b}, t1, {g1c}, {g1b}, g1]"
ALL2=f"[{t2c}, {t2b}, t2, {g2c}, {g2b}, g2]"
ALL12=f"[res, aden, anum, fden, fnum, {P2}, {P1}, Pb, {Q2}, {Q1}, Qb]"
G1C=f"[{g1c}, {g1b}, g1]"; G2C=f"[{g2c}, {g2b}, g2]"
names=["g1","g2","t1","t2","Q","P","fnum","fden","anum","aden","mark"]
lv={"g1":"g1","g2":"g2","t1":"t1","t2":"t2","Q":"Qb","P":"Pb","fnum":"fnum","fden":"fden","anum":"anum","aden":"aden","mark":"mk"}
def lookups(L,hL,prev,ind="  "):
    out=""
    for n in names:
        out+=f"{ind}have {L}_{n} : {L} \"{n}\" = some (.word {lv[n]}) := by rw [← {hL}]; lk [{prev}_{n}]\n"
    out+=f"{ind}have {L}_i : {L} \"i\" = some (.word iw) := by rw [← {hL}]; lk [{prev}_i]\n"
    out+=f"{ind}have {L}_nt : {L} \"nontrivial\" = some (.word nw) := by rw [← {hL}]; lk [{prev}_nt]\n"
    return out
def retpath(ind):
    return (f"{ind}refine WPs.seq_call_ret (fun vs g m' ffi hret => ?_)\n"
            f"{ind}refine WPs.ret (w := 2#64) (of_eval (eval_const _ _)) ?_\n"
            f"{ind}simp only [restorePanValueFfiLocal]\n")
src=open('tools/pairing-round.template').read()
src=src.replace("LOOKUPS1\n",lookups("L1","hL1","l")).replace("LOOKUPS2\n",lookups("L2","hL2","L1")).replace("LOOKUPS3\n",lookups("L3","hL3","L2")).replace("LOOKUPS4\n",lookups("L4","hL4","L3")).replace("LOOKUPS5\n",lookups("L5","hL5","L4"))
src=src.replace("RETPATH6\n",retpath("      ")).replace("RETPATH4\n",retpath("    "))
for k,v in [("ALL12",ALL12),("ALL1",ALL1),("ALL2",ALL2),("G1CC",g1c),("G1C",G1C),("G2CC",g2c),("G2C",G2C),("G1B",g1b),("T1B",t1b),("T1CC",t1c),("G2B",g2b),("T2B",t2b),("T2CC",t2c),("QQ1",Q1),("QQ2",Q2),("PP1",P1),("PP2",P2),
            ("BNR",".rStruct [.word 4891460686036598785#64, .word 2896914383306846353#64, .word 13281191951274694749#64, .word 3486998266802970665#64]")]:
    src=src.replace(k,v)
open('submission/InitECandidate/Solver/GuestBound/PairingRound.lean','w').write(src)
