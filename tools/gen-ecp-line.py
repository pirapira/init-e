#!/usr/bin/env python3
"""Regenerate GuestBound/EcpLine.lean (the step lists of ecp_linefunc). Run from the repository root."""
val={"mn":"hp","md":"q1","t1":"q2","t2":"q3","num":"N","den":"Dn",
     "x1":"P1","y1":"P1 + 384#64","z1":"P1 + 768#64","x2":"P2","y2":"P2 + 384#64","z2":"P2 + 768#64",
     "xt":"T","yt":"T + 384#64","zt":"T + 768#64"}
low={"mn":"(Or.inl l0)","md":"(Or.inl l1)","t1":"(Or.inl l2)","t2":"(Or.inl l3)","num":"wN","den":"wD"}
MEM="(by simp [m1a, m1b, m1c, m2a, m2b, m2c, mta, mtb, mtc])"
DMEM="(by simp [hN, hD])"
def step(op,d,args,ind="  "):
    if op=="set_zero":
        return f"{ind}refine WPs.fe_set_zero_step hE (D := {val[d]}) (by lk [Lfld]) (by lk [L{d}]) hB\n{ind}  {DMEM} {low[d]} (fun m hB => ?_)\n{ind}try dsimp only\n"
    evs=" ".join(f"(by lk [L{a}])" for a in args)
    extra=" (eval_const _ _)" if op=="mul_small" else ""
    hg=" hGq" if op in("mul","sqr") else ""
    mems=" ".join(MEM for _ in args)
    names=f"(A := {val[args[0]]})"+(f" (B := {val[args[1]]})" if len(args)>1 else "")
    return f"{ind}refine WPs.fe_{op}_step hE (D := {val[d]}) {names} (by lk [Lfld]) (by lk [L{d}]) {evs}{extra}{hg} hB\n{ind}  {DMEM} {low[d]} {mems} (fun m hB => ?_)\n{ind}try dsimp only\n"
def block(steps,ind,last_skip):
    out=""
    for i,(op,d,args) in enumerate(steps):
        if last_skip and i==len(steps)-1:
            out+=f"{ind}refine WPs.of_seq_skip ?_\n"
        out+=step(op,d,args,ind)
    return out
MONO="(fun B hB' => by\n{ind}  simp only [List.mem_cons] at hB'\n{ind}  rcases hB' with rfl | rfl | hB' <;> simp [*])"
def fin(ind):
    return f"""{ind}refine WPs.seq_call_ret (fun vs g m4 ffi hret => ?_)
{ind}obtain ⟨hg', hm, hf⟩ := release_ret hE hret (mv := hp) (pv := q4) (by lk [Lmark]) hGq
{ind}subst g m4 ffi
{ind}refine WPs.ret (of_eval (eval_const _ _)) ?_
{ind}simp only [restorePanValueFfiLocal, ← hG, hp_update_update]
{ind}rw [update_same _ _ _ hg]
{ind}refine ⟨_, m, rfl, Bufs.restrict hB0 hB (fun B hB' => ?_)⟩
{ind}simp only [List.mem_cons] at hB'
{ind}rcases hB' with rfl | rfl | hB'
{ind}· exact ⟨hN, by simp⟩
{ind}· exact ⟨hD, by simp⟩
{ind}· exact ⟨hB0.sub B hB', by simp [hB']⟩
"""
A_else=[("mul","mn",["y2","z1"]),("mul","t1",["y1","z2"]),("sub","mn",["mn","t1"]),("mul","md",["x2","z1"]),("mul","t1",["x1","z2"]),("sub","md",["md","t1"])]
A_then=[("set_zero","mn",[]),("set_zero","md",[])]
B_tt=[("sqr","t1",["x1"]),("mul_small","mn",["t1"]),("mul","md",["y1","z1"]),("mul_small","md",["md"])]
B_ret=[("mul","num",["xt","z1"]),("mul","t1",["x1","zt"]),("sub","num",["num","t1"]),("mul","den",["z1","zt"])]
C=[("mul","t1",["xt","z1"]),("mul","t2",["x1","zt"]),("sub","t1",["t1","t2"]),("mul","t1",["mn","t1"]),("mul","t2",["yt","z1"]),("mul","num",["y1","zt"]),("sub","t2",["t2","num"]),("mul","t2",["md","t2"]),("sub","num",["t1","t2"]),("mul","den",["md","zt"]),("mul","den",["den","z1"])]
names=["fld","mark","num","den","mn","md","t1","t2","x1","y1","z1","x2","y2","z2","xt","yt","zt"]
lv=dict(val); lv["fld"]="12#64"; lv["mark"]="hp"
lookups="".join(f"  have L{n} : L \"{n}\" = some (.word ({lv[n]})) := by rw [← hL]; lk [hfld, hnum, hden]\n" for n in names)
src=open('tools/ecp-line.template').read()
src=src.replace("LOOKUPS\n",lookups)
src=src.replace("A_ELSE\n",block(A_else,"      ",True)).replace("A_THEN\n",block(A_then,"      ",True))
src=src.replace("B_TT\n",block(B_tt,"        ",True)).replace("B_RET\n",block(B_ret,"        ",False)+fin("        "))
src=src.replace("C_STEPS\n",block(C,"  ",False)+fin("  "))
for ind in ["      ","        "]:
    pass
src=src.replace("MONO6",MONO.replace("{ind}","      ")).replace("MONO8",MONO.replace("{ind}","        "))
open('submission/InitECandidate/Solver/GuestBound/EcpLine.lean','w').write(src)
