#!/usr/bin/env python3
"""Regenerate GuestBound/Miller.lean (the step lists of bn254_miller_raw). Run from the repository root."""
MEM="(by simp [qa, qb, qc, pa, pb, pc, hFn, hFd])"
val={"R":"hp","nQ":"q1","Q1":"q2","nQ2":"q3","n":"q4","d":"q5","Q":"Qp","P":"Pp","fnum":"Fn","fden":"Fd"}
wr={"R":"(Or.inl l0)","nQ":"(Or.inl l1)","Q1":"(Or.inl l2)","nQ2":"(Or.inl l3)","n":"(Or.inl l4)","d":"(Or.inl l5)","fnum":"wFn","fden":"wFd"}
def w3(v):
    if v in("fnum","fden"): raise Exception
    return f"{wr[v]} (Or.inl (by omega)) (Or.inl (by omega))"
def pt3(L): return f"{MEM} {MEM} {MEM}"
def linefunc(L,p2,ind):
    return (f"{ind}refine WPs.ecp_linefunc_step hE (N := q4) (Dn := q5) (P1 := hp) (P2 := {val[p2]}) (T := Pp)\n"
            f"{ind}  (eval_const _ _) (by lk [{L}_n]) (by lk [{L}_d]) (by lk [{L}_R]) (by lk [{L}_{p2}]) (by lk [{L}_P]) hGq hB\n"
            f"{ind}  {MEM} {MEM} {MEM} {MEM} {MEM} {MEM} {MEM} {MEM} {MEM}\n"
            f"{ind}  (by simp) (by simp) (Or.inl l4) (Or.inl l5) (fun m hB => ?_)\n{ind}try dsimp only\n")
def mul(L,d,b,ind):
    return (f"{ind}refine WPs.fq12_mul_step hE (D := {val[d]}) (A := {val[d]}) (B := {val[b]}) (by lk [{L}_{d}]) (by lk [{L}_{d}])\n"
            f"{ind}  (by lk [{L}_{b}]) hGq hB {MEM} {wr[d]} {MEM} {MEM} (fun m hB => ?_)\n{ind}try dsimp only\n")
def sqr(L,d,ind):
    return (f"{ind}refine WPs.fq12_sqr_step hE (D := {val[d]}) (A := {val[d]}) (by lk [{L}_{d}]) (by lk [{L}_{d}])\n"
            f"{ind}  hGq hB {MEM} {wr[d]} {MEM} (fun m hB => ?_)\n{ind}try dsimp only\n")
def dbl(L,ind):
    return (f"{ind}refine WPs.ecp_double_step hE (O := hp) (P := hp) (eval_const _ _) (by lk [{L}_R]) (by lk [{L}_R]) hGq hB\n"
            f"{ind}  {MEM} {MEM} {MEM} {MEM} {MEM} {MEM} {w3('R')} (fun m hB => ?_)\n{ind}try dsimp only\n")
def add(L,p2,rel2,ind,last=False):
    pre=f"{ind}refine WPs.of_seq_skip ?_\n" if last else ""
    return (pre+f"{ind}refine WPs.ecp_add_step hE (O := hp) (P1 := hp) (P2 := {val[p2]}) (eval_const _ _) (by lk [{L}_R])\n"
            f"{ind}  (by lk [{L}_R]) (by lk [{L}_{p2}]) hGq hB {MEM} {MEM} {MEM} {MEM} {MEM} {MEM} {MEM} {MEM} {MEM}\n"
            f"{ind}  {w3('R')} (Or.inl rfl) {rel2} (fun m hB => ?_)\n{ind}try dsimp only\n")
def frob(L,d,a,off,ind):
    o={0:"",384:" + 384#64",768:" + 768#64"}[off]
    ev={0:"by lk [{L}_{v}]",384:"by ev [{L}_{v}]",768:"by ev [evalPanOp, {L}_{v}]"}[off]
    wd={0:wr[d],384:"(Or.inl (by omega))",768:"(Or.inl (by omega))"}[off]
    return (f"{ind}refine WPs.fq12_frob_step hE (D := {val[d]}{o}) (A := {val[a]}{o}) (Gt := Gt) ({ev.format(L=L,v=d)})\n"
            f"{ind}  ({ev.format(L=L,v=a)}) hgG hB {MEM} {wd} {MEM}\n"
            f"{ind}  (fun m hB => ?_)\n{ind}try dsimp only\n")
def neg(L,d,a,ind):
    return (f"{ind}refine WPs.fe_neg_step hE (D := {val[d]} + 384#64) (A := {val[a]} + 384#64) (eval_const _ _)\n"
            f"{ind}  (by ev [{L}_{d}]) (by ev [{L}_{a}]) hB {MEM} (Or.inl (by omega)) {MEM} (fun m hB => ?_)\n{ind}try dsimp only\n")
names=["fnum","fden","Q","P","mark","R","nQ","Q1","nQ2","n","d"]
lv=dict(val); lv["mark"]="hp"
def lookups(L,how,ind="  ",var=None):
    var=var or L
    return "".join(f"{ind}have {L}_{n} : {var} \"{n}\" = some (.word ({lv[n]})) := {how.format(n=n)}\n" for n in names)
body=(linefunc("Lc","R","    ")+sqr("Lc","fnum","    ")+mul("Lc","fnum","n","    ")+sqr("Lc","fden","    ")
      +mul("Lc","fden","d","    ")+dbl("Lc","    "))
br1=linefunc("Lc","Q","        ")+mul("Lc","fnum","n","        ")+mul("Lc","fden","d","        ")+add("Lc","Q","(Or.inr (Or.inr (by omega)))","        ",True)
br2=linefunc("Lc","nQ","      ")+mul("Lc","fnum","n","      ")+mul("Lc","fden","d","      ")+add("Lc","nQ","(Or.inr (Or.inl (by omega)))","      ",True)
tail=(frob("La","Q1","Q",0,"  ")+frob("La","Q1","Q",384,"  ")+frob("La","Q1","Q",768,"  ")
      +frob("La","nQ2","Q1",0,"  ")+frob("La","nQ2","Q1",384,"  ")+neg("La","nQ2","nQ2","  ")+frob("La","nQ2","Q1",768,"  ")
      +linefunc("La","Q1","  ")+mul("La","fnum","n","  ")+mul("La","fden","d","  ")+add("La","Q1","(Or.inr (Or.inl (by omega)))","  ")
      +linefunc("La","nQ2","  ")+mul("La","fnum","n","  ")+mul("La","fden","d","  "))
src=open('tools/miller.template').read()
src=src.replace("LOOKUPS_L\n",lookups("L","by rw [← hL]; lk [hfnum, hfden, hQ, hP]"))
src=src.replace("LOOKUPS_L2\n",lookups("L2","by rw [hL2]; lk [L_{n}]"))
src=src.replace("LOOKUPS_LC\n",lookups("Lc","by rw [← hLc]; lk [(hloc _ (by decide)).trans L2_{n}]","    "))
src=src.replace("LOOKUPS_LA\n",lookups("La","(hloc _ (by decide)).trans L2_{n}","  ","la"))
src=src.replace("BODY\n",body).replace("BR1\n",br1).replace("BR2\n",br2).replace("TAIL\n",tail)
ALLI="q5 :: q4 :: (q3 + 768#64) :: (q3 + 384#64) :: q3 :: (q2 + 768#64) :: (q2 + 384#64) :: q2 :: (q1 + 768#64) :: (q1 + 384#64) :: q1 :: (hp + 768#64) :: (hp + 384#64) :: hp :: All"
CNI="Fd :: Fn :: (q1 + 384#64) :: (q1 + 768#64) :: (q1 + 384#64) :: q1 :: (hp + 768#64) :: (hp + 384#64) :: hp :: Cn"
CNM="(hp + 768#64) :: (hp + 384#64) :: hp :: Fd :: Fd :: Fn :: Fn :: q4 :: q5 :: "+CNI
src=src.replace("ALLI",ALLI).replace("CNM",CNM)
open('submission/InitECandidate/Solver/GuestBound/Miller.lean','w').write(src)
