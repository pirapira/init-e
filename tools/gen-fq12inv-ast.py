#!/usr/bin/env python3
"""Regenerate GuestBound/Fq12InvAst.lean: named pieces of the fq12_inv body, cut out of Guest/SoftwareAst.lean. Run from the repository root."""
import re,sys
src=open('Guest/SoftwareAst.lean').read()
def body(name):
    i=src.index('{ name := "%s"'%name)
    j=src.index('body :=',i)
    k=src.index('(',j)
    return bal(src,k)
def bal(s,k):
    d=0
    for q in range(k,len(s)):
        if s[q]=='(' : d+=1
        elif s[q]==')':
            d-=1
            if d==0: return s[k:q+1]
    raise Exception
def sub(s,marker,occ=0):
    idx=-1
    for _ in range(occ+1):
        idx=s.index(marker,idx+1)
    return bal(s,idx)
def flat(s): return re.sub(r'\s+',' ',s)
b=flat(body("fq12_inv"))
def fl(x): return flat(x)
inner=sub(b,'(Prog.while (Exp.cmp Cmp.notLess (Exp.var VarKind.local "d0")')
ig=sub(inner,'(Exp.cmp Cmp.notLess')
ib=sub(inner,'(Prog.dec "top"')
tail=sub(b,'(Prog.seq (Prog.call (some (none, none)) "memcpy" [(Exp.var VarKind.local "tmp")')
jw=sub(tail,'(Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "j")')
jb=sub(jw,'(Prog.dec "qj"')
swap=sub(tail,'(Prog.dec "t"')
ob=sub(b,'(Prog.decCall "d1"')
suffix=sub(b,'(Prog.decCall "dz"')
brk=sub(ob,'(Prog.ite (Exp.cmp Cmp.notLess (Exp.const')
mzq=sub(ob,'(Prog.call (some (none, none)) "memzero" [(Exp.var VarKind.local "q")')
rest=sub(b,'(Prog.seq (Prog.call (some (none, none)) "memzero" [(Exp.var VarKind.local "r0")')
out='''import InitECandidate.Solver.GuestBound.PolyCalls

/-! Parts of the body of `fq12_inv`, cut out of `Guest/SoftwareAst.lean` by a script. -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

'''
for name,val in [('FQI_IG',ig),('FQI_IB',ib),('FQI_TAIL',tail),('FQI_JB',jb),('FQI_SWAP',swap),('FQI_OB',ob),('FQI_SUFFIX',suffix),('FQI_BRK',brk),('FQI_MZQ',mzq),('FQI_REST',rest)]:
    ty = 'Exp Word' if name=='FQI_IG' else 'Prog Word'
    out+='notation "%s" => (%s : %s)\n\n'%(name,fl(val),ty)
out+='end InitECandidate.Solver.GuestBound\n'
open('submission/InitECandidate/Solver/GuestBound/Fq12InvAst.lean','w').write(out)
