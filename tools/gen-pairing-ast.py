#!/usr/bin/env python3
"""Regenerate GuestBound/PairingAst.lean: named pieces of bn254_pairing_check, cut out of Guest/SoftwareAst.lean. Run from the repository root."""
import re
src=open('Guest/SoftwareAst.lean').read()
def bal(s,k):
    d=0
    for q in range(k,len(s)):
        if s[q]=='(' : d+=1
        elif s[q]==')':
            d-=1
            if d==0: return s[k:q+1]
    raise Exception
def body(name):
    i=src.index('{ name := "%s"'%name)
    j=src.index('body :=',i)
    return bal(src,src.index('(',j))
def flat(s): return re.sub(r'\s+',' ',s)
b=flat(body('bn254_pairing_check'))
loop=bal(b,b.index('(Prog.while (Exp.cmp Cmp.lower (Exp.var VarKind.local "i") (Exp.var VarKind.local "n_pairs"))'))
guard=bal(loop,loop.index('(Exp.cmp Cmp.lower'))
lbody=bal(loop,loop.index('(Prog.dec "chunk"'))
tail=bal(b,b.index('(Prog.seq (Prog.call (some (none, none)) "fq12_mul" [(Exp.var VarKind.local "anum"), (Exp.var VarKind.local "anum"), (Exp.var VarKind.local "aden")])'))
last=bal(b,b.index('(Prog.seq (Prog.call (some (none, none)) "heap_release" [(Exp.var VarKind.local "mark")]) (Prog.return (Exp.var VarKind.local "ok")))'))
out='''import InitECandidate.Solver.GuestBound.PairingSteps

/-! Parts of the body of `bn254_pairing_check`, cut out of `Guest/SoftwareAst.lean` by `tools/gen-pairing-ast.py`. -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

'''
for name,val,ty in [('PC_GUARD',guard,'Exp Word'),('PC_BODY',lbody,'Prog Word'),('PC_LOOP',loop,'Prog Word'),('PC_TAIL',tail,'Prog Word'),('PC_LAST',last,'Prog Word')]:
    out+='notation "%s" => (%s : %s)\n\n'%(name,val,ty)
out+='end InitECandidate.Solver.GuestBound\n'
open('submission/InitECandidate/Solver/GuestBound/PairingAst.lean','w').write(out)
