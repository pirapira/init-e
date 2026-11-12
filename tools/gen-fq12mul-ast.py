#!/usr/bin/env python3
"""Regenerate GuestBound/Fq12MulAst.lean: the inner loop of fq12_mul, cut out of Guest/SoftwareAst.lean. Run from the repository root."""
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
b=flat(body('fq12_mul'))
inner=bal(b,b.index('(Prog.while (Exp.cmp Cmp.notLower (Exp.var VarKind.local "iend")'))
out='''import InitECandidate.Solver.GuestBound.Fq12Reduce

/-! The inner loop of `fq12_mul`, cut out of `Guest/SoftwareAst.lean` by `tools/gen-fq12mul-ast.py`. -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

notation "FQM_INNER" => (%s : Prog Word)

end InitECandidate.Solver.GuestBound
''' % inner
open('submission/InitECandidate/Solver/GuestBound/Fq12MulAst.lean','w').write(out)
