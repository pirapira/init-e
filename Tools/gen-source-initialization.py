#!/usr/bin/env python3
"""Propose small exact-source initialization certificates; Lean checks each chunk."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
source = (root / 'Guest/SoftwareAst.lean').read_text()
names = re.findall(r'guest\w+', source[source.index('def guestAst'):])[1:]
folder = root / 'InitE/SourceWitness'
folder.mkdir(exist_ok=True)
chunk_size = 16
count = (len(names)+chunk_size-1)//chunk_size
header = '''import InitE.SourceReduction
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
'''
base = header + '''
abbrev CodeTable := HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)
abbrev GlobalTable := HolFiniteMapExact MlS (ValueHOL 64)
abbrev ExceptionTable := HolFiniteMapExact MlS ShapeHOL

/-- Proposed installation; per-chunk certificates check the original interpreter. -/
def installCode (d : DeclHOL 64) (code : CodeTable) : CodeTable :=
  match d with
  | .function fn => code.update (fn.name, fn.params, fn.body, fn.returnShape)
  | _ => code

def installGlobal (d : DeclHOL 64) (globals : GlobalTable) : GlobalTable :=
  match d with
  | .decl _ name _ => globals.update (name, .val (.word 0))
  | _ => globals

def installException (d : DeclHOL 64) (exceptions : ExceptionTable) : ExceptionTable :=
  match d with
  | .exnDecl name shape => exceptions.update (name, shape)
  | _ => exceptions

def code0000 : CodeTable := HolFiniteMapExact.empty
def globals0000 : GlobalTable := HolFiniteMapExact.empty
def exceptions0000 : ExceptionTable := HolFiniteMapExact.empty

def state0000 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0000
    code := code0000
    eshapes := exceptions0000
    structs := [] }

end InitE.SourceWitness
'''
(folder / 'InitializationBase.lean').write_text(base)
for index, start in enumerate(range(0,len(names),chunk_size)):
    end = min(start+chunk_size,len(names))
    previous = 'InitializationBase' if index == 0 else f'Terms{index-1:03d}'
    terms = header.replace('import InitE.SourceReduction', f'import InitE.SourceWitness.{previous}')
    for j in range(start,end):
        i, name = j+1, names[j]
        for table, typ, installer in [('code','CodeTable','installCode'),('globals','GlobalTable','installGlobal'),('exceptions','ExceptionTable','installException')]:
            terms += f'''def {table}{i:04d} : {typ} :=
  {installer} (declToHOL Guest.Software.{name}) {table}{j:04d}
'''
    terms += f'''
def state{end:04d} (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  {{ s with
    globals := globals{end:04d}
    code := code{end:04d}
    eshapes := exceptions{end:04d}
    structs := [] }}

end InitE.SourceWitness
'''
    (folder / f'Terms{index:03d}.lean').write_text(terms)
    chunk = ',\n    '.join('declToHOL Guest.Software.'+n for n in names[start:end])
    certificate = header.replace('import InitE.SourceReduction', f'import InitE.SourceWitness.Terms{index:03d}')
    certificate += f'''
attribute [local cbv_opaque] code{start:04d} globals{start:04d}

def chunk{index:03d} : List (DeclHOL 64) :=
  [{chunk}]

theorem chunk{index:03d}_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state{start:04d} s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk{index:03d} =
        some (state{end:04d} s) := by
  cbv

end InitE.SourceWitness
'''
    (folder / f'Init{index:03d}.lean').write_text(certificate)
(folder / 'InitializationTerms.lean').write_text(f'import InitE.SourceWitness.Terms{count-1:03d}\n')
assembly = '\n'.join(f'import InitE.SourceWitness.Init{i:03d}' for i in range(count)) + '\n'
assembly += header[header.index('set_option'):]
assembly += f'''
def suffix{count:03d} : List (DeclHOL 64) := []
theorem suffix{count:03d}_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state{len(names):04d} s)
      (inferInstanceAs (DecidablePred s.memaddrs)) suffix{count:03d} =
        some (state{len(names):04d} s) := by rfl

'''
for index in reversed(range(count)):
    start,end = index*chunk_size,min((index+1)*chunk_size,len(names))
    assembly += f'''def suffix{index:03d} : List (DeclHOL 64) := chunk{index:03d} ++ suffix{index+1:03d}
theorem suffix{index:03d}_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state{start:04d} s)
      (inferInstanceAs (DecidablePred s.memaddrs)) suffix{index:03d} =
        some (state{len(names):04d} s) := by
  exact source_declarations_append chunk{index:03d} suffix{index+1:03d}
    (state{start:04d} s) (state{end:04d} s) (state{len(names):04d} s)
    (inferInstanceAs (DecidablePred s.memaddrs)) (inferInstanceAs (DecidablePred s.memaddrs))
    (chunk{index:03d}_run s) (suffix{index+1:03d}_run s)

'''
assembly += '''theorem source_declarations_eq_suffix :
    Guest.Software.guestAst.map declToHOL = suffix000 := by rfl

theorem source_structures_empty :
    decsStcnamesHOLExact [] (Guest.Software.guestAst.map declToHOL) = some [] := by rfl

end InitE.SourceWitness
'''
(folder / 'Initialization.lean').write_text(assembly)
print(f'Proposed {len(names)} declarations in {count} chunks')
