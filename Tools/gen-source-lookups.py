#!/usr/bin/env python3
"""Propose literal source-code lookups; every result is certified by Lean."""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[1]
text = (root / 'Guest/SoftwareAst.lean').read_text()
functions = re.findall(r'def (guestFn_\w+) : Decl \(BitVec 64\) :=\s+Decl.function\s+\{ name := "([^"]+)"',text)
folder = root / 'InitE/SourceWitness'
for index,start in enumerate(range(0,len(functions),16)):
    body = '''import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang
'''
    for alias,name in functions[start:start+16]:
        literal = 'Basis.Pure.MlString.MlString.implode [' + ', '.join(f'{ord(c)}#8' for c in name) + ']'
        body += f'''
@[scoped cbv_eval] theorem code_{alias} :
    code0890.lookup ({literal}) = literalEntry (declToHOL Guest.Software.{alias}) := by
  rfl
'''
    body += '\nend InitE.SourceWitness\n'
    (folder / f'Lookups{index:03d}.lean').write_text(body)
count = (len(functions)+15)//16
body = '\n'.join(f'import InitE.SourceWitness.Lookups{i:03d}' for i in range(count))
body += '''
namespace InitE.SourceWitness
attribute [scoped cbv_opaque] code0890
end InitE.SourceWitness
'''
(folder / 'Lookups.lean').write_text(body)
print(f'Proposed {len(functions)} code lookups in {count} modules')


# Compact the two small tables without traversing function bodies during runs.
names = re.findall(r'guest\w+', text[text.index('def guestAst'):])[1:]
body = "import InitE.SourceWitness.InitializationTerms\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace InitE.SourceWitness\nopen Flapjack Flapjack.Pancake.PanLang\n"
for label,typ,prefix,install,target in [
    ('compactGlobals','GlobalTable','guestGlobal_','installGlobal','globals0890'),
    ('compactExceptions','ExceptionTable','guestExn_','installException','exceptions0890')]:
    expr = 'HolFiniteMapExact.empty'
    for name in names:
        if name.startswith(prefix):
            expr = f'{install} (declToHOL Guest.Software.{name}) ({expr})'
    body += f'def {label} : {typ} :=\n  {expr}\n\n@[scoped cbv_eval] theorem expose_{label} : {target} = {label} := by rfl\n\n'
body += 'end InitE.SourceWitness\n'
(folder / 'CompactTables.lean').write_text(body)
