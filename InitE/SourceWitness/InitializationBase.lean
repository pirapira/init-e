import InitE.SourceReduction
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

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
