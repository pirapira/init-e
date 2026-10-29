import InitE.SourceWitness.InitializationTerms

namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

def literalEntry (declaration : DeclHOL 64) :
    Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  match declaration with
  | .function fn => some (fn.params, fn.body, fn.returnShape)
  | _ => none

end InitE.SourceWitness
