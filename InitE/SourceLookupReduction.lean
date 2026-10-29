import InitE.SourceWitness.LookupBase

namespace InitE.SourceLookupReduction
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def finiteEntry (entry : Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (arguments : List (ValueHOL 64)) :=
  match entry with
  | none => none
  | some (parameters, body, returnShape) =>
    if (parameters.map Prod.fst).Nodup ∧ parameters.length = arguments.length ∧
        ((parameters.zip arguments).all
          (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true then
      some (body,
        HolFiniteMapExact.updateListEq HolFiniteMapExact.empty
          ((parameters.map Prod.fst).zip arguments), returnShape)
    else none

theorem forget_injective : Function.Injective
    (fun (entry : Option (ProgHOL 64 × HolFiniteMapExact MlS (ValueHOL 64) × ShapeHOL)) =>
      entry.map (fun (body, locals, shape) => (body, locals.lookup, shape))) := by
  intro a b equal
  cases a with
  | none => cases b <;> simp_all
  | some a =>
    rcases a with ⟨body, locals, shape⟩
    cases b with
    | none => simp at equal
    | some b =>
      rcases b with ⟨body', locals', shape'⟩
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at equal
      rcases equal with ⟨rfl, hlocals, rfl⟩
      rw [HolFiniteMapExact.ext hlocals]

@[scoped cbv_eval] theorem finite_lookup
    (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name : MlS) (arguments : List (ValueHOL 64)) :
    lookupCodeHOLFinite code name arguments = finiteEntry (code name) arguments := by
  apply forget_injective
  have projection :
      (lookupCodeHOLFinite code name arguments).map
        (fun (body, locals, shape) => (body, locals.lookup, shape)) =
      lookupCodeHOLExact code name arguments := by
    unfold lookupCodeHOLFinite
    split <;> simp_all
  dsimp only
  rw [projection]
  unfold lookupCodeHOLExact finiteEntry
  cases code name with
  | none => rfl
  | some entry =>
    rcases entry with ⟨parameters, body, returnShape⟩
    dsimp only
    split <;> rfl

end InitE.SourceLookupReduction
