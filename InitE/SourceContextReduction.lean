import InitE.SourceReduction

namespace InitE.SourceContextReduction
open Flapjack Flapjack.PanSemStateFiniteExact Lean Meta Sym Meta.Tactic.Cbv

set_option warn.classDefReducibility false in
def ordinaryDecider : DecidablePred arithmeticOrdinaryDomain := inferInstance
set_option warn.classDefReducibility false in
def sharedDecider : DecidablePred arithmeticSharedDomain := inferInstance

theorem replace_deciders {σ : Type} (state : PanSemStateFiniteExact 64 σ)
    (oldOrdinary newOrdinary : DecidablePred state.memaddrs)
    (oldShared newShared : DecidablePred state.shMemaddrs) :
    (⟨state, oldOrdinary, oldShared⟩ : FiniteEvalContext 64 σ) =
      ⟨state, newOrdinary, newShared⟩ := by
  have hm : oldOrdinary = newOrdinary := Subsingleton.elim _ _
  have hs : oldShared = newShared := Subsingleton.elim _ _
  subst hm
  subst hs
  rfl

scoped cbv_simproc ↓ holdOrdinary (ordinaryDecider) :=
  fun e => return .rfl (done := e.getAppNumArgs == 0)
scoped cbv_simproc ↓ holdShared (sharedDecider) :=
  fun e => return .rfl (done := e.getAppNumArgs == 0)

/- Replace accumulated transports once state fields have been normalized. -/
scoped cbv_simproc cbv_eval compactContext
    (@FiniteEvalContext.mk _ _ _ _ _ _) := fun e => do
  let args := e.getAppArgs
  let width := args[0]!
  let state := args[3]!
  let oldOrdinary := args[4]!
  let oldShared := args[5]!
  unless (← isDefEq width (mkNatLit 64)) do return .rfl
  let ordinary := mkConst ``ordinaryDecider
  let shared := mkConst ``sharedDecider
  if oldOrdinary == ordinary && oldShared == shared then return .rfl
  unless (← isDefEq (← Meta.inferType ordinary) (← Meta.inferType oldOrdinary)) do
    return .rfl
  unless (← isDefEq (← Meta.inferType shared) (← Meta.inferType oldShared)) do
    return .rfl
  let result := mkAppN e.getAppFn #[width, args[1]!, args[2]!, state, ordinary, shared]
  let proof ← mkAppM ``replace_deciders #[state, oldOrdinary, ordinary, oldShared, shared]
  return .step (← Sym.shareCommon result) proof

end InitE.SourceContextReduction
