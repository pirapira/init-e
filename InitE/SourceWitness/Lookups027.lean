import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_op_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_sub :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 117#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_sub) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_div :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 100#8, 105#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_div) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_sdiv :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 100#8, 105#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_sdiv) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_mod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_mod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_smod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_smod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_addmod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 97#8, 100#8, 100#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_addmod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_mulmod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 117#8, 108#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_mulmod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_exp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 101#8, 120#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_exp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_signextend :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 105#8, 103#8, 110#8, 101#8, 120#8, 116#8, 101#8, 110#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_signextend) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_lt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 108#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_lt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_gt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 103#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_gt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_slt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 108#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_slt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_sgt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 103#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_sgt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_eq :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 101#8, 113#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_eq) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_iszero :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 105#8, 115#8, 122#8, 101#8, 114#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_iszero) := by
  rfl

end InitE.SourceWitness
