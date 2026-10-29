import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_op_timestamp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 116#8, 105#8, 109#8, 101#8, 115#8, 116#8, 97#8, 109#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_timestamp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_number :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 110#8, 117#8, 109#8, 98#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_number) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_gaslimit :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 103#8, 97#8, 115#8, 108#8, 105#8, 109#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_gaslimit) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_chainid :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 104#8, 97#8, 105#8, 110#8, 105#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_chainid) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_prevrandao :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 112#8, 114#8, 101#8, 118#8, 114#8, 97#8, 110#8, 100#8, 97#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_prevrandao) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_slotnum :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 108#8, 111#8, 116#8, 110#8, 117#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_slotnum) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_evm_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 118#8, 109#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_evm_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_emit_transfer_log :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 109#8, 105#8, 116#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 102#8, 101#8, 114#8, 95#8, 108#8, 111#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_emit_transfer_log) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_return :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 114#8, 101#8, 116#8, 117#8, 114#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_return) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_revert :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 114#8, 101#8, 118#8, 101#8, 114#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_revert) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_selfdestruct :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 101#8, 108#8, 102#8, 100#8, 101#8, 115#8, 116#8, 114#8, 117#8, 99#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_selfdestruct) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_delegated_code_address :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 100#8, 101#8, 108#8, 101#8, 103#8, 97#8, 116#8, 101#8, 100#8, 95#8, 99#8, 111#8, 100#8, 101#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_delegated_code_address) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_recover_authority :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8, 95#8, 97#8, 117#8, 116#8, 104#8, 111#8, 114#8, 105#8, 116#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_recover_authority) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_calculate_delegation_cost :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 97#8, 108#8, 99#8, 117#8, 108#8, 97#8, 116#8, 101#8, 95#8, 100#8, 101#8, 108#8, 101#8, 103#8, 97#8, 116#8, 105#8, 111#8, 110#8, 95#8, 99#8, 111#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_calculate_delegation_cost) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_validate_authorization_checks :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 97#8, 117#8, 116#8, 104#8, 111#8, 114#8, 105#8, 122#8, 97#8, 116#8, 105#8, 111#8, 110#8, 95#8, 99#8, 104#8, 101#8, 99#8, 107#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_validate_authorization_checks) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_set_delegation :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 116#8, 95#8, 100#8, 101#8, 108#8, 101#8, 103#8, 97#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_set_delegation) := by
  rfl

end InitE.SourceWitness
