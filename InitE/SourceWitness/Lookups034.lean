import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_incorporate_child_on_success :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 110#8, 99#8, 111#8, 114#8, 112#8, 111#8, 114#8, 97#8, 116#8, 101#8, 95#8, 99#8, 104#8, 105#8, 108#8, 100#8, 95#8, 111#8, 110#8, 95#8, 115#8, 117#8, 99#8, 99#8, 101#8, 115#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_incorporate_child_on_success) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rollback_child_access :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 111#8, 108#8, 108#8, 98#8, 97#8, 99#8, 107#8, 95#8, 99#8, 104#8, 105#8, 108#8, 100#8, 95#8, 97#8, 99#8, 99#8, 101#8, 115#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_rollback_child_access) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_child_message :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 104#8, 105#8, 108#8, 100#8, 95#8, 109#8, 101#8, 115#8, 115#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_child_message) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_set_retdata :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 116#8, 95#8, 114#8, 101#8, 116#8, 100#8, 97#8, 116#8, 97#8]) = literalEntry (declToHOL Guest.Software.guestFn_set_retdata) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_compute_contract_address :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 111#8, 109#8, 112#8, 117#8, 116#8, 101#8, 95#8, 99#8, 111#8, 110#8, 116#8, 114#8, 97#8, 99#8, 116#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_compute_contract_address) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_compute_create2_contract_address :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 111#8, 109#8, 112#8, 117#8, 116#8, 101#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 50#8, 95#8, 99#8, 111#8, 110#8, 116#8, 114#8, 97#8, 99#8, 116#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_compute_create2_contract_address) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_generic_create :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 110#8, 101#8, 114#8, 105#8, 99#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_generic_create) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_create :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_create) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_create2 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_create2) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_generic_call :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 110#8, 101#8, 114#8, 105#8, 99#8, 95#8, 99#8, 97#8, 108#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_generic_call) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_calculate_message_call_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 97#8, 108#8, 99#8, 117#8, 108#8, 97#8, 116#8, 101#8, 95#8, 109#8, 101#8, 115#8, 115#8, 97#8, 103#8, 101#8, 95#8, 99#8, 97#8, 108#8, 108#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_calculate_message_call_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_call :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 97#8, 108#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_call) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_callcode :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 97#8, 108#8, 108#8, 99#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_callcode) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_delegatecall :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 100#8, 101#8, 108#8, 101#8, 103#8, 97#8, 116#8, 101#8, 99#8, 97#8, 108#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_delegatecall) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_staticcall :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 116#8, 97#8, 116#8, 105#8, 99#8, 99#8, 97#8, 108#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_staticcall) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_process_message_call :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 109#8, 101#8, 115#8, 115#8, 97#8, 103#8, 101#8, 95#8, 99#8, 97#8, 108#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_process_message_call) := by
  rfl

end InitE.SourceWitness
