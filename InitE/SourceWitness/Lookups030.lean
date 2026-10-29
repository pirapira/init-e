import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_op_log :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 108#8, 111#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_log) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_is_warm_storage_key :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 115#8, 95#8, 119#8, 97#8, 114#8, 109#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 107#8, 101#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_is_warm_storage_key) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_warm_storage_key :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 97#8, 114#8, 109#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 107#8, 101#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_warm_storage_key) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_sload :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 108#8, 111#8, 97#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_sload) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_sstore :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 115#8, 116#8, 111#8, 114#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_sstore) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_tload :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 116#8, 108#8, 111#8, 97#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_tload) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_tstore :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 116#8, 115#8, 116#8, 111#8, 114#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_tstore) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_address :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_address) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_balance :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 98#8, 97#8, 108#8, 97#8, 110#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_balance) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_origin :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 111#8, 114#8, 105#8, 103#8, 105#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_origin) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_caller :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 97#8, 108#8, 108#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_caller) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_callvalue :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 97#8, 108#8, 108#8, 118#8, 97#8, 108#8, 117#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_callvalue) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_calldataload :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 97#8, 108#8, 108#8, 100#8, 97#8, 116#8, 97#8, 108#8, 111#8, 97#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_calldataload) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_calldatasize :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 97#8, 108#8, 108#8, 100#8, 97#8, 116#8, 97#8, 115#8, 105#8, 122#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_calldatasize) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_copy_from_buffer :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 111#8, 112#8, 121#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 98#8, 117#8, 102#8, 102#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_copy_from_buffer) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_calldatacopy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 97#8, 108#8, 108#8, 100#8, 97#8, 116#8, 97#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_calldatacopy) := by
  rfl

end InitE.SourceWitness
