import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_pre_blake2f :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 97#8, 107#8, 101#8, 50#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_blake2f) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_modexp_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 111#8, 100#8, 101#8, 120#8, 112#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_modexp_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_modexp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 109#8, 111#8, 100#8, 101#8, 120#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_modexp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_run_precompile :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 117#8, 110#8, 95#8, 112#8, 114#8, 101#8, 99#8, 111#8, 109#8, 112#8, 105#8, 108#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_run_precompile) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_add_to_bloom :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 95#8, 116#8, 111#8, 95#8, 98#8, 108#8, 111#8, 111#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_add_to_bloom) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_logs_bloom :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 111#8, 103#8, 115#8, 95#8, 98#8, 108#8, 111#8, 111#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_logs_bloom) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_finish_list :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 102#8, 105#8, 110#8, 105#8, 115#8, 104#8, 95#8, 108#8, 105#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_finish_list) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_logs_encoded_bound :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 111#8, 103#8, 115#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 100#8, 95#8, 98#8, 111#8, 117#8, 110#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_logs_encoded_bound) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_encode_logs :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 108#8, 111#8, 103#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_encode_logs) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_encode_receipt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 114#8, 101#8, 99#8, 101#8, 105#8, 112#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_encode_receipt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_withdrawal_rlp_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 105#8, 116#8, 104#8, 100#8, 114#8, 97#8, 119#8, 97#8, 108#8, 95#8, 114#8, 108#8, 112#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_withdrawal_rlp_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_encode_withdrawal_rlp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 119#8, 105#8, 116#8, 104#8, 100#8, 114#8, 97#8, 119#8, 97#8, 108#8, 95#8, 114#8, 108#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_encode_withdrawal_rlp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_encode_execution_requests :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 101#8, 120#8, 101#8, 99#8, 117#8, 116#8, 105#8, 111#8, 110#8, 95#8, 114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_encode_execution_requests) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_compute_requests_hash :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 111#8, 109#8, 112#8, 117#8, 116#8, 101#8, 95#8, 114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8, 115#8, 95#8, 104#8, 97#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_compute_requests_hash) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_extract_deposit_data :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 120#8, 116#8, 114#8, 97#8, 99#8, 116#8, 95#8, 100#8, 101#8, 112#8, 111#8, 115#8, 105#8, 116#8, 95#8, 100#8, 97#8, 116#8, 97#8]) = literalEntry (declToHOL Guest.Software.guestFn_extract_deposit_data) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_cache_get_root :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 97#8, 99#8, 104#8, 101#8, 95#8, 103#8, 101#8, 116#8, 95#8, 114#8, 111#8, 111#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_cache_get_root) := by
  rfl

end InitE.SourceWitness
