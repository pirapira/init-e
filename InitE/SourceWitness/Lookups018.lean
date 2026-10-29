import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_tx_has_access_list :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 104#8, 97#8, 115#8, 95#8, 97#8, 99#8, 99#8, 101#8, 115#8, 115#8, 95#8, 108#8, 105#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_has_access_list) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_blob_count :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 98#8, 108#8, 111#8, 98#8, 95#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_blob_count) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_calculate_total_blob_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 97#8, 108#8, 99#8, 117#8, 108#8, 97#8, 116#8, 101#8, 95#8, 116#8, 111#8, 116#8, 97#8, 108#8, 95#8, 98#8, 108#8, 111#8, 98#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_calculate_total_blob_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_put_u256 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 112#8, 117#8, 116#8, 95#8, 117#8, 50#8, 53#8, 54#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_put_u256) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_u256_encoded_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 117#8, 50#8, 53#8, 54#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 100#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_u256_encoded_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_put_to :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 112#8, 117#8, 116#8, 95#8, 116#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_put_to) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_access_list_payload_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 101#8, 115#8, 115#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 112#8, 97#8, 121#8, 108#8, 111#8, 97#8, 100#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_access_list_payload_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_put_access_list :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 112#8, 117#8, 116#8, 95#8, 97#8, 99#8, 99#8, 101#8, 115#8, 115#8, 95#8, 108#8, 105#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_put_access_list) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_put_blob_hashes :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 112#8, 117#8, 116#8, 95#8, 98#8, 108#8, 111#8, 98#8, 95#8, 104#8, 97#8, 115#8, 104#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_put_blob_hashes) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_auth_payload_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 117#8, 116#8, 104#8, 95#8, 112#8, 97#8, 121#8, 108#8, 111#8, 97#8, 100#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_auth_payload_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_auth_list_payload_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 117#8, 116#8, 104#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 112#8, 97#8, 121#8, 108#8, 111#8, 97#8, 100#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_auth_list_payload_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_put_authorizations :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 112#8, 117#8, 116#8, 95#8, 97#8, 117#8, 116#8, 104#8, 111#8, 114#8, 105#8, 122#8, 97#8, 116#8, 105#8, 111#8, 110#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_put_authorizations) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_encode_bound :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 98#8, 111#8, 117#8, 110#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_encode_bound) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_encode_generic :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 103#8, 101#8, 110#8, 101#8, 114#8, 105#8, 99#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_encode_generic) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_encode_transaction :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_encode_transaction) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_transaction_hash :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8, 95#8, 104#8, 97#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_transaction_hash) := by
  rfl

end InitE.SourceWitness
