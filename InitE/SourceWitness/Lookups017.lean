import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_tx_bytes_item :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8, 95#8, 105#8, 116#8, 101#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_bytes_item) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_fixed_bytes :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 102#8, 105#8, 120#8, 101#8, 100#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_fixed_bytes) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_to_item :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 116#8, 111#8, 95#8, 105#8, 116#8, 101#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_to_item) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_list_item :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 105#8, 116#8, 101#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_list_item) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_decode_access_list :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 97#8, 99#8, 99#8, 101#8, 115#8, 115#8, 95#8, 108#8, 105#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_decode_access_list) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_decode_blob_hashes :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 98#8, 108#8, 111#8, 98#8, 95#8, 104#8, 97#8, 115#8, 104#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_decode_blob_hashes) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_decode_authorizations :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 97#8, 117#8, 116#8, 104#8, 111#8, 114#8, 105#8, 122#8, 97#8, 116#8, 105#8, 111#8, 110#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_decode_authorizations) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_decode_transaction_rlp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8, 95#8, 114#8, 108#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_decode_transaction_rlp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_decode_transaction :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_decode_transaction) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_nonce :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 110#8, 111#8, 110#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_nonce) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_to :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 116#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_to) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_value :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 118#8, 97#8, 108#8, 117#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_value) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_data :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 100#8, 97#8, 116#8, 97#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_data) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_r :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_r) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_s :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_s) := by
  rfl

end InitE.SourceWitness
