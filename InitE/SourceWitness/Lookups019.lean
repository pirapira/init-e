import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_tx_signing_hash_mode :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 115#8, 105#8, 103#8, 110#8, 105#8, 110#8, 103#8, 95#8, 104#8, 97#8, 115#8, 104#8, 95#8, 109#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_signing_hash_mode) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_signing_hash_pre155 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 105#8, 103#8, 110#8, 105#8, 110#8, 103#8, 95#8, 104#8, 97#8, 115#8, 104#8, 95#8, 112#8, 114#8, 101#8, 49#8, 53#8, 53#8]) = literalEntry (declToHOL Guest.Software.guestFn_signing_hash_pre155) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_signing_hash_155 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 105#8, 103#8, 110#8, 105#8, 110#8, 103#8, 95#8, 104#8, 97#8, 115#8, 104#8, 95#8, 49#8, 53#8, 53#8]) = literalEntry (declToHOL Guest.Software.guestFn_signing_hash_155) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_signing_hash_2930 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 105#8, 103#8, 110#8, 105#8, 110#8, 103#8, 95#8, 104#8, 97#8, 115#8, 104#8, 95#8, 50#8, 57#8, 51#8, 48#8]) = literalEntry (declToHOL Guest.Software.guestFn_signing_hash_2930) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_signing_hash_1559 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 105#8, 103#8, 110#8, 105#8, 110#8, 103#8, 95#8, 104#8, 97#8, 115#8, 104#8, 95#8, 49#8, 53#8, 53#8, 57#8]) = literalEntry (declToHOL Guest.Software.guestFn_signing_hash_1559) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_signing_hash_4844 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 105#8, 103#8, 110#8, 105#8, 110#8, 103#8, 95#8, 104#8, 97#8, 115#8, 104#8, 95#8, 52#8, 56#8, 52#8, 52#8]) = literalEntry (declToHOL Guest.Software.guestFn_signing_hash_4844) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_signing_hash_7702 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 105#8, 103#8, 110#8, 105#8, 110#8, 103#8, 95#8, 104#8, 97#8, 115#8, 104#8, 95#8, 55#8, 55#8, 48#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_signing_hash_7702) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_chain_id :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 99#8, 104#8, 97#8, 105#8, 110#8, 95#8, 105#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_chain_id) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_signature_recovery_parameters :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 105#8, 103#8, 110#8, 97#8, 116#8, 117#8, 114#8, 101#8, 95#8, 114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8, 121#8, 95#8, 112#8, 97#8, 114#8, 97#8, 109#8, 101#8, 116#8, 101#8, 114#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_signature_recovery_parameters) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_recover_transaction_public_key :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8, 95#8, 112#8, 117#8, 98#8, 108#8, 105#8, 99#8, 95#8, 107#8, 101#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_recover_transaction_public_key) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sender_address_from_public_key :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 110#8, 100#8, 101#8, 114#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 112#8, 117#8, 98#8, 108#8, 105#8, 99#8, 95#8, 107#8, 101#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_sender_address_from_public_key) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_recover_sender :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8, 95#8, 115#8, 101#8, 110#8, 100#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_recover_sender) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_recover_sender_with_chain_id :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8, 95#8, 115#8, 101#8, 110#8, 100#8, 101#8, 114#8, 95#8, 119#8, 105#8, 116#8, 104#8, 95#8, 99#8, 104#8, 97#8, 105#8, 110#8, 95#8, 105#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_recover_sender_with_chain_id) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_count_tokens_in_data :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 116#8, 111#8, 107#8, 101#8, 110#8, 115#8, 95#8, 105#8, 110#8, 95#8, 100#8, 97#8, 116#8, 97#8]) = literalEntry (declToHOL Guest.Software.guestFn_count_tokens_in_data) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_calculate_intrinsic_cost :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 97#8, 108#8, 99#8, 117#8, 108#8, 97#8, 116#8, 101#8, 95#8, 105#8, 110#8, 116#8, 114#8, 105#8, 110#8, 115#8, 105#8, 99#8, 95#8, 99#8, 111#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_calculate_intrinsic_cost) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_validate_transaction :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_validate_transaction) := by
  rfl

end InitE.SourceWitness
