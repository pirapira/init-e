import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_decode_header :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_decode_header) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_put_u256 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 112#8, 117#8, 116#8, 95#8, 117#8, 50#8, 53#8, 54#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_put_u256) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_encode_header :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_encode_header) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_header_hash :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 101#8, 97#8, 100#8, 101#8, 114#8, 95#8, 104#8, 97#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_header_hash) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_validate_headers :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_validate_headers) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_taylor_exponential :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 97#8, 121#8, 108#8, 111#8, 114#8, 95#8, 101#8, 120#8, 112#8, 111#8, 110#8, 101#8, 110#8, 116#8, 105#8, 97#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_taylor_exponential) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_calculate_blob_gas_price :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 97#8, 108#8, 99#8, 117#8, 108#8, 97#8, 116#8, 101#8, 95#8, 98#8, 108#8, 111#8, 98#8, 95#8, 103#8, 97#8, 115#8, 95#8, 112#8, 114#8, 105#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_calculate_blob_gas_price) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_calculate_excess_blob_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 97#8, 108#8, 99#8, 117#8, 108#8, 97#8, 116#8, 101#8, 95#8, 101#8, 120#8, 99#8, 101#8, 115#8, 115#8, 95#8, 98#8, 108#8, 111#8, 98#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_calculate_excess_blob_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_check_gas_limit :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 104#8, 101#8, 99#8, 107#8, 95#8, 103#8, 97#8, 115#8, 95#8, 108#8, 105#8, 109#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_check_gas_limit) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_calculate_base_fee_per_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 97#8, 108#8, 99#8, 117#8, 108#8, 97#8, 116#8, 101#8, 95#8, 98#8, 97#8, 115#8, 101#8, 95#8, 102#8, 101#8, 101#8, 95#8, 112#8, 101#8, 114#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_calculate_base_fee_per_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_header_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 101#8, 97#8, 100#8, 101#8, 114#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_header_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_validate_header :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_validate_header) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mpt_fail :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 102#8, 97#8, 105#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_mpt_fail) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mpt_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_mpt_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_key_to_nibbles :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [107#8, 101#8, 121#8, 95#8, 116#8, 111#8, 95#8, 110#8, 105#8, 98#8, 98#8, 108#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_key_to_nibbles) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_compact_to_nibbles :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 111#8, 109#8, 112#8, 97#8, 99#8, 116#8, 95#8, 116#8, 111#8, 95#8, 110#8, 105#8, 98#8, 98#8, 108#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_compact_to_nibbles) := by
  rfl

end InitE.SourceWitness
