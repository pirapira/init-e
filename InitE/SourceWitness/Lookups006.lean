import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_rlp_decode_fully :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 102#8, 117#8, 108#8, 108#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_decode_fully) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_item_header :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 105#8, 116#8, 101#8, 109#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_item_header) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__rlp_validate_items_body :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 114#8, 108#8, 112#8, 95#8, 118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 105#8, 116#8, 101#8, 109#8, 115#8, 95#8, 98#8, 111#8, 100#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn__rlp_validate_items_body) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_validate_items :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 105#8, 116#8, 101#8, 109#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_validate_items) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_item_total :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 105#8, 116#8, 101#8, 109#8, 95#8, 116#8, 111#8, 116#8, 97#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_item_total) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_list_count :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_list_count) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_item_total_unchecked :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 105#8, 116#8, 101#8, 109#8, 95#8, 116#8, 111#8, 116#8, 97#8, 108#8, 95#8, 117#8, 110#8, 99#8, 104#8, 101#8, 99#8, 107#8, 101#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_item_total_unchecked) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_list_to_slices :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 116#8, 111#8, 95#8, 115#8, 108#8, 105#8, 99#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_list_to_slices) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_bytes_to_word :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8, 95#8, 116#8, 111#8, 95#8, 119#8, 111#8, 114#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_bytes_to_word) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_check_uint_bytes :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 99#8, 104#8, 101#8, 99#8, 107#8, 95#8, 117#8, 105#8, 110#8, 116#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_check_uint_bytes) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_be_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 98#8, 101#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_be_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_put_be :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 112#8, 117#8, 116#8, 95#8, 98#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_put_be) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_write_header :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 119#8, 114#8, 105#8, 116#8, 101#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_write_header) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_header_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_header_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_encode_bytes :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_encode_bytes) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_encode_word :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 119#8, 111#8, 114#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_encode_word) := by
  rfl

end InitE.SourceWitness
