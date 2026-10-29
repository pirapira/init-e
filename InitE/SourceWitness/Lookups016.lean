import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn__node_rlp_finish :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 110#8, 111#8, 100#8, 101#8, 95#8, 114#8, 108#8, 112#8, 95#8, 102#8, 105#8, 110#8, 105#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn__node_rlp_finish) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__node_needs_rlp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 110#8, 111#8, 100#8, 101#8, 95#8, 110#8, 101#8, 101#8, 100#8, 115#8, 95#8, 114#8, 108#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn__node_needs_rlp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__node_rlp_fill :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 110#8, 111#8, 100#8, 101#8, 95#8, 114#8, 108#8, 112#8, 95#8, 102#8, 105#8, 108#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn__node_rlp_fill) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_node_rlp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 114#8, 108#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_node_rlp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_value_encoded_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 118#8, 97#8, 108#8, 117#8, 101#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 100#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_value_encoded_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_node_ref_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 114#8, 101#8, 102#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_node_ref_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_node_hash_cached :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 104#8, 97#8, 115#8, 104#8, 95#8, 99#8, 97#8, 99#8, 104#8, 101#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_node_hash_cached) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_node_write_ref :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 119#8, 114#8, 105#8, 116#8, 101#8, 95#8, 114#8, 101#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_node_write_ref) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_node_hash :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 104#8, 97#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_node_hash) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mpt_root :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 114#8, 111#8, 111#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_mpt_root) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_build_mpt_indexed :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 117#8, 105#8, 108#8, 100#8, 95#8, 109#8, 112#8, 116#8, 95#8, 105#8, 110#8, 100#8, 101#8, 120#8, 101#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_build_mpt_indexed) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_decode_account_from_leaf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 108#8, 101#8, 97#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_decode_account_from_leaf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_encode_account :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_encode_account) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_scalar_item :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 115#8, 99#8, 97#8, 108#8, 97#8, 114#8, 95#8, 105#8, 116#8, 101#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_scalar_item) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_scalar_u256 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 115#8, 99#8, 97#8, 108#8, 97#8, 114#8, 95#8, 117#8, 50#8, 53#8, 54#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_scalar_u256) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_scalar_word :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 115#8, 99#8, 97#8, 108#8, 97#8, 114#8, 95#8, 119#8, 111#8, 114#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_scalar_word) := by
  rfl

end InitE.SourceWitness
