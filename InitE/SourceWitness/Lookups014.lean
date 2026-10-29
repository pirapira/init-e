import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_nibble_list_to_compact :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 105#8, 98#8, 98#8, 108#8, 101#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 116#8, 111#8, 95#8, 99#8, 111#8, 109#8, 112#8, 97#8, 99#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_nibble_list_to_compact) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_common_prefix_length :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 111#8, 109#8, 109#8, 111#8, 110#8, 95#8, 112#8, 114#8, 101#8, 102#8, 105#8, 120#8, 95#8, 108#8, 101#8, 110#8, 103#8, 116#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_common_prefix_length) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_nibbles_concat :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 105#8, 98#8, 98#8, 108#8, 101#8, 115#8, 95#8, 99#8, 111#8, 110#8, 99#8, 97#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_nibbles_concat) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_nodedb_build :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 100#8, 98#8, 95#8, 98#8, 117#8, 105#8, 108#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_nodedb_build) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_nodedb_lookup :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 100#8, 98#8, 95#8, 108#8, 111#8, 111#8, 107#8, 117#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_nodedb_lookup) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_node_new_hashed :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 110#8, 101#8, 119#8, 95#8, 104#8, 97#8, 115#8, 104#8, 101#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_node_new_hashed) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_node_new_leaf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 110#8, 101#8, 119#8, 95#8, 108#8, 101#8, 97#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_node_new_leaf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_node_new_ext :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 110#8, 101#8, 119#8, 95#8, 101#8, 120#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_node_new_ext) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_node_new_branch :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 110#8, 101#8, 119#8, 95#8, 98#8, 114#8, 97#8, 110#8, 99#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_node_new_branch) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_node_invalidate :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 111#8, 100#8, 101#8, 95#8, 105#8, 110#8, 118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_node_invalidate) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__resolve_step :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 114#8, 101#8, 115#8, 111#8, 108#8, 118#8, 101#8, 95#8, 115#8, 116#8, 101#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn__resolve_step) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__decode_step :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 115#8, 116#8, 101#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn__decode_step) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__decode_witness_node_body :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 119#8, 105#8, 116#8, 110#8, 101#8, 115#8, 115#8, 95#8, 110#8, 111#8, 100#8, 101#8, 95#8, 98#8, 111#8, 100#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn__decode_witness_node_body) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__decode_witness_node_mpt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 119#8, 105#8, 116#8, 110#8, 101#8, 115#8, 115#8, 95#8, 110#8, 111#8, 100#8, 101#8, 95#8, 109#8, 112#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn__decode_witness_node_mpt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__decode_witness_node :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 119#8, 105#8, 116#8, 110#8, 101#8, 115#8, 115#8, 95#8, 110#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn__decode_witness_node) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_decode_witness_to_mpt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 119#8, 105#8, 116#8, 110#8, 101#8, 115#8, 115#8, 95#8, 116#8, 111#8, 95#8, 109#8, 112#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_decode_witness_to_mpt) := by
  rfl

end InitE.SourceWitness
