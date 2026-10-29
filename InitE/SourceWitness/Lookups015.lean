import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_trie_walk :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 114#8, 105#8, 101#8, 95#8, 119#8, 97#8, 108#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_trie_walk) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_trie_lookup :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 114#8, 105#8, 101#8, 95#8, 108#8, 111#8, 111#8, 107#8, 117#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_trie_lookup) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mpt_new :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 110#8, 101#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_mpt_new) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mpt_from_witness :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 119#8, 105#8, 116#8, 110#8, 101#8, 115#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_mpt_from_witness) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mpt_nibble_key :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 110#8, 105#8, 98#8, 98#8, 108#8, 101#8, 95#8, 107#8, 101#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_mpt_nibble_key) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mpt_get :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 103#8, 101#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_mpt_get) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__create_branch_from_two_leaves :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 95#8, 98#8, 114#8, 97#8, 110#8, 99#8, 104#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 116#8, 119#8, 111#8, 95#8, 108#8, 101#8, 97#8, 118#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn__create_branch_from_two_leaves) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__insert_into_leaf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 105#8, 110#8, 115#8, 101#8, 114#8, 116#8, 95#8, 105#8, 110#8, 116#8, 111#8, 95#8, 108#8, 101#8, 97#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn__insert_into_leaf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__split_extension :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 115#8, 112#8, 108#8, 105#8, 116#8, 95#8, 101#8, 120#8, 116#8, 101#8, 110#8, 115#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn__split_extension) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__mpt_insert_node :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 109#8, 112#8, 116#8, 95#8, 105#8, 110#8, 115#8, 101#8, 114#8, 116#8, 95#8, 110#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn__mpt_insert_node) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__collapse_branch :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 99#8, 111#8, 108#8, 108#8, 97#8, 112#8, 115#8, 101#8, 95#8, 98#8, 114#8, 97#8, 110#8, 99#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn__collapse_branch) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__delete_ext_finish :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 100#8, 101#8, 108#8, 101#8, 116#8, 101#8, 95#8, 101#8, 120#8, 116#8, 95#8, 102#8, 105#8, 110#8, 105#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn__delete_ext_finish) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__mpt_delete_node_body :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 109#8, 112#8, 116#8, 95#8, 100#8, 101#8, 108#8, 101#8, 116#8, 101#8, 95#8, 110#8, 111#8, 100#8, 101#8, 95#8, 98#8, 111#8, 100#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn__mpt_delete_node_body) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__mpt_delete_node :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 109#8, 112#8, 116#8, 95#8, 100#8, 101#8, 108#8, 101#8, 116#8, 101#8, 95#8, 110#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn__mpt_delete_node) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mpt_set :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 112#8, 116#8, 95#8, 115#8, 101#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_mpt_set) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn__node_rlp_begin :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [95#8, 110#8, 111#8, 100#8, 101#8, 95#8, 114#8, 108#8, 112#8, 95#8, 98#8, 101#8, 103#8, 105#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn__node_rlp_begin) := by
  rfl

end InitE.SourceWitness
