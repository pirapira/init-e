import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_rlp_encode_list_header :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_encode_list_header) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_bytes_encoded_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 100#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_bytes_encoded_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_list_header_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_list_header_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_word_encoded_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 119#8, 111#8, 114#8, 100#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 100#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_word_encoded_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_new :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 110#8, 101#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_new) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_new_scratch :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 110#8, 101#8, 119#8, 95#8, 115#8, 99#8, 114#8, 97#8, 116#8, 99#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_new_scratch) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_first_diff :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 102#8, 105#8, 114#8, 115#8, 116#8, 95#8, 100#8, 105#8, 102#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_first_diff) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_find_leaf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 102#8, 105#8, 110#8, 100#8, 95#8, 108#8, 101#8, 97#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_find_leaf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_get :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 103#8, 101#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_get) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_has :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 104#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_has) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_new_node :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 110#8, 101#8, 119#8, 95#8, 110#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_new_node) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_new_leaf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 110#8, 101#8, 119#8, 95#8, 108#8, 101#8, 97#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_new_leaf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_new_internal :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 110#8, 101#8, 119#8, 95#8, 105#8, 110#8, 116#8, 101#8, 114#8, 110#8, 97#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_new_internal) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_grow :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 103#8, 114#8, 111#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_grow) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_set :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 115#8, 101#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_set) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_del :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 100#8, 101#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_del) := by
  rfl

end InitE.SourceWitness
