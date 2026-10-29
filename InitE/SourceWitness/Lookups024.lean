import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_idx_start_storage :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 100#8, 120#8, 95#8, 115#8, 116#8, 97#8, 114#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_idx_start_storage) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bal_list_remove_idx :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 97#8, 108#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 114#8, 101#8, 109#8, 111#8, 118#8, 101#8, 95#8, 105#8, 100#8, 120#8]) = literalEntry (declToHOL Guest.Software.guestFn_bal_list_remove_idx) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bal_remove_change :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 97#8, 108#8, 95#8, 114#8, 101#8, 109#8, 111#8, 118#8, 101#8, 95#8, 99#8, 104#8, 97#8, 110#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_bal_remove_change) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_remove_storage_write :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 101#8, 109#8, 111#8, 118#8, 101#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 119#8, 114#8, 105#8, 116#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_remove_storage_write) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_update_builder_from_tx :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 112#8, 100#8, 97#8, 116#8, 101#8, 95#8, 98#8, 117#8, 105#8, 108#8, 100#8, 101#8, 114#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 116#8, 120#8]) = literalEntry (declToHOL Guest.Software.guestFn_update_builder_from_tx) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_incorporate_tx_into_block :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 110#8, 99#8, 111#8, 114#8, 112#8, 111#8, 114#8, 97#8, 116#8, 101#8, 95#8, 116#8, 120#8, 95#8, 105#8, 110#8, 116#8, 111#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_incorporate_tx_into_block) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bal_sort_gt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 97#8, 108#8, 95#8, 115#8, 111#8, 114#8, 116#8, 95#8, 103#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_bal_sort_gt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sort_elems :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 111#8, 114#8, 116#8, 95#8, 101#8, 108#8, 101#8, 109#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_sort_elems) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sorted_keys32 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 111#8, 114#8, 116#8, 101#8, 100#8, 95#8, 107#8, 101#8, 121#8, 115#8, 51#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_sorted_keys32) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bal_encode_account :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 97#8, 108#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_bal_encode_account) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_build_block_access_list_rlp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 117#8, 105#8, 108#8, 100#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8, 95#8, 97#8, 99#8, 99#8, 101#8, 115#8, 115#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 114#8, 108#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_build_block_access_list_rlp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_validate_block_access_list_gas_limit :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [118#8, 97#8, 108#8, 105#8, 100#8, 97#8, 116#8, 101#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8, 95#8, 97#8, 99#8, 99#8, 101#8, 115#8, 115#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 103#8, 97#8, 115#8, 95#8, 108#8, 105#8, 109#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_validate_block_access_list_gas_limit) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sat_word :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 97#8, 116#8, 95#8, 119#8, 111#8, 114#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_sat_word) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_add_sat :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 95#8, 115#8, 97#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_add_sat) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ceil32 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 101#8, 105#8, 108#8, 51#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_ceil32) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_words_of :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 111#8, 114#8, 100#8, 115#8, 95#8, 111#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_words_of) := by
  rfl

end InitE.SourceWitness
