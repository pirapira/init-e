import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_track_ancestor_access :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 114#8, 97#8, 99#8, 107#8, 95#8, 97#8, 110#8, 99#8, 101#8, 115#8, 116#8, 111#8, 114#8, 95#8, 97#8, 99#8, 99#8, 101#8, 115#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_track_ancestor_access) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_lst_new :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 115#8, 116#8, 95#8, 110#8, 101#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_lst_new) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_lst_new_scratch :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 115#8, 116#8, 95#8, 110#8, 101#8, 119#8, 95#8, 115#8, 99#8, 114#8, 97#8, 116#8, 99#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_lst_new_scratch) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_lst_push :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 115#8, 116#8, 95#8, 112#8, 117#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_lst_push) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bal_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 97#8, 108#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_bal_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bal_ensure_account :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 97#8, 108#8, 95#8, 101#8, 110#8, 115#8, 117#8, 114#8, 101#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_bal_ensure_account) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_lst_upsert_idx :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 115#8, 116#8, 95#8, 117#8, 112#8, 115#8, 101#8, 114#8, 116#8, 95#8, 105#8, 100#8, 120#8]) = literalEntry (declToHOL Guest.Software.guestFn_lst_upsert_idx) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_add_storage_write :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 119#8, 114#8, 105#8, 116#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_add_storage_write) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_add_storage_read :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 114#8, 101#8, 97#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_add_storage_read) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_add_balance_change :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 95#8, 98#8, 97#8, 108#8, 97#8, 110#8, 99#8, 101#8, 95#8, 99#8, 104#8, 97#8, 110#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_add_balance_change) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_add_nonce_change :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 95#8, 110#8, 111#8, 110#8, 99#8, 101#8, 95#8, 99#8, 104#8, 97#8, 110#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_add_nonce_change) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_add_code_change :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 95#8, 99#8, 111#8, 100#8, 101#8, 95#8, 99#8, 104#8, 97#8, 110#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_add_code_change) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_add_touched_account :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 95#8, 116#8, 111#8, 117#8, 99#8, 104#8, 101#8, 100#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_add_touched_account) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_pre_tx_account :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 112#8, 114#8, 101#8, 95#8, 116#8, 120#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_pre_tx_account) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_pre_tx_storage :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 112#8, 114#8, 101#8, 95#8, 116#8, 120#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_pre_tx_storage) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_idx_start_account :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 100#8, 120#8, 95#8, 115#8, 116#8, 97#8, 114#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_idx_start_account) := by
  rfl

end InitE.SourceWitness
