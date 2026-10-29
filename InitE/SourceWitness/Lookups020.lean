import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_state_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_state_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_state_fresh_tx :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 102#8, 114#8, 101#8, 115#8, 104#8, 95#8, 116#8, 120#8]) = literalEntry (declToHOL Guest.Software.guestFn_state_fresh_tx) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_jset :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [106#8, 115#8, 101#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_jset) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_jdel :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [106#8, 100#8, 101#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_jdel) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_state_snapshot :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 115#8, 110#8, 97#8, 112#8, 115#8, 104#8, 111#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_state_snapshot) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_state_restore :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 114#8, 101#8, 115#8, 116#8, 111#8, 114#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_state_restore) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sk_make :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 107#8, 95#8, 109#8, 97#8, 107#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_sk_make) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_acct_new :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 116#8, 95#8, 110#8, 101#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_acct_new) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_acct_empty :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 116#8, 95#8, 101#8, 109#8, 112#8, 116#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_acct_empty) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_acct_copy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 116#8, 95#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_acct_copy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_record_pre_state_read :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 101#8, 99#8, 111#8, 114#8, 100#8, 95#8, 112#8, 114#8, 101#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 114#8, 101#8, 97#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_record_pre_state_read) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ws_account_leaf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 115#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 108#8, 101#8, 97#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_ws_account_leaf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ws_get_account_optional :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 115#8, 95#8, 103#8, 101#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 111#8, 112#8, 116#8, 105#8, 111#8, 110#8, 97#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_ws_get_account_optional) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ws_storage_root_of :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 115#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 114#8, 111#8, 111#8, 116#8, 95#8, 111#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_ws_storage_root_of) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ws_storage_trie :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 115#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 116#8, 114#8, 105#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_ws_storage_trie) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ws_get_storage :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 115#8, 95#8, 103#8, 101#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_ws_get_storage) := by
  rfl

end InitE.SourceWitness
