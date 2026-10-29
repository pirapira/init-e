import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_ws_get_code :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 115#8, 95#8, 103#8, 101#8, 116#8, 95#8, 99#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_ws_get_code) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ws_account_has_storage :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 115#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 104#8, 97#8, 115#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_ws_account_has_storage) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_pre_state_account_optional :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 112#8, 114#8, 101#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 111#8, 112#8, 116#8, 105#8, 111#8, 110#8, 97#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_pre_state_account_optional) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_pre_state_account :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 112#8, 114#8, 101#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_pre_state_account) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_account_optional :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 111#8, 112#8, 116#8, 105#8, 111#8, 110#8, 97#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_account_optional) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_account :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_account) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_code :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 99#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_code) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_stor_lookup :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 111#8, 114#8, 95#8, 108#8, 111#8, 111#8, 107#8, 117#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_stor_lookup) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_storage :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_storage) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_storage_original :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8, 95#8, 111#8, 114#8, 105#8, 103#8, 105#8, 110#8, 97#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_storage_original) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_get_transient_storage :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 101#8, 116#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 105#8, 101#8, 110#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_get_transient_storage) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_account_exists :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 101#8, 120#8, 105#8, 115#8, 116#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_account_exists) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_account_has_storage :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 104#8, 97#8, 115#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_account_has_storage) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_account_deployable :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 100#8, 101#8, 112#8, 108#8, 111#8, 121#8, 97#8, 98#8, 108#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_account_deployable) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_acct_is_empty :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 116#8, 95#8, 105#8, 115#8, 95#8, 101#8, 109#8, 112#8, 116#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_acct_is_empty) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_account_exists_and_is_empty :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 101#8, 120#8, 105#8, 115#8, 116#8, 115#8, 95#8, 97#8, 110#8, 100#8, 95#8, 105#8, 115#8, 95#8, 101#8, 109#8, 112#8, 116#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_account_exists_and_is_empty) := by
  rfl

end InitE.SourceWitness
