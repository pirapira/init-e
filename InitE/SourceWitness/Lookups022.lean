import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_is_account_alive :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 115#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 97#8, 108#8, 105#8, 118#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_is_account_alive) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_set_account :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_set_account) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_set_storage :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_set_storage) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_destroy_storage :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 115#8, 116#8, 114#8, 111#8, 121#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_destroy_storage) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_destroy_account :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 115#8, 116#8, 114#8, 111#8, 121#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_destroy_account) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_modify_state_commit :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 111#8, 100#8, 105#8, 102#8, 121#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 99#8, 111#8, 109#8, 109#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_modify_state_commit) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_clear_account_preserving_balance :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 108#8, 101#8, 97#8, 114#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 112#8, 114#8, 101#8, 115#8, 101#8, 114#8, 118#8, 105#8, 110#8, 103#8, 95#8, 98#8, 97#8, 108#8, 97#8, 110#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_clear_account_preserving_balance) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mark_account_created :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 97#8, 114#8, 107#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_mark_account_created) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_set_transient_storage :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 116#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 105#8, 101#8, 110#8, 116#8, 95#8, 115#8, 116#8, 111#8, 114#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_set_transient_storage) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_move_ether :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 111#8, 118#8, 101#8, 95#8, 101#8, 116#8, 104#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_move_ether) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_create_ether :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 95#8, 101#8, 116#8, 104#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_create_ether) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_set_account_balance :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 116#8, 95#8, 97#8, 99#8, 99#8, 111#8, 117#8, 110#8, 116#8, 95#8, 98#8, 97#8, 108#8, 97#8, 110#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_set_account_balance) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_increment_nonce :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 110#8, 99#8, 114#8, 101#8, 109#8, 101#8, 110#8, 116#8, 95#8, 110#8, 111#8, 110#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_increment_nonce) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_set_code :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 116#8, 95#8, 99#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_set_code) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_union_into :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 117#8, 110#8, 105#8, 111#8, 110#8, 95#8, 105#8, 110#8, 116#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_union_into) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_merge_tx_into_block :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 101#8, 114#8, 103#8, 101#8, 95#8, 116#8, 120#8, 95#8, 105#8, 110#8, 116#8, 111#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_merge_tx_into_block) := by
  rfl

end InitE.SourceWitness
