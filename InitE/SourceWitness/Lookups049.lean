import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_compute_state_root :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 111#8, 109#8, 112#8, 117#8, 116#8, 101#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 114#8, 111#8, 111#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_compute_state_root) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_addr_from_words :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 114#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 119#8, 111#8, 114#8, 100#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_addr_from_words) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fork_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 111#8, 114#8, 107#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_fork_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_block_rlp_length :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 111#8, 99#8, 107#8, 95#8, 114#8, 108#8, 112#8, 95#8, 108#8, 101#8, 110#8, 103#8, 116#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_block_rlp_length) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_payload_header :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 97#8, 121#8, 108#8, 111#8, 97#8, 100#8, 95#8, 104#8, 101#8, 97#8, 100#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_payload_header) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_is_blob :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 105#8, 115#8, 95#8, 98#8, 108#8, 111#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_is_blob) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_tx_is_setcode :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 120#8, 95#8, 105#8, 115#8, 95#8, 115#8, 101#8, 116#8, 99#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_tx_is_setcode) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fee_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 101#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fee_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_is_valid_versioned_hashes :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 115#8, 95#8, 118#8, 97#8, 108#8, 105#8, 100#8, 95#8, 118#8, 101#8, 114#8, 115#8, 105#8, 111#8, 110#8, 101#8, 100#8, 95#8, 104#8, 97#8, 115#8, 104#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_is_valid_versioned_hashes) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_te_new :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 101#8, 95#8, 110#8, 101#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_te_new) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_process_unchecked_system_transaction :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 117#8, 110#8, 99#8, 104#8, 101#8, 99#8, 107#8, 101#8, 100#8, 95#8, 115#8, 121#8, 115#8, 116#8, 101#8, 109#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_process_unchecked_system_transaction) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_process_checked_system_transaction :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 99#8, 104#8, 101#8, 99#8, 107#8, 101#8, 100#8, 95#8, 115#8, 121#8, 115#8, 116#8, 101#8, 109#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_process_checked_system_transaction) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_check_transaction :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 104#8, 101#8, 99#8, 107#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_check_transaction) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_process_transaction :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 116#8, 114#8, 97#8, 110#8, 115#8, 97#8, 99#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_process_transaction) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_udiv_small5 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 100#8, 105#8, 118#8, 95#8, 115#8, 109#8, 97#8, 108#8, 108#8, 53#8]) = literalEntry (declToHOL Guest.Software.guestFn_udiv_small5) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_process_withdrawals :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 119#8, 105#8, 116#8, 104#8, 100#8, 114#8, 97#8, 119#8, 97#8, 108#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_process_withdrawals) := by
  rfl

end InitE.SourceWitness
