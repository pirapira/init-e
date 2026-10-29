import InitE.SourceWitness.Terms025
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0417 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_add_balance_change) code0416
def globals0417 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_add_balance_change) globals0416
def exceptions0417 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_add_balance_change) exceptions0416
def code0418 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_add_nonce_change) code0417
def globals0418 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_add_nonce_change) globals0417
def exceptions0418 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_add_nonce_change) exceptions0417
def code0419 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_add_code_change) code0418
def globals0419 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_add_code_change) globals0418
def exceptions0419 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_add_code_change) exceptions0418
def code0420 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_add_touched_account) code0419
def globals0420 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_add_touched_account) globals0419
def exceptions0420 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_add_touched_account) exceptions0419
def code0421 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_pre_tx_account) code0420
def globals0421 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_pre_tx_account) globals0420
def exceptions0421 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_pre_tx_account) exceptions0420
def code0422 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_pre_tx_storage) code0421
def globals0422 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_pre_tx_storage) globals0421
def exceptions0422 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_pre_tx_storage) exceptions0421
def code0423 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_idx_start_account) code0422
def globals0423 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_idx_start_account) globals0422
def exceptions0423 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_idx_start_account) exceptions0422
def code0424 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_idx_start_storage) code0423
def globals0424 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_idx_start_storage) globals0423
def exceptions0424 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_idx_start_storage) exceptions0423
def code0425 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bal_list_remove_idx) code0424
def globals0425 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bal_list_remove_idx) globals0424
def exceptions0425 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bal_list_remove_idx) exceptions0424
def code0426 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bal_remove_change) code0425
def globals0426 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bal_remove_change) globals0425
def exceptions0426 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bal_remove_change) exceptions0425
def code0427 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_remove_storage_write) code0426
def globals0427 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_remove_storage_write) globals0426
def exceptions0427 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_remove_storage_write) exceptions0426
def code0428 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_update_builder_from_tx) code0427
def globals0428 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_update_builder_from_tx) globals0427
def exceptions0428 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_update_builder_from_tx) exceptions0427
def code0429 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_incorporate_tx_into_block) code0428
def globals0429 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_incorporate_tx_into_block) globals0428
def exceptions0429 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_incorporate_tx_into_block) exceptions0428
def code0430 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bal_sort_gt) code0429
def globals0430 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bal_sort_gt) globals0429
def exceptions0430 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bal_sort_gt) exceptions0429
def code0431 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_sort_elems) code0430
def globals0431 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_sort_elems) globals0430
def exceptions0431 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_sort_elems) exceptions0430
def code0432 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_sorted_keys32) code0431
def globals0432 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_sorted_keys32) globals0431
def exceptions0432 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_sorted_keys32) exceptions0431

def state0432 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0432
    code := code0432
    eshapes := exceptions0432
    structs := [] }

end InitE.SourceWitness
