import InitE.SourceWitness.Terms024
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0401 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_htab_union_into) code0400
def globals0401 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_htab_union_into) globals0400
def exceptions0401 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_htab_union_into) exceptions0400
def code0402 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_merge_tx_into_block) code0401
def globals0402 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_merge_tx_into_block) globals0401
def exceptions0402 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_merge_tx_into_block) exceptions0401
def code0403 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_track_ancestor_access) code0402
def globals0403 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_track_ancestor_access) globals0402
def exceptions0403 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_track_ancestor_access) exceptions0402
def code0404 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_bal_accounts) code0403
def globals0404 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_bal_accounts) globals0403
def exceptions0404 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_bal_accounts) exceptions0403
def code0405 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_bal_index) code0404
def globals0405 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_bal_index) globals0404
def exceptions0405 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_bal_index) exceptions0404
def code0406 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_bal_idx_accts) code0405
def globals0406 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_bal_idx_accts) globals0405
def exceptions0406 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_bal_idx_accts) exceptions0405
def code0407 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_bal_idx_stor) code0406
def globals0407 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_bal_idx_stor) globals0406
def exceptions0407 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_bal_idx_stor) exceptions0406
def code0408 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_bal_key_buf) code0407
def globals0408 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_bal_key_buf) globals0407
def exceptions0408 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_bal_key_buf) exceptions0407
def code0409 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_lst_new) code0408
def globals0409 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_lst_new) globals0408
def exceptions0409 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_lst_new) exceptions0408
def code0410 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_lst_new_scratch) code0409
def globals0410 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_lst_new_scratch) globals0409
def exceptions0410 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_lst_new_scratch) exceptions0409
def code0411 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_lst_push) code0410
def globals0411 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_lst_push) globals0410
def exceptions0411 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_lst_push) exceptions0410
def code0412 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bal_init) code0411
def globals0412 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bal_init) globals0411
def exceptions0412 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bal_init) exceptions0411
def code0413 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bal_ensure_account) code0412
def globals0413 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bal_ensure_account) globals0412
def exceptions0413 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bal_ensure_account) exceptions0412
def code0414 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_lst_upsert_idx) code0413
def globals0414 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_lst_upsert_idx) globals0413
def exceptions0414 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_lst_upsert_idx) exceptions0413
def code0415 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_add_storage_write) code0414
def globals0415 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_add_storage_write) globals0414
def exceptions0415 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_add_storage_write) exceptions0414
def code0416 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_add_storage_read) code0415
def globals0416 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_add_storage_read) globals0415
def exceptions0416 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_add_storage_read) exceptions0415

def state0416 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0416
    code := code0416
    eshapes := exceptions0416
    structs := [] }

end InitE.SourceWitness
