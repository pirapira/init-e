import InitE.SourceWitness.Terms021
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0353 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_journal) code0352
def globals0353 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_journal) globals0352
def exceptions0353 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_journal) exceptions0352
def code0354 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_journal_cap) code0353
def globals0354 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_journal_cap) globals0353
def exceptions0354 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_journal_cap) exceptions0353
def code0355 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_state_init) code0354
def globals0355 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_state_init) globals0354
def exceptions0355 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_state_init) exceptions0354
def code0356 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_state_fresh_tx) code0355
def globals0356 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_state_fresh_tx) globals0355
def exceptions0356 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_state_fresh_tx) exceptions0355
def code0357 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_jset) code0356
def globals0357 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_jset) globals0356
def exceptions0357 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_jset) exceptions0356
def code0358 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_jdel) code0357
def globals0358 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_jdel) globals0357
def exceptions0358 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_jdel) exceptions0357
def code0359 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_state_snapshot) code0358
def globals0359 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_state_snapshot) globals0358
def exceptions0359 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_state_snapshot) exceptions0358
def code0360 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_state_restore) code0359
def globals0360 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_state_restore) globals0359
def exceptions0360 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_state_restore) exceptions0359
def code0361 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_sk_make) code0360
def globals0361 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_sk_make) globals0360
def exceptions0361 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_sk_make) exceptions0360
def code0362 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_acct_new) code0361
def globals0362 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_acct_new) globals0361
def exceptions0362 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_acct_new) exceptions0361
def code0363 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_acct_empty) code0362
def globals0363 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_acct_empty) globals0362
def exceptions0363 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_acct_empty) exceptions0362
def code0364 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_acct_copy) code0363
def globals0364 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_acct_copy) globals0363
def exceptions0364 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_acct_copy) exceptions0363
def code0365 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_record_pre_state_read) code0364
def globals0365 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_record_pre_state_read) globals0364
def exceptions0365 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_record_pre_state_read) exceptions0364
def code0366 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ws_account_leaf) code0365
def globals0366 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ws_account_leaf) globals0365
def exceptions0366 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ws_account_leaf) exceptions0365
def code0367 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ws_get_account_optional) code0366
def globals0367 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ws_get_account_optional) globals0366
def exceptions0367 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ws_get_account_optional) exceptions0366
def code0368 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ws_storage_root_of) code0367
def globals0368 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ws_storage_root_of) globals0367
def exceptions0368 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ws_storage_root_of) exceptions0367

def state0368 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0368
    code := code0368
    eshapes := exceptions0368
    structs := [] }

end InitE.SourceWitness
