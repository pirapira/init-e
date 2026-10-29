import InitE.SourceWitness.Terms023
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0385 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_acct_is_empty) code0384
def globals0385 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_acct_is_empty) globals0384
def exceptions0385 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_acct_is_empty) exceptions0384
def code0386 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_account_exists_and_is_empty) code0385
def globals0386 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_account_exists_and_is_empty) globals0385
def exceptions0386 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_account_exists_and_is_empty) exceptions0385
def code0387 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_is_account_alive) code0386
def globals0387 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_is_account_alive) globals0386
def exceptions0387 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_is_account_alive) exceptions0386
def code0388 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_set_account) code0387
def globals0388 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_set_account) globals0387
def exceptions0388 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_set_account) exceptions0387
def code0389 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_set_storage) code0388
def globals0389 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_set_storage) globals0388
def exceptions0389 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_set_storage) exceptions0388
def code0390 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_destroy_storage) code0389
def globals0390 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_destroy_storage) globals0389
def exceptions0390 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_destroy_storage) exceptions0389
def code0391 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_destroy_account) code0390
def globals0391 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_destroy_account) globals0390
def exceptions0391 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_destroy_account) exceptions0390
def code0392 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_modify_state_commit) code0391
def globals0392 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_modify_state_commit) globals0391
def exceptions0392 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_modify_state_commit) exceptions0391
def code0393 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_clear_account_preserving_balance) code0392
def globals0393 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_clear_account_preserving_balance) globals0392
def exceptions0393 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_clear_account_preserving_balance) exceptions0392
def code0394 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_mark_account_created) code0393
def globals0394 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_mark_account_created) globals0393
def exceptions0394 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_mark_account_created) exceptions0393
def code0395 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_set_transient_storage) code0394
def globals0395 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_set_transient_storage) globals0394
def exceptions0395 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_set_transient_storage) exceptions0394
def code0396 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_move_ether) code0395
def globals0396 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_move_ether) globals0395
def exceptions0396 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_move_ether) exceptions0395
def code0397 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_create_ether) code0396
def globals0397 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_create_ether) globals0396
def exceptions0397 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_create_ether) exceptions0396
def code0398 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_set_account_balance) code0397
def globals0398 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_set_account_balance) globals0397
def exceptions0398 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_set_account_balance) exceptions0397
def code0399 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_increment_nonce) code0398
def globals0399 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_increment_nonce) globals0398
def exceptions0399 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_increment_nonce) exceptions0398
def code0400 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_set_code) code0399
def globals0400 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_set_code) globals0399
def exceptions0400 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_set_code) exceptions0399

def state0400 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0400
    code := code0400
    eshapes := exceptions0400
    structs := [] }

end InitE.SourceWitness
