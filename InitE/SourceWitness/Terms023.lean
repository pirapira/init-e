import InitE.SourceWitness.Terms022
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0369 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ws_storage_trie) code0368
def globals0369 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ws_storage_trie) globals0368
def exceptions0369 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ws_storage_trie) exceptions0368
def code0370 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ws_get_storage) code0369
def globals0370 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ws_get_storage) globals0369
def exceptions0370 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ws_get_storage) exceptions0369
def code0371 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ws_get_code) code0370
def globals0371 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ws_get_code) globals0370
def exceptions0371 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ws_get_code) exceptions0370
def code0372 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ws_account_has_storage) code0371
def globals0372 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ws_account_has_storage) globals0371
def exceptions0372 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ws_account_has_storage) exceptions0371
def code0373 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_pre_state_account_optional) code0372
def globals0373 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_pre_state_account_optional) globals0372
def exceptions0373 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_pre_state_account_optional) exceptions0372
def code0374 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_pre_state_account) code0373
def globals0374 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_pre_state_account) globals0373
def exceptions0374 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_pre_state_account) exceptions0373
def code0375 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_account_optional) code0374
def globals0375 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_account_optional) globals0374
def exceptions0375 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_account_optional) exceptions0374
def code0376 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_account) code0375
def globals0376 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_account) globals0375
def exceptions0376 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_account) exceptions0375
def code0377 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_code) code0376
def globals0377 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_code) globals0376
def exceptions0377 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_code) exceptions0376
def code0378 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_stor_lookup) code0377
def globals0378 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_stor_lookup) globals0377
def exceptions0378 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_stor_lookup) exceptions0377
def code0379 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_storage) code0378
def globals0379 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_storage) globals0378
def exceptions0379 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_storage) exceptions0378
def code0380 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_storage_original) code0379
def globals0380 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_storage_original) globals0379
def exceptions0380 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_storage_original) exceptions0379
def code0381 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_transient_storage) code0380
def globals0381 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_transient_storage) globals0380
def exceptions0381 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_transient_storage) exceptions0380
def code0382 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_account_exists) code0381
def globals0382 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_account_exists) globals0381
def exceptions0382 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_account_exists) exceptions0381
def code0383 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_account_has_storage) code0382
def globals0383 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_account_has_storage) globals0382
def exceptions0383 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_account_has_storage) exceptions0382
def code0384 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_account_deployable) code0383
def globals0384 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_account_deployable) globals0383
def exceptions0384 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_account_deployable) exceptions0383

def state0384 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0384
    code := code0384
    eshapes := exceptions0384
    structs := [] }

end InitE.SourceWitness
