import InitE.SourceWitness.Terms018
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0305 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_decode_blob_hashes) code0304
def globals0305 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_decode_blob_hashes) globals0304
def exceptions0305 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_decode_blob_hashes) exceptions0304
def code0306 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_decode_authorizations) code0305
def globals0306 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_decode_authorizations) globals0305
def exceptions0306 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_decode_authorizations) exceptions0305
def code0307 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_decode_transaction_rlp) code0306
def globals0307 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_decode_transaction_rlp) globals0306
def exceptions0307 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_decode_transaction_rlp) exceptions0306
def code0308 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_decode_transaction) code0307
def globals0308 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_decode_transaction) globals0307
def exceptions0308 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_decode_transaction) exceptions0307
def code0309 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_gas) code0308
def globals0309 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_gas) globals0308
def exceptions0309 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_gas) exceptions0308
def code0310 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_nonce) code0309
def globals0310 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_nonce) globals0309
def exceptions0310 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_nonce) exceptions0309
def code0311 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_to) code0310
def globals0311 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_to) globals0310
def exceptions0311 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_to) exceptions0310
def code0312 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_value) code0311
def globals0312 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_value) globals0311
def exceptions0312 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_value) exceptions0311
def code0313 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_data) code0312
def globals0313 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_data) globals0312
def exceptions0313 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_data) exceptions0312
def code0314 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_r) code0313
def globals0314 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_r) globals0313
def exceptions0314 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_r) exceptions0313
def code0315 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_s) code0314
def globals0315 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_s) globals0314
def exceptions0315 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_s) exceptions0314
def code0316 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_has_access_list) code0315
def globals0316 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_has_access_list) globals0315
def exceptions0316 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_has_access_list) exceptions0315
def code0317 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_blob_count) code0316
def globals0317 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_blob_count) globals0316
def exceptions0317 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_blob_count) exceptions0316
def code0318 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_calculate_total_blob_gas) code0317
def globals0318 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_calculate_total_blob_gas) globals0317
def exceptions0318 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_calculate_total_blob_gas) exceptions0317
def code0319 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_put_u256) code0318
def globals0319 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_put_u256) globals0318
def exceptions0319 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_put_u256) exceptions0318
def code0320 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_u256_encoded_len) code0319
def globals0320 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_u256_encoded_len) globals0319
def exceptions0320 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_u256_encoded_len) exceptions0319

def state0320 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0320
    code := code0320
    eshapes := exceptions0320
    structs := [] }

end InitE.SourceWitness
