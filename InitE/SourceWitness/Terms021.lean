import InitE.SourceWitness.Terms020
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0337 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_signing_hash_4844) code0336
def globals0337 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_signing_hash_4844) globals0336
def exceptions0337 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_signing_hash_4844) exceptions0336
def code0338 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_signing_hash_7702) code0337
def globals0338 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_signing_hash_7702) globals0337
def exceptions0338 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_signing_hash_7702) exceptions0337
def code0339 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_chain_id) code0338
def globals0339 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_chain_id) globals0338
def exceptions0339 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_chain_id) exceptions0338
def code0340 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_signature_recovery_parameters) code0339
def globals0340 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_signature_recovery_parameters) globals0339
def exceptions0340 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_signature_recovery_parameters) exceptions0339
def code0341 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_recover_transaction_public_key) code0340
def globals0341 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_recover_transaction_public_key) globals0340
def exceptions0341 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_recover_transaction_public_key) exceptions0340
def code0342 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_sender_address_from_public_key) code0341
def globals0342 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_sender_address_from_public_key) globals0341
def exceptions0342 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_sender_address_from_public_key) exceptions0341
def code0343 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_recover_sender) code0342
def globals0343 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_recover_sender) globals0342
def exceptions0343 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_recover_sender) exceptions0342
def code0344 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_recover_sender_with_chain_id) code0343
def globals0344 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_recover_sender_with_chain_id) globals0343
def exceptions0344 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_recover_sender_with_chain_id) exceptions0343
def code0345 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_count_tokens_in_data) code0344
def globals0345 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_count_tokens_in_data) globals0344
def exceptions0345 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_count_tokens_in_data) exceptions0344
def code0346 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_calculate_intrinsic_cost) code0345
def globals0346 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_calculate_intrinsic_cost) globals0345
def exceptions0346 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_calculate_intrinsic_cost) exceptions0345
def code0347 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_validate_transaction) code0346
def globals0347 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_validate_transaction) globals0346
def exceptions0347 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_validate_transaction) exceptions0346
def code0348 : CodeTable :=
  installCode (declToHOL Guest.Software.guestExn_StateErr) code0347
def globals0348 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestExn_StateErr) globals0347
def exceptions0348 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestExn_StateErr) exceptions0347
def code0349 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_ws) code0348
def globals0349 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_ws) globals0348
def exceptions0349 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_ws) exceptions0348
def code0350 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_bs) code0349
def globals0350 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_bs) globals0349
def exceptions0350 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_bs) exceptions0349
def code0351 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_ts) code0350
def globals0351 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_ts) globals0350
def exceptions0351 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_ts) exceptions0350
def code0352 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_sk_buf) code0351
def globals0352 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_sk_buf) globals0351
def exceptions0352 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_sk_buf) exceptions0351

def state0352 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0352
    code := code0352
    eshapes := exceptions0352
    structs := [] }

end InitE.SourceWitness
