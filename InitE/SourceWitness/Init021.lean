import InitE.SourceWitness.Terms021
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0336 globals0336

def chunk021 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_signing_hash_4844,
    declToHOL Guest.Software.guestFn_signing_hash_7702,
    declToHOL Guest.Software.guestFn_tx_chain_id,
    declToHOL Guest.Software.guestFn_signature_recovery_parameters,
    declToHOL Guest.Software.guestFn_recover_transaction_public_key,
    declToHOL Guest.Software.guestFn_sender_address_from_public_key,
    declToHOL Guest.Software.guestFn_recover_sender,
    declToHOL Guest.Software.guestFn_recover_sender_with_chain_id,
    declToHOL Guest.Software.guestFn_count_tokens_in_data,
    declToHOL Guest.Software.guestFn_calculate_intrinsic_cost,
    declToHOL Guest.Software.guestFn_validate_transaction,
    declToHOL Guest.Software.guestExn_StateErr,
    declToHOL Guest.Software.guestGlobal_ws,
    declToHOL Guest.Software.guestGlobal_bs,
    declToHOL Guest.Software.guestGlobal_ts,
    declToHOL Guest.Software.guestGlobal_sk_buf]

theorem chunk021_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0336 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk021 =
        some (state0352 s) := by
  cbv

end InitE.SourceWitness
