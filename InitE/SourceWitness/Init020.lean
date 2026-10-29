import InitE.SourceWitness.Terms020
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0320 globals0320

def chunk020 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_tx_put_to,
    declToHOL Guest.Software.guestFn_access_list_payload_len,
    declToHOL Guest.Software.guestFn_tx_put_access_list,
    declToHOL Guest.Software.guestFn_tx_put_blob_hashes,
    declToHOL Guest.Software.guestFn_auth_payload_len,
    declToHOL Guest.Software.guestFn_auth_list_payload_len,
    declToHOL Guest.Software.guestFn_tx_put_authorizations,
    declToHOL Guest.Software.guestFn_tx_encode_bound,
    declToHOL Guest.Software.guestFn_tx_encode_generic,
    declToHOL Guest.Software.guestFn_encode_transaction,
    declToHOL Guest.Software.guestFn_get_transaction_hash,
    declToHOL Guest.Software.guestFn_tx_signing_hash_mode,
    declToHOL Guest.Software.guestFn_signing_hash_pre155,
    declToHOL Guest.Software.guestFn_signing_hash_155,
    declToHOL Guest.Software.guestFn_signing_hash_2930,
    declToHOL Guest.Software.guestFn_signing_hash_1559]

theorem chunk020_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0320 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk020 =
        some (state0336 s) := by
  cbv

end InitE.SourceWitness
