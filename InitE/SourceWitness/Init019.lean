import InitE.SourceWitness.Terms019
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0304 globals0304

def chunk019 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_decode_blob_hashes,
    declToHOL Guest.Software.guestFn_decode_authorizations,
    declToHOL Guest.Software.guestFn_decode_transaction_rlp,
    declToHOL Guest.Software.guestFn_decode_transaction,
    declToHOL Guest.Software.guestFn_tx_gas,
    declToHOL Guest.Software.guestFn_tx_nonce,
    declToHOL Guest.Software.guestFn_tx_to,
    declToHOL Guest.Software.guestFn_tx_value,
    declToHOL Guest.Software.guestFn_tx_data,
    declToHOL Guest.Software.guestFn_tx_r,
    declToHOL Guest.Software.guestFn_tx_s,
    declToHOL Guest.Software.guestFn_tx_has_access_list,
    declToHOL Guest.Software.guestFn_tx_blob_count,
    declToHOL Guest.Software.guestFn_calculate_total_blob_gas,
    declToHOL Guest.Software.guestFn_tx_put_u256,
    declToHOL Guest.Software.guestFn_tx_u256_encoded_len]

theorem chunk019_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0304 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk019 =
        some (state0320 s) := by
  cbv

end InitE.SourceWitness
