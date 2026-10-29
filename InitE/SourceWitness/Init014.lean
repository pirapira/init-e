import InitE.SourceWitness.Terms014
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0224 globals0224

def chunk014 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_hdr_u256_field,
    declToHOL Guest.Software.guestFn_hdr_bytes_field,
    declToHOL Guest.Software.guestFn_hdr_raw_field,
    declToHOL Guest.Software.guestFn_decode_header,
    declToHOL Guest.Software.guestFn_rlp_put_u256,
    declToHOL Guest.Software.guestFn_encode_header,
    declToHOL Guest.Software.guestFn_header_hash,
    declToHOL Guest.Software.guestFn_validate_headers,
    declToHOL Guest.Software.guestFn_taylor_exponential,
    declToHOL Guest.Software.guestFn_calculate_blob_gas_price,
    declToHOL Guest.Software.guestFn_calculate_excess_blob_gas,
    declToHOL Guest.Software.guestFn_check_gas_limit,
    declToHOL Guest.Software.guestFn_calculate_base_fee_per_gas,
    declToHOL Guest.Software.guestGlobal_hdr_zero8,
    declToHOL Guest.Software.guestFn_header_init,
    declToHOL Guest.Software.guestFn_validate_header]

theorem chunk014_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0224 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk014 =
        some (state0240 s) := by
  cbv

end InitE.SourceWitness
