import InitE.SourceWitness.Terms012
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0192 globals0192

def chunk012 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_pack_bytes,
    declToHOL Guest.Software.guestFn_htr_bytes_vector,
    declToHOL Guest.Software.guestFn_htr_bytes_list,
    declToHOL Guest.Software.guestFn_htr_u64_at,
    declToHOL Guest.Software.guestFn_ssz_fail,
    declToHOL Guest.Software.guestFn_host_input_byte,
    declToHOL Guest.Software.guestFn_host_input_le32,
    declToHOL Guest.Software.guestFn_precheck_host_ssz_header,
    declToHOL Guest.Software.guestFn_decode_host_input,
    declToHOL Guest.Software.guestFn_ssz_check_offsets,
    declToHOL Guest.Software.guestFn_ssz_split_var_list,
    declToHOL Guest.Software.guestFn_ssz_fixed_list_count,
    declToHOL Guest.Software.guestFn_decode_payload,
    declToHOL Guest.Software.guestFn_decode_requests,
    declToHOL Guest.Software.guestFn_decode_bytes_list,
    declToHOL Guest.Software.guestFn_decode_stateless_input]

theorem chunk012_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0192 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk012 =
        some (state0208 s) := by
  cbv

end InitE.SourceWitness
