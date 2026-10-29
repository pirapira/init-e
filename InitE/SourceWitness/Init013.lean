import InitE.SourceWitness.Terms013
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0208 globals0208

def chunk013 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_htr_withdrawal,
    declToHOL Guest.Software.guestFn_htr_list_roots,
    declToHOL Guest.Software.guestFn_htr_payload,
    declToHOL Guest.Software.guestFn_htr_deposit,
    declToHOL Guest.Software.guestFn_htr_wdreq,
    declToHOL Guest.Software.guestFn_htr_cons,
    declToHOL Guest.Software.guestFn_htr_bdep,
    declToHOL Guest.Software.guestFn_htr_bexit,
    declToHOL Guest.Software.guestFn_htr_request_list,
    declToHOL Guest.Software.guestFn_htr_requests,
    declToHOL Guest.Software.guestFn_htr_new_payload_request,
    declToHOL Guest.Software.guestFn_serialize_result,
    declToHOL Guest.Software.guestExn_HdrErr,
    declToHOL Guest.Software.guestExn_BlockErr,
    declToHOL Guest.Software.guestFn_hdr_uint_field,
    declToHOL Guest.Software.guestFn_hdr_word_field]

theorem chunk013_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0208 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk013 =
        some (state0224 s) := by
  cbv

end InitE.SourceWitness
