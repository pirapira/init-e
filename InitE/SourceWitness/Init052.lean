import InitE.SourceWitness.Terms052
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0832 globals0832

def chunk052 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_logs_bloom,
    declToHOL Guest.Software.guestFn_rlp_finish_list,
    declToHOL Guest.Software.guestFn_logs_encoded_bound,
    declToHOL Guest.Software.guestFn_encode_logs,
    declToHOL Guest.Software.guestFn_encode_receipt,
    declToHOL Guest.Software.guestFn_withdrawal_rlp_len,
    declToHOL Guest.Software.guestFn_encode_withdrawal_rlp,
    declToHOL Guest.Software.guestFn_encode_execution_requests,
    declToHOL Guest.Software.guestFn_compute_requests_hash,
    declToHOL Guest.Software.guestFn_extract_deposit_data,
    declToHOL Guest.Software.guestFn_cache_get_root,
    declToHOL Guest.Software.guestFn_compute_state_root,
    declToHOL Guest.Software.guestExn_Fail,
    declToHOL Guest.Software.guestGlobal_be,
    declToHOL Guest.Software.guestGlobal_bo,
    declToHOL Guest.Software.guestGlobal_precompile_addrs]

theorem chunk052_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0832 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk052 =
        some (state0848 s) := by
  cbv

end InitE.SourceWitness
