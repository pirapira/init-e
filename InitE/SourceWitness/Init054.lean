import InitE.SourceWitness.Terms054
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0864 globals0864

def chunk054 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_payload_header,
    declToHOL Guest.Software.guestFn_tx_is_blob,
    declToHOL Guest.Software.guestFn_tx_is_setcode,
    declToHOL Guest.Software.guestFn_fee_mul,
    declToHOL Guest.Software.guestFn_is_valid_versioned_hashes,
    declToHOL Guest.Software.guestFn_te_new,
    declToHOL Guest.Software.guestFn_process_unchecked_system_transaction,
    declToHOL Guest.Software.guestFn_process_checked_system_transaction,
    declToHOL Guest.Software.guestFn_check_transaction,
    declToHOL Guest.Software.guestFn_process_transaction,
    declToHOL Guest.Software.guestFn_udiv_small5,
    declToHOL Guest.Software.guestFn_process_withdrawals,
    declToHOL Guest.Software.guestFn_requests_append,
    declToHOL Guest.Software.guestFn_process_general_purpose_requests,
    declToHOL Guest.Software.guestFn_execute_block,
    declToHOL Guest.Software.guestFn_run_attempt]

theorem chunk054_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0864 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk054 =
        some (state0880 s) := by
  cbv

end InitE.SourceWitness
