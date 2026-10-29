import InitE.SourceWitness.Terms037
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0592 globals0592

def chunk037 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_incorporate_child_on_success,
    declToHOL Guest.Software.guestFn_rollback_child_access,
    declToHOL Guest.Software.guestFn_child_message,
    declToHOL Guest.Software.guestFn_set_retdata,
    declToHOL Guest.Software.guestFn_compute_contract_address,
    declToHOL Guest.Software.guestFn_compute_create2_contract_address,
    declToHOL Guest.Software.guestFn_generic_create,
    declToHOL Guest.Software.guestFn_op_create,
    declToHOL Guest.Software.guestFn_op_create2,
    declToHOL Guest.Software.guestFn_generic_call,
    declToHOL Guest.Software.guestFn_calculate_message_call_gas,
    declToHOL Guest.Software.guestFn_op_call,
    declToHOL Guest.Software.guestFn_op_callcode,
    declToHOL Guest.Software.guestFn_op_delegatecall,
    declToHOL Guest.Software.guestFn_op_staticcall,
    declToHOL Guest.Software.guestFn_process_message_call]

theorem chunk037_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0592 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk037 =
        some (state0608 s) := by
  cbv

end InitE.SourceWitness
