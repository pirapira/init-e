import InitE.SourceWitness.Terms035
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0560 globals0560

def chunk035 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_op_prevrandao,
    declToHOL Guest.Software.guestFn_op_slotnum,
    declToHOL Guest.Software.guestGlobal_cur_cont,
    declToHOL Guest.Software.guestGlobal_transfer_topic,
    declToHOL Guest.Software.guestGlobal_vm_system_address,
    declToHOL Guest.Software.guestGlobal_null_address,
    declToHOL Guest.Software.guestFn_evm_init,
    declToHOL Guest.Software.guestFn_emit_transfer_log,
    declToHOL Guest.Software.guestFn_op_return,
    declToHOL Guest.Software.guestFn_op_revert,
    declToHOL Guest.Software.guestFn_op_selfdestruct,
    declToHOL Guest.Software.guestFn_get_delegated_code_address,
    declToHOL Guest.Software.guestFn_recover_authority,
    declToHOL Guest.Software.guestFn_calculate_delegation_cost,
    declToHOL Guest.Software.guestFn_validate_authorization_checks,
    declToHOL Guest.Software.guestFn_set_delegation]

theorem chunk035_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0560 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk035 =
        some (state0576 s) := by
  cbv

end InitE.SourceWitness
