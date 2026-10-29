import InitE.SourceWitness.Terms028
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0448 globals0448

def chunk028 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_charge_gas,
    declToHOL Guest.Software.guestFn_charge_state_gas,
    declToHOL Guest.Software.guestFn_credit_state_gas_refund,
    declToHOL Guest.Software.guestFn_frame_state_gas_used,
    declToHOL Guest.Software.guestFn_refill_frame_state_gas,
    declToHOL Guest.Software.guestFn_stack_pop,
    declToHOL Guest.Software.guestFn_stack_push,
    declToHOL Guest.Software.guestFn_stack_push_word,
    declToHOL Guest.Software.guestFn_stack_push_bool,
    declToHOL Guest.Software.guestFn_memory_gas_cost,
    declToHOL Guest.Software.guestFn_extend_memory_cost1,
    declToHOL Guest.Software.guestFn_extend_memory_cost2,
    declToHOL Guest.Software.guestFn_extend_memory,
    declToHOL Guest.Software.guestFn_charge_with_memory,
    declToHOL Guest.Software.guestFn_buffer_read,
    declToHOL Guest.Software.guestFn_compute_jumpdests]

theorem chunk028_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0448 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk028 =
        some (state0464 s) := by
  cbv

end InitE.SourceWitness
