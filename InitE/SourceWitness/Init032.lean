import InitE.SourceWitness.Terms032
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0512 globals0512

def chunk032 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_op_mcopy,
    declToHOL Guest.Software.guestFn_op_pop,
    declToHOL Guest.Software.guestFn_op_push,
    declToHOL Guest.Software.guestFn_op_dup,
    declToHOL Guest.Software.guestFn_stack_swap_positions,
    declToHOL Guest.Software.guestFn_op_swap,
    declToHOL Guest.Software.guestFn_code_imm,
    declToHOL Guest.Software.guestFn_decode_single,
    declToHOL Guest.Software.guestFn_op_dupn,
    declToHOL Guest.Software.guestFn_op_swapn,
    declToHOL Guest.Software.guestFn_op_exchange,
    declToHOL Guest.Software.guestFn_log_append,
    declToHOL Guest.Software.guestFn_op_log,
    declToHOL Guest.Software.guestFn_is_warm_storage_key,
    declToHOL Guest.Software.guestFn_warm_storage_key,
    declToHOL Guest.Software.guestFn_op_sload]

theorem chunk032_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0512 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk032 =
        some (state0528 s) := by
  cbv

end InitE.SourceWitness
