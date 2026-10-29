import InitE.SourceWitness.Terms029
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0464 globals0464

def chunk029 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_is_valid_jumpdest,
    declToHOL Guest.Software.guestFn_msg_new,
    declToHOL Guest.Software.guestFn_msg_new_scratch,
    declToHOL Guest.Software.guestFn_frame_new,
    declToHOL Guest.Software.guestFn_pc_add,
    declToHOL Guest.Software.guestFn_cur_msg,
    declToHOL Guest.Software.guestFn_require_not_static,
    declToHOL Guest.Software.guestFn_is_warm_address,
    declToHOL Guest.Software.guestFn_warm_address,
    declToHOL Guest.Software.guestFn_access_gas_cost,
    declToHOL Guest.Software.guestFn_warm_after_charge,
    declToHOL Guest.Software.guestFn_op_add,
    declToHOL Guest.Software.guestFn_op_mul,
    declToHOL Guest.Software.guestFn_op_sub,
    declToHOL Guest.Software.guestFn_op_div,
    declToHOL Guest.Software.guestFn_op_sdiv]

theorem chunk029_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0464 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk029 =
        some (state0480 s) := by
  cbv

end InitE.SourceWitness
