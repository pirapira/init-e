import InitE.SourceWitness.Terms033
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0528 globals0528

def chunk033 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_op_sstore,
    declToHOL Guest.Software.guestFn_op_tload,
    declToHOL Guest.Software.guestFn_op_tstore,
    declToHOL Guest.Software.guestFn_op_address,
    declToHOL Guest.Software.guestFn_op_balance,
    declToHOL Guest.Software.guestFn_op_origin,
    declToHOL Guest.Software.guestFn_op_caller,
    declToHOL Guest.Software.guestFn_op_callvalue,
    declToHOL Guest.Software.guestFn_op_calldataload,
    declToHOL Guest.Software.guestFn_op_calldatasize,
    declToHOL Guest.Software.guestFn_copy_from_buffer,
    declToHOL Guest.Software.guestFn_op_calldatacopy,
    declToHOL Guest.Software.guestFn_op_codesize,
    declToHOL Guest.Software.guestFn_op_codecopy,
    declToHOL Guest.Software.guestFn_op_gasprice,
    declToHOL Guest.Software.guestFn_ext_code_of]

theorem chunk033_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0528 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk033 =
        some (state0544 s) := by
  cbv

end InitE.SourceWitness
