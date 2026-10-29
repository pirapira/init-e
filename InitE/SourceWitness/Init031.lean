import InitE.SourceWitness.Terms031
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0496 globals0496

def chunk031 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_op_byte,
    declToHOL Guest.Software.guestFn_op_shl,
    declToHOL Guest.Software.guestFn_op_shr,
    declToHOL Guest.Software.guestFn_op_sar,
    declToHOL Guest.Software.guestFn_op_clz,
    declToHOL Guest.Software.guestFn_op_keccak,
    declToHOL Guest.Software.guestFn_op_stop,
    declToHOL Guest.Software.guestFn_op_jump,
    declToHOL Guest.Software.guestFn_op_jumpi,
    declToHOL Guest.Software.guestFn_op_pc,
    declToHOL Guest.Software.guestFn_op_gas,
    declToHOL Guest.Software.guestFn_op_jumpdest,
    declToHOL Guest.Software.guestFn_op_mstore,
    declToHOL Guest.Software.guestFn_op_mstore8,
    declToHOL Guest.Software.guestFn_op_mload,
    declToHOL Guest.Software.guestFn_op_msize]

theorem chunk031_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0496 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk031 =
        some (state0512 s) := by
  cbv

end InitE.SourceWitness
