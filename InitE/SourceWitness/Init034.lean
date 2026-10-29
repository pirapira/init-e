import InitE.SourceWitness.Terms034
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0544 globals0544

def chunk034 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_op_extcodesize,
    declToHOL Guest.Software.guestFn_op_extcodecopy,
    declToHOL Guest.Software.guestFn_op_returndatasize,
    declToHOL Guest.Software.guestFn_op_returndatacopy,
    declToHOL Guest.Software.guestFn_op_extcodehash,
    declToHOL Guest.Software.guestFn_op_selfbalance,
    declToHOL Guest.Software.guestFn_block_env,
    declToHOL Guest.Software.guestFn_op_basefee,
    declToHOL Guest.Software.guestFn_op_blobhash,
    declToHOL Guest.Software.guestFn_op_blobbasefee,
    declToHOL Guest.Software.guestFn_op_blockhash,
    declToHOL Guest.Software.guestFn_op_coinbase,
    declToHOL Guest.Software.guestFn_op_timestamp,
    declToHOL Guest.Software.guestFn_op_number,
    declToHOL Guest.Software.guestFn_op_gaslimit,
    declToHOL Guest.Software.guestFn_op_chainid]

theorem chunk034_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0544 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk034 =
        some (state0560 s) := by
  cbv

end InitE.SourceWitness
