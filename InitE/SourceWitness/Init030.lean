import InitE.SourceWitness.Terms030
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0480 globals0480

def chunk030 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_op_mod,
    declToHOL Guest.Software.guestFn_op_smod,
    declToHOL Guest.Software.guestFn_op_addmod,
    declToHOL Guest.Software.guestFn_op_mulmod,
    declToHOL Guest.Software.guestFn_op_exp,
    declToHOL Guest.Software.guestFn_op_signextend,
    declToHOL Guest.Software.guestFn_op_lt,
    declToHOL Guest.Software.guestFn_op_gt,
    declToHOL Guest.Software.guestFn_op_slt,
    declToHOL Guest.Software.guestFn_op_sgt,
    declToHOL Guest.Software.guestFn_op_eq,
    declToHOL Guest.Software.guestFn_op_iszero,
    declToHOL Guest.Software.guestFn_op_and,
    declToHOL Guest.Software.guestFn_op_or,
    declToHOL Guest.Software.guestFn_op_xor,
    declToHOL Guest.Software.guestFn_op_not]

theorem chunk030_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0480 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk030 =
        some (state0496 s) := by
  cbv

end InitE.SourceWitness
