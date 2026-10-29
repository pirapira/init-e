import InitE.SourceWitness.Terms005
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0080 globals0080

def chunk005 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_u256_exp,
    declToHOL Guest.Software.guestFn_u256_shl,
    declToHOL Guest.Software.guestFn_u256_shr,
    declToHOL Guest.Software.guestFn_u256_sar,
    declToHOL Guest.Software.guestFn_u256_signextend,
    declToHOL Guest.Software.guestFn_u256_byte,
    declToHOL Guest.Software.guestFn_u256_from_be,
    declToHOL Guest.Software.guestFn_u256_to_be32,
    declToHOL Guest.Software.guestFn_u256_to_be_min,
    declToHOL Guest.Software.guestGlobal_sha_st,
    declToHOL Guest.Software.guestGlobal_sha_pad,
    declToHOL Guest.Software.guestFn_sha256_init,
    declToHOL Guest.Software.guestFn_sha256_state_init,
    declToHOL Guest.Software.guestFn_sha256_block,
    declToHOL Guest.Software.guestFn_sha256_finish,
    declToHOL Guest.Software.guestFn_sha256]

theorem chunk005_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0080 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk005 =
        some (state0096 s) := by
  cbv

end InitE.SourceWitness
