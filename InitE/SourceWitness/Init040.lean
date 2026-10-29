import InitE.SourceWitness.Terms040
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0640 globals0640

def chunk040 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_p256_ec_add_affine,
    declToHOL Guest.Software.guestFn_p256_ec_mul2,
    declToHOL Guest.Software.guestFn_p256_ec_to_affine,
    declToHOL Guest.Software.guestFn_p256_on_curve,
    declToHOL Guest.Software.guestFn_p256_verify,
    declToHOL Guest.Software.guestFn_pre_p256verify,
    declToHOL Guest.Software.guestGlobal_bn_gamma,
    declToHOL Guest.Software.guestGlobal_bn_expw,
    declToHOL Guest.Software.guestFn_bn254_init,
    declToHOL Guest.Software.guestFn_fq_add,
    declToHOL Guest.Software.guestFn_fq_sub,
    declToHOL Guest.Software.guestFn_fq_neg,
    declToHOL Guest.Software.guestFn_fq_mul,
    declToHOL Guest.Software.guestFn_fq_to_mont,
    declToHOL Guest.Software.guestFn_fq_from_mont,
    declToHOL Guest.Software.guestFn_fq_inv]

theorem chunk040_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0640 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk040 =
        some (state0656 s) := by
  cbv

end InitE.SourceWitness
