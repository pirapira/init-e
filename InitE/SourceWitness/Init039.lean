import InitE.SourceWitness.Terms039
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0624 globals0624

def chunk039 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_bn_from_be,
    declToHOL Guest.Software.guestFn_bn_to_be,
    declToHOL Guest.Software.guestFn_bn_mul,
    declToHOL Guest.Software.guestFn_bn_divmnu,
    declToHOL Guest.Software.guestFn_bn_mod,
    declToHOL Guest.Software.guestFn_be_top_bit,
    declToHOL Guest.Software.guestFn_modexp,
    declToHOL Guest.Software.guestFn_p256_fp_add,
    declToHOL Guest.Software.guestFn_p256_fp_sub,
    declToHOL Guest.Software.guestFn_p256_fp_reduce,
    declToHOL Guest.Software.guestFn_p256_fp_mul,
    declToHOL Guest.Software.guestFn_p256_fp_sqr,
    declToHOL Guest.Software.guestFn_p256_fp_inv,
    declToHOL Guest.Software.guestFn_p256_set_infinity,
    declToHOL Guest.Software.guestFn_p256_set_affine,
    declToHOL Guest.Software.guestFn_p256_ec_double]

theorem chunk039_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0624 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk039 =
        some (state0640 s) := by
  cbv

end InitE.SourceWitness
