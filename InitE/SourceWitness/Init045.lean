import InitE.SourceWitness.Terms045
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0720 globals0720

def chunk045 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_bls_fp_encode64,
    declToHOL Guest.Software.guestFn_fp2_copy,
    declToHOL Guest.Software.guestFn_fp2_set_zero,
    declToHOL Guest.Software.guestFn_fp2_set_one,
    declToHOL Guest.Software.guestFn_fp2_is_zero,
    declToHOL Guest.Software.guestFn_fp2_eq,
    declToHOL Guest.Software.guestFn_fp2_add,
    declToHOL Guest.Software.guestFn_fp2_sub,
    declToHOL Guest.Software.guestFn_fp2_neg,
    declToHOL Guest.Software.guestFn_fp2_dbl,
    declToHOL Guest.Software.guestFn_fp2_conj,
    declToHOL Guest.Software.guestFn_fp2_mul,
    declToHOL Guest.Software.guestFn_fp2_sqr,
    declToHOL Guest.Software.guestFn_fp2_mul_xi,
    declToHOL Guest.Software.guestFn_fp2_scale,
    declToHOL Guest.Software.guestFn_fp2_inv]

theorem chunk045_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0720 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk045 =
        some (state0736 s) := by
  cbv

end InitE.SourceWitness
