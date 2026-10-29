import InitE.SourceWitness.Terms044
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0704 globals0704

def chunk044 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_bls_fp_neg,
    declToHOL Guest.Software.guestFn_bls_fp_dbl,
    declToHOL Guest.Software.guestFn_bls_fp_mul,
    declToHOL Guest.Software.guestFn_bls_fp_sqr,
    declToHOL Guest.Software.guestFn_bls_fp_to_mont,
    declToHOL Guest.Software.guestFn_bls_fp_from_mont,
    declToHOL Guest.Software.guestFn_bls_fp_shr1,
    declToHOL Guest.Software.guestFn_bls_fp_half_can,
    declToHOL Guest.Software.guestFn_bls_fp_inv_raw,
    declToHOL Guest.Software.guestFn_bls_fp_inv,
    declToHOL Guest.Software.guestFn_bls_fp_pow,
    declToHOL Guest.Software.guestFn_bls_fp_sgn0,
    declToHOL Guest.Software.guestFn_bls_fp_is_high,
    declToHOL Guest.Software.guestFn_bls_fp_from_be48,
    declToHOL Guest.Software.guestFn_bls_fp_to_be48,
    declToHOL Guest.Software.guestFn_bls_fp_decode64]

theorem chunk044_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0704 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk044 =
        some (state0720 s) := by
  cbv

end InitE.SourceWitness
