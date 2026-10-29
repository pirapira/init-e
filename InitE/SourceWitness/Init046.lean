import InitE.SourceWitness.Terms046
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0736 globals0736

def chunk046 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_fp2_pow,
    declToHOL Guest.Software.guestFn_fp2_sgn0,
    declToHOL Guest.Software.guestFn_fp6_copy,
    declToHOL Guest.Software.guestFn_fp6_set_zero,
    declToHOL Guest.Software.guestFn_fp6_set_one,
    declToHOL Guest.Software.guestFn_fp6_add,
    declToHOL Guest.Software.guestFn_fp6_sub,
    declToHOL Guest.Software.guestFn_fp6_neg,
    declToHOL Guest.Software.guestFn_fp6_mul,
    declToHOL Guest.Software.guestFn_fp6_mul_v,
    declToHOL Guest.Software.guestFn_fp6_inv,
    declToHOL Guest.Software.guestFn_fp12_copy,
    declToHOL Guest.Software.guestFn_fp12_set_one,
    declToHOL Guest.Software.guestFn_fp12_is_one,
    declToHOL Guest.Software.guestFn_fp12_mul,
    declToHOL Guest.Software.guestFn_fp12_sqr]

theorem chunk046_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0736 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk046 =
        some (state0752 s) := by
  cbv

end InitE.SourceWitness
