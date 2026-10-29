import InitE.SourceWitness.Terms041
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0656 globals0656

def chunk041 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_fq_mul_small,
    declToHOL Guest.Software.guestFn_fq2_mul,
    declToHOL Guest.Software.guestFn_fq12_reduce,
    declToHOL Guest.Software.guestFn_fq12_mul,
    declToHOL Guest.Software.guestFn_fq12_sqr,
    declToHOL Guest.Software.guestFn_fe_mul,
    declToHOL Guest.Software.guestFn_fe_sqr,
    declToHOL Guest.Software.guestFn_fe_add,
    declToHOL Guest.Software.guestFn_fe_sub,
    declToHOL Guest.Software.guestFn_fe_neg,
    declToHOL Guest.Software.guestFn_fe_mul_small,
    declToHOL Guest.Software.guestFn_fe_is_zero,
    declToHOL Guest.Software.guestFn_fe_eq,
    declToHOL Guest.Software.guestFn_fe_set_zero,
    declToHOL Guest.Software.guestFn_fe_set_one,
    declToHOL Guest.Software.guestFn_ecp_set_inf]

theorem chunk041_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0656 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk041 =
        some (state0672 s) := by
  cbv

end InitE.SourceWitness
