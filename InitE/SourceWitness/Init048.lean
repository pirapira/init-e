import InitE.SourceWitness.Terms048
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0768 globals0768

def chunk048 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_g1_encode,
    declToHOL Guest.Software.guestFn_g1_subgroup_check,
    declToHOL Guest.Software.guestFn_g2_set_inf,
    declToHOL Guest.Software.guestFn_g2_is_inf,
    declToHOL Guest.Software.guestFn_g2_copy,
    declToHOL Guest.Software.guestFn_g2_neg,
    declToHOL Guest.Software.guestFn_g2_double,
    declToHOL Guest.Software.guestFn_g2_add,
    declToHOL Guest.Software.guestFn_g2_mul,
    declToHOL Guest.Software.guestFn_g2_normalize,
    declToHOL Guest.Software.guestFn_g2_on_curve,
    declToHOL Guest.Software.guestFn_g2_decode,
    declToHOL Guest.Software.guestFn_g2_encode,
    declToHOL Guest.Software.guestFn_g2_subgroup_check,
    declToHOL Guest.Software.guestFn_pair_doubling_step,
    declToHOL Guest.Software.guestFn_pair_addition_step]

theorem chunk048_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0768 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk048 =
        some (state0784 s) := by
  cbv

end InitE.SourceWitness
