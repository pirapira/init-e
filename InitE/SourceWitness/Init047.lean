import InitE.SourceWitness.Terms047
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0752 globals0752

def chunk047 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_fp12_conj,
    declToHOL Guest.Software.guestFn_fp12_inv,
    declToHOL Guest.Software.guestFn_fp12_frob,
    declToHOL Guest.Software.guestFn_fp12_pow_absx,
    declToHOL Guest.Software.guestFn_fp12_exp_x,
    declToHOL Guest.Software.guestFn_fp12_final_exp,
    declToHOL Guest.Software.guestFn_g1_set_inf,
    declToHOL Guest.Software.guestFn_g1_is_inf,
    declToHOL Guest.Software.guestFn_g1_copy,
    declToHOL Guest.Software.guestFn_g1_neg,
    declToHOL Guest.Software.guestFn_g1_double,
    declToHOL Guest.Software.guestFn_g1_add,
    declToHOL Guest.Software.guestFn_g1_mul,
    declToHOL Guest.Software.guestFn_g1_normalize,
    declToHOL Guest.Software.guestFn_g1_on_curve,
    declToHOL Guest.Software.guestFn_g1_decode]

theorem chunk047_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0752 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk047 =
        some (state0768 s) := by
  cbv

end InitE.SourceWitness
