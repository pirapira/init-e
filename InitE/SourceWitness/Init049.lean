import InitE.SourceWitness.Terms049
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0784 globals0784

def chunk049 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_pair_ell,
    declToHOL Guest.Software.guestFn_pair_miller_loop,
    declToHOL Guest.Software.guestFn_pair_accumulate,
    declToHOL Guest.Software.guestFn_swu_sqrt_division_fp,
    declToHOL Guest.Software.guestFn_swu_g1,
    declToHOL Guest.Software.guestFn_iso_horner_fp,
    declToHOL Guest.Software.guestFn_iso_map_g1,
    declToHOL Guest.Software.guestFn_map_fp_to_g1,
    declToHOL Guest.Software.guestFn_swu_sqrt_division_fp2,
    declToHOL Guest.Software.guestFn_swu_g2,
    declToHOL Guest.Software.guestFn_iso_horner_fp2,
    declToHOL Guest.Software.guestFn_iso_map_g2,
    declToHOL Guest.Software.guestFn_map_fp2_to_g2,
    declToHOL Guest.Software.guestFn_kzg_decompress_g1,
    declToHOL Guest.Software.guestFn_kzg_load_g1,
    declToHOL Guest.Software.guestFn_kzg_neg_scalar]

theorem chunk049_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0784 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk049 =
        some (state0800 s) := by
  cbv

end InitE.SourceWitness
