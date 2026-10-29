import InitE.SourceWitness.Terms050
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0800 globals0800

def chunk050 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_kzg_verify,
    declToHOL Guest.Software.guestFn_bls_lib_init,
    declToHOL Guest.Software.guestFn_bls_g1_add_exec,
    declToHOL Guest.Software.guestFn_bls_g1_msm_exec,
    declToHOL Guest.Software.guestFn_bls_g2_add_exec,
    declToHOL Guest.Software.guestFn_bls_g2_msm_exec,
    declToHOL Guest.Software.guestFn_bls_pairing_exec,
    declToHOL Guest.Software.guestFn_bls_map_fp_to_g1_exec,
    declToHOL Guest.Software.guestFn_bls_map_fp2_to_g2_exec,
    declToHOL Guest.Software.guestFn_kzg_point_evaluation_exec,
    declToHOL Guest.Software.guestGlobal_bls_discount,
    declToHOL Guest.Software.guestFn_bls_precompiles_init,
    declToHOL Guest.Software.guestFn_bls_g1_msm_discount,
    declToHOL Guest.Software.guestFn_bls_g2_msm_discount,
    declToHOL Guest.Software.guestFn_pre_bls_g1_add,
    declToHOL Guest.Software.guestFn_pre_bls_g1_msm]

theorem chunk050_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0800 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk050 =
        some (state0816 s) := by
  cbv

end InitE.SourceWitness
