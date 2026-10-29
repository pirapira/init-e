import InitE.SourceWitness.Terms051
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0816 globals0816

def chunk051 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_pre_bls_g2_add,
    declToHOL Guest.Software.guestFn_pre_bls_g2_msm,
    declToHOL Guest.Software.guestFn_pre_bls_pairing,
    declToHOL Guest.Software.guestFn_pre_bls_map_fp_to_g1,
    declToHOL Guest.Software.guestFn_pre_bls_map_fp2_to_g2,
    declToHOL Guest.Software.guestFn_pre_kzg_point_evaluation,
    declToHOL Guest.Software.guestFn_precompile_index,
    declToHOL Guest.Software.guestFn_pre_identity,
    declToHOL Guest.Software.guestFn_pre_sha256,
    declToHOL Guest.Software.guestFn_pre_ecrecover,
    declToHOL Guest.Software.guestFn_pre_ripemd160,
    declToHOL Guest.Software.guestFn_pre_blake2f,
    declToHOL Guest.Software.guestFn_modexp_gas,
    declToHOL Guest.Software.guestFn_pre_modexp,
    declToHOL Guest.Software.guestFn_run_precompile,
    declToHOL Guest.Software.guestFn_add_to_bloom]

theorem chunk051_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0816 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk051 =
        some (state0832 s) := by
  cbv

end InitE.SourceWitness
