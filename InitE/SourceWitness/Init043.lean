import InitE.SourceWitness.Terms043
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0688 globals0688

def chunk043 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_bn254_g1_to_bytes,
    declToHOL Guest.Software.guestFn_bn254_g1_add,
    declToHOL Guest.Software.guestFn_bn254_g1_mul,
    declToHOL Guest.Software.guestFn_bn254_pairing_check,
    declToHOL Guest.Software.guestFn_pre_alt_bn128_add,
    declToHOL Guest.Software.guestFn_pre_alt_bn128_mul,
    declToHOL Guest.Software.guestFn_pre_alt_bn128_pairing_check,
    declToHOL Guest.Software.guestGlobal_bls_c,
    declToHOL Guest.Software.guestFn_bls_consts_init,
    declToHOL Guest.Software.guestFn_bls_fp_is_zero,
    declToHOL Guest.Software.guestFn_bls_fp_eq,
    declToHOL Guest.Software.guestFn_bls_fp_lt_raw,
    declToHOL Guest.Software.guestFn_bls_fp_add_raw,
    declToHOL Guest.Software.guestFn_bls_fp_sub_raw,
    declToHOL Guest.Software.guestFn_bls_fp_add,
    declToHOL Guest.Software.guestFn_bls_fp_sub]

theorem chunk043_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0688 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk043 =
        some (state0704 s) := by
  cbv

end InitE.SourceWitness
