import InitE.SourceWitness.Terms042
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0672 globals0672

def chunk042 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_ecp_is_inf,
    declToHOL Guest.Software.guestFn_ecp_double,
    declToHOL Guest.Software.guestFn_ecp_add,
    declToHOL Guest.Software.guestFn_ecp_mul,
    declToHOL Guest.Software.guestFn_ecp_linefunc,
    declToHOL Guest.Software.guestFn_fq12_twist,
    declToHOL Guest.Software.guestFn_fq12_cast,
    declToHOL Guest.Software.guestFn_fq12_frob,
    declToHOL Guest.Software.guestFn_fq_poly_deg,
    declToHOL Guest.Software.guestFn_fq_poly_submul,
    declToHOL Guest.Software.guestFn_fq12_inv,
    declToHOL Guest.Software.guestFn_fq12_pow_words,
    declToHOL Guest.Software.guestFn_bn254_miller_raw,
    declToHOL Guest.Software.guestFn_bn254_pairing,
    declToHOL Guest.Software.guestFn_bn254_parse_g1,
    declToHOL Guest.Software.guestFn_bn254_parse_g2]

theorem chunk042_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0672 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk042 =
        some (state0688 s) := by
  cbv

end InitE.SourceWitness
