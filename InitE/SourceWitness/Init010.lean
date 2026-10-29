import InitE.SourceWitness.Terms010
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0160 globals0160

def chunk010 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_fp_inv,
    declToHOL Guest.Software.guestFn_fp_sqrt,
    declToHOL Guest.Software.guestFn_fn_mul,
    declToHOL Guest.Software.guestFn_fn_add,
    declToHOL Guest.Software.guestFn_fn_pow,
    declToHOL Guest.Software.guestFn_fn_inv_fermat,
    declToHOL Guest.Software.guestFn_fn_inv,
    declToHOL Guest.Software.guestFn_ec_set_infinity,
    declToHOL Guest.Software.guestFn_ec_set_affine,
    declToHOL Guest.Software.guestFn_ec_is_infinity,
    declToHOL Guest.Software.guestFn_ec_double,
    declToHOL Guest.Software.guestFn_ec_add_affine,
    declToHOL Guest.Software.guestFn_ec_add,
    declToHOL Guest.Software.guestFn_ec_mul,
    declToHOL Guest.Software.guestFn_ec_mul2,
    declToHOL Guest.Software.guestFn_ec_to_affine]

theorem chunk010_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0160 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk010 =
        some (state0176 s) := by
  cbv

end InitE.SourceWitness
