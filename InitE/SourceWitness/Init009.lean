import InitE.SourceWitness.Terms009
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0144 globals0144

def chunk009 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_htab_keys,
    declToHOL Guest.Software.guestFn_htab_copy,
    declToHOL Guest.Software.guestFn_htab_copy_scratch,
    declToHOL Guest.Software.guestGlobal_secp_accel_scratch,
    declToHOL Guest.Software.guestFn_secp256k1_init,
    declToHOL Guest.Software.guestFn_fp_add,
    declToHOL Guest.Software.guestFn_fp_sub,
    declToHOL Guest.Software.guestFn_fp_neg,
    declToHOL Guest.Software.guestFn_fp_reduce,
    declToHOL Guest.Software.guestFn_fp_mul,
    declToHOL Guest.Software.guestFn_fp_sqr,
    declToHOL Guest.Software.guestFn_fp_pow,
    declToHOL Guest.Software.guestFn_fp_inv_fermat,
    declToHOL Guest.Software.guestFn_modinv_bin,
    declToHOL Guest.Software.guestFn_mod_half,
    declToHOL Guest.Software.guestFn_mod_sub]

theorem chunk009_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0144 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk009 =
        some (state0160 s) := by
  cbv

end InitE.SourceWitness
