import InitE.SourceWitness.Terms038
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0608 globals0608

def chunk038 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestGlobal_rmd_tab,
    declToHOL Guest.Software.guestGlobal_rmd_x,
    declToHOL Guest.Software.guestGlobal_rmd_h,
    declToHOL Guest.Software.guestGlobal_rmd_pad,
    declToHOL Guest.Software.guestFn_ripemd160_init,
    declToHOL Guest.Software.guestFn_rmd_f,
    declToHOL Guest.Software.guestFn_rmd_k,
    declToHOL Guest.Software.guestFn_rmd_kp,
    declToHOL Guest.Software.guestFn_ripemd160_block,
    declToHOL Guest.Software.guestFn_ripemd160,
    declToHOL Guest.Software.guestGlobal_b2_sigma,
    declToHOL Guest.Software.guestGlobal_b2_iv,
    declToHOL Guest.Software.guestGlobal_b2_v,
    declToHOL Guest.Software.guestFn_blake2_init,
    declToHOL Guest.Software.guestFn_blake2_g,
    declToHOL Guest.Software.guestFn_blake2b_f]

theorem chunk038_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0608 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk038 =
        some (state0624 s) := by
  cbv

end InitE.SourceWitness
