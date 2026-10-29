import InitE.SourceWitness.Terms002
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0032 globals0032

def chunk002 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_max,
    declToHOL Guest.Software.guestFn_udivmod,
    declToHOL Guest.Software.guestFn_udiv,
    declToHOL Guest.Software.guestFn_umod,
    declToHOL Guest.Software.guestFn_ceil_log2,
    declToHOL Guest.Software.guestGlobal_u256_ws,
    declToHOL Guest.Software.guestFn_u256_ws_init,
    declToHOL Guest.Software.guestFn_u256_from_word,
    declToHOL Guest.Software.guestFn_u256_low,
    declToHOL Guest.Software.guestFn_u256_fits_word,
    declToHOL Guest.Software.guestFn_u256_is_zero,
    declToHOL Guest.Software.guestFn_u256_limb,
    declToHOL Guest.Software.guestFn_u256_bit,
    declToHOL Guest.Software.guestFn_u256_eq,
    declToHOL Guest.Software.guestFn_u256_lt,
    declToHOL Guest.Software.guestFn_u256_gt]

theorem chunk002_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0032 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk002 =
        some (state0048 s) := by
  cbv

end InitE.SourceWitness
