import InitE.SourceWitness.Terms003
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0048 globals0048

def chunk003 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_u256_slt,
    declToHOL Guest.Software.guestFn_u256_sgt,
    declToHOL Guest.Software.guestFn_u256_cmp,
    declToHOL Guest.Software.guestFn_u256_not,
    declToHOL Guest.Software.guestFn_u256_and,
    declToHOL Guest.Software.guestFn_u256_or,
    declToHOL Guest.Software.guestFn_u256_xor,
    declToHOL Guest.Software.guestFn_u256_add_carry,
    declToHOL Guest.Software.guestFn_u256_add,
    declToHOL Guest.Software.guestFn_u256_sub,
    declToHOL Guest.Software.guestFn_u256_neg,
    declToHOL Guest.Software.guestFn_mul64x64,
    declToHOL Guest.Software.guestFn_u256_mul,
    declToHOL Guest.Software.guestFn_u256_mul_full,
    declToHOL Guest.Software.guestFn_nlz32,
    declToHOL Guest.Software.guestFn_div64by32]

theorem chunk003_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0048 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk003 =
        some (state0064 s) := by
  cbv

end InitE.SourceWitness
