import InitE.SourceWitness.Terms004
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0064 globals0064

def chunk004 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_u256_to_digits,
    declToHOL Guest.Software.guestFn_digits_to_u256,
    declToHOL Guest.Software.guestFn_digits_len,
    declToHOL Guest.Software.guestFn_divmnu,
    declToHOL Guest.Software.guestFn_digits_divmod,
    declToHOL Guest.Software.guestFn_u256_divmod,
    declToHOL Guest.Software.guestFn_u256_div,
    declToHOL Guest.Software.guestFn_u256_mod,
    declToHOL Guest.Software.guestFn_u256_abs,
    declToHOL Guest.Software.guestFn_u256_sdiv,
    declToHOL Guest.Software.guestFn_u256_smod,
    declToHOL Guest.Software.guestFn_u256_addmod,
    declToHOL Guest.Software.guestFn_u256_mulmod,
    declToHOL Guest.Software.guestFn_bit_length64,
    declToHOL Guest.Software.guestFn_u256_bit_length,
    declToHOL Guest.Software.guestFn_u256_byte_length]

theorem chunk004_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0064 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk004 =
        some (state0080 s) := by
  cbv

end InitE.SourceWitness
