import InitE.SourceWitness.Terms001
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0016 globals0016

def chunk001 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_memcpy,
    declToHOL Guest.Software.guestFn_memzero,
    declToHOL Guest.Software.guestFn_memeq,
    declToHOL Guest.Software.guestFn_is_zero_bytes,
    declToHOL Guest.Software.guestFn_ld_le32,
    declToHOL Guest.Software.guestFn_ld_le64,
    declToHOL Guest.Software.guestFn_ld_be32,
    declToHOL Guest.Software.guestFn_bswap64,
    declToHOL Guest.Software.guestFn_ld_be64,
    declToHOL Guest.Software.guestFn_st_le32,
    declToHOL Guest.Software.guestFn_st_le64,
    declToHOL Guest.Software.guestFn_st_be32,
    declToHOL Guest.Software.guestFn_st_be64,
    declToHOL Guest.Software.guestFn_input_blob,
    declToHOL Guest.Software.guestFn_output_write,
    declToHOL Guest.Software.guestFn_min]

theorem chunk001_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0016 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk001 =
        some (state0032 s) := by
  cbv

end InitE.SourceWitness
