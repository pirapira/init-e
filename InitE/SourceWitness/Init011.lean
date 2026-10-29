import InitE.SourceWitness.Terms011
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0176 globals0176

def chunk011 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_ec_on_curve,
    declToHOL Guest.Software.guestFn_secp256k1_decompress_r,
    declToHOL Guest.Software.guestFn_secp256k1_recover,
    declToHOL Guest.Software.guestFn_secp256k1_address_of_point,
    declToHOL Guest.Software.guestFn_secp256k1_ecrecover,
    declToHOL Guest.Software.guestExn_SszErr,
    declToHOL Guest.Software.guestGlobal_zero_hashes,
    declToHOL Guest.Software.guestGlobal_ssz_len_chunk,
    declToHOL Guest.Software.guestGlobal_ssz_offs,
    declToHOL Guest.Software.guestFn_ssz_init,
    declToHOL Guest.Software.guestFn_merkleize,
    declToHOL Guest.Software.guestFn_mix_in_length,
    declToHOL Guest.Software.guestFn_merkleize_progressive,
    declToHOL Guest.Software.guestFn_htr_plist_chunks,
    declToHOL Guest.Software.guestFn_htr_pbytes,
    declToHOL Guest.Software.guestFn_htr_pcontainer]

theorem chunk011_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0176 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk011 =
        some (state0192 s) := by
  cbv

end InitE.SourceWitness
