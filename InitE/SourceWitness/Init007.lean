import InitE.SourceWitness.Terms007
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0112 globals0112

def chunk007 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_rlp_item_total,
    declToHOL Guest.Software.guestFn_rlp_list_count,
    declToHOL Guest.Software.guestFn_rlp_item_total_unchecked,
    declToHOL Guest.Software.guestFn_rlp_list_to_slices,
    declToHOL Guest.Software.guestFn_rlp_bytes_to_word,
    declToHOL Guest.Software.guestFn_rlp_check_uint_bytes,
    declToHOL Guest.Software.guestFn_rlp_be_len,
    declToHOL Guest.Software.guestFn_rlp_put_be,
    declToHOL Guest.Software.guestFn_rlp_write_header,
    declToHOL Guest.Software.guestFn_rlp_header_len,
    declToHOL Guest.Software.guestFn_rlp_encode_bytes,
    declToHOL Guest.Software.guestFn_rlp_encode_word,
    declToHOL Guest.Software.guestFn_rlp_encode_list_header,
    declToHOL Guest.Software.guestFn_rlp_bytes_encoded_len,
    declToHOL Guest.Software.guestFn_rlp_list_header_len,
    declToHOL Guest.Software.guestFn_rlp_word_encoded_len]

theorem chunk007_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0112 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk007 =
        some (state0128 s) := by
  cbv

end InitE.SourceWitness
