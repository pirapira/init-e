import InitE.SourceWitness.Terms006
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0096 globals0096

def chunk006 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_sha256_pair,
    declToHOL Guest.Software.guestGlobal_keccak_rc,
    declToHOL Guest.Software.guestGlobal_keccak_st,
    declToHOL Guest.Software.guestGlobal_keccak_pad,
    declToHOL Guest.Software.guestFn_keccak_init,
    declToHOL Guest.Software.guestFn_keccak_f1600,
    declToHOL Guest.Software.guestFn_keccak_absorb_block,
    declToHOL Guest.Software.guestFn_keccak256,
    declToHOL Guest.Software.guestExn_RlpErr,
    declToHOL Guest.Software.guestFn_rlp_fail,
    declToHOL Guest.Software.guestFn_rlp_read_length,
    declToHOL Guest.Software.guestFn_rlp_item,
    declToHOL Guest.Software.guestFn_rlp_decode_fully,
    declToHOL Guest.Software.guestFn_rlp_item_header,
    declToHOL Guest.Software.guestFn__rlp_validate_items_body,
    declToHOL Guest.Software.guestFn_rlp_validate_items]

theorem chunk006_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0096 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk006 =
        some (state0112 s) := by
  cbv

end InitE.SourceWitness
