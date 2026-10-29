import InitE.SourceWitness.Terms018
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0288 globals0288

def chunk018 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_node_hash_cached,
    declToHOL Guest.Software.guestFn_node_write_ref,
    declToHOL Guest.Software.guestFn_node_hash,
    declToHOL Guest.Software.guestFn_mpt_root,
    declToHOL Guest.Software.guestFn_build_mpt_indexed,
    declToHOL Guest.Software.guestFn_decode_account_from_leaf,
    declToHOL Guest.Software.guestFn_encode_account,
    declToHOL Guest.Software.guestExn_TxErr,
    declToHOL Guest.Software.guestFn_tx_scalar_item,
    declToHOL Guest.Software.guestFn_tx_scalar_u256,
    declToHOL Guest.Software.guestFn_tx_scalar_word,
    declToHOL Guest.Software.guestFn_tx_bytes_item,
    declToHOL Guest.Software.guestFn_tx_fixed_bytes,
    declToHOL Guest.Software.guestFn_tx_to_item,
    declToHOL Guest.Software.guestFn_tx_list_item,
    declToHOL Guest.Software.guestFn_decode_access_list]

theorem chunk018_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0288 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk018 =
        some (state0304 s) := by
  cbv

end InitE.SourceWitness
