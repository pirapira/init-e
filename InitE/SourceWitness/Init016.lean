import InitE.SourceWitness.Terms016
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0256 globals0256

def chunk016 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_node_new_leaf,
    declToHOL Guest.Software.guestFn_node_new_ext,
    declToHOL Guest.Software.guestFn_node_new_branch,
    declToHOL Guest.Software.guestFn_node_invalidate,
    declToHOL Guest.Software.guestFn__resolve_step,
    declToHOL Guest.Software.guestFn__decode_step,
    declToHOL Guest.Software.guestFn__decode_witness_node_body,
    declToHOL Guest.Software.guestFn__decode_witness_node_mpt,
    declToHOL Guest.Software.guestFn__decode_witness_node,
    declToHOL Guest.Software.guestFn_decode_witness_to_mpt,
    declToHOL Guest.Software.guestFn_trie_walk,
    declToHOL Guest.Software.guestFn_trie_lookup,
    declToHOL Guest.Software.guestFn_mpt_new,
    declToHOL Guest.Software.guestFn_mpt_from_witness,
    declToHOL Guest.Software.guestFn_mpt_nibble_key,
    declToHOL Guest.Software.guestFn_mpt_get]

theorem chunk016_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0256 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk016 =
        some (state0272 s) := by
  cbv

end InitE.SourceWitness
