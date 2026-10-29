import InitE.SourceWitness.Terms015
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0240 globals0240

def chunk015 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestExn_MptErr,
    declToHOL Guest.Software.guestGlobal_empty_trie_root,
    declToHOL Guest.Software.guestGlobal_empty_code_hash,
    declToHOL Guest.Software.guestGlobal_mpt_nib_scratch,
    declToHOL Guest.Software.guestGlobal_mpt_hash_scratch,
    declToHOL Guest.Software.guestGlobal_mpt_key_scratch,
    declToHOL Guest.Software.guestFn_mpt_fail,
    declToHOL Guest.Software.guestFn_mpt_init,
    declToHOL Guest.Software.guestFn_key_to_nibbles,
    declToHOL Guest.Software.guestFn_compact_to_nibbles,
    declToHOL Guest.Software.guestFn_nibble_list_to_compact,
    declToHOL Guest.Software.guestFn_common_prefix_length,
    declToHOL Guest.Software.guestFn_nibbles_concat,
    declToHOL Guest.Software.guestFn_nodedb_build,
    declToHOL Guest.Software.guestFn_nodedb_lookup,
    declToHOL Guest.Software.guestFn_node_new_hashed]

theorem chunk015_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0240 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk015 =
        some (state0256 s) := by
  cbv

end InitE.SourceWitness
