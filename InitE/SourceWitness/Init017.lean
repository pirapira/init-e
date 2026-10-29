import InitE.SourceWitness.Terms017
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0272 globals0272

def chunk017 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn__create_branch_from_two_leaves,
    declToHOL Guest.Software.guestFn__insert_into_leaf,
    declToHOL Guest.Software.guestFn__split_extension,
    declToHOL Guest.Software.guestFn__mpt_insert_node,
    declToHOL Guest.Software.guestFn__collapse_branch,
    declToHOL Guest.Software.guestFn__delete_ext_finish,
    declToHOL Guest.Software.guestFn__mpt_delete_node_body,
    declToHOL Guest.Software.guestFn__mpt_delete_node,
    declToHOL Guest.Software.guestFn_mpt_set,
    declToHOL Guest.Software.guestFn__node_rlp_begin,
    declToHOL Guest.Software.guestFn__node_rlp_finish,
    declToHOL Guest.Software.guestFn__node_needs_rlp,
    declToHOL Guest.Software.guestFn__node_rlp_fill,
    declToHOL Guest.Software.guestFn_node_rlp,
    declToHOL Guest.Software.guestFn_rlp_value_encoded_len,
    declToHOL Guest.Software.guestFn_node_ref_len]

theorem chunk017_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0272 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk017 =
        some (state0288 s) := by
  cbv

end InitE.SourceWitness
