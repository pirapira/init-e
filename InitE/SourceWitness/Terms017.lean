import InitE.SourceWitness.Terms016
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0273 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__create_branch_from_two_leaves) code0272
def globals0273 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__create_branch_from_two_leaves) globals0272
def exceptions0273 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__create_branch_from_two_leaves) exceptions0272
def code0274 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__insert_into_leaf) code0273
def globals0274 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__insert_into_leaf) globals0273
def exceptions0274 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__insert_into_leaf) exceptions0273
def code0275 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__split_extension) code0274
def globals0275 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__split_extension) globals0274
def exceptions0275 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__split_extension) exceptions0274
def code0276 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__mpt_insert_node) code0275
def globals0276 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__mpt_insert_node) globals0275
def exceptions0276 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__mpt_insert_node) exceptions0275
def code0277 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__collapse_branch) code0276
def globals0277 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__collapse_branch) globals0276
def exceptions0277 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__collapse_branch) exceptions0276
def code0278 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__delete_ext_finish) code0277
def globals0278 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__delete_ext_finish) globals0277
def exceptions0278 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__delete_ext_finish) exceptions0277
def code0279 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__mpt_delete_node_body) code0278
def globals0279 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__mpt_delete_node_body) globals0278
def exceptions0279 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__mpt_delete_node_body) exceptions0278
def code0280 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__mpt_delete_node) code0279
def globals0280 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__mpt_delete_node) globals0279
def exceptions0280 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__mpt_delete_node) exceptions0279
def code0281 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_mpt_set) code0280
def globals0281 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_mpt_set) globals0280
def exceptions0281 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_mpt_set) exceptions0280
def code0282 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__node_rlp_begin) code0281
def globals0282 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__node_rlp_begin) globals0281
def exceptions0282 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__node_rlp_begin) exceptions0281
def code0283 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__node_rlp_finish) code0282
def globals0283 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__node_rlp_finish) globals0282
def exceptions0283 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__node_rlp_finish) exceptions0282
def code0284 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__node_needs_rlp) code0283
def globals0284 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__node_needs_rlp) globals0283
def exceptions0284 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__node_needs_rlp) exceptions0283
def code0285 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__node_rlp_fill) code0284
def globals0285 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__node_rlp_fill) globals0284
def exceptions0285 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__node_rlp_fill) exceptions0284
def code0286 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_node_rlp) code0285
def globals0286 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_node_rlp) globals0285
def exceptions0286 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_node_rlp) exceptions0285
def code0287 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rlp_value_encoded_len) code0286
def globals0287 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rlp_value_encoded_len) globals0286
def exceptions0287 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rlp_value_encoded_len) exceptions0286
def code0288 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_node_ref_len) code0287
def globals0288 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_node_ref_len) globals0287
def exceptions0288 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_node_ref_len) exceptions0287

def state0288 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0288
    code := code0288
    eshapes := exceptions0288
    structs := [] }

end InitE.SourceWitness
