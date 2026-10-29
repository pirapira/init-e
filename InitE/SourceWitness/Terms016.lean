import InitE.SourceWitness.Terms015
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0257 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_node_new_leaf) code0256
def globals0257 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_node_new_leaf) globals0256
def exceptions0257 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_node_new_leaf) exceptions0256
def code0258 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_node_new_ext) code0257
def globals0258 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_node_new_ext) globals0257
def exceptions0258 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_node_new_ext) exceptions0257
def code0259 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_node_new_branch) code0258
def globals0259 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_node_new_branch) globals0258
def exceptions0259 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_node_new_branch) exceptions0258
def code0260 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_node_invalidate) code0259
def globals0260 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_node_invalidate) globals0259
def exceptions0260 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_node_invalidate) exceptions0259
def code0261 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__resolve_step) code0260
def globals0261 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__resolve_step) globals0260
def exceptions0261 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__resolve_step) exceptions0260
def code0262 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__decode_step) code0261
def globals0262 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__decode_step) globals0261
def exceptions0262 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__decode_step) exceptions0261
def code0263 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__decode_witness_node_body) code0262
def globals0263 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__decode_witness_node_body) globals0262
def exceptions0263 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__decode_witness_node_body) exceptions0262
def code0264 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__decode_witness_node_mpt) code0263
def globals0264 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__decode_witness_node_mpt) globals0263
def exceptions0264 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__decode_witness_node_mpt) exceptions0263
def code0265 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__decode_witness_node) code0264
def globals0265 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__decode_witness_node) globals0264
def exceptions0265 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__decode_witness_node) exceptions0264
def code0266 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_decode_witness_to_mpt) code0265
def globals0266 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_decode_witness_to_mpt) globals0265
def exceptions0266 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_decode_witness_to_mpt) exceptions0265
def code0267 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_trie_walk) code0266
def globals0267 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_trie_walk) globals0266
def exceptions0267 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_trie_walk) exceptions0266
def code0268 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_trie_lookup) code0267
def globals0268 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_trie_lookup) globals0267
def exceptions0268 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_trie_lookup) exceptions0267
def code0269 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_mpt_new) code0268
def globals0269 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_mpt_new) globals0268
def exceptions0269 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_mpt_new) exceptions0268
def code0270 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_mpt_from_witness) code0269
def globals0270 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_mpt_from_witness) globals0269
def exceptions0270 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_mpt_from_witness) exceptions0269
def code0271 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_mpt_nibble_key) code0270
def globals0271 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_mpt_nibble_key) globals0270
def exceptions0271 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_mpt_nibble_key) exceptions0270
def code0272 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_mpt_get) code0271
def globals0272 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_mpt_get) globals0271
def exceptions0272 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_mpt_get) exceptions0271

def state0272 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0272
    code := code0272
    eshapes := exceptions0272
    structs := [] }

end InitE.SourceWitness
