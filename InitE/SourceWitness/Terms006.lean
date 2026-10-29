import InitE.SourceWitness.Terms005
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0097 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_sha256_pair) code0096
def globals0097 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_sha256_pair) globals0096
def exceptions0097 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_sha256_pair) exceptions0096
def code0098 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_keccak_rc) code0097
def globals0098 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_keccak_rc) globals0097
def exceptions0098 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_keccak_rc) exceptions0097
def code0099 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_keccak_st) code0098
def globals0099 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_keccak_st) globals0098
def exceptions0099 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_keccak_st) exceptions0098
def code0100 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_keccak_pad) code0099
def globals0100 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_keccak_pad) globals0099
def exceptions0100 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_keccak_pad) exceptions0099
def code0101 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_keccak_init) code0100
def globals0101 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_keccak_init) globals0100
def exceptions0101 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_keccak_init) exceptions0100
def code0102 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_keccak_f1600) code0101
def globals0102 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_keccak_f1600) globals0101
def exceptions0102 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_keccak_f1600) exceptions0101
def code0103 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_keccak_absorb_block) code0102
def globals0103 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_keccak_absorb_block) globals0102
def exceptions0103 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_keccak_absorb_block) exceptions0102
def code0104 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_keccak256) code0103
def globals0104 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_keccak256) globals0103
def exceptions0104 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_keccak256) exceptions0103
def code0105 : CodeTable :=
  installCode (declToHOL Guest.Software.guestExn_RlpErr) code0104
def globals0105 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestExn_RlpErr) globals0104
def exceptions0105 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestExn_RlpErr) exceptions0104
def code0106 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rlp_fail) code0105
def globals0106 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rlp_fail) globals0105
def exceptions0106 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rlp_fail) exceptions0105
def code0107 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rlp_read_length) code0106
def globals0107 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rlp_read_length) globals0106
def exceptions0107 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rlp_read_length) exceptions0106
def code0108 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rlp_item) code0107
def globals0108 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rlp_item) globals0107
def exceptions0108 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rlp_item) exceptions0107
def code0109 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rlp_decode_fully) code0108
def globals0109 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rlp_decode_fully) globals0108
def exceptions0109 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rlp_decode_fully) exceptions0108
def code0110 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rlp_item_header) code0109
def globals0110 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rlp_item_header) globals0109
def exceptions0110 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rlp_item_header) exceptions0109
def code0111 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn__rlp_validate_items_body) code0110
def globals0111 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn__rlp_validate_items_body) globals0110
def exceptions0111 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn__rlp_validate_items_body) exceptions0110
def code0112 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rlp_validate_items) code0111
def globals0112 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rlp_validate_items) globals0111
def exceptions0112 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rlp_validate_items) exceptions0111

def state0112 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0112
    code := code0112
    eshapes := exceptions0112
    structs := [] }

end InitE.SourceWitness
