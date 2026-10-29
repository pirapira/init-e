import InitE.SourceWitness.Terms004
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0081 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_exp) code0080
def globals0081 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_exp) globals0080
def exceptions0081 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_exp) exceptions0080
def code0082 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_shl) code0081
def globals0082 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_shl) globals0081
def exceptions0082 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_shl) exceptions0081
def code0083 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_shr) code0082
def globals0083 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_shr) globals0082
def exceptions0083 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_shr) exceptions0082
def code0084 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_sar) code0083
def globals0084 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_sar) globals0083
def exceptions0084 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_sar) exceptions0083
def code0085 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_signextend) code0084
def globals0085 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_signextend) globals0084
def exceptions0085 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_signextend) exceptions0084
def code0086 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_byte) code0085
def globals0086 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_byte) globals0085
def exceptions0086 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_byte) exceptions0085
def code0087 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_from_be) code0086
def globals0087 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_from_be) globals0086
def exceptions0087 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_from_be) exceptions0086
def code0088 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_to_be32) code0087
def globals0088 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_to_be32) globals0087
def exceptions0088 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_to_be32) exceptions0087
def code0089 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_to_be_min) code0088
def globals0089 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_to_be_min) globals0088
def exceptions0089 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_to_be_min) exceptions0088
def code0090 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_sha_st) code0089
def globals0090 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_sha_st) globals0089
def exceptions0090 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_sha_st) exceptions0089
def code0091 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_sha_pad) code0090
def globals0091 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_sha_pad) globals0090
def exceptions0091 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_sha_pad) exceptions0090
def code0092 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_sha256_init) code0091
def globals0092 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_sha256_init) globals0091
def exceptions0092 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_sha256_init) exceptions0091
def code0093 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_sha256_state_init) code0092
def globals0093 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_sha256_state_init) globals0092
def exceptions0093 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_sha256_state_init) exceptions0092
def code0094 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_sha256_block) code0093
def globals0094 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_sha256_block) globals0093
def exceptions0094 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_sha256_block) exceptions0093
def code0095 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_sha256_finish) code0094
def globals0095 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_sha256_finish) globals0094
def exceptions0095 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_sha256_finish) exceptions0094
def code0096 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_sha256) code0095
def globals0096 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_sha256) globals0095
def exceptions0096 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_sha256) exceptions0095

def state0096 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0096
    code := code0096
    eshapes := exceptions0096
    structs := [] }

end InitE.SourceWitness
