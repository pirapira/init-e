import InitE.SourceWitness.Terms003
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0065 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_to_digits) code0064
def globals0065 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_to_digits) globals0064
def exceptions0065 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_to_digits) exceptions0064
def code0066 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_digits_to_u256) code0065
def globals0066 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_digits_to_u256) globals0065
def exceptions0066 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_digits_to_u256) exceptions0065
def code0067 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_digits_len) code0066
def globals0067 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_digits_len) globals0066
def exceptions0067 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_digits_len) exceptions0066
def code0068 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_divmnu) code0067
def globals0068 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_divmnu) globals0067
def exceptions0068 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_divmnu) exceptions0067
def code0069 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_digits_divmod) code0068
def globals0069 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_digits_divmod) globals0068
def exceptions0069 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_digits_divmod) exceptions0068
def code0070 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_divmod) code0069
def globals0070 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_divmod) globals0069
def exceptions0070 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_divmod) exceptions0069
def code0071 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_div) code0070
def globals0071 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_div) globals0070
def exceptions0071 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_div) exceptions0070
def code0072 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_mod) code0071
def globals0072 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_mod) globals0071
def exceptions0072 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_mod) exceptions0071
def code0073 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_abs) code0072
def globals0073 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_abs) globals0072
def exceptions0073 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_abs) exceptions0072
def code0074 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_sdiv) code0073
def globals0074 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_sdiv) globals0073
def exceptions0074 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_sdiv) exceptions0073
def code0075 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_smod) code0074
def globals0075 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_smod) globals0074
def exceptions0075 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_smod) exceptions0074
def code0076 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_addmod) code0075
def globals0076 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_addmod) globals0075
def exceptions0076 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_addmod) exceptions0075
def code0077 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_mulmod) code0076
def globals0077 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_mulmod) globals0076
def exceptions0077 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_mulmod) exceptions0076
def code0078 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bit_length64) code0077
def globals0078 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bit_length64) globals0077
def exceptions0078 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bit_length64) exceptions0077
def code0079 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_bit_length) code0078
def globals0079 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_bit_length) globals0078
def exceptions0079 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_bit_length) exceptions0078
def code0080 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_byte_length) code0079
def globals0080 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_byte_length) globals0079
def exceptions0080 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_byte_length) exceptions0079

def state0080 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0080
    code := code0080
    eshapes := exceptions0080
    structs := [] }

end InitE.SourceWitness
