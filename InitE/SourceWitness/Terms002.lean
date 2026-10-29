import InitE.SourceWitness.Terms001
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0033 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_max) code0032
def globals0033 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_max) globals0032
def exceptions0033 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_max) exceptions0032
def code0034 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_udivmod) code0033
def globals0034 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_udivmod) globals0033
def exceptions0034 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_udivmod) exceptions0033
def code0035 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_udiv) code0034
def globals0035 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_udiv) globals0034
def exceptions0035 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_udiv) exceptions0034
def code0036 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_umod) code0035
def globals0036 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_umod) globals0035
def exceptions0036 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_umod) exceptions0035
def code0037 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ceil_log2) code0036
def globals0037 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ceil_log2) globals0036
def exceptions0037 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ceil_log2) exceptions0036
def code0038 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_u256_ws) code0037
def globals0038 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_u256_ws) globals0037
def exceptions0038 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_u256_ws) exceptions0037
def code0039 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_ws_init) code0038
def globals0039 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_ws_init) globals0038
def exceptions0039 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_ws_init) exceptions0038
def code0040 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_from_word) code0039
def globals0040 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_from_word) globals0039
def exceptions0040 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_from_word) exceptions0039
def code0041 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_low) code0040
def globals0041 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_low) globals0040
def exceptions0041 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_low) exceptions0040
def code0042 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_fits_word) code0041
def globals0042 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_fits_word) globals0041
def exceptions0042 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_fits_word) exceptions0041
def code0043 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_is_zero) code0042
def globals0043 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_is_zero) globals0042
def exceptions0043 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_is_zero) exceptions0042
def code0044 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_limb) code0043
def globals0044 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_limb) globals0043
def exceptions0044 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_limb) exceptions0043
def code0045 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_bit) code0044
def globals0045 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_bit) globals0044
def exceptions0045 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_bit) exceptions0044
def code0046 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_eq) code0045
def globals0046 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_eq) globals0045
def exceptions0046 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_eq) exceptions0045
def code0047 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_lt) code0046
def globals0047 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_lt) globals0046
def exceptions0047 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_lt) exceptions0046
def code0048 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_gt) code0047
def globals0048 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_gt) globals0047
def exceptions0048 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_gt) exceptions0047

def state0048 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0048
    code := code0048
    eshapes := exceptions0048
    structs := [] }

end InitE.SourceWitness
