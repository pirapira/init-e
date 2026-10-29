import InitE.SourceWitness.Terms002
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0049 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_slt) code0048
def globals0049 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_slt) globals0048
def exceptions0049 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_slt) exceptions0048
def code0050 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_sgt) code0049
def globals0050 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_sgt) globals0049
def exceptions0050 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_sgt) exceptions0049
def code0051 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_cmp) code0050
def globals0051 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_cmp) globals0050
def exceptions0051 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_cmp) exceptions0050
def code0052 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_not) code0051
def globals0052 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_not) globals0051
def exceptions0052 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_not) exceptions0051
def code0053 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_and) code0052
def globals0053 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_and) globals0052
def exceptions0053 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_and) exceptions0052
def code0054 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_or) code0053
def globals0054 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_or) globals0053
def exceptions0054 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_or) exceptions0053
def code0055 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_xor) code0054
def globals0055 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_xor) globals0054
def exceptions0055 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_xor) exceptions0054
def code0056 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_add_carry) code0055
def globals0056 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_add_carry) globals0055
def exceptions0056 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_add_carry) exceptions0055
def code0057 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_add) code0056
def globals0057 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_add) globals0056
def exceptions0057 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_add) exceptions0056
def code0058 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_sub) code0057
def globals0058 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_sub) globals0057
def exceptions0058 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_sub) exceptions0057
def code0059 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_neg) code0058
def globals0059 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_neg) globals0058
def exceptions0059 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_neg) exceptions0058
def code0060 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_mul64x64) code0059
def globals0060 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_mul64x64) globals0059
def exceptions0060 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_mul64x64) exceptions0059
def code0061 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_mul) code0060
def globals0061 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_mul) globals0060
def exceptions0061 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_mul) exceptions0060
def code0062 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_u256_mul_full) code0061
def globals0062 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_u256_mul_full) globals0061
def exceptions0062 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_u256_mul_full) exceptions0061
def code0063 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_nlz32) code0062
def globals0063 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_nlz32) globals0062
def exceptions0063 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_nlz32) exceptions0062
def code0064 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_div64by32) code0063
def globals0064 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_div64by32) globals0063
def exceptions0064 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_div64by32) exceptions0063

def state0064 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0064
    code := code0064
    eshapes := exceptions0064
    structs := [] }

end InitE.SourceWitness
