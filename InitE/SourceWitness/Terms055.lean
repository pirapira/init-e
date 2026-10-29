import InitE.SourceWitness.Terms054
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0881 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_attempt_l1) code0880
def globals0881 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_attempt_l1) globals0880
def exceptions0881 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_attempt_l1) exceptions0880
def code0882 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_attempt_l2) code0881
def globals0882 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_attempt_l2) globals0881
def exceptions0882 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_attempt_l2) exceptions0881
def code0883 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_attempt_l3) code0882
def globals0883 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_attempt_l3) globals0882
def exceptions0883 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_attempt_l3) exceptions0882
def code0884 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_attempt_l4) code0883
def globals0884 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_attempt_l4) globals0883
def exceptions0884 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_attempt_l4) exceptions0883
def code0885 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_attempt_l5) code0884
def globals0885 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_attempt_l5) globals0884
def exceptions0885 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_attempt_l5) exceptions0884
def code0886 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_attempt_l6) code0885
def globals0886 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_attempt_l6) globals0885
def exceptions0886 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_attempt_l6) exceptions0885
def code0887 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_attempt_l7) code0886
def globals0887 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_attempt_l7) globals0886
def exceptions0887 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_attempt_l7) exceptions0886
def code0888 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_verify_stateless_new_payload) code0887
def globals0888 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_verify_stateless_new_payload) globals0887
def exceptions0888 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_verify_stateless_new_payload) exceptions0887
def code0889 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_fail_code) code0888
def globals0889 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_fail_code) globals0888
def exceptions0889 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_fail_code) exceptions0888
def code0890 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_main) code0889
def globals0890 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_main) globals0889
def exceptions0890 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_main) exceptions0889

def state0890 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0890
    code := code0890
    eshapes := exceptions0890
    structs := [] }

end InitE.SourceWitness
