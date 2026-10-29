import InitE.SourceWitness.Terms032
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0529 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_sstore) code0528
def globals0529 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_sstore) globals0528
def exceptions0529 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_sstore) exceptions0528
def code0530 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_tload) code0529
def globals0530 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_tload) globals0529
def exceptions0530 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_tload) exceptions0529
def code0531 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_tstore) code0530
def globals0531 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_tstore) globals0530
def exceptions0531 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_tstore) exceptions0530
def code0532 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_address) code0531
def globals0532 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_address) globals0531
def exceptions0532 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_address) exceptions0531
def code0533 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_balance) code0532
def globals0533 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_balance) globals0532
def exceptions0533 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_balance) exceptions0532
def code0534 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_origin) code0533
def globals0534 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_origin) globals0533
def exceptions0534 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_origin) exceptions0533
def code0535 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_caller) code0534
def globals0535 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_caller) globals0534
def exceptions0535 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_caller) exceptions0534
def code0536 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_callvalue) code0535
def globals0536 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_callvalue) globals0535
def exceptions0536 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_callvalue) exceptions0535
def code0537 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_calldataload) code0536
def globals0537 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_calldataload) globals0536
def exceptions0537 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_calldataload) exceptions0536
def code0538 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_calldatasize) code0537
def globals0538 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_calldatasize) globals0537
def exceptions0538 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_calldatasize) exceptions0537
def code0539 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_copy_from_buffer) code0538
def globals0539 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_copy_from_buffer) globals0538
def exceptions0539 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_copy_from_buffer) exceptions0538
def code0540 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_calldatacopy) code0539
def globals0540 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_calldatacopy) globals0539
def exceptions0540 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_calldatacopy) exceptions0539
def code0541 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_codesize) code0540
def globals0541 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_codesize) globals0540
def exceptions0541 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_codesize) exceptions0540
def code0542 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_codecopy) code0541
def globals0542 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_codecopy) globals0541
def exceptions0542 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_codecopy) exceptions0541
def code0543 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_gasprice) code0542
def globals0543 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_gasprice) globals0542
def exceptions0543 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_gasprice) exceptions0542
def code0544 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ext_code_of) code0543
def globals0544 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ext_code_of) globals0543
def exceptions0544 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ext_code_of) exceptions0543

def state0544 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0544
    code := code0544
    eshapes := exceptions0544
    structs := [] }

end InitE.SourceWitness
