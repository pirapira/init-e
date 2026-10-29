import InitE.SourceWitness.Terms036
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0593 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_incorporate_child_on_success) code0592
def globals0593 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_incorporate_child_on_success) globals0592
def exceptions0593 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_incorporate_child_on_success) exceptions0592
def code0594 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rollback_child_access) code0593
def globals0594 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rollback_child_access) globals0593
def exceptions0594 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rollback_child_access) exceptions0593
def code0595 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_child_message) code0594
def globals0595 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_child_message) globals0594
def exceptions0595 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_child_message) exceptions0594
def code0596 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_set_retdata) code0595
def globals0596 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_set_retdata) globals0595
def exceptions0596 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_set_retdata) exceptions0595
def code0597 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_compute_contract_address) code0596
def globals0597 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_compute_contract_address) globals0596
def exceptions0597 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_compute_contract_address) exceptions0596
def code0598 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_compute_create2_contract_address) code0597
def globals0598 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_compute_create2_contract_address) globals0597
def exceptions0598 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_compute_create2_contract_address) exceptions0597
def code0599 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_generic_create) code0598
def globals0599 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_generic_create) globals0598
def exceptions0599 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_generic_create) exceptions0598
def code0600 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_create) code0599
def globals0600 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_create) globals0599
def exceptions0600 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_create) exceptions0599
def code0601 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_create2) code0600
def globals0601 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_create2) globals0600
def exceptions0601 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_create2) exceptions0600
def code0602 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_generic_call) code0601
def globals0602 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_generic_call) globals0601
def exceptions0602 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_generic_call) exceptions0601
def code0603 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_calculate_message_call_gas) code0602
def globals0603 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_calculate_message_call_gas) globals0602
def exceptions0603 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_calculate_message_call_gas) exceptions0602
def code0604 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_call) code0603
def globals0604 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_call) globals0603
def exceptions0604 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_call) exceptions0603
def code0605 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_callcode) code0604
def globals0605 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_callcode) globals0604
def exceptions0605 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_callcode) exceptions0604
def code0606 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_delegatecall) code0605
def globals0606 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_delegatecall) globals0605
def exceptions0606 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_delegatecall) exceptions0605
def code0607 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_staticcall) code0606
def globals0607 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_staticcall) globals0606
def exceptions0607 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_staticcall) exceptions0606
def code0608 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_process_message_call) code0607
def globals0608 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_process_message_call) globals0607
def exceptions0608 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_process_message_call) exceptions0607

def state0608 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0608
    code := code0608
    eshapes := exceptions0608
    structs := [] }

end InitE.SourceWitness
