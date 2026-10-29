import InitE.SourceWitness.Terms034
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0561 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_prevrandao) code0560
def globals0561 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_prevrandao) globals0560
def exceptions0561 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_prevrandao) exceptions0560
def code0562 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_slotnum) code0561
def globals0562 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_slotnum) globals0561
def exceptions0562 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_slotnum) exceptions0561
def code0563 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_cur_cont) code0562
def globals0563 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_cur_cont) globals0562
def exceptions0563 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_cur_cont) exceptions0562
def code0564 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_transfer_topic) code0563
def globals0564 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_transfer_topic) globals0563
def exceptions0564 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_transfer_topic) exceptions0563
def code0565 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_vm_system_address) code0564
def globals0565 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_vm_system_address) globals0564
def exceptions0565 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_vm_system_address) exceptions0564
def code0566 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_null_address) code0565
def globals0566 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_null_address) globals0565
def exceptions0566 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_null_address) exceptions0565
def code0567 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_evm_init) code0566
def globals0567 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_evm_init) globals0566
def exceptions0567 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_evm_init) exceptions0566
def code0568 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_emit_transfer_log) code0567
def globals0568 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_emit_transfer_log) globals0567
def exceptions0568 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_emit_transfer_log) exceptions0567
def code0569 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_return) code0568
def globals0569 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_return) globals0568
def exceptions0569 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_return) exceptions0568
def code0570 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_revert) code0569
def globals0570 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_revert) globals0569
def exceptions0570 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_revert) exceptions0569
def code0571 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_selfdestruct) code0570
def globals0571 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_selfdestruct) globals0570
def exceptions0571 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_selfdestruct) exceptions0570
def code0572 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_get_delegated_code_address) code0571
def globals0572 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_get_delegated_code_address) globals0571
def exceptions0572 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_get_delegated_code_address) exceptions0571
def code0573 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_recover_authority) code0572
def globals0573 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_recover_authority) globals0572
def exceptions0573 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_recover_authority) exceptions0572
def code0574 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_calculate_delegation_cost) code0573
def globals0574 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_calculate_delegation_cost) globals0573
def exceptions0574 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_calculate_delegation_cost) exceptions0573
def code0575 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_validate_authorization_checks) code0574
def globals0575 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_validate_authorization_checks) globals0574
def exceptions0575 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_validate_authorization_checks) exceptions0574
def code0576 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_set_delegation) code0575
def globals0576 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_set_delegation) globals0575
def exceptions0576 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_set_delegation) exceptions0575

def state0576 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0576
    code := code0576
    eshapes := exceptions0576
    structs := [] }

end InitE.SourceWitness
