import InitE.SourceWitness.Terms031
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0513 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_mcopy) code0512
def globals0513 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_mcopy) globals0512
def exceptions0513 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_mcopy) exceptions0512
def code0514 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_pop) code0513
def globals0514 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_pop) globals0513
def exceptions0514 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_pop) exceptions0513
def code0515 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_push) code0514
def globals0515 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_push) globals0514
def exceptions0515 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_push) exceptions0514
def code0516 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_dup) code0515
def globals0516 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_dup) globals0515
def exceptions0516 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_dup) exceptions0515
def code0517 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_stack_swap_positions) code0516
def globals0517 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_stack_swap_positions) globals0516
def exceptions0517 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_stack_swap_positions) exceptions0516
def code0518 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_swap) code0517
def globals0518 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_swap) globals0517
def exceptions0518 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_swap) exceptions0517
def code0519 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_code_imm) code0518
def globals0519 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_code_imm) globals0518
def exceptions0519 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_code_imm) exceptions0518
def code0520 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_decode_single) code0519
def globals0520 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_decode_single) globals0519
def exceptions0520 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_decode_single) exceptions0519
def code0521 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_dupn) code0520
def globals0521 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_dupn) globals0520
def exceptions0521 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_dupn) exceptions0520
def code0522 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_swapn) code0521
def globals0522 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_swapn) globals0521
def exceptions0522 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_swapn) exceptions0521
def code0523 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_exchange) code0522
def globals0523 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_exchange) globals0522
def exceptions0523 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_exchange) exceptions0522
def code0524 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_log_append) code0523
def globals0524 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_log_append) globals0523
def exceptions0524 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_log_append) exceptions0523
def code0525 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_log) code0524
def globals0525 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_log) globals0524
def exceptions0525 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_log) exceptions0524
def code0526 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_is_warm_storage_key) code0525
def globals0526 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_is_warm_storage_key) globals0525
def exceptions0526 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_is_warm_storage_key) exceptions0525
def code0527 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_warm_storage_key) code0526
def globals0527 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_warm_storage_key) globals0526
def exceptions0527 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_warm_storage_key) exceptions0526
def code0528 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_sload) code0527
def globals0528 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_sload) globals0527
def exceptions0528 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_sload) exceptions0527

def state0528 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0528
    code := code0528
    eshapes := exceptions0528
    structs := [] }

end InitE.SourceWitness
