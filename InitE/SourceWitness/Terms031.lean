import InitE.SourceWitness.Terms030
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0497 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_byte) code0496
def globals0497 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_byte) globals0496
def exceptions0497 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_byte) exceptions0496
def code0498 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_shl) code0497
def globals0498 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_shl) globals0497
def exceptions0498 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_shl) exceptions0497
def code0499 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_shr) code0498
def globals0499 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_shr) globals0498
def exceptions0499 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_shr) exceptions0498
def code0500 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_sar) code0499
def globals0500 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_sar) globals0499
def exceptions0500 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_sar) exceptions0499
def code0501 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_clz) code0500
def globals0501 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_clz) globals0500
def exceptions0501 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_clz) exceptions0500
def code0502 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_keccak) code0501
def globals0502 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_keccak) globals0501
def exceptions0502 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_keccak) exceptions0501
def code0503 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_stop) code0502
def globals0503 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_stop) globals0502
def exceptions0503 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_stop) exceptions0502
def code0504 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_jump) code0503
def globals0504 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_jump) globals0503
def exceptions0504 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_jump) exceptions0503
def code0505 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_jumpi) code0504
def globals0505 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_jumpi) globals0504
def exceptions0505 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_jumpi) exceptions0504
def code0506 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_pc) code0505
def globals0506 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_pc) globals0505
def exceptions0506 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_pc) exceptions0505
def code0507 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_gas) code0506
def globals0507 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_gas) globals0506
def exceptions0507 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_gas) exceptions0506
def code0508 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_jumpdest) code0507
def globals0508 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_jumpdest) globals0507
def exceptions0508 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_jumpdest) exceptions0507
def code0509 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_mstore) code0508
def globals0509 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_mstore) globals0508
def exceptions0509 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_mstore) exceptions0508
def code0510 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_mstore8) code0509
def globals0510 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_mstore8) globals0509
def exceptions0510 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_mstore8) exceptions0509
def code0511 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_mload) code0510
def globals0511 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_mload) globals0510
def exceptions0511 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_mload) exceptions0510
def code0512 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_msize) code0511
def globals0512 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_msize) globals0511
def exceptions0512 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_msize) exceptions0511

def state0512 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0512
    code := code0512
    eshapes := exceptions0512
    structs := [] }

end InitE.SourceWitness
