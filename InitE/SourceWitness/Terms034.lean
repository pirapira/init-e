import InitE.SourceWitness.Terms033
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0545 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_extcodesize) code0544
def globals0545 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_extcodesize) globals0544
def exceptions0545 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_extcodesize) exceptions0544
def code0546 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_extcodecopy) code0545
def globals0546 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_extcodecopy) globals0545
def exceptions0546 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_extcodecopy) exceptions0545
def code0547 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_returndatasize) code0546
def globals0547 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_returndatasize) globals0546
def exceptions0547 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_returndatasize) exceptions0546
def code0548 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_returndatacopy) code0547
def globals0548 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_returndatacopy) globals0547
def exceptions0548 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_returndatacopy) exceptions0547
def code0549 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_extcodehash) code0548
def globals0549 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_extcodehash) globals0548
def exceptions0549 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_extcodehash) exceptions0548
def code0550 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_selfbalance) code0549
def globals0550 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_selfbalance) globals0549
def exceptions0550 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_selfbalance) exceptions0549
def code0551 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_block_env) code0550
def globals0551 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_block_env) globals0550
def exceptions0551 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_block_env) exceptions0550
def code0552 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_basefee) code0551
def globals0552 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_basefee) globals0551
def exceptions0552 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_basefee) exceptions0551
def code0553 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_blobhash) code0552
def globals0553 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_blobhash) globals0552
def exceptions0553 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_blobhash) exceptions0552
def code0554 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_blobbasefee) code0553
def globals0554 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_blobbasefee) globals0553
def exceptions0554 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_blobbasefee) exceptions0553
def code0555 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_blockhash) code0554
def globals0555 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_blockhash) globals0554
def exceptions0555 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_blockhash) exceptions0554
def code0556 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_coinbase) code0555
def globals0556 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_coinbase) globals0555
def exceptions0556 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_coinbase) exceptions0555
def code0557 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_timestamp) code0556
def globals0557 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_timestamp) globals0556
def exceptions0557 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_timestamp) exceptions0556
def code0558 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_number) code0557
def globals0558 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_number) globals0557
def exceptions0558 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_number) exceptions0557
def code0559 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_gaslimit) code0558
def globals0559 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_gaslimit) globals0558
def exceptions0559 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_gaslimit) exceptions0558
def code0560 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_chainid) code0559
def globals0560 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_chainid) globals0559
def exceptions0560 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_chainid) exceptions0559

def state0560 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0560
    code := code0560
    eshapes := exceptions0560
    structs := [] }

end InitE.SourceWitness
