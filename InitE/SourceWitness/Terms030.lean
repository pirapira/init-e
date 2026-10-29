import InitE.SourceWitness.Terms029
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0481 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_mod) code0480
def globals0481 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_mod) globals0480
def exceptions0481 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_mod) exceptions0480
def code0482 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_smod) code0481
def globals0482 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_smod) globals0481
def exceptions0482 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_smod) exceptions0481
def code0483 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_addmod) code0482
def globals0483 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_addmod) globals0482
def exceptions0483 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_addmod) exceptions0482
def code0484 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_mulmod) code0483
def globals0484 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_mulmod) globals0483
def exceptions0484 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_mulmod) exceptions0483
def code0485 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_exp) code0484
def globals0485 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_exp) globals0484
def exceptions0485 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_exp) exceptions0484
def code0486 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_signextend) code0485
def globals0486 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_signextend) globals0485
def exceptions0486 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_signextend) exceptions0485
def code0487 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_lt) code0486
def globals0487 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_lt) globals0486
def exceptions0487 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_lt) exceptions0486
def code0488 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_gt) code0487
def globals0488 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_gt) globals0487
def exceptions0488 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_gt) exceptions0487
def code0489 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_slt) code0488
def globals0489 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_slt) globals0488
def exceptions0489 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_slt) exceptions0488
def code0490 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_sgt) code0489
def globals0490 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_sgt) globals0489
def exceptions0490 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_sgt) exceptions0489
def code0491 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_eq) code0490
def globals0491 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_eq) globals0490
def exceptions0491 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_eq) exceptions0490
def code0492 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_iszero) code0491
def globals0492 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_iszero) globals0491
def exceptions0492 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_iszero) exceptions0491
def code0493 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_and) code0492
def globals0493 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_and) globals0492
def exceptions0493 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_and) exceptions0492
def code0494 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_or) code0493
def globals0494 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_or) globals0493
def exceptions0494 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_or) exceptions0493
def code0495 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_xor) code0494
def globals0495 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_xor) globals0494
def exceptions0495 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_xor) exceptions0494
def code0496 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_not) code0495
def globals0496 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_not) globals0495
def exceptions0496 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_not) exceptions0495

def state0496 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0496
    code := code0496
    eshapes := exceptions0496
    structs := [] }

end InitE.SourceWitness
