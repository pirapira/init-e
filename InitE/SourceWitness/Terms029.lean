import InitE.SourceWitness.Terms028
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0465 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_is_valid_jumpdest) code0464
def globals0465 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_is_valid_jumpdest) globals0464
def exceptions0465 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_is_valid_jumpdest) exceptions0464
def code0466 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_msg_new) code0465
def globals0466 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_msg_new) globals0465
def exceptions0466 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_msg_new) exceptions0465
def code0467 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_msg_new_scratch) code0466
def globals0467 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_msg_new_scratch) globals0466
def exceptions0467 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_msg_new_scratch) exceptions0466
def code0468 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_new) code0467
def globals0468 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_new) globals0467
def exceptions0468 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_new) exceptions0467
def code0469 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_pc_add) code0468
def globals0469 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_pc_add) globals0468
def exceptions0469 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_pc_add) exceptions0468
def code0470 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_cur_msg) code0469
def globals0470 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_cur_msg) globals0469
def exceptions0470 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_cur_msg) exceptions0469
def code0471 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_require_not_static) code0470
def globals0471 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_require_not_static) globals0470
def exceptions0471 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_require_not_static) exceptions0470
def code0472 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_is_warm_address) code0471
def globals0472 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_is_warm_address) globals0471
def exceptions0472 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_is_warm_address) exceptions0471
def code0473 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_warm_address) code0472
def globals0473 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_warm_address) globals0472
def exceptions0473 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_warm_address) exceptions0472
def code0474 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_access_gas_cost) code0473
def globals0474 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_access_gas_cost) globals0473
def exceptions0474 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_access_gas_cost) exceptions0473
def code0475 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_warm_after_charge) code0474
def globals0475 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_warm_after_charge) globals0474
def exceptions0475 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_warm_after_charge) exceptions0474
def code0476 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_add) code0475
def globals0476 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_add) globals0475
def exceptions0476 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_add) exceptions0475
def code0477 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_mul) code0476
def globals0477 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_mul) globals0476
def exceptions0477 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_mul) exceptions0476
def code0478 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_sub) code0477
def globals0478 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_sub) globals0477
def exceptions0478 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_sub) exceptions0477
def code0479 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_div) code0478
def globals0479 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_div) globals0478
def exceptions0479 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_div) exceptions0478
def code0480 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_sdiv) code0479
def globals0480 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_sdiv) globals0479
def exceptions0480 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_sdiv) exceptions0479

def state0480 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0480
    code := code0480
    eshapes := exceptions0480
    structs := [] }

end InitE.SourceWitness
