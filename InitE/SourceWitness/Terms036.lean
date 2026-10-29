import InitE.SourceWitness.Terms035
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0577 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_prepare_dispatch) code0576
def globals0577 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_prepare_dispatch) globals0576
def exceptions0577 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_prepare_dispatch) exceptions0576
def code0578 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_op_dispatch) code0577
def globals0578 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_op_dispatch) globals0577
def exceptions0578 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_op_dispatch) exceptions0577
def code0579 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_open) code0578
def globals0579 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_open) globals0578
def exceptions0579 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_open) exceptions0578
def code0580 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_exception) code0579
def globals0580 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_exception) globals0579
def exceptions0580 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_exception) exceptions0579
def code0581 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_prologue) code0580
def globals0581 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_prologue) globals0580
def exceptions0581 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_prologue) exceptions0580
def code0582 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_start) code0581
def globals0582 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_start) globals0581
def exceptions0582 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_start) exceptions0581
def code0583 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_epilogue) code0582
def globals0583 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_epilogue) globals0582
def exceptions0583 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_epilogue) exceptions0582
def code0584 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_finish_child) code0583
def globals0584 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_finish_child) globals0583
def exceptions0584 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_finish_child) exceptions0583
def code0585 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_run_frames) code0584
def globals0585 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_run_frames) globals0584
def exceptions0585 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_run_frames) exceptions0584
def code0586 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_start_child) code0585
def globals0586 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_start_child) globals0585
def exceptions0586 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_start_child) exceptions0585
def code0587 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_halt) code0586
def globals0587 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_halt) globals0586
def exceptions0587 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_halt) exceptions0586
def code0588 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_depth0_prepare) code0587
def globals0588 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_depth0_prepare) globals0587
def exceptions0588 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_depth0_prepare) exceptions0587
def code0589 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_process_message) code0588
def globals0589 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_process_message) globals0588
def exceptions0589 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_process_message) exceptions0588
def code0590 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_create_finish) code0589
def globals0590 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_create_finish) globals0589
def exceptions0590 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_create_finish) exceptions0589
def code0591 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_process_create_message) code0590
def globals0591 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_process_create_message) globals0590
def exceptions0591 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_process_create_message) exceptions0590
def code0592 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_incorporate_child_on_error) code0591
def globals0592 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_incorporate_child_on_error) globals0591
def exceptions0592 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_incorporate_child_on_error) exceptions0591

def state0592 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0592
    code := code0592
    eshapes := exceptions0592
    structs := [] }

end InitE.SourceWitness
