import InitE.SourceWitness.Terms036
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0576 globals0576

def chunk036 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_prepare_dispatch,
    declToHOL Guest.Software.guestFn_op_dispatch,
    declToHOL Guest.Software.guestFn_frame_open,
    declToHOL Guest.Software.guestFn_frame_exception,
    declToHOL Guest.Software.guestFn_frame_prologue,
    declToHOL Guest.Software.guestFn_frame_start,
    declToHOL Guest.Software.guestFn_frame_epilogue,
    declToHOL Guest.Software.guestFn_finish_child,
    declToHOL Guest.Software.guestFn_run_frames,
    declToHOL Guest.Software.guestFn_start_child,
    declToHOL Guest.Software.guestFn_frame_halt,
    declToHOL Guest.Software.guestFn_depth0_prepare,
    declToHOL Guest.Software.guestFn_process_message,
    declToHOL Guest.Software.guestFn_create_finish,
    declToHOL Guest.Software.guestFn_process_create_message,
    declToHOL Guest.Software.guestFn_incorporate_child_on_error]

theorem chunk036_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0576 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk036 =
        some (state0592 s) := by
  cbv

end InitE.SourceWitness
