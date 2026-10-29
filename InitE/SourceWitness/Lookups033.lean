import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_prepare_dispatch :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 112#8, 97#8, 114#8, 101#8, 95#8, 100#8, 105#8, 115#8, 112#8, 97#8, 116#8, 99#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_prepare_dispatch) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_dispatch :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 100#8, 105#8, 115#8, 112#8, 97#8, 116#8, 99#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_dispatch) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_open :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 111#8, 112#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_open) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_exception :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 101#8, 120#8, 99#8, 101#8, 112#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_exception) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_prologue :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 112#8, 114#8, 111#8, 108#8, 111#8, 103#8, 117#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_prologue) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_start :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 115#8, 116#8, 97#8, 114#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_start) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_epilogue :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 101#8, 112#8, 105#8, 108#8, 111#8, 103#8, 117#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_epilogue) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_finish_child :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 105#8, 110#8, 105#8, 115#8, 104#8, 95#8, 99#8, 104#8, 105#8, 108#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_finish_child) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_run_frames :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 117#8, 110#8, 95#8, 102#8, 114#8, 97#8, 109#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_run_frames) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_start_child :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 114#8, 116#8, 95#8, 99#8, 104#8, 105#8, 108#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_start_child) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_halt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 104#8, 97#8, 108#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_halt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_depth0_prepare :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 112#8, 116#8, 104#8, 48#8, 95#8, 112#8, 114#8, 101#8, 112#8, 97#8, 114#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_depth0_prepare) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_process_message :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 109#8, 101#8, 115#8, 115#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_process_message) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_create_finish :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 95#8, 102#8, 105#8, 110#8, 105#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_create_finish) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_process_create_message :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 111#8, 99#8, 101#8, 115#8, 115#8, 95#8, 99#8, 114#8, 101#8, 97#8, 116#8, 101#8, 95#8, 109#8, 101#8, 115#8, 115#8, 97#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_process_create_message) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_incorporate_child_on_error :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 110#8, 99#8, 111#8, 114#8, 112#8, 111#8, 114#8, 97#8, 116#8, 101#8, 95#8, 99#8, 104#8, 105#8, 108#8, 100#8, 95#8, 111#8, 110#8, 95#8, 101#8, 114#8, 114#8, 111#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_incorporate_child_on_error) := by
  rfl

end InitE.SourceWitness
