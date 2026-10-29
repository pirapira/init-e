import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_extend_memory :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 120#8, 116#8, 101#8, 110#8, 100#8, 95#8, 109#8, 101#8, 109#8, 111#8, 114#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_extend_memory) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_charge_with_memory :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 104#8, 97#8, 114#8, 103#8, 101#8, 95#8, 119#8, 105#8, 116#8, 104#8, 95#8, 109#8, 101#8, 109#8, 111#8, 114#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_charge_with_memory) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_buffer_read :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 117#8, 102#8, 102#8, 101#8, 114#8, 95#8, 114#8, 101#8, 97#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_buffer_read) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_compute_jumpdests :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 111#8, 109#8, 112#8, 117#8, 116#8, 101#8, 95#8, 106#8, 117#8, 109#8, 112#8, 100#8, 101#8, 115#8, 116#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_compute_jumpdests) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_is_valid_jumpdest :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 115#8, 95#8, 118#8, 97#8, 108#8, 105#8, 100#8, 95#8, 106#8, 117#8, 109#8, 112#8, 100#8, 101#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_is_valid_jumpdest) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_msg_new :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 115#8, 103#8, 95#8, 110#8, 101#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_msg_new) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_msg_new_scratch :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 115#8, 103#8, 95#8, 110#8, 101#8, 119#8, 95#8, 115#8, 99#8, 114#8, 97#8, 116#8, 99#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_msg_new_scratch) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_new :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 110#8, 101#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_new) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pc_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 99#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_pc_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_cur_msg :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 117#8, 114#8, 95#8, 109#8, 115#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_cur_msg) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_require_not_static :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 101#8, 113#8, 117#8, 105#8, 114#8, 101#8, 95#8, 110#8, 111#8, 116#8, 95#8, 115#8, 116#8, 97#8, 116#8, 105#8, 99#8]) = literalEntry (declToHOL Guest.Software.guestFn_require_not_static) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_is_warm_address :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 115#8, 95#8, 119#8, 97#8, 114#8, 109#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_is_warm_address) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_warm_address :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 97#8, 114#8, 109#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_warm_address) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_access_gas_cost :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 99#8, 99#8, 101#8, 115#8, 115#8, 95#8, 103#8, 97#8, 115#8, 95#8, 99#8, 111#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_access_gas_cost) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_warm_after_charge :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [119#8, 97#8, 114#8, 109#8, 95#8, 97#8, 102#8, 116#8, 101#8, 114#8, 95#8, 99#8, 104#8, 97#8, 114#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_warm_after_charge) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_add) := by
  rfl

end InitE.SourceWitness
