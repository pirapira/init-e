import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_op_mstore :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 115#8, 116#8, 111#8, 114#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_mstore) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_mstore8 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 115#8, 116#8, 111#8, 114#8, 101#8, 56#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_mstore8) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_mload :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 108#8, 111#8, 97#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_mload) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_msize :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 115#8, 105#8, 122#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_msize) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_mcopy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 109#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_mcopy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_pop :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 112#8, 111#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_pop) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_push :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 112#8, 117#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_push) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_dup :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 100#8, 117#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_dup) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_stack_swap_positions :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 99#8, 107#8, 95#8, 115#8, 119#8, 97#8, 112#8, 95#8, 112#8, 111#8, 115#8, 105#8, 116#8, 105#8, 111#8, 110#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_stack_swap_positions) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_swap :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 119#8, 97#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_swap) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_code_imm :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 111#8, 100#8, 101#8, 95#8, 105#8, 109#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_code_imm) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_decode_single :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 95#8, 115#8, 105#8, 110#8, 103#8, 108#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_decode_single) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_dupn :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 100#8, 117#8, 112#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_dupn) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_swapn :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 119#8, 97#8, 112#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_swapn) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_exchange :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 101#8, 120#8, 99#8, 104#8, 97#8, 110#8, 103#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_exchange) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_log_append :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 111#8, 103#8, 95#8, 97#8, 112#8, 112#8, 101#8, 110#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_log_append) := by
  rfl

end InitE.SourceWitness
