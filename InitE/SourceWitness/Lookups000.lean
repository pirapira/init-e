import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_trap_with :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 114#8, 97#8, 112#8, 95#8, 119#8, 105#8, 116#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_trap_with) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mem_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 101#8, 109#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_mem_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_alloc :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 108#8, 108#8, 111#8, 99#8]) = literalEntry (declToHOL Guest.Software.guestFn_alloc) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_heap_mark :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 101#8, 97#8, 112#8, 95#8, 109#8, 97#8, 114#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_heap_mark) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_heap_release :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 101#8, 97#8, 112#8, 95#8, 114#8, 101#8, 108#8, 101#8, 97#8, 115#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_heap_release) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_mem_alloc :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 109#8, 101#8, 109#8, 95#8, 97#8, 108#8, 108#8, 111#8, 99#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_mem_alloc) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_mem_mark :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 109#8, 101#8, 109#8, 95#8, 109#8, 97#8, 114#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_mem_mark) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_mem_release :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 109#8, 101#8, 109#8, 95#8, 114#8, 101#8, 108#8, 101#8, 97#8, 115#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_mem_release) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_scratch_alloc :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 99#8, 114#8, 97#8, 116#8, 99#8, 104#8, 95#8, 97#8, 108#8, 108#8, 111#8, 99#8]) = literalEntry (declToHOL Guest.Software.guestFn_scratch_alloc) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_scratch_mark :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 99#8, 114#8, 97#8, 116#8, 99#8, 104#8, 95#8, 109#8, 97#8, 114#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_scratch_mark) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_scratch_release :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 99#8, 114#8, 97#8, 116#8, 99#8, 104#8, 95#8, 114#8, 101#8, 108#8, 101#8, 97#8, 115#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_scratch_release) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_memcpy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 101#8, 109#8, 99#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_memcpy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_memzero :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 101#8, 109#8, 122#8, 101#8, 114#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_memzero) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_memeq :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 101#8, 109#8, 101#8, 113#8]) = literalEntry (declToHOL Guest.Software.guestFn_memeq) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_is_zero_bytes :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 115#8, 95#8, 122#8, 101#8, 114#8, 111#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_is_zero_bytes) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ld_le32 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 100#8, 95#8, 108#8, 101#8, 51#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_ld_le32) := by
  rfl

end InitE.SourceWitness
