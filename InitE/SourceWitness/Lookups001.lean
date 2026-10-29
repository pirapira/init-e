import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_ld_le64 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 100#8, 95#8, 108#8, 101#8, 54#8, 52#8]) = literalEntry (declToHOL Guest.Software.guestFn_ld_le64) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ld_be32 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 100#8, 95#8, 98#8, 101#8, 51#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_ld_be32) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bswap64 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 115#8, 119#8, 97#8, 112#8, 54#8, 52#8]) = literalEntry (declToHOL Guest.Software.guestFn_bswap64) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ld_be64 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [108#8, 100#8, 95#8, 98#8, 101#8, 54#8, 52#8]) = literalEntry (declToHOL Guest.Software.guestFn_ld_be64) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_st_le32 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 95#8, 108#8, 101#8, 51#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_st_le32) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_st_le64 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 95#8, 108#8, 101#8, 54#8, 52#8]) = literalEntry (declToHOL Guest.Software.guestFn_st_le64) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_st_be32 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 95#8, 98#8, 101#8, 51#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_st_be32) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_st_be64 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 95#8, 98#8, 101#8, 54#8, 52#8]) = literalEntry (declToHOL Guest.Software.guestFn_st_be64) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_input_blob :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 110#8, 112#8, 117#8, 116#8, 95#8, 98#8, 108#8, 111#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_input_blob) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_output_write :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 117#8, 116#8, 112#8, 117#8, 116#8, 95#8, 119#8, 114#8, 105#8, 116#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_output_write) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_min :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 105#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_min) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_max :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 97#8, 120#8]) = literalEntry (declToHOL Guest.Software.guestFn_max) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_udivmod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 100#8, 105#8, 118#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_udivmod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_udiv :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 100#8, 105#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_udiv) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_umod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_umod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ceil_log2 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 101#8, 105#8, 108#8, 95#8, 108#8, 111#8, 103#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_ceil_log2) := by
  rfl

end InitE.SourceWitness
