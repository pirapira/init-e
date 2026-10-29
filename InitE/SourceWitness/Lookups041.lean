import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_bls_fp_pow :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 112#8, 111#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_bls_fp_pow) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bls_fp_sgn0 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 115#8, 103#8, 110#8, 48#8]) = literalEntry (declToHOL Guest.Software.guestFn_bls_fp_sgn0) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bls_fp_is_high :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 105#8, 115#8, 95#8, 104#8, 105#8, 103#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_bls_fp_is_high) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bls_fp_from_be48 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 98#8, 101#8, 52#8, 56#8]) = literalEntry (declToHOL Guest.Software.guestFn_bls_fp_from_be48) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bls_fp_to_be48 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 116#8, 111#8, 95#8, 98#8, 101#8, 52#8, 56#8]) = literalEntry (declToHOL Guest.Software.guestFn_bls_fp_to_be48) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bls_fp_decode64 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8, 54#8, 52#8]) = literalEntry (declToHOL Guest.Software.guestFn_bls_fp_decode64) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bls_fp_encode64 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 102#8, 112#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8, 54#8, 52#8]) = literalEntry (declToHOL Guest.Software.guestFn_bls_fp_encode64) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_copy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_copy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_set_zero :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 115#8, 101#8, 116#8, 95#8, 122#8, 101#8, 114#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_set_zero) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_set_one :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 115#8, 101#8, 116#8, 95#8, 111#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_set_one) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_is_zero :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 105#8, 115#8, 95#8, 122#8, 101#8, 114#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_is_zero) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_eq :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 101#8, 113#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_eq) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_sub :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 115#8, 117#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_sub) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_neg :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 110#8, 101#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_neg) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_dbl :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 100#8, 98#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_dbl) := by
  rfl

end InitE.SourceWitness
