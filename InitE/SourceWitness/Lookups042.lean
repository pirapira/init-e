import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_fp2_conj :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 99#8, 111#8, 110#8, 106#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_conj) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_sqr :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 115#8, 113#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_sqr) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_mul_xi :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 109#8, 117#8, 108#8, 95#8, 120#8, 105#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_mul_xi) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_scale :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 115#8, 99#8, 97#8, 108#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_scale) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_inv :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 105#8, 110#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_inv) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_pow :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 112#8, 111#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_pow) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp2_sgn0 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 50#8, 95#8, 115#8, 103#8, 110#8, 48#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp2_sgn0) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp6_copy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp6_copy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp6_set_zero :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 115#8, 101#8, 116#8, 95#8, 122#8, 101#8, 114#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp6_set_zero) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp6_set_one :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 115#8, 101#8, 116#8, 95#8, 111#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp6_set_one) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp6_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp6_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp6_sub :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 115#8, 117#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp6_sub) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp6_neg :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 110#8, 101#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp6_neg) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp6_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp6_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp6_mul_v :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 109#8, 117#8, 108#8, 95#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp6_mul_v) := by
  rfl

end InitE.SourceWitness
