import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_fp6_inv :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 54#8, 95#8, 105#8, 110#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp6_inv) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_copy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_copy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_set_one :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 115#8, 101#8, 116#8, 95#8, 111#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_set_one) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_is_one :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 105#8, 115#8, 95#8, 111#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_is_one) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_sqr :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 115#8, 113#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_sqr) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_conj :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 99#8, 111#8, 110#8, 106#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_conj) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_inv :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 105#8, 110#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_inv) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_frob :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 102#8, 114#8, 111#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_frob) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_pow_absx :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 112#8, 111#8, 119#8, 95#8, 97#8, 98#8, 115#8, 120#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_pow_absx) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_exp_x :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 101#8, 120#8, 112#8, 95#8, 120#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_exp_x) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp12_final_exp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 49#8, 50#8, 95#8, 102#8, 105#8, 110#8, 97#8, 108#8, 95#8, 101#8, 120#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp12_final_exp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_set_inf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 115#8, 101#8, 116#8, 95#8, 105#8, 110#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_set_inf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_is_inf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 105#8, 115#8, 95#8, 105#8, 110#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_is_inf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_copy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_copy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_neg :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 110#8, 101#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_neg) := by
  rfl

end InitE.SourceWitness
