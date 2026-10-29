import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_fq_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq_sub :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 95#8, 115#8, 117#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq_sub) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq_neg :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 95#8, 110#8, 101#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq_neg) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq_to_mont :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 95#8, 116#8, 111#8, 95#8, 109#8, 111#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq_to_mont) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq_from_mont :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 109#8, 111#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq_from_mont) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq_inv :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 95#8, 105#8, 110#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq_inv) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq_mul_small :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 95#8, 109#8, 117#8, 108#8, 95#8, 115#8, 109#8, 97#8, 108#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq_mul_small) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq2_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 50#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq2_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq12_reduce :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 49#8, 50#8, 95#8, 114#8, 101#8, 100#8, 117#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq12_reduce) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq12_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 49#8, 50#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq12_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq12_sqr :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 49#8, 50#8, 95#8, 115#8, 113#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq12_sqr) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fe_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fe_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fe_sqr :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 115#8, 113#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_fe_sqr) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fe_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_fe_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fe_sub :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 115#8, 117#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_fe_sub) := by
  rfl

end InitE.SourceWitness
