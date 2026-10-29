import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_fe_neg :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 110#8, 101#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_fe_neg) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fe_mul_small :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 109#8, 117#8, 108#8, 95#8, 115#8, 109#8, 97#8, 108#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fe_mul_small) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fe_is_zero :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 105#8, 115#8, 95#8, 122#8, 101#8, 114#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_fe_is_zero) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fe_eq :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 101#8, 113#8]) = literalEntry (declToHOL Guest.Software.guestFn_fe_eq) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fe_set_zero :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 115#8, 101#8, 116#8, 95#8, 122#8, 101#8, 114#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_fe_set_zero) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fe_set_one :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 101#8, 95#8, 115#8, 101#8, 116#8, 95#8, 111#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_fe_set_one) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ecp_set_inf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 112#8, 95#8, 115#8, 101#8, 116#8, 95#8, 105#8, 110#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_ecp_set_inf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ecp_is_inf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 112#8, 95#8, 105#8, 115#8, 95#8, 105#8, 110#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_ecp_is_inf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ecp_double :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 112#8, 95#8, 100#8, 111#8, 117#8, 98#8, 108#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_ecp_double) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ecp_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 112#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_ecp_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ecp_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 112#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_ecp_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ecp_linefunc :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 112#8, 95#8, 108#8, 105#8, 110#8, 101#8, 102#8, 117#8, 110#8, 99#8]) = literalEntry (declToHOL Guest.Software.guestFn_ecp_linefunc) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq12_twist :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 49#8, 50#8, 95#8, 116#8, 119#8, 105#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq12_twist) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq12_cast :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 49#8, 50#8, 95#8, 99#8, 97#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq12_cast) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq12_frob :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 49#8, 50#8, 95#8, 102#8, 114#8, 111#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq12_frob) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fq_poly_deg :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 113#8, 95#8, 112#8, 111#8, 108#8, 121#8, 95#8, 100#8, 101#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_fq_poly_deg) := by
  rfl

end InitE.SourceWitness
