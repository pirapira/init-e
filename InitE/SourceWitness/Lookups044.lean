import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_g1_double :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 100#8, 111#8, 117#8, 98#8, 108#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_double) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_normalize :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 110#8, 111#8, 114#8, 109#8, 97#8, 108#8, 105#8, 122#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_normalize) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_on_curve :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 111#8, 110#8, 95#8, 99#8, 117#8, 114#8, 118#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_on_curve) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_decode :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_decode) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_encode :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_encode) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g1_subgroup_check :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 49#8, 95#8, 115#8, 117#8, 98#8, 103#8, 114#8, 111#8, 117#8, 112#8, 95#8, 99#8, 104#8, 101#8, 99#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_g1_subgroup_check) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_set_inf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 115#8, 101#8, 116#8, 95#8, 105#8, 110#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_set_inf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_is_inf :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 105#8, 115#8, 95#8, 105#8, 110#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_is_inf) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_copy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_copy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_neg :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 110#8, 101#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_neg) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_double :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 100#8, 111#8, 117#8, 98#8, 108#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_double) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_normalize :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 110#8, 111#8, 114#8, 109#8, 97#8, 108#8, 105#8, 122#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_normalize) := by
  rfl

end InitE.SourceWitness
