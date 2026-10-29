import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_g2_on_curve :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 111#8, 110#8, 95#8, 99#8, 117#8, 114#8, 118#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_on_curve) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_decode :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 100#8, 101#8, 99#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_decode) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_encode :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 101#8, 110#8, 99#8, 111#8, 100#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_encode) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_g2_subgroup_check :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [103#8, 50#8, 95#8, 115#8, 117#8, 98#8, 103#8, 114#8, 111#8, 117#8, 112#8, 95#8, 99#8, 104#8, 101#8, 99#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_g2_subgroup_check) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pair_doubling_step :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 97#8, 105#8, 114#8, 95#8, 100#8, 111#8, 117#8, 98#8, 108#8, 105#8, 110#8, 103#8, 95#8, 115#8, 116#8, 101#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_pair_doubling_step) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pair_addition_step :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 97#8, 105#8, 114#8, 95#8, 97#8, 100#8, 100#8, 105#8, 116#8, 105#8, 111#8, 110#8, 95#8, 115#8, 116#8, 101#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_pair_addition_step) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pair_ell :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 97#8, 105#8, 114#8, 95#8, 101#8, 108#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_pair_ell) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pair_miller_loop :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 97#8, 105#8, 114#8, 95#8, 109#8, 105#8, 108#8, 108#8, 101#8, 114#8, 95#8, 108#8, 111#8, 111#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_pair_miller_loop) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pair_accumulate :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 97#8, 105#8, 114#8, 95#8, 97#8, 99#8, 99#8, 117#8, 109#8, 117#8, 108#8, 97#8, 116#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_pair_accumulate) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_swu_sqrt_division_fp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 119#8, 117#8, 95#8, 115#8, 113#8, 114#8, 116#8, 95#8, 100#8, 105#8, 118#8, 105#8, 115#8, 105#8, 111#8, 110#8, 95#8, 102#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_swu_sqrt_division_fp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_swu_g1 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 119#8, 117#8, 95#8, 103#8, 49#8]) = literalEntry (declToHOL Guest.Software.guestFn_swu_g1) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_iso_horner_fp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 115#8, 111#8, 95#8, 104#8, 111#8, 114#8, 110#8, 101#8, 114#8, 95#8, 102#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_iso_horner_fp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_iso_map_g1 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 115#8, 111#8, 95#8, 109#8, 97#8, 112#8, 95#8, 103#8, 49#8]) = literalEntry (declToHOL Guest.Software.guestFn_iso_map_g1) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_map_fp_to_g1 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 97#8, 112#8, 95#8, 102#8, 112#8, 95#8, 116#8, 111#8, 95#8, 103#8, 49#8]) = literalEntry (declToHOL Guest.Software.guestFn_map_fp_to_g1) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_swu_sqrt_division_fp2 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 119#8, 117#8, 95#8, 115#8, 113#8, 114#8, 116#8, 95#8, 100#8, 105#8, 118#8, 105#8, 115#8, 105#8, 111#8, 110#8, 95#8, 102#8, 112#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_swu_sqrt_division_fp2) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_swu_g2 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 119#8, 117#8, 95#8, 103#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_swu_g2) := by
  rfl

end InitE.SourceWitness
