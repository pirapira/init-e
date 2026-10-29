import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_modinv_bin :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 111#8, 100#8, 105#8, 110#8, 118#8, 95#8, 98#8, 105#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_modinv_bin) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mod_half :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 111#8, 100#8, 95#8, 104#8, 97#8, 108#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_mod_half) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mod_sub :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 111#8, 100#8, 95#8, 115#8, 117#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_mod_sub) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp_inv :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 95#8, 105#8, 110#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp_inv) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp_sqrt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 95#8, 115#8, 113#8, 114#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp_sqrt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fn_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 110#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fn_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fn_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 110#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_fn_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fn_pow :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 110#8, 95#8, 112#8, 111#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_fn_pow) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fn_inv_fermat :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 110#8, 95#8, 105#8, 110#8, 118#8, 95#8, 102#8, 101#8, 114#8, 109#8, 97#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_fn_inv_fermat) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fn_inv :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 110#8, 95#8, 105#8, 110#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_fn_inv) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ec_set_infinity :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 95#8, 115#8, 101#8, 116#8, 95#8, 105#8, 110#8, 102#8, 105#8, 110#8, 105#8, 116#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_ec_set_infinity) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ec_set_affine :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 95#8, 115#8, 101#8, 116#8, 95#8, 97#8, 102#8, 102#8, 105#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_ec_set_affine) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ec_is_infinity :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 95#8, 105#8, 115#8, 95#8, 105#8, 110#8, 102#8, 105#8, 110#8, 105#8, 116#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_ec_is_infinity) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ec_double :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 95#8, 100#8, 111#8, 117#8, 98#8, 108#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_ec_double) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ec_add_affine :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 95#8, 97#8, 100#8, 100#8, 95#8, 97#8, 102#8, 102#8, 105#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_ec_add_affine) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ec_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_ec_add) := by
  rfl

end InitE.SourceWitness
