import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_p256_fp_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 102#8, 112#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_fp_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_fp_sub :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 102#8, 112#8, 95#8, 115#8, 117#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_fp_sub) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_fp_reduce :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 102#8, 112#8, 95#8, 114#8, 101#8, 100#8, 117#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_fp_reduce) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_fp_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 102#8, 112#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_fp_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_fp_sqr :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 102#8, 112#8, 95#8, 115#8, 113#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_fp_sqr) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_fp_inv :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 102#8, 112#8, 95#8, 105#8, 110#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_fp_inv) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_set_infinity :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 115#8, 101#8, 116#8, 95#8, 105#8, 110#8, 102#8, 105#8, 110#8, 105#8, 116#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_set_infinity) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_set_affine :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 115#8, 101#8, 116#8, 95#8, 97#8, 102#8, 102#8, 105#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_set_affine) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_ec_double :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 101#8, 99#8, 95#8, 100#8, 111#8, 117#8, 98#8, 108#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_ec_double) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_ec_add_affine :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 101#8, 99#8, 95#8, 97#8, 100#8, 100#8, 95#8, 97#8, 102#8, 102#8, 105#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_ec_add_affine) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_ec_mul2 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 101#8, 99#8, 95#8, 109#8, 117#8, 108#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_ec_mul2) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_ec_to_affine :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 101#8, 99#8, 95#8, 116#8, 111#8, 95#8, 97#8, 102#8, 102#8, 105#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_ec_to_affine) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_on_curve :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 111#8, 110#8, 95#8, 99#8, 117#8, 114#8, 118#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_on_curve) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_p256_verify :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 50#8, 53#8, 54#8, 95#8, 118#8, 101#8, 114#8, 105#8, 102#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_p256_verify) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_p256verify :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 112#8, 50#8, 53#8, 54#8, 118#8, 101#8, 114#8, 105#8, 102#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_p256verify) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bn254_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 110#8, 50#8, 53#8, 52#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_bn254_init) := by
  rfl

end InitE.SourceWitness
