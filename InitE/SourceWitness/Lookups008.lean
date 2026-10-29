import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_htab_truncate :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 116#8, 114#8, 117#8, 110#8, 99#8, 97#8, 116#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_truncate) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_count :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_count) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_cap :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 99#8, 97#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_cap) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_item :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 105#8, 116#8, 101#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_item) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_keys :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 107#8, 101#8, 121#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_keys) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_copy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_copy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htab_copy_scratch :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 97#8, 98#8, 95#8, 99#8, 111#8, 112#8, 121#8, 95#8, 115#8, 99#8, 114#8, 97#8, 116#8, 99#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_htab_copy_scratch) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_secp256k1_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 99#8, 112#8, 50#8, 53#8, 54#8, 107#8, 49#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_secp256k1_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp_sub :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 95#8, 115#8, 117#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp_sub) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp_neg :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 95#8, 110#8, 101#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp_neg) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp_reduce :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 95#8, 114#8, 101#8, 100#8, 117#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp_reduce) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp_sqr :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 95#8, 115#8, 113#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp_sqr) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp_pow :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 95#8, 112#8, 111#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp_pow) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_fp_inv_fermat :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 112#8, 95#8, 105#8, 110#8, 118#8, 95#8, 102#8, 101#8, 114#8, 109#8, 97#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_fp_inv_fermat) := by
  rfl

end InitE.SourceWitness
