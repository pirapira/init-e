import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_bls_precompiles_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 112#8, 114#8, 101#8, 99#8, 111#8, 109#8, 112#8, 105#8, 108#8, 101#8, 115#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_bls_precompiles_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bls_g1_msm_discount :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 103#8, 49#8, 95#8, 109#8, 115#8, 109#8, 95#8, 100#8, 105#8, 115#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_bls_g1_msm_discount) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bls_g2_msm_discount :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 115#8, 95#8, 103#8, 50#8, 95#8, 109#8, 115#8, 109#8, 95#8, 100#8, 105#8, 115#8, 99#8, 111#8, 117#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_bls_g2_msm_discount) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_bls_g1_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 103#8, 49#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_bls_g1_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_bls_g1_msm :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 103#8, 49#8, 95#8, 109#8, 115#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_bls_g1_msm) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_bls_g2_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 103#8, 50#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_bls_g2_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_bls_g2_msm :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 103#8, 50#8, 95#8, 109#8, 115#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_bls_g2_msm) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_bls_pairing :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 112#8, 97#8, 105#8, 114#8, 105#8, 110#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_bls_pairing) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_bls_map_fp_to_g1 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 109#8, 97#8, 112#8, 95#8, 102#8, 112#8, 95#8, 116#8, 111#8, 95#8, 103#8, 49#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_bls_map_fp_to_g1) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_bls_map_fp2_to_g2 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 98#8, 108#8, 115#8, 95#8, 109#8, 97#8, 112#8, 95#8, 102#8, 112#8, 50#8, 95#8, 116#8, 111#8, 95#8, 103#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_bls_map_fp2_to_g2) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_kzg_point_evaluation :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 107#8, 122#8, 103#8, 95#8, 112#8, 111#8, 105#8, 110#8, 116#8, 95#8, 101#8, 118#8, 97#8, 108#8, 117#8, 97#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_kzg_point_evaluation) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_precompile_index :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 99#8, 111#8, 109#8, 112#8, 105#8, 108#8, 101#8, 95#8, 105#8, 110#8, 100#8, 101#8, 120#8]) = literalEntry (declToHOL Guest.Software.guestFn_precompile_index) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_identity :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 105#8, 100#8, 101#8, 110#8, 116#8, 105#8, 116#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_identity) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_sha256 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 115#8, 104#8, 97#8, 50#8, 53#8, 54#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_sha256) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_ecrecover :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 101#8, 99#8, 114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_ecrecover) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pre_ripemd160 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 114#8, 101#8, 95#8, 114#8, 105#8, 112#8, 101#8, 109#8, 100#8, 49#8, 54#8, 48#8]) = literalEntry (declToHOL Guest.Software.guestFn_pre_ripemd160) := by
  rfl

end InitE.SourceWitness
