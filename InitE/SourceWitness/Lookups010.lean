import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_ec_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_ec_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ec_mul2 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 95#8, 109#8, 117#8, 108#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_ec_mul2) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ec_to_affine :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 95#8, 116#8, 111#8, 95#8, 97#8, 102#8, 102#8, 105#8, 110#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_ec_to_affine) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ec_on_curve :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 99#8, 95#8, 111#8, 110#8, 95#8, 99#8, 117#8, 114#8, 118#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_ec_on_curve) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_secp256k1_decompress_r :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 99#8, 112#8, 50#8, 53#8, 54#8, 107#8, 49#8, 95#8, 100#8, 101#8, 99#8, 111#8, 109#8, 112#8, 114#8, 101#8, 115#8, 115#8, 95#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_secp256k1_decompress_r) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_secp256k1_recover :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 99#8, 112#8, 50#8, 53#8, 54#8, 107#8, 49#8, 95#8, 114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_secp256k1_recover) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_secp256k1_address_of_point :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 99#8, 112#8, 50#8, 53#8, 54#8, 107#8, 49#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8, 95#8, 111#8, 102#8, 95#8, 112#8, 111#8, 105#8, 110#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_secp256k1_address_of_point) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_secp256k1_ecrecover :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 99#8, 112#8, 50#8, 53#8, 54#8, 107#8, 49#8, 95#8, 101#8, 99#8, 114#8, 101#8, 99#8, 111#8, 118#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_secp256k1_ecrecover) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ssz_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 115#8, 122#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_ssz_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_merkleize :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 101#8, 114#8, 107#8, 108#8, 101#8, 105#8, 122#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_merkleize) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mix_in_length :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 105#8, 120#8, 95#8, 105#8, 110#8, 95#8, 108#8, 101#8, 110#8, 103#8, 116#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_mix_in_length) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_merkleize_progressive :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 101#8, 114#8, 107#8, 108#8, 101#8, 105#8, 122#8, 101#8, 95#8, 112#8, 114#8, 111#8, 103#8, 114#8, 101#8, 115#8, 115#8, 105#8, 118#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_merkleize_progressive) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_plist_chunks :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 112#8, 108#8, 105#8, 115#8, 116#8, 95#8, 99#8, 104#8, 117#8, 110#8, 107#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_plist_chunks) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_pbytes :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 112#8, 98#8, 121#8, 116#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_pbytes) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_pcontainer :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 112#8, 99#8, 111#8, 110#8, 116#8, 97#8, 105#8, 110#8, 101#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_pcontainer) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_pack_bytes :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [112#8, 97#8, 99#8, 107#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_pack_bytes) := by
  rfl

end InitE.SourceWitness
