import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_u256_from_be :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 98#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_from_be) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_to_be32 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 116#8, 111#8, 95#8, 98#8, 101#8, 51#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_to_be32) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_to_be_min :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 116#8, 111#8, 95#8, 98#8, 101#8, 95#8, 109#8, 105#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_to_be_min) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sha256_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 104#8, 97#8, 50#8, 53#8, 54#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_sha256_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sha256_state_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 104#8, 97#8, 50#8, 53#8, 54#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_sha256_state_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sha256_block :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 104#8, 97#8, 50#8, 53#8, 54#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_sha256_block) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sha256_finish :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 104#8, 97#8, 50#8, 53#8, 54#8, 95#8, 102#8, 105#8, 110#8, 105#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_sha256_finish) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sha256 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 104#8, 97#8, 50#8, 53#8, 54#8]) = literalEntry (declToHOL Guest.Software.guestFn_sha256) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_sha256_pair :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 104#8, 97#8, 50#8, 53#8, 54#8, 95#8, 112#8, 97#8, 105#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_sha256_pair) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_keccak_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [107#8, 101#8, 99#8, 99#8, 97#8, 107#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_keccak_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_keccak_f1600 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [107#8, 101#8, 99#8, 99#8, 97#8, 107#8, 95#8, 102#8, 49#8, 54#8, 48#8, 48#8]) = literalEntry (declToHOL Guest.Software.guestFn_keccak_f1600) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_keccak_absorb_block :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [107#8, 101#8, 99#8, 99#8, 97#8, 107#8, 95#8, 97#8, 98#8, 115#8, 111#8, 114#8, 98#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_keccak_absorb_block) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_keccak256 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [107#8, 101#8, 99#8, 99#8, 97#8, 107#8, 50#8, 53#8, 54#8]) = literalEntry (declToHOL Guest.Software.guestFn_keccak256) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_fail :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 102#8, 97#8, 105#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_fail) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_read_length :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 114#8, 101#8, 97#8, 100#8, 95#8, 108#8, 101#8, 110#8, 103#8, 116#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_read_length) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_rlp_item :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 108#8, 112#8, 95#8, 105#8, 116#8, 101#8, 109#8]) = literalEntry (declToHOL Guest.Software.guestFn_rlp_item) := by
  rfl

end InitE.SourceWitness
