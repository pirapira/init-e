import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_u256_xor :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 120#8, 111#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_xor) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_add_carry :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 97#8, 100#8, 100#8, 95#8, 99#8, 97#8, 114#8, 114#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_add_carry) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_add :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 97#8, 100#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_add) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_sub :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 115#8, 117#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_sub) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_neg :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 110#8, 101#8, 103#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_neg) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_mul64x64 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 117#8, 108#8, 54#8, 52#8, 120#8, 54#8, 52#8]) = literalEntry (declToHOL Guest.Software.guestFn_mul64x64) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_mul :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 109#8, 117#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_mul) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_mul_full :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 109#8, 117#8, 108#8, 95#8, 102#8, 117#8, 108#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_mul_full) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_nlz32 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [110#8, 108#8, 122#8, 51#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_nlz32) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_div64by32 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 105#8, 118#8, 54#8, 52#8, 98#8, 121#8, 51#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_div64by32) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_to_digits :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 116#8, 111#8, 95#8, 100#8, 105#8, 103#8, 105#8, 116#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_to_digits) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_digits_to_u256 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 105#8, 103#8, 105#8, 116#8, 115#8, 95#8, 116#8, 111#8, 95#8, 117#8, 50#8, 53#8, 54#8]) = literalEntry (declToHOL Guest.Software.guestFn_digits_to_u256) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_digits_len :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 105#8, 103#8, 105#8, 116#8, 115#8, 95#8, 108#8, 101#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_digits_len) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_divmnu :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 105#8, 118#8, 109#8, 110#8, 117#8]) = literalEntry (declToHOL Guest.Software.guestFn_divmnu) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_digits_divmod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [100#8, 105#8, 103#8, 105#8, 116#8, 115#8, 95#8, 100#8, 105#8, 118#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_digits_divmod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_divmod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 100#8, 105#8, 118#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_divmod) := by
  rfl

end InitE.SourceWitness
