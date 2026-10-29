import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_u256_ws_init :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 119#8, 115#8, 95#8, 105#8, 110#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_ws_init) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_from_word :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 102#8, 114#8, 111#8, 109#8, 95#8, 119#8, 111#8, 114#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_from_word) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_low :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 108#8, 111#8, 119#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_low) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_fits_word :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 102#8, 105#8, 116#8, 115#8, 95#8, 119#8, 111#8, 114#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_fits_word) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_is_zero :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 105#8, 115#8, 95#8, 122#8, 101#8, 114#8, 111#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_is_zero) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_limb :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 108#8, 105#8, 109#8, 98#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_limb) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_bit :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 98#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_bit) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_eq :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 101#8, 113#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_eq) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_lt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 108#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_lt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_gt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 103#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_gt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_slt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 115#8, 108#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_slt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_sgt :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 115#8, 103#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_sgt) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_cmp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 99#8, 109#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_cmp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_not :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 110#8, 111#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_not) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_and :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 97#8, 110#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_and) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_or :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 111#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_or) := by
  rfl

end InitE.SourceWitness
