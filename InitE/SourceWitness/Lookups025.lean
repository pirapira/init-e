import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_to_address_masked :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [116#8, 111#8, 95#8, 97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8, 95#8, 109#8, 97#8, 115#8, 107#8, 101#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_to_address_masked) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_address_to_u256 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [97#8, 100#8, 100#8, 114#8, 101#8, 115#8, 115#8, 95#8, 116#8, 111#8, 95#8, 117#8, 50#8, 53#8, 54#8]) = literalEntry (declToHOL Guest.Software.guestFn_address_to_u256) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_is_valid_delegation :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [105#8, 115#8, 95#8, 118#8, 97#8, 108#8, 105#8, 100#8, 95#8, 100#8, 101#8, 108#8, 101#8, 103#8, 97#8, 116#8, 105#8, 111#8, 110#8]) = literalEntry (declToHOL Guest.Software.guestFn_is_valid_delegation) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_check_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 104#8, 101#8, 99#8, 107#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_check_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_charge_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 104#8, 97#8, 114#8, 103#8, 101#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_charge_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_charge_state_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 104#8, 97#8, 114#8, 103#8, 101#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_charge_state_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_credit_state_gas_refund :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [99#8, 114#8, 101#8, 100#8, 105#8, 116#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 103#8, 97#8, 115#8, 95#8, 114#8, 101#8, 102#8, 117#8, 110#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_credit_state_gas_refund) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_frame_state_gas_used :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 103#8, 97#8, 115#8, 95#8, 117#8, 115#8, 101#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_frame_state_gas_used) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_refill_frame_state_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [114#8, 101#8, 102#8, 105#8, 108#8, 108#8, 95#8, 102#8, 114#8, 97#8, 109#8, 101#8, 95#8, 115#8, 116#8, 97#8, 116#8, 101#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_refill_frame_state_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_stack_pop :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 99#8, 107#8, 95#8, 112#8, 111#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_stack_pop) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_stack_push :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 99#8, 107#8, 95#8, 112#8, 117#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_stack_push) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_stack_push_word :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 99#8, 107#8, 95#8, 112#8, 117#8, 115#8, 104#8, 95#8, 119#8, 111#8, 114#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_stack_push_word) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_stack_push_bool :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 116#8, 97#8, 99#8, 107#8, 95#8, 112#8, 117#8, 115#8, 104#8, 95#8, 98#8, 111#8, 111#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_stack_push_bool) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_memory_gas_cost :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [109#8, 101#8, 109#8, 111#8, 114#8, 121#8, 95#8, 103#8, 97#8, 115#8, 95#8, 99#8, 111#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_memory_gas_cost) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_extend_memory_cost1 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 120#8, 116#8, 101#8, 110#8, 100#8, 95#8, 109#8, 101#8, 109#8, 111#8, 114#8, 121#8, 95#8, 99#8, 111#8, 115#8, 116#8, 49#8]) = literalEntry (declToHOL Guest.Software.guestFn_extend_memory_cost1) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_extend_memory_cost2 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 120#8, 116#8, 101#8, 110#8, 100#8, 95#8, 109#8, 101#8, 109#8, 111#8, 114#8, 121#8, 95#8, 99#8, 111#8, 115#8, 116#8, 50#8]) = literalEntry (declToHOL Guest.Software.guestFn_extend_memory_cost2) := by
  rfl

end InitE.SourceWitness
