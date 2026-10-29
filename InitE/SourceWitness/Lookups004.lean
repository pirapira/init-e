import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_u256_div :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 100#8, 105#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_div) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_mod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_mod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_abs :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 97#8, 98#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_abs) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_sdiv :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 115#8, 100#8, 105#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_sdiv) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_smod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 115#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_smod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_addmod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 97#8, 100#8, 100#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_addmod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_mulmod :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 109#8, 117#8, 108#8, 109#8, 111#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_mulmod) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_bit_length64 :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 105#8, 116#8, 95#8, 108#8, 101#8, 110#8, 103#8, 116#8, 104#8, 54#8, 52#8]) = literalEntry (declToHOL Guest.Software.guestFn_bit_length64) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_bit_length :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 98#8, 105#8, 116#8, 95#8, 108#8, 101#8, 110#8, 103#8, 116#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_bit_length) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_byte_length :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 98#8, 121#8, 116#8, 101#8, 95#8, 108#8, 101#8, 110#8, 103#8, 116#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_byte_length) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_exp :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 101#8, 120#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_exp) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_shl :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 115#8, 104#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_shl) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_shr :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 115#8, 104#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_shr) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_sar :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 115#8, 97#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_sar) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_signextend :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 115#8, 105#8, 103#8, 110#8, 101#8, 120#8, 116#8, 101#8, 110#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_signextend) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_u256_byte :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [117#8, 50#8, 53#8, 54#8, 95#8, 98#8, 121#8, 116#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_u256_byte) := by
  rfl

end InitE.SourceWitness
