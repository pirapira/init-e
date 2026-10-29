import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_op_and :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 97#8, 110#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_and) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_or :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 111#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_or) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_xor :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 120#8, 111#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_xor) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_not :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 110#8, 111#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_not) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_byte :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 98#8, 121#8, 116#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_byte) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_shl :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 104#8, 108#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_shl) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_shr :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 104#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_shr) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_sar :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 97#8, 114#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_sar) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_clz :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 108#8, 122#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_clz) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_keccak :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 107#8, 101#8, 99#8, 99#8, 97#8, 107#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_keccak) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_stop :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 116#8, 111#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_stop) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_jump :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 106#8, 117#8, 109#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_jump) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_jumpi :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 106#8, 117#8, 109#8, 112#8, 105#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_jumpi) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_pc :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 112#8, 99#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_pc) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_gas :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 103#8, 97#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_gas) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_jumpdest :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 106#8, 117#8, 109#8, 112#8, 100#8, 101#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_jumpdest) := by
  rfl

end InitE.SourceWitness
