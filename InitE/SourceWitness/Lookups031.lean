import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_op_codesize :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 111#8, 100#8, 101#8, 115#8, 105#8, 122#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_codesize) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_codecopy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 111#8, 100#8, 101#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_codecopy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_gasprice :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 103#8, 97#8, 115#8, 112#8, 114#8, 105#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_gasprice) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_ext_code_of :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [101#8, 120#8, 116#8, 95#8, 99#8, 111#8, 100#8, 101#8, 95#8, 111#8, 102#8]) = literalEntry (declToHOL Guest.Software.guestFn_ext_code_of) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_extcodesize :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 101#8, 120#8, 116#8, 99#8, 111#8, 100#8, 101#8, 115#8, 105#8, 122#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_extcodesize) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_extcodecopy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 101#8, 120#8, 116#8, 99#8, 111#8, 100#8, 101#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_extcodecopy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_returndatasize :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 114#8, 101#8, 116#8, 117#8, 114#8, 110#8, 100#8, 97#8, 116#8, 97#8, 115#8, 105#8, 122#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_returndatasize) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_returndatacopy :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 114#8, 101#8, 116#8, 117#8, 114#8, 110#8, 100#8, 97#8, 116#8, 97#8, 99#8, 111#8, 112#8, 121#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_returndatacopy) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_extcodehash :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 101#8, 120#8, 116#8, 99#8, 111#8, 100#8, 101#8, 104#8, 97#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_extcodehash) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_selfbalance :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 115#8, 101#8, 108#8, 102#8, 98#8, 97#8, 108#8, 97#8, 110#8, 99#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_selfbalance) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_block_env :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [98#8, 108#8, 111#8, 99#8, 107#8, 95#8, 101#8, 110#8, 118#8]) = literalEntry (declToHOL Guest.Software.guestFn_block_env) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_basefee :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 98#8, 97#8, 115#8, 101#8, 102#8, 101#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_basefee) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_blobhash :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 98#8, 108#8, 111#8, 98#8, 104#8, 97#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_blobhash) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_blobbasefee :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 98#8, 108#8, 111#8, 98#8, 98#8, 97#8, 115#8, 101#8, 102#8, 101#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_blobbasefee) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_blockhash :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 98#8, 108#8, 111#8, 99#8, 107#8, 104#8, 97#8, 115#8, 104#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_blockhash) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_op_coinbase :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [111#8, 112#8, 95#8, 99#8, 111#8, 105#8, 110#8, 98#8, 97#8, 115#8, 101#8]) = literalEntry (declToHOL Guest.Software.guestFn_op_coinbase) := by
  rfl

end InitE.SourceWitness
