import InitE.SourceWitness.LookupBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.Pancake.PanLang

@[scoped cbv_eval] theorem code_guestFn_htr_list_roots :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 108#8, 105#8, 115#8, 116#8, 95#8, 114#8, 111#8, 111#8, 116#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_list_roots) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_payload :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 112#8, 97#8, 121#8, 108#8, 111#8, 97#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_payload) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_deposit :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 100#8, 101#8, 112#8, 111#8, 115#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_deposit) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_wdreq :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 119#8, 100#8, 114#8, 101#8, 113#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_wdreq) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_cons :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 99#8, 111#8, 110#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_cons) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_bdep :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 98#8, 100#8, 101#8, 112#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_bdep) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_bexit :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 98#8, 101#8, 120#8, 105#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_bexit) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_request_list :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8, 95#8, 108#8, 105#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_request_list) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_requests :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8, 115#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_requests) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_htr_new_payload_request :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 116#8, 114#8, 95#8, 110#8, 101#8, 119#8, 95#8, 112#8, 97#8, 121#8, 108#8, 111#8, 97#8, 100#8, 95#8, 114#8, 101#8, 113#8, 117#8, 101#8, 115#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_htr_new_payload_request) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_serialize_result :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [115#8, 101#8, 114#8, 105#8, 97#8, 108#8, 105#8, 122#8, 101#8, 95#8, 114#8, 101#8, 115#8, 117#8, 108#8, 116#8]) = literalEntry (declToHOL Guest.Software.guestFn_serialize_result) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_hdr_uint_field :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 100#8, 114#8, 95#8, 117#8, 105#8, 110#8, 116#8, 95#8, 102#8, 105#8, 101#8, 108#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_hdr_uint_field) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_hdr_word_field :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 100#8, 114#8, 95#8, 119#8, 111#8, 114#8, 100#8, 95#8, 102#8, 105#8, 101#8, 108#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_hdr_word_field) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_hdr_u256_field :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 100#8, 114#8, 95#8, 117#8, 50#8, 53#8, 54#8, 95#8, 102#8, 105#8, 101#8, 108#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_hdr_u256_field) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_hdr_bytes_field :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 100#8, 114#8, 95#8, 98#8, 121#8, 116#8, 101#8, 115#8, 95#8, 102#8, 105#8, 101#8, 108#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_hdr_bytes_field) := by
  rfl

@[scoped cbv_eval] theorem code_guestFn_hdr_raw_field :
    code0890.lookup (Basis.Pure.MlString.MlString.implode [104#8, 100#8, 114#8, 95#8, 114#8, 97#8, 119#8, 95#8, 102#8, 105#8, 101#8, 108#8, 100#8]) = literalEntry (declToHOL Guest.Software.guestFn_hdr_raw_field) := by
  rfl

end InitE.SourceWitness
