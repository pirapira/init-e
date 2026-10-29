import InitE.SourceWitness.Terms053
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0865 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_payload_header) code0864
def globals0865 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_payload_header) globals0864
def exceptions0865 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_payload_header) exceptions0864
def code0866 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_is_blob) code0865
def globals0866 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_is_blob) globals0865
def exceptions0866 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_is_blob) exceptions0865
def code0867 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_tx_is_setcode) code0866
def globals0867 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_tx_is_setcode) globals0866
def exceptions0867 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_tx_is_setcode) exceptions0866
def code0868 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fee_mul) code0867
def globals0868 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fee_mul) globals0867
def exceptions0868 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fee_mul) exceptions0867
def code0869 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_is_valid_versioned_hashes) code0868
def globals0869 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_is_valid_versioned_hashes) globals0868
def exceptions0869 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_is_valid_versioned_hashes) exceptions0868
def code0870 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_te_new) code0869
def globals0870 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_te_new) globals0869
def exceptions0870 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_te_new) exceptions0869
def code0871 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_process_unchecked_system_transaction) code0870
def globals0871 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_process_unchecked_system_transaction) globals0870
def exceptions0871 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_process_unchecked_system_transaction) exceptions0870
def code0872 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_process_checked_system_transaction) code0871
def globals0872 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_process_checked_system_transaction) globals0871
def exceptions0872 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_process_checked_system_transaction) exceptions0871
def code0873 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_check_transaction) code0872
def globals0873 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_check_transaction) globals0872
def exceptions0873 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_check_transaction) exceptions0872
def code0874 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_process_transaction) code0873
def globals0874 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_process_transaction) globals0873
def exceptions0874 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_process_transaction) exceptions0873
def code0875 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_udiv_small5) code0874
def globals0875 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_udiv_small5) globals0874
def exceptions0875 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_udiv_small5) exceptions0874
def code0876 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_process_withdrawals) code0875
def globals0876 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_process_withdrawals) globals0875
def exceptions0876 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_process_withdrawals) exceptions0875
def code0877 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_requests_append) code0876
def globals0877 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_requests_append) globals0876
def exceptions0877 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_requests_append) exceptions0876
def code0878 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_process_general_purpose_requests) code0877
def globals0878 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_process_general_purpose_requests) globals0877
def exceptions0878 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_process_general_purpose_requests) exceptions0877
def code0879 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_execute_block) code0878
def globals0879 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_execute_block) globals0878
def exceptions0879 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_execute_block) exceptions0878
def code0880 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_run_attempt) code0879
def globals0880 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_run_attempt) globals0879
def exceptions0880 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_run_attempt) exceptions0879

def state0880 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0880
    code := code0880
    eshapes := exceptions0880
    structs := [] }

end InitE.SourceWitness
