import InitE.SourceWitness.Terms052
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0849 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_zero32) code0848
def globals0849 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_zero32) globals0848
def exceptions0849 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_zero32) exceptions0848
def code0850 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_block_hashes) code0849
def globals0850 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_block_hashes) globals0849
def exceptions0850 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_block_hashes) exceptions0849
def code0851 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_block_hashes_n) code0850
def globals0851 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_block_hashes_n) globals0850
def exceptions0851 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_block_hashes_n) exceptions0850
def code0852 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_cur_si) code0851
def globals0852 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_cur_si) globals0851
def exceptions0852 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_cur_si) exceptions0851
def code0853 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_beacon_roots_address) code0852
def globals0853 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_beacon_roots_address) globals0852
def exceptions0853 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_beacon_roots_address) exceptions0852
def code0854 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_history_storage_address) code0853
def globals0854 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_history_storage_address) globals0853
def exceptions0854 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_history_storage_address) exceptions0853
def code0855 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_withdrawal_request_address) code0854
def globals0855 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_withdrawal_request_address) globals0854
def exceptions0855 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_withdrawal_request_address) exceptions0854
def code0856 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_consolidation_request_address) code0855
def globals0856 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_consolidation_request_address) globals0855
def exceptions0856 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_consolidation_request_address) exceptions0855
def code0857 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_builder_deposit_address) code0856
def globals0857 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_builder_deposit_address) globals0856
def exceptions0857 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_builder_deposit_address) exceptions0856
def code0858 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_builder_exit_address) code0857
def globals0858 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_builder_exit_address) globals0857
def exceptions0858 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_builder_exit_address) exceptions0857
def code0859 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_deposit_contract_address) code0858
def globals0859 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_deposit_contract_address) globals0858
def exceptions0859 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_deposit_contract_address) exceptions0858
def code0860 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_deposit_event_signature_hash) code0859
def globals0860 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_deposit_event_signature_hash) globals0859
def exceptions0860 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_deposit_event_signature_hash) exceptions0859
def code0861 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_addr_from_words) code0860
def globals0861 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_addr_from_words) globals0860
def exceptions0861 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_addr_from_words) exceptions0860
def code0862 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fork_init) code0861
def globals0862 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fork_init) globals0861
def exceptions0862 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fork_init) exceptions0861
def code0863 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_block_rlp_length) code0862
def globals0863 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_block_rlp_length) globals0862
def exceptions0863 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_block_rlp_length) exceptions0862
def code0864 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_wd_rlp_slices) code0863
def globals0864 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_wd_rlp_slices) globals0863
def exceptions0864 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_wd_rlp_slices) exceptions0863

def state0864 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0864
    code := code0864
    eshapes := exceptions0864
    structs := [] }

end InitE.SourceWitness
