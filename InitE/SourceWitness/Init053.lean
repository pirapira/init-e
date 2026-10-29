import InitE.SourceWitness.Terms053
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0848 globals0848

def chunk053 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestGlobal_zero32,
    declToHOL Guest.Software.guestGlobal_block_hashes,
    declToHOL Guest.Software.guestGlobal_block_hashes_n,
    declToHOL Guest.Software.guestGlobal_cur_si,
    declToHOL Guest.Software.guestGlobal_beacon_roots_address,
    declToHOL Guest.Software.guestGlobal_history_storage_address,
    declToHOL Guest.Software.guestGlobal_withdrawal_request_address,
    declToHOL Guest.Software.guestGlobal_consolidation_request_address,
    declToHOL Guest.Software.guestGlobal_builder_deposit_address,
    declToHOL Guest.Software.guestGlobal_builder_exit_address,
    declToHOL Guest.Software.guestGlobal_deposit_contract_address,
    declToHOL Guest.Software.guestGlobal_deposit_event_signature_hash,
    declToHOL Guest.Software.guestFn_addr_from_words,
    declToHOL Guest.Software.guestFn_fork_init,
    declToHOL Guest.Software.guestFn_block_rlp_length,
    declToHOL Guest.Software.guestGlobal_wd_rlp_slices]

theorem chunk053_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0848 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk053 =
        some (state0864 s) := by
  cbv

end InitE.SourceWitness
