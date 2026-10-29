import InitE.SourceWitness.Terms026
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0416 globals0416

def chunk026 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_add_balance_change,
    declToHOL Guest.Software.guestFn_add_nonce_change,
    declToHOL Guest.Software.guestFn_add_code_change,
    declToHOL Guest.Software.guestFn_add_touched_account,
    declToHOL Guest.Software.guestFn_get_pre_tx_account,
    declToHOL Guest.Software.guestFn_get_pre_tx_storage,
    declToHOL Guest.Software.guestFn_idx_start_account,
    declToHOL Guest.Software.guestFn_idx_start_storage,
    declToHOL Guest.Software.guestFn_bal_list_remove_idx,
    declToHOL Guest.Software.guestFn_bal_remove_change,
    declToHOL Guest.Software.guestFn_remove_storage_write,
    declToHOL Guest.Software.guestFn_update_builder_from_tx,
    declToHOL Guest.Software.guestFn_incorporate_tx_into_block,
    declToHOL Guest.Software.guestFn_bal_sort_gt,
    declToHOL Guest.Software.guestFn_sort_elems,
    declToHOL Guest.Software.guestFn_sorted_keys32]

theorem chunk026_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0416 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk026 =
        some (state0432 s) := by
  cbv

end InitE.SourceWitness
