import InitE.SourceWitness.Terms025
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0400 globals0400

def chunk025 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_htab_union_into,
    declToHOL Guest.Software.guestFn_merge_tx_into_block,
    declToHOL Guest.Software.guestFn_track_ancestor_access,
    declToHOL Guest.Software.guestGlobal_bal_accounts,
    declToHOL Guest.Software.guestGlobal_bal_index,
    declToHOL Guest.Software.guestGlobal_bal_idx_accts,
    declToHOL Guest.Software.guestGlobal_bal_idx_stor,
    declToHOL Guest.Software.guestGlobal_bal_key_buf,
    declToHOL Guest.Software.guestFn_lst_new,
    declToHOL Guest.Software.guestFn_lst_new_scratch,
    declToHOL Guest.Software.guestFn_lst_push,
    declToHOL Guest.Software.guestFn_bal_init,
    declToHOL Guest.Software.guestFn_bal_ensure_account,
    declToHOL Guest.Software.guestFn_lst_upsert_idx,
    declToHOL Guest.Software.guestFn_add_storage_write,
    declToHOL Guest.Software.guestFn_add_storage_read]

theorem chunk025_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0400 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk025 =
        some (state0416 s) := by
  cbv

end InitE.SourceWitness
