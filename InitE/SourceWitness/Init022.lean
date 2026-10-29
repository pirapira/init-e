import InitE.SourceWitness.Terms022
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0352 globals0352

def chunk022 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestGlobal_journal,
    declToHOL Guest.Software.guestGlobal_journal_cap,
    declToHOL Guest.Software.guestFn_state_init,
    declToHOL Guest.Software.guestFn_state_fresh_tx,
    declToHOL Guest.Software.guestFn_jset,
    declToHOL Guest.Software.guestFn_jdel,
    declToHOL Guest.Software.guestFn_state_snapshot,
    declToHOL Guest.Software.guestFn_state_restore,
    declToHOL Guest.Software.guestFn_sk_make,
    declToHOL Guest.Software.guestFn_acct_new,
    declToHOL Guest.Software.guestFn_acct_empty,
    declToHOL Guest.Software.guestFn_acct_copy,
    declToHOL Guest.Software.guestFn_record_pre_state_read,
    declToHOL Guest.Software.guestFn_ws_account_leaf,
    declToHOL Guest.Software.guestFn_ws_get_account_optional,
    declToHOL Guest.Software.guestFn_ws_storage_root_of]

theorem chunk022_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0352 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk022 =
        some (state0368 s) := by
  cbv

end InitE.SourceWitness
