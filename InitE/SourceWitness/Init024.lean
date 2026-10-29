import InitE.SourceWitness.Terms024
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0384 globals0384

def chunk024 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_acct_is_empty,
    declToHOL Guest.Software.guestFn_account_exists_and_is_empty,
    declToHOL Guest.Software.guestFn_is_account_alive,
    declToHOL Guest.Software.guestFn_set_account,
    declToHOL Guest.Software.guestFn_set_storage,
    declToHOL Guest.Software.guestFn_destroy_storage,
    declToHOL Guest.Software.guestFn_destroy_account,
    declToHOL Guest.Software.guestFn_modify_state_commit,
    declToHOL Guest.Software.guestFn_clear_account_preserving_balance,
    declToHOL Guest.Software.guestFn_mark_account_created,
    declToHOL Guest.Software.guestFn_set_transient_storage,
    declToHOL Guest.Software.guestFn_move_ether,
    declToHOL Guest.Software.guestFn_create_ether,
    declToHOL Guest.Software.guestFn_set_account_balance,
    declToHOL Guest.Software.guestFn_increment_nonce,
    declToHOL Guest.Software.guestFn_set_code]

theorem chunk024_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0384 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk024 =
        some (state0400 s) := by
  cbv

end InitE.SourceWitness
