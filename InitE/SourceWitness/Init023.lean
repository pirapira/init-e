import InitE.SourceWitness.Terms023
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0368 globals0368

def chunk023 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_ws_storage_trie,
    declToHOL Guest.Software.guestFn_ws_get_storage,
    declToHOL Guest.Software.guestFn_ws_get_code,
    declToHOL Guest.Software.guestFn_ws_account_has_storage,
    declToHOL Guest.Software.guestFn_get_pre_state_account_optional,
    declToHOL Guest.Software.guestFn_get_pre_state_account,
    declToHOL Guest.Software.guestFn_get_account_optional,
    declToHOL Guest.Software.guestFn_get_account,
    declToHOL Guest.Software.guestFn_get_code,
    declToHOL Guest.Software.guestFn_stor_lookup,
    declToHOL Guest.Software.guestFn_get_storage,
    declToHOL Guest.Software.guestFn_get_storage_original,
    declToHOL Guest.Software.guestFn_get_transient_storage,
    declToHOL Guest.Software.guestFn_account_exists,
    declToHOL Guest.Software.guestFn_account_has_storage,
    declToHOL Guest.Software.guestFn_account_deployable]

theorem chunk023_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0368 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk023 =
        some (state0384 s) := by
  cbv

end InitE.SourceWitness
