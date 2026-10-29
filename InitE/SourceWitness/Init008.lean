import InitE.SourceWitness.Terms008
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0128 globals0128

def chunk008 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_htab_new,
    declToHOL Guest.Software.guestFn_htab_new_scratch,
    declToHOL Guest.Software.guestFn_htab_first_diff,
    declToHOL Guest.Software.guestFn_htab_find_leaf,
    declToHOL Guest.Software.guestFn_htab_get,
    declToHOL Guest.Software.guestFn_htab_has,
    declToHOL Guest.Software.guestFn_htab_new_node,
    declToHOL Guest.Software.guestFn_htab_new_leaf,
    declToHOL Guest.Software.guestFn_htab_new_internal,
    declToHOL Guest.Software.guestFn_htab_grow,
    declToHOL Guest.Software.guestFn_htab_set,
    declToHOL Guest.Software.guestFn_htab_del,
    declToHOL Guest.Software.guestFn_htab_truncate,
    declToHOL Guest.Software.guestFn_htab_count,
    declToHOL Guest.Software.guestFn_htab_cap,
    declToHOL Guest.Software.guestFn_htab_item]

theorem chunk008_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0128 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk008 =
        some (state0144 s) := by
  cbv

end InitE.SourceWitness
