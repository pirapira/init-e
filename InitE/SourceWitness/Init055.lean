import InitE.SourceWitness.Terms055
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0880 globals0880

def chunk055 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_attempt_l1,
    declToHOL Guest.Software.guestFn_attempt_l2,
    declToHOL Guest.Software.guestFn_attempt_l3,
    declToHOL Guest.Software.guestFn_attempt_l4,
    declToHOL Guest.Software.guestFn_attempt_l5,
    declToHOL Guest.Software.guestFn_attempt_l6,
    declToHOL Guest.Software.guestFn_attempt_l7,
    declToHOL Guest.Software.guestFn_verify_stateless_new_payload,
    declToHOL Guest.Software.guestGlobal_fail_code,
    declToHOL Guest.Software.guestFn_main]

theorem chunk055_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0880 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk055 =
        some (state0890 s) := by
  cbv

end InitE.SourceWitness
