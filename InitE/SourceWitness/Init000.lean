import InitE.SourceWitness.Terms000
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0000 globals0000

def chunk000 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestGlobal_heap_ptr,
    declToHOL Guest.Software.guestGlobal_journal_n,
    declToHOL Guest.Software.guestExn_TrapErr,
    declToHOL Guest.Software.guestFn_trap_with,
    declToHOL Guest.Software.guestGlobal_scratch_ptr,
    declToHOL Guest.Software.guestGlobal_frame_mem_ptr,
    declToHOL Guest.Software.guestFn_mem_init,
    declToHOL Guest.Software.guestFn_alloc,
    declToHOL Guest.Software.guestFn_heap_mark,
    declToHOL Guest.Software.guestFn_heap_release,
    declToHOL Guest.Software.guestFn_frame_mem_alloc,
    declToHOL Guest.Software.guestFn_frame_mem_mark,
    declToHOL Guest.Software.guestFn_frame_mem_release,
    declToHOL Guest.Software.guestFn_scratch_alloc,
    declToHOL Guest.Software.guestFn_scratch_mark,
    declToHOL Guest.Software.guestFn_scratch_release]

theorem chunk000_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0000 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk000 =
        some (state0016 s) := by
  cbv

end InitE.SourceWitness
