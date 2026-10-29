import InitE.SourceWitness.InitializationBase
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0001 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_heap_ptr) code0000
def globals0001 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_heap_ptr) globals0000
def exceptions0001 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_heap_ptr) exceptions0000
def code0002 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_journal_n) code0001
def globals0002 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_journal_n) globals0001
def exceptions0002 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_journal_n) exceptions0001
def code0003 : CodeTable :=
  installCode (declToHOL Guest.Software.guestExn_TrapErr) code0002
def globals0003 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestExn_TrapErr) globals0002
def exceptions0003 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestExn_TrapErr) exceptions0002
def code0004 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_trap_with) code0003
def globals0004 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_trap_with) globals0003
def exceptions0004 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_trap_with) exceptions0003
def code0005 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_scratch_ptr) code0004
def globals0005 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_scratch_ptr) globals0004
def exceptions0005 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_scratch_ptr) exceptions0004
def code0006 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_frame_mem_ptr) code0005
def globals0006 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_frame_mem_ptr) globals0005
def exceptions0006 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_frame_mem_ptr) exceptions0005
def code0007 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_mem_init) code0006
def globals0007 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_mem_init) globals0006
def exceptions0007 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_mem_init) exceptions0006
def code0008 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_alloc) code0007
def globals0008 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_alloc) globals0007
def exceptions0008 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_alloc) exceptions0007
def code0009 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_heap_mark) code0008
def globals0009 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_heap_mark) globals0008
def exceptions0009 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_heap_mark) exceptions0008
def code0010 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_heap_release) code0009
def globals0010 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_heap_release) globals0009
def exceptions0010 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_heap_release) exceptions0009
def code0011 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_mem_alloc) code0010
def globals0011 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_mem_alloc) globals0010
def exceptions0011 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_mem_alloc) exceptions0010
def code0012 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_mem_mark) code0011
def globals0012 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_mem_mark) globals0011
def exceptions0012 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_mem_mark) exceptions0011
def code0013 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_mem_release) code0012
def globals0013 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_mem_release) globals0012
def exceptions0013 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_mem_release) exceptions0012
def code0014 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_scratch_alloc) code0013
def globals0014 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_scratch_alloc) globals0013
def exceptions0014 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_scratch_alloc) exceptions0013
def code0015 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_scratch_mark) code0014
def globals0015 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_scratch_mark) globals0014
def exceptions0015 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_scratch_mark) exceptions0014
def code0016 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_scratch_release) code0015
def globals0016 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_scratch_release) globals0015
def exceptions0016 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_scratch_release) exceptions0015

def state0016 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0016
    code := code0016
    eshapes := exceptions0016
    structs := [] }

end InitE.SourceWitness
