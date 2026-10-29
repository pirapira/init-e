import InitE.SourceWitness.Terms027
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0449 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_charge_gas) code0448
def globals0449 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_charge_gas) globals0448
def exceptions0449 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_charge_gas) exceptions0448
def code0450 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_charge_state_gas) code0449
def globals0450 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_charge_state_gas) globals0449
def exceptions0450 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_charge_state_gas) exceptions0449
def code0451 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_credit_state_gas_refund) code0450
def globals0451 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_credit_state_gas_refund) globals0450
def exceptions0451 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_credit_state_gas_refund) exceptions0450
def code0452 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_frame_state_gas_used) code0451
def globals0452 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_frame_state_gas_used) globals0451
def exceptions0452 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_frame_state_gas_used) exceptions0451
def code0453 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_refill_frame_state_gas) code0452
def globals0453 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_refill_frame_state_gas) globals0452
def exceptions0453 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_refill_frame_state_gas) exceptions0452
def code0454 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_stack_pop) code0453
def globals0454 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_stack_pop) globals0453
def exceptions0454 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_stack_pop) exceptions0453
def code0455 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_stack_push) code0454
def globals0455 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_stack_push) globals0454
def exceptions0455 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_stack_push) exceptions0454
def code0456 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_stack_push_word) code0455
def globals0456 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_stack_push_word) globals0455
def exceptions0456 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_stack_push_word) exceptions0455
def code0457 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_stack_push_bool) code0456
def globals0457 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_stack_push_bool) globals0456
def exceptions0457 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_stack_push_bool) exceptions0456
def code0458 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_memory_gas_cost) code0457
def globals0458 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_memory_gas_cost) globals0457
def exceptions0458 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_memory_gas_cost) exceptions0457
def code0459 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_extend_memory_cost1) code0458
def globals0459 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_extend_memory_cost1) globals0458
def exceptions0459 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_extend_memory_cost1) exceptions0458
def code0460 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_extend_memory_cost2) code0459
def globals0460 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_extend_memory_cost2) globals0459
def exceptions0460 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_extend_memory_cost2) exceptions0459
def code0461 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_extend_memory) code0460
def globals0461 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_extend_memory) globals0460
def exceptions0461 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_extend_memory) exceptions0460
def code0462 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_charge_with_memory) code0461
def globals0462 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_charge_with_memory) globals0461
def exceptions0462 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_charge_with_memory) exceptions0461
def code0463 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_buffer_read) code0462
def globals0463 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_buffer_read) globals0462
def exceptions0463 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_buffer_read) exceptions0462
def code0464 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_compute_jumpdests) code0463
def globals0464 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_compute_jumpdests) globals0463
def exceptions0464 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_compute_jumpdests) exceptions0463

def state0464 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0464
    code := code0464
    eshapes := exceptions0464
    structs := [] }

end InitE.SourceWitness
