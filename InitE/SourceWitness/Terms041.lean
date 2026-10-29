import InitE.SourceWitness.Terms040
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0657 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq_mul_small) code0656
def globals0657 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq_mul_small) globals0656
def exceptions0657 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq_mul_small) exceptions0656
def code0658 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq2_mul) code0657
def globals0658 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq2_mul) globals0657
def exceptions0658 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq2_mul) exceptions0657
def code0659 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq12_reduce) code0658
def globals0659 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq12_reduce) globals0658
def exceptions0659 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq12_reduce) exceptions0658
def code0660 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq12_mul) code0659
def globals0660 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq12_mul) globals0659
def exceptions0660 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq12_mul) exceptions0659
def code0661 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq12_sqr) code0660
def globals0661 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq12_sqr) globals0660
def exceptions0661 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq12_sqr) exceptions0660
def code0662 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fe_mul) code0661
def globals0662 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fe_mul) globals0661
def exceptions0662 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fe_mul) exceptions0661
def code0663 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fe_sqr) code0662
def globals0663 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fe_sqr) globals0662
def exceptions0663 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fe_sqr) exceptions0662
def code0664 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fe_add) code0663
def globals0664 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fe_add) globals0663
def exceptions0664 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fe_add) exceptions0663
def code0665 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fe_sub) code0664
def globals0665 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fe_sub) globals0664
def exceptions0665 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fe_sub) exceptions0664
def code0666 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fe_neg) code0665
def globals0666 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fe_neg) globals0665
def exceptions0666 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fe_neg) exceptions0665
def code0667 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fe_mul_small) code0666
def globals0667 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fe_mul_small) globals0666
def exceptions0667 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fe_mul_small) exceptions0666
def code0668 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fe_is_zero) code0667
def globals0668 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fe_is_zero) globals0667
def exceptions0668 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fe_is_zero) exceptions0667
def code0669 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fe_eq) code0668
def globals0669 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fe_eq) globals0668
def exceptions0669 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fe_eq) exceptions0668
def code0670 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fe_set_zero) code0669
def globals0670 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fe_set_zero) globals0669
def exceptions0670 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fe_set_zero) exceptions0669
def code0671 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fe_set_one) code0670
def globals0671 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fe_set_one) globals0670
def exceptions0671 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fe_set_one) exceptions0670
def code0672 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ecp_set_inf) code0671
def globals0672 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ecp_set_inf) globals0671
def exceptions0672 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ecp_set_inf) exceptions0671

def state0672 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0672
    code := code0672
    eshapes := exceptions0672
    structs := [] }

end InitE.SourceWitness
