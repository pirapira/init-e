import InitE.SourceWitness.Terms047
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0769 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_encode) code0768
def globals0769 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_encode) globals0768
def exceptions0769 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_encode) exceptions0768
def code0770 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_subgroup_check) code0769
def globals0770 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_subgroup_check) globals0769
def exceptions0770 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_subgroup_check) exceptions0769
def code0771 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_set_inf) code0770
def globals0771 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_set_inf) globals0770
def exceptions0771 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_set_inf) exceptions0770
def code0772 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_is_inf) code0771
def globals0772 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_is_inf) globals0771
def exceptions0772 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_is_inf) exceptions0771
def code0773 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_copy) code0772
def globals0773 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_copy) globals0772
def exceptions0773 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_copy) exceptions0772
def code0774 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_neg) code0773
def globals0774 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_neg) globals0773
def exceptions0774 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_neg) exceptions0773
def code0775 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_double) code0774
def globals0775 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_double) globals0774
def exceptions0775 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_double) exceptions0774
def code0776 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_add) code0775
def globals0776 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_add) globals0775
def exceptions0776 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_add) exceptions0775
def code0777 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_mul) code0776
def globals0777 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_mul) globals0776
def exceptions0777 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_mul) exceptions0776
def code0778 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_normalize) code0777
def globals0778 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_normalize) globals0777
def exceptions0778 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_normalize) exceptions0777
def code0779 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_on_curve) code0778
def globals0779 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_on_curve) globals0778
def exceptions0779 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_on_curve) exceptions0778
def code0780 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_decode) code0779
def globals0780 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_decode) globals0779
def exceptions0780 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_decode) exceptions0779
def code0781 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_encode) code0780
def globals0781 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_encode) globals0780
def exceptions0781 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_encode) exceptions0780
def code0782 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g2_subgroup_check) code0781
def globals0782 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g2_subgroup_check) globals0781
def exceptions0782 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g2_subgroup_check) exceptions0781
def code0783 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_pair_doubling_step) code0782
def globals0783 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_pair_doubling_step) globals0782
def exceptions0783 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_pair_doubling_step) exceptions0782
def code0784 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_pair_addition_step) code0783
def globals0784 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_pair_addition_step) globals0783
def exceptions0784 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_pair_addition_step) exceptions0783

def state0784 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0784
    code := code0784
    eshapes := exceptions0784
    structs := [] }

end InitE.SourceWitness
