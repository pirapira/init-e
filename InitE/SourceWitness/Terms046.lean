import InitE.SourceWitness.Terms045
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0737 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_pow) code0736
def globals0737 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_pow) globals0736
def exceptions0737 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_pow) exceptions0736
def code0738 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_sgn0) code0737
def globals0738 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_sgn0) globals0737
def exceptions0738 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_sgn0) exceptions0737
def code0739 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp6_copy) code0738
def globals0739 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp6_copy) globals0738
def exceptions0739 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp6_copy) exceptions0738
def code0740 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp6_set_zero) code0739
def globals0740 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp6_set_zero) globals0739
def exceptions0740 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp6_set_zero) exceptions0739
def code0741 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp6_set_one) code0740
def globals0741 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp6_set_one) globals0740
def exceptions0741 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp6_set_one) exceptions0740
def code0742 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp6_add) code0741
def globals0742 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp6_add) globals0741
def exceptions0742 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp6_add) exceptions0741
def code0743 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp6_sub) code0742
def globals0743 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp6_sub) globals0742
def exceptions0743 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp6_sub) exceptions0742
def code0744 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp6_neg) code0743
def globals0744 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp6_neg) globals0743
def exceptions0744 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp6_neg) exceptions0743
def code0745 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp6_mul) code0744
def globals0745 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp6_mul) globals0744
def exceptions0745 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp6_mul) exceptions0744
def code0746 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp6_mul_v) code0745
def globals0746 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp6_mul_v) globals0745
def exceptions0746 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp6_mul_v) exceptions0745
def code0747 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp6_inv) code0746
def globals0747 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp6_inv) globals0746
def exceptions0747 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp6_inv) exceptions0746
def code0748 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_copy) code0747
def globals0748 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_copy) globals0747
def exceptions0748 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_copy) exceptions0747
def code0749 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_set_one) code0748
def globals0749 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_set_one) globals0748
def exceptions0749 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_set_one) exceptions0748
def code0750 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_is_one) code0749
def globals0750 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_is_one) globals0749
def exceptions0750 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_is_one) exceptions0749
def code0751 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_mul) code0750
def globals0751 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_mul) globals0750
def exceptions0751 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_mul) exceptions0750
def code0752 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_sqr) code0751
def globals0752 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_sqr) globals0751
def exceptions0752 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_sqr) exceptions0751

def state0752 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0752
    code := code0752
    eshapes := exceptions0752
    structs := [] }

end InitE.SourceWitness
