import InitE.SourceWitness.Terms044
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0721 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_encode64) code0720
def globals0721 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_encode64) globals0720
def exceptions0721 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_encode64) exceptions0720
def code0722 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_copy) code0721
def globals0722 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_copy) globals0721
def exceptions0722 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_copy) exceptions0721
def code0723 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_set_zero) code0722
def globals0723 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_set_zero) globals0722
def exceptions0723 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_set_zero) exceptions0722
def code0724 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_set_one) code0723
def globals0724 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_set_one) globals0723
def exceptions0724 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_set_one) exceptions0723
def code0725 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_is_zero) code0724
def globals0725 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_is_zero) globals0724
def exceptions0725 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_is_zero) exceptions0724
def code0726 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_eq) code0725
def globals0726 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_eq) globals0725
def exceptions0726 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_eq) exceptions0725
def code0727 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_add) code0726
def globals0727 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_add) globals0726
def exceptions0727 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_add) exceptions0726
def code0728 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_sub) code0727
def globals0728 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_sub) globals0727
def exceptions0728 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_sub) exceptions0727
def code0729 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_neg) code0728
def globals0729 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_neg) globals0728
def exceptions0729 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_neg) exceptions0728
def code0730 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_dbl) code0729
def globals0730 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_dbl) globals0729
def exceptions0730 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_dbl) exceptions0729
def code0731 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_conj) code0730
def globals0731 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_conj) globals0730
def exceptions0731 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_conj) exceptions0730
def code0732 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_mul) code0731
def globals0732 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_mul) globals0731
def exceptions0732 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_mul) exceptions0731
def code0733 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_sqr) code0732
def globals0733 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_sqr) globals0732
def exceptions0733 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_sqr) exceptions0732
def code0734 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_mul_xi) code0733
def globals0734 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_mul_xi) globals0733
def exceptions0734 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_mul_xi) exceptions0733
def code0735 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_scale) code0734
def globals0735 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_scale) globals0734
def exceptions0735 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_scale) exceptions0734
def code0736 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp2_inv) code0735
def globals0736 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp2_inv) globals0735
def exceptions0736 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp2_inv) exceptions0735

def state0736 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0736
    code := code0736
    eshapes := exceptions0736
    structs := [] }

end InitE.SourceWitness
