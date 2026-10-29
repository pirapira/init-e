import InitE.SourceWitness.Terms043
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0705 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_neg) code0704
def globals0705 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_neg) globals0704
def exceptions0705 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_neg) exceptions0704
def code0706 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_dbl) code0705
def globals0706 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_dbl) globals0705
def exceptions0706 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_dbl) exceptions0705
def code0707 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_mul) code0706
def globals0707 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_mul) globals0706
def exceptions0707 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_mul) exceptions0706
def code0708 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_sqr) code0707
def globals0708 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_sqr) globals0707
def exceptions0708 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_sqr) exceptions0707
def code0709 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_to_mont) code0708
def globals0709 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_to_mont) globals0708
def exceptions0709 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_to_mont) exceptions0708
def code0710 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_from_mont) code0709
def globals0710 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_from_mont) globals0709
def exceptions0710 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_from_mont) exceptions0709
def code0711 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_shr1) code0710
def globals0711 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_shr1) globals0710
def exceptions0711 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_shr1) exceptions0710
def code0712 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_half_can) code0711
def globals0712 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_half_can) globals0711
def exceptions0712 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_half_can) exceptions0711
def code0713 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_inv_raw) code0712
def globals0713 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_inv_raw) globals0712
def exceptions0713 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_inv_raw) exceptions0712
def code0714 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_inv) code0713
def globals0714 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_inv) globals0713
def exceptions0714 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_inv) exceptions0713
def code0715 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_pow) code0714
def globals0715 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_pow) globals0714
def exceptions0715 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_pow) exceptions0714
def code0716 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_sgn0) code0715
def globals0716 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_sgn0) globals0715
def exceptions0716 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_sgn0) exceptions0715
def code0717 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_is_high) code0716
def globals0717 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_is_high) globals0716
def exceptions0717 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_is_high) exceptions0716
def code0718 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_from_be48) code0717
def globals0718 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_from_be48) globals0717
def exceptions0718 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_from_be48) exceptions0717
def code0719 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_to_be48) code0718
def globals0719 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_to_be48) globals0718
def exceptions0719 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_to_be48) exceptions0718
def code0720 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bls_fp_decode64) code0719
def globals0720 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bls_fp_decode64) globals0719
def exceptions0720 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bls_fp_decode64) exceptions0719

def state0720 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0720
    code := code0720
    eshapes := exceptions0720
    structs := [] }

end InitE.SourceWitness
