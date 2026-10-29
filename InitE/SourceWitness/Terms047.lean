import InitE.SourceWitness.Terms046
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0753 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_conj) code0752
def globals0753 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_conj) globals0752
def exceptions0753 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_conj) exceptions0752
def code0754 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_inv) code0753
def globals0754 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_inv) globals0753
def exceptions0754 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_inv) exceptions0753
def code0755 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_frob) code0754
def globals0755 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_frob) globals0754
def exceptions0755 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_frob) exceptions0754
def code0756 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_pow_absx) code0755
def globals0756 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_pow_absx) globals0755
def exceptions0756 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_pow_absx) exceptions0755
def code0757 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_exp_x) code0756
def globals0757 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_exp_x) globals0756
def exceptions0757 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_exp_x) exceptions0756
def code0758 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp12_final_exp) code0757
def globals0758 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp12_final_exp) globals0757
def exceptions0758 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp12_final_exp) exceptions0757
def code0759 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_set_inf) code0758
def globals0759 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_set_inf) globals0758
def exceptions0759 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_set_inf) exceptions0758
def code0760 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_is_inf) code0759
def globals0760 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_is_inf) globals0759
def exceptions0760 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_is_inf) exceptions0759
def code0761 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_copy) code0760
def globals0761 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_copy) globals0760
def exceptions0761 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_copy) exceptions0760
def code0762 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_neg) code0761
def globals0762 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_neg) globals0761
def exceptions0762 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_neg) exceptions0761
def code0763 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_double) code0762
def globals0763 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_double) globals0762
def exceptions0763 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_double) exceptions0762
def code0764 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_add) code0763
def globals0764 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_add) globals0763
def exceptions0764 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_add) exceptions0763
def code0765 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_mul) code0764
def globals0765 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_mul) globals0764
def exceptions0765 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_mul) exceptions0764
def code0766 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_normalize) code0765
def globals0766 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_normalize) globals0765
def exceptions0766 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_normalize) exceptions0765
def code0767 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_on_curve) code0766
def globals0767 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_on_curve) globals0766
def exceptions0767 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_on_curve) exceptions0766
def code0768 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_g1_decode) code0767
def globals0768 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_g1_decode) globals0767
def exceptions0768 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_g1_decode) exceptions0767

def state0768 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0768
    code := code0768
    eshapes := exceptions0768
    structs := [] }

end InitE.SourceWitness
