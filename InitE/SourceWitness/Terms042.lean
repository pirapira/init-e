import InitE.SourceWitness.Terms041
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0673 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ecp_is_inf) code0672
def globals0673 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ecp_is_inf) globals0672
def exceptions0673 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ecp_is_inf) exceptions0672
def code0674 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ecp_double) code0673
def globals0674 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ecp_double) globals0673
def exceptions0674 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ecp_double) exceptions0673
def code0675 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ecp_add) code0674
def globals0675 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ecp_add) globals0674
def exceptions0675 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ecp_add) exceptions0674
def code0676 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ecp_mul) code0675
def globals0676 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ecp_mul) globals0675
def exceptions0676 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ecp_mul) exceptions0675
def code0677 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ecp_linefunc) code0676
def globals0677 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ecp_linefunc) globals0676
def exceptions0677 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ecp_linefunc) exceptions0676
def code0678 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq12_twist) code0677
def globals0678 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq12_twist) globals0677
def exceptions0678 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq12_twist) exceptions0677
def code0679 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq12_cast) code0678
def globals0679 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq12_cast) globals0678
def exceptions0679 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq12_cast) exceptions0678
def code0680 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq12_frob) code0679
def globals0680 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq12_frob) globals0679
def exceptions0680 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq12_frob) exceptions0679
def code0681 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq_poly_deg) code0680
def globals0681 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq_poly_deg) globals0680
def exceptions0681 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq_poly_deg) exceptions0680
def code0682 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq_poly_submul) code0681
def globals0682 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq_poly_submul) globals0681
def exceptions0682 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq_poly_submul) exceptions0681
def code0683 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq12_inv) code0682
def globals0683 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq12_inv) globals0682
def exceptions0683 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq12_inv) exceptions0682
def code0684 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fq12_pow_words) code0683
def globals0684 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fq12_pow_words) globals0683
def exceptions0684 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fq12_pow_words) exceptions0683
def code0685 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bn254_miller_raw) code0684
def globals0685 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bn254_miller_raw) globals0684
def exceptions0685 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bn254_miller_raw) exceptions0684
def code0686 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bn254_pairing) code0685
def globals0686 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bn254_pairing) globals0685
def exceptions0686 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bn254_pairing) exceptions0685
def code0687 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bn254_parse_g1) code0686
def globals0687 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bn254_parse_g1) globals0686
def exceptions0687 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bn254_parse_g1) exceptions0686
def code0688 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bn254_parse_g2) code0687
def globals0688 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bn254_parse_g2) globals0687
def exceptions0688 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bn254_parse_g2) exceptions0687

def state0688 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0688
    code := code0688
    eshapes := exceptions0688
    structs := [] }

end InitE.SourceWitness
