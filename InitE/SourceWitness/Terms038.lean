import InitE.SourceWitness.Terms037
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0609 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_rmd_tab) code0608
def globals0609 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_rmd_tab) globals0608
def exceptions0609 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_rmd_tab) exceptions0608
def code0610 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_rmd_x) code0609
def globals0610 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_rmd_x) globals0609
def exceptions0610 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_rmd_x) exceptions0609
def code0611 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_rmd_h) code0610
def globals0611 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_rmd_h) globals0610
def exceptions0611 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_rmd_h) exceptions0610
def code0612 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_rmd_pad) code0611
def globals0612 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_rmd_pad) globals0611
def exceptions0612 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_rmd_pad) exceptions0611
def code0613 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ripemd160_init) code0612
def globals0613 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ripemd160_init) globals0612
def exceptions0613 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ripemd160_init) exceptions0612
def code0614 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rmd_f) code0613
def globals0614 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rmd_f) globals0613
def exceptions0614 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rmd_f) exceptions0613
def code0615 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rmd_k) code0614
def globals0615 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rmd_k) globals0614
def exceptions0615 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rmd_k) exceptions0614
def code0616 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_rmd_kp) code0615
def globals0616 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_rmd_kp) globals0615
def exceptions0616 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_rmd_kp) exceptions0615
def code0617 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ripemd160_block) code0616
def globals0617 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ripemd160_block) globals0616
def exceptions0617 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ripemd160_block) exceptions0616
def code0618 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ripemd160) code0617
def globals0618 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ripemd160) globals0617
def exceptions0618 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ripemd160) exceptions0617
def code0619 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_b2_sigma) code0618
def globals0619 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_b2_sigma) globals0618
def exceptions0619 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_b2_sigma) exceptions0618
def code0620 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_b2_iv) code0619
def globals0620 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_b2_iv) globals0619
def exceptions0620 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_b2_iv) exceptions0619
def code0621 : CodeTable :=
  installCode (declToHOL Guest.Software.guestGlobal_b2_v) code0620
def globals0621 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestGlobal_b2_v) globals0620
def exceptions0621 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestGlobal_b2_v) exceptions0620
def code0622 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_blake2_init) code0621
def globals0622 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_blake2_init) globals0621
def exceptions0622 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_blake2_init) exceptions0621
def code0623 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_blake2_g) code0622
def globals0623 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_blake2_g) globals0622
def exceptions0623 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_blake2_g) exceptions0622
def code0624 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_blake2b_f) code0623
def globals0624 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_blake2b_f) globals0623
def exceptions0624 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_blake2b_f) exceptions0623

def state0624 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0624
    code := code0624
    eshapes := exceptions0624
    structs := [] }

end InitE.SourceWitness
