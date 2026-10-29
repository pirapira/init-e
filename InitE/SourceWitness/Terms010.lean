import InitE.SourceWitness.Terms009
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0161 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp_inv) code0160
def globals0161 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp_inv) globals0160
def exceptions0161 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp_inv) exceptions0160
def code0162 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fp_sqrt) code0161
def globals0162 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fp_sqrt) globals0161
def exceptions0162 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fp_sqrt) exceptions0161
def code0163 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fn_mul) code0162
def globals0163 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fn_mul) globals0162
def exceptions0163 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fn_mul) exceptions0162
def code0164 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fn_add) code0163
def globals0164 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fn_add) globals0163
def exceptions0164 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fn_add) exceptions0163
def code0165 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fn_pow) code0164
def globals0165 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fn_pow) globals0164
def exceptions0165 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fn_pow) exceptions0164
def code0166 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fn_inv_fermat) code0165
def globals0166 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fn_inv_fermat) globals0165
def exceptions0166 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fn_inv_fermat) exceptions0165
def code0167 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_fn_inv) code0166
def globals0167 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_fn_inv) globals0166
def exceptions0167 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_fn_inv) exceptions0166
def code0168 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ec_set_infinity) code0167
def globals0168 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ec_set_infinity) globals0167
def exceptions0168 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ec_set_infinity) exceptions0167
def code0169 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ec_set_affine) code0168
def globals0169 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ec_set_affine) globals0168
def exceptions0169 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ec_set_affine) exceptions0168
def code0170 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ec_is_infinity) code0169
def globals0170 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ec_is_infinity) globals0169
def exceptions0170 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ec_is_infinity) exceptions0169
def code0171 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ec_double) code0170
def globals0171 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ec_double) globals0170
def exceptions0171 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ec_double) exceptions0170
def code0172 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ec_add_affine) code0171
def globals0172 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ec_add_affine) globals0171
def exceptions0172 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ec_add_affine) exceptions0171
def code0173 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ec_add) code0172
def globals0173 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ec_add) globals0172
def exceptions0173 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ec_add) exceptions0172
def code0174 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ec_mul) code0173
def globals0174 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ec_mul) globals0173
def exceptions0174 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ec_mul) exceptions0173
def code0175 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ec_mul2) code0174
def globals0175 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ec_mul2) globals0174
def exceptions0175 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ec_mul2) exceptions0174
def code0176 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ec_to_affine) code0175
def globals0176 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ec_to_affine) globals0175
def exceptions0176 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ec_to_affine) exceptions0175

def state0176 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0176
    code := code0176
    eshapes := exceptions0176
    structs := [] }

end InitE.SourceWitness
