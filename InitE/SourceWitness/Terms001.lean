import InitE.SourceWitness.Terms000
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang
def code0017 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_memcpy) code0016
def globals0017 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_memcpy) globals0016
def exceptions0017 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_memcpy) exceptions0016
def code0018 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_memzero) code0017
def globals0018 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_memzero) globals0017
def exceptions0018 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_memzero) exceptions0017
def code0019 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_memeq) code0018
def globals0019 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_memeq) globals0018
def exceptions0019 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_memeq) exceptions0018
def code0020 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_is_zero_bytes) code0019
def globals0020 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_is_zero_bytes) globals0019
def exceptions0020 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_is_zero_bytes) exceptions0019
def code0021 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ld_le32) code0020
def globals0021 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ld_le32) globals0020
def exceptions0021 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ld_le32) exceptions0020
def code0022 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ld_le64) code0021
def globals0022 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ld_le64) globals0021
def exceptions0022 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ld_le64) exceptions0021
def code0023 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ld_be32) code0022
def globals0023 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ld_be32) globals0022
def exceptions0023 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ld_be32) exceptions0022
def code0024 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_bswap64) code0023
def globals0024 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_bswap64) globals0023
def exceptions0024 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_bswap64) exceptions0023
def code0025 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_ld_be64) code0024
def globals0025 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_ld_be64) globals0024
def exceptions0025 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_ld_be64) exceptions0024
def code0026 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_st_le32) code0025
def globals0026 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_st_le32) globals0025
def exceptions0026 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_st_le32) exceptions0025
def code0027 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_st_le64) code0026
def globals0027 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_st_le64) globals0026
def exceptions0027 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_st_le64) exceptions0026
def code0028 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_st_be32) code0027
def globals0028 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_st_be32) globals0027
def exceptions0028 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_st_be32) exceptions0027
def code0029 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_st_be64) code0028
def globals0029 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_st_be64) globals0028
def exceptions0029 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_st_be64) exceptions0028
def code0030 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_input_blob) code0029
def globals0030 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_input_blob) globals0029
def exceptions0030 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_input_blob) exceptions0029
def code0031 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_output_write) code0030
def globals0031 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_output_write) globals0030
def exceptions0031 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_output_write) exceptions0030
def code0032 : CodeTable :=
  installCode (declToHOL Guest.Software.guestFn_min) code0031
def globals0032 : GlobalTable :=
  installGlobal (declToHOL Guest.Software.guestFn_min) globals0031
def exceptions0032 : ExceptionTable :=
  installException (declToHOL Guest.Software.guestFn_min) exceptions0031

def state0032 (s : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { s with
    globals := globals0032
    code := code0032
    eshapes := exceptions0032
    structs := [] }

end InitE.SourceWitness
