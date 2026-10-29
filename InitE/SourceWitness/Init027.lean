import InitE.SourceWitness.Terms027
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
open scoped InitE.SourceReduction InitE.NameComputation
namespace InitE.SourceWitness
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

attribute [local cbv_opaque] code0432 globals0432

def chunk027 : List (DeclHOL 64) :=
  [declToHOL Guest.Software.guestFn_bal_encode_account,
    declToHOL Guest.Software.guestFn_build_block_access_list_rlp,
    declToHOL Guest.Software.guestFn_validate_block_access_list_gas_limit,
    declToHOL Guest.Software.guestExn_EvmErr,
    declToHOL Guest.Software.guestGlobal_ev,
    declToHOL Guest.Software.guestGlobal_evm_empty,
    declToHOL Guest.Software.guestGlobal_pre_hdr_buf,
    declToHOL Guest.Software.guestGlobal_evm_key_buf,
    declToHOL Guest.Software.guestFn_sat_word,
    declToHOL Guest.Software.guestFn_add_sat,
    declToHOL Guest.Software.guestFn_ceil32,
    declToHOL Guest.Software.guestFn_words_of,
    declToHOL Guest.Software.guestFn_to_address_masked,
    declToHOL Guest.Software.guestFn_address_to_u256,
    declToHOL Guest.Software.guestFn_is_valid_delegation,
    declToHOL Guest.Software.guestFn_check_gas]

theorem chunk027_run (s : PanSemStateFiniteExact 64 σ) [DecidablePred s.memaddrs] :
    @evaluateDeclsHOLFinite 64 σ _ (state0432 s)
      (inferInstanceAs (DecidablePred s.memaddrs)) chunk027 =
        some (state0448 s) := by
  cbv

end InitE.SourceWitness
