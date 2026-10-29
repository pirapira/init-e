import InitE.SourceWitness.Lookups
import InitE.SourceLookupReduction
import InitE.SourceMemoryReduction
import InitE.SourceWitness.CompactTables

/-! Reuse the separately checked code-table facts during source execution.
The simproc selects a theorem; its proof is checked against the requested key. -/
namespace InitE.SourceWitness
open Flapjack Lean Meta Sym Meta.Tactic.Cbv

noncomputable def codeLookup := code0890.lookup
attribute [scoped cbv_opaque] codeLookup

@[scoped cbv_eval] theorem expose_code :
    code0890 = ⟨codeLookup, code0890.finiteSupport⟩ := rfl

scoped cbv_simproc cbv_eval code_lookup (codeLookup _) := fun e => do
  let_expr codeLookup key := e | return .rfl
  let_expr Flapjack.Basis.Pure.MlString.MlString.implode bytes := key | return .rfl
  let some bytes := getListLitElems bytes | return .rfl
  let mut chars : List Char := []
  for byte in bytes do
    let some value := Sym.getBitVecValue? byte | return .rfl
    if value.n != 8 then return .rfl
    chars := Char.ofNat value.val.toNat :: chars
  let label := String.ofList chars.reverse
  let fact := Name.str `InitE.SourceWitness ("code_guestFn_" ++ label)
  let some info := (← getEnv).find? fact | return .rfl
  let some (_, _, result) := info.type.eq? | return .rfl
  return .step (← Sym.shareCommon result) (mkConst fact)

end InitE.SourceWitness
