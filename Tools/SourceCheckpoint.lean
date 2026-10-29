import InitE.SourceWitness.CodeReduction
import InitE.SourceContextReduction
import InitE.SourceAtomicReduction
import InitE.SourceSupportReduction

/-! Build a named intermediate term and its equality proof. The kernel checks
both declarations; the mutable counter only chooses where reduction pauses. -/
namespace Tools.SourceCheckpoint
open Lean Meta Elab Command Term Sym Meta.Tactic.Cbv

initialize remaining : IO.Ref Nat ← IO.mkRef 0

scoped cbv_simproc cbv_eval pauseEvaluator
    (@Flapjack.PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext _ _ _ _ _) :=
  fun _ => do
    let budget ← remaining.get
    if budget == 0 then return .rfl (done := true)
    remaining.set (budget - 1)
    return .rfl

scoped syntax (name := checkpoint) "source_checkpoint " ident " := " term " budget " num : command

elab_rules : command
  | `(source_checkpoint $name:ident := $term:term budget $limit:num) => do
    liftTermElabM do
      let input ← elabTerm term none
      synthesizeSyntheticMVarsNoPostponing
      let input ← instantiateMVars input
      if input.hasMVar || input.hasSorry then throwError "Checkpoint input is incomplete"
      lambdaTelescope input fun parameters body => do
        let inputType ← inferType body
        remaining.set limit.getNat
        let reduceInput := (← Meta.unfoldDefinition? body).getD body
        let started ← IO.monoMsNow
        let result ← cbvEntry reduceInput
        let reducedAt ← IO.monoMsNow
        let output := result.getResultExpr reduceInput
        let proof ← match result with
          | .rfl .. => mkEqRefl reduceInput
          | .step _ proof .. => pure proof
        if output.hasMVar || proof.hasMVar || output.hasSorry || proof.hasSorry then
          throwError "Checkpoint reduction produced an incomplete term or proof"
        let validatedAt ← IO.monoMsNow
        let qualified := (← getCurrNamespace) ++ name.getId
        addDecl (.defnDecl {
          name := qualified, levelParams := [], type := ← mkForallFVars parameters inputType,
          value := ← mkLambdaFVars parameters output, hints := .regular 0, safety := .safe })
        addDecl (.thmDecl {
          name := qualified.appendAfter "_eq", levelParams := [],
          type := ← mkForallFVars parameters (← mkEq body (mkAppN (mkConst qualified) parameters)),
          value := ← mkLambdaFVars parameters proof })
        let checkedAt ← IO.monoMsNow
        let pending := output.getUsedConstants.any (fun n =>
          n.toString.startsWith "Flapjack.PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext")
        logInfo m!"Checked {qualified} and {qualified.appendAfter "_eq"}; evaluator pending: {pending}; budget left: {← remaining.get}; reduce/check ms: {reducedAt-started}/{checkedAt-validatedAt}; validate ms: {validatedAt-reducedAt}"

end Tools.SourceCheckpoint
