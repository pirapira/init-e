import InitECandidate.Solver.GuestBound.Decls
import InitECandidate.Solver.GuestBound.ExpCostEval
import InitECandidate.Solver.GuestBound.Loops
import InitECandidate.Solver.GuestBound.WalkMBound
import Guest.SoftwareAst
import Lean.Elab.Tactic

/-!
# Environments running the guest, and the syntax-directed cost tactic

`GuestEnv E` collects what the per-function proofs need to know about the
evaluator environment. `guest_cost` proves `FunCost E "f" N` by walking the
body of `Guest.Software.guestFn_f` with the unconditional cost rules; callee
costs come from the theorems `Fn.<callee>`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- An evaluator environment whose function table comes from the guest AST. -/
structure GuestEnv {σ : Type} (E : Env σ) : Prop where
  functions : FunctionsFrom E.functions Guest.Software.guestAst
  word : WordEnv E

variable {σ : Type} {E : Env σ}

theorem FunCost.mono {f : FunName} {B B' : Nat} (h : FunCost E f B) (hle : B ≤ B') :
    FunCost E f B' :=
  fun parameters body hlookup =>
    (h parameters body hlookup).consequence (fun _ hP => hP) hle (fun _ hQ => hQ)

theorem Costs.callNone {f : FunName} {B : Nat} (arguments : List (Exp Word))
    (hf : FunCost E f B) :
    Costs E (.call none f arguments) (panValueExpsStepCost arguments + B + 0 + 1) :=
  Costs.call (info := none) (H := 0) arguments hf trivial

theorem Costs.callDest {f : FunName} {B : Nat} (destination : Option (VarKind × VarName))
    (arguments : List (Exp Word)) (hf : FunCost E f B) :
    Costs E (.call (some (destination, none)) f arguments)
      (panValueExpsStepCost arguments + B + 0 + 1) :=
  Costs.call (info := some (destination, none)) (H := 0) arguments hf trivial

theorem Costs.callHandler {f : FunName} {B H : Nat} (destination : Option (VarKind × VarName))
    (exception : ExceptionId) (handlerVar : VarName) {handlerProgram : Prog Word}
    (arguments : List (Exp Word)) (hf : FunCost E f B) (hh : Costs E handlerProgram H) :
    Costs E (.call (some (destination, some (exception, handlerVar, handlerProgram))) f arguments)
      (panValueExpsStepCost arguments + B + H + 1) :=
  Costs.call (info := some (destination, some (exception, handlerVar, handlerProgram)))
    arguments hf hh

/-! Rules with every argument explicit and costs in the kernel-reducible
`expCost`; `cost_derive` assembles proof terms from them without elaboration. -/
namespace X

theorem skip (σ : Type) (E : Env σ) : Costs E .skip 1 := Costs.skip
theorem «break» (σ : Type) (E : Env σ) : Costs E .break 1 := Costs.break
theorem «continue» (σ : Type) (E : Env σ) : Costs E .continue 1 := Costs.continue
theorem tick (σ : Type) (E : Env σ) : Costs E .tick 1 := Costs.tick
theorem annot (σ : Type) (E : Env σ) (key value : String) : Costs E (.annot key value) 1 :=
  Costs.annot key value

theorem assign (σ : Type) (E : Env σ) (kind : VarKind) (name : VarName) (value : Exp Word) :
    Costs E (.assign kind name value) (expCost value + 1) := by
  rw [← stepCost_eq]
  cases kind
  · exact Costs.assignLocal name value
  · exact Costs.assignGlobal name value

theorem primitive (σ : Type) (E : Env σ) (name : VarName) (operator : PrimOp)
    (arguments : List (Exp Word)) :
    Costs E (.primitive name operator arguments) (expsCost arguments + 1) := by
  rw [← stepsCost_eq]; exact Costs.primitive name operator arguments

theorem store (σ : Type) (E : Env σ) (address value : Exp Word) :
    Costs E (.store address value) (expCost address + expCost value + 1) := by
  rw [← stepCost_eq, ← stepCost_eq]; exact Costs.store address value

theorem store32 (σ : Type) (E : Env σ) (address value : Exp Word) :
    Costs E (.store32 address value) (expCost address + expCost value + 1) := by
  rw [← stepCost_eq, ← stepCost_eq]; exact Costs.store32 address value

theorem storeByte (σ : Type) (E : Env σ) (address value : Exp Word) :
    Costs E (.storeByte address value) (expCost address + expCost value + 1) := by
  rw [← stepCost_eq, ← stepCost_eq]; exact Costs.storeByte address value

theorem ret (σ : Type) (E : Env σ) (value : Exp Word) :
    Costs E (.return value) (expCost value + 1) := by
  rw [← stepCost_eq]; exact Costs.return value

theorem raise (σ : Type) (E : Env σ) (exception : ExceptionId) (value : Exp Word) :
    Costs E (.raise exception value) (expCost value + 1) := by
  rw [← stepCost_eq]; exact Costs.raise exception value

theorem shMemLoad (σ : Type) (E : Env σ) (size : OpSize) (kind : VarKind) (name : VarName)
    (address : Exp Word) :
    Costs E (.shMemLoad size kind name address) (expCost address + 1) := by
  rw [← stepCost_eq]; exact Costs.shMemLoad size kind name address

theorem shMemStore (σ : Type) (E : Env σ) (size : OpSize) (address value : Exp Word) :
    Costs E (.shMemStore size address value) (expCost address + expCost value + 1) := by
  rw [← stepCost_eq, ← stepCost_eq]; exact Costs.shMemStore size address value

theorem extCall (σ : Type) (E : Env σ) (function : FunName)
    (configuration configurationLength array arrayLength : Exp Word) :
    Costs E (.extCall function configuration configurationLength array arrayLength)
      (expsCost [configuration, configurationLength, array, arrayLength] + 1) := by
  rw [← stepsCost_eq]
  exact Costs.extCall function configuration configurationLength array arrayLength

theorem seq (σ : Type) (E : Env σ) (first second : Prog Word) (B₁ B₂ : Nat)
    (h₁ : Costs E first B₁) (h₂ : Costs E second B₂) :
    Costs E (.seq first second) (B₁ + B₂ + 1) := Costs.seq h₁ h₂

theorem ite (σ : Type) (E : Env σ) (c : Exp Word) (thenBranch elseBranch : Prog Word)
    (B₁ B₂ : Nat) (h₁ : Costs E thenBranch B₁) (h₂ : Costs E elseBranch B₂) :
    Costs E (.ite c thenBranch elseBranch) (expCost c + max B₁ B₂ + 1) := by
  rw [← stepCost_eq]; exact Costs.ite c h₁ h₂

theorem dec (σ : Type) (E : Env σ) (name : VarName) (shape : Shape) (value : Exp Word)
    (body : Prog Word) (B : Nat) (h : Costs E body B) :
    Costs E (.dec name shape value body) (expCost value + B + 1) := by
  rw [← stepCost_eq]; exact Costs.dec name shape value h

theorem decCall (σ : Type) (E : Env σ) (name : VarName) (shape : Shape) (f : FunName)
    (arguments : List (Exp Word)) (body : Prog Word) (B C : Nat) (hf : FunCost E f B)
    (hbody : Costs E body C) :
    Costs E (.decCall name shape f arguments body) (expsCost arguments + B + C + 1) := by
  rw [← stepsCost_eq]; exact Costs.decCall name shape arguments hf hbody

theorem callNone (σ : Type) (E : Env σ) (f : FunName) (arguments : List (Exp Word)) (B : Nat)
    (hf : FunCost E f B) :
    Costs E (.call none f arguments) (expsCost arguments + B + 0 + 1) := by
  rw [← stepsCost_eq]; exact Costs.callNone arguments hf

theorem callDest (σ : Type) (E : Env σ) (destination : Option (VarKind × VarName))
    (f : FunName) (arguments : List (Exp Word)) (B : Nat) (hf : FunCost E f B) :
    Costs E (.call (some (destination, none)) f arguments) (expsCost arguments + B + 0 + 1) := by
  rw [← stepsCost_eq]; exact Costs.callDest destination arguments hf

theorem callHandler (σ : Type) (E : Env σ) (destination : Option (VarKind × VarName))
    (exception : ExceptionId) (handlerVar : VarName) (handlerProgram : Prog Word)
    (f : FunName) (arguments : List (Exp Word)) (B H : Nat) (hf : FunCost E f B)
    (hh : Costs E handlerProgram H) :
    Costs E (.call (some (destination, some (exception, handlerVar, handlerProgram))) f arguments)
      (expsCost arguments + B + H + 1) := by
  rw [← stepsCost_eq]
  exact Costs.callHandler destination exception handlerVar arguments hf hh

theorem whileCounter (σ : Type) (E : Env σ) (hE : GuestEnv E) (c : Exp Word)
    (body : Prog Word) (b : Nat) (hcheck : loopOk Guest.Software.guestAst c body = true)
    (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) :=
  loop_costs hE.word hE.functions c body b hcheck hbody

theorem whileWalk (σ : Type) (E : Env σ) (hE : GuestEnv E) (c : Exp Word) (body : Prog Word)
    (b : Nat) (hcheck : walkMLoop body = true) (hbody : Costs E body b) :
    Costs E (.while c body) (walkIters (assignedLocals body).length * (expCost c + b + 1)) :=
  walkMLoop_costs hE.word c body b hcheck hbody

end X

/-! ### Hand-proved loops

A loop that no syntactic check accepts can be bounded by hand. State the
theorem as

```
theorem Manual.«f».loopK {σ : Type} {E : Env σ} (hE : GuestEnv E) (b : Nat)
    (hbody : Costs E (loopBody i K) b) :
    Costs E (.while (loopGuard i K) (loopBody i K)) (N * (expCost (loopGuard i K) + b + 1))
```

where `i` is the position of `f` in the AST and `K` the loop's pre-order index
in `f`, register `f K N <module>` in `GuestBound/manual-loops.txt`, and
regenerate. `cost_derive` uses the theorem when the loop's hint is `2`. -/

/-- The loops of a program in pre-order, as (guard, body). -/
def loopsOf : Prog Word → List (Exp Word × Prog Word)
  | .dec _ _ _ body => loopsOf body
  | .seq first second => loopsOf first ++ loopsOf second
  | .ite _ thenBranch elseBranch => loopsOf thenBranch ++ loopsOf elseBranch
  | .while c body => (c, body) :: loopsOf body
  | .call (some (_, some (_, _, handlerProgram))) _ _ => loopsOf handlerProgram
  | .decCall _ _ _ _ body => loopsOf body
  | _ => []

/-- The body of the function at position `i` of the guest AST. -/
def guestBody (i : Nat) : Prog Word :=
  match Guest.Software.guestAst[i]? with
  | some (.function d) => d.body
  | _ => .skip

/-- The guard of the `k`-th loop of the function at position `i`. -/
def loopGuard (i k : Nat) : Exp Word :=
  match (loopsOf (guestBody i))[k]? with
  | some (c, _) => c
  | none => .const 0

/-- The body of the `k`-th loop of the function at position `i`. -/
def loopBody (i k : Nat) : Prog Word :=
  match (loopsOf (guestBody i))[k]? with
  | some (_, body) => body
  | none => .skip

/-- Namespace of the per-function cost theorems `Fn.<name>`. -/
def fnNamespace : Lean.Name := `InitECandidate.Solver.GuestBound.Fn

open Lean Elab Tactic Meta in
/-- Close a goal `FunCost E "f" ?B` with the theorem `Fn.f`, using a `GuestEnv` hypothesis. -/
elab "fun_cost" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let arguments := target.getAppArgs
  let some name := arguments[2]? | throwError "fun_cost: unexpected goal {target}"
  let .lit (.strVal function) ← whnfR name | throwError "fun_cost: no literal name in {target}"
  let theoremName := mkIdent (fnNamespace ++ Name.mkSimple function)
  evalTactic (← `(tactic| exact $theoremName ‹GuestEnv _›))

open Lean Elab Tactic Meta in
/-- Close a goal `guestAst[i]? = some (Decl.function ?d)` by reading the `i`-th
entry of the AST list syntactically; the kernel checks the resulting `rfl`. -/
elab "guest_decl_at" i:num : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let some (_, lhs, rhs) := target.eq? | throwError "guest_decl_at: not an equation"
  let mut list ← whnfD (mkConst ``Guest.Software.guestAst)
  for _ in [0:i.getNat] do
    let some (_, _, tail) := list.app3? ``List.cons | throwError "guest_decl_at: index out of range"
    list ← whnfD tail
  let some (_, entry, _) := list.app3? ``List.cons | throwError "guest_decl_at: index out of range"
  let some entryName := entry.constName? | throwError "guest_decl_at: entry is not a constant"
  let value := (← getConstInfo entryName).value!
  unless value.isAppOf ``Flapjack.Decl.function do
    throwError "guest_decl_at: entry {entryName} is not a function"
  let declaration := value.appArg!
  let hole := rhs.appArg!.appArg!
  unless (← isDefEq hole declaration) do
    throwError "guest_decl_at: cannot assign the declaration"
  goal.assign (← mkEqRefl lhs)

namespace Derive
open Lean Meta

/-- The bound `B` of a proof of `Costs E p B` or `FunCost E f B`. -/
def boundOf (proof : Expr) : MetaM Expr := do
  return (← instantiateMVars (← inferType proof)).appArg!

def rule (name : Name) : Expr := mkConst (`InitECandidate.Solver.GuestBound.X ++ name)

/-- Build a proof of `Costs E p ?B` by recursion on the constructor form of `p`.
No unification is performed; the kernel checks the assembled term. -/
partial def derive (fnName : String) (σ E hE : Expr) (p : Expr) :
    StateRefT (List Nat × Nat) MetaM Expr := do
  let fn := p.getAppFn
  let args := p.getAppArgs
  let some ctor := fn.constName? | throwError "cost_derive: not a constructor: {p}"
  let callee (f : Expr) : StateRefT (List Nat × Nat) MetaM Expr := do
    let .lit (.strVal function) := f | throwError "cost_derive: callee is not a literal: {f}"
    return mkApp3 (mkConst (fnNamespace ++ Name.mkSimple function)) σ E hE
  match ctor with
  | ``Flapjack.Prog.skip => return mkApp2 (rule `skip) σ E
  | ``Flapjack.Prog.break => return mkApp2 (rule `break) σ E
  | ``Flapjack.Prog.continue => return mkApp2 (rule `continue) σ E
  | ``Flapjack.Prog.tick => return mkApp2 (rule `tick) σ E
  | ``Flapjack.Prog.annot => return mkAppN (rule `annot) #[σ, E, args[1]!, args[2]!]
  | ``Flapjack.Prog.assign => return mkAppN (rule `assign) #[σ, E, args[1]!, args[2]!, args[3]!]
  | ``Flapjack.Prog.primitive =>
      return mkAppN (rule `primitive) #[σ, E, args[1]!, args[2]!, args[3]!]
  | ``Flapjack.Prog.store => return mkAppN (rule `store) #[σ, E, args[1]!, args[2]!]
  | ``Flapjack.Prog.store32 => return mkAppN (rule `store32) #[σ, E, args[1]!, args[2]!]
  | ``Flapjack.Prog.storeByte => return mkAppN (rule `storeByte) #[σ, E, args[1]!, args[2]!]
  | ``Flapjack.Prog.return => return mkAppN (rule `ret) #[σ, E, args[1]!]
  | ``Flapjack.Prog.raise => return mkAppN (rule `raise) #[σ, E, args[1]!, args[2]!]
  | ``Flapjack.Prog.shMemLoad =>
      return mkAppN (rule `shMemLoad) #[σ, E, args[1]!, args[2]!, args[3]!, args[4]!]
  | ``Flapjack.Prog.shMemStore =>
      return mkAppN (rule `shMemStore) #[σ, E, args[1]!, args[2]!, args[3]!]
  | ``Flapjack.Prog.extCall =>
      return mkAppN (rule `extCall) #[σ, E, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!]
  | ``Flapjack.Prog.seq => do
      let h₁ ← derive fnName σ E hE args[1]!
      let h₂ ← derive fnName σ E hE args[2]!
      return mkAppN (rule `seq) #[σ, E, args[1]!, args[2]!, ← boundOf h₁, ← boundOf h₂, h₁, h₂]
  | ``Flapjack.Prog.ite => do
      let h₁ ← derive fnName σ E hE args[2]!
      let h₂ ← derive fnName σ E hE args[3]!
      return mkAppN (rule `ite)
        #[σ, E, args[1]!, args[2]!, args[3]!, ← boundOf h₁, ← boundOf h₂, h₁, h₂]
  | ``Flapjack.Prog.dec => do
      let h ← derive fnName σ E hE args[4]!
      return mkAppN (rule `dec) #[σ, E, args[1]!, args[2]!, args[3]!, args[4]!, ← boundOf h, h]
  | ``Flapjack.Prog.decCall => do
      let hf ← callee args[3]!
      let h ← derive fnName σ E hE args[5]!
      return mkAppN (rule `decCall)
        #[σ, E, args[1]!, args[2]!, args[3]!, args[4]!, args[5]!, ← boundOf hf, ← boundOf h, hf, h]
  | ``Flapjack.Prog.call => do
      let info := args[1]!
      let hf ← callee args[2]!
      if info.isAppOf ``Option.none then
        return mkAppN (rule `callNone) #[σ, E, args[2]!, args[3]!, ← boundOf hf, hf]
      let pair := info.appArg!
      let destination := pair.appFn!.appArg!
      let handler := pair.appArg!
      if handler.isAppOf ``Option.none then
        return mkAppN (rule `callDest) #[σ, E, destination, args[2]!, args[3]!, ← boundOf hf, hf]
      let triple := handler.appArg!
      let exception := triple.appFn!.appArg!
      let rest := triple.appArg!
      let handlerVar := rest.appFn!.appArg!
      let handlerProgram := rest.appArg!
      let hh ← derive fnName σ E hE handlerProgram
      return mkAppN (rule `callHandler)
        #[σ, E, destination, exception, handlerVar, handlerProgram, args[2]!, args[3]!,
          ← boundOf hf, ← boundOf hh, hf, hh]
  | ``Flapjack.Prog.while => do
      -- hints are consumed in pre-order: 0 (default) uses `loopOk`, 1 uses `walkMLoop`,
      -- 2 uses the hand-proved theorem `Manual.<fn>.loop<index>`
      let (hint, index) ← modifyGet fun (hints, index) =>
        ((hints.headD 0, index), (hints.tail, index + 1))
      let h ← derive fnName σ E hE args[2]!
      if hint == 2 then
        let manual := `InitECandidate.Solver.GuestBound.Manual ++ Name.mkSimple fnName ++
          Name.mkSimple s!"loop{index}"
        return mkAppN (mkConst manual) #[σ, E, hE, ← boundOf h, h]
      let check := mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true)
      let name := if hint == 1 then `whileWalk else `whileCounter
      return mkAppN (rule name) #[σ, E, hE, args[1]!, args[2]!, ← boundOf h, check, h]
  | _ => throwError "cost_derive: unsupported statement {ctor}"

end Derive

open Lean Elab Tactic Meta in
/-- Prove `Costs E body ?B` for a loop-free body in constructor form, assigning `?B`. -/
elab "cost_derive" "[" hints:num,* "]" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let arguments := target.getAppArgs
  let σ := arguments[0]!
  let E := arguments[1]!
  let body := arguments[2]!
  let some hE ← (← getLCtx).findDeclM? fun declaration => do
      if (← instantiateMVars declaration.type).isAppOf ``GuestEnv then
        return some declaration.toExpr
      else return none
    | throwError "cost_derive: no GuestEnv hypothesis"
  let hintList := hints.getElems.toList.map (·.getNat)
  let some declName ← Term.getDeclName? | throwError "cost_derive: not inside a declaration"
  let fnName := match declName with
    | .str _ last => last
    | _ => ""
  let (proof, _) ← (Derive.derive fnName σ E hE body).run (hintList, 0)
  let bound ← Derive.boundOf proof
  let hole := arguments[3]!
  if hole.isMVar then hole.mvarId!.assign bound
  goal.assign proof

open Lean Elab Tactic Meta in
/-- Reduce the structure projection in a goal `Costs E d.body ?B` (one step, no traversal). -/
elab "reduce_body" : tactic => do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let arguments := target.getAppArgs
  let some body := arguments[2]? | throwError "reduce_body: unexpected goal"
  let body ← whnfR body
  let newTarget := mkAppN target.getAppFn (arguments.set! 2 body)
  replaceMainGoal [← goal.replaceTargetDefEq newTarget]

/-- Prove `FunCost E "f" N` for the guest function at position `i` of the AST.
`guest_cost i [h₀, h₁, …]` gives one hint per loop of the function, in
pre-order: `0` for a loop accepted by `loopOk`, `1` for one accepted by `walkMLoop`. -/
macro "guest_cost" i:num "[" hints:num,* "]" : tactic => `(tactic| (
  apply FunCost.mono
  · apply funCost_of_index $i (GuestEnv.functions ‹GuestEnv _›)
      (by guest_decl_at $i) (by decide +kernel)
    reduce_body
    cost_derive [$hints,*]
  · decide +kernel))

macro "guest_cost" i:num : tactic => `(tactic| guest_cost $i [])

end InitECandidate.Solver.GuestBound
