import InitECandidate.Solver.GuestBound.CostLogic

/-!
# Syntactic check for counter loops

`counterLoop c body` recognises loops whose guard compares a local variable
`i` and whose body, on every path back to the loop head, changes `i` by
exactly one step (`i = i + 1` or `i = i - 1`) and otherwise leaves it alone.
The soundness proof is in `CounterSound.lean`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- Direction of a counter. -/
inductive Mode where
  | up
  | down
  deriving DecidableEq, Repr

/-- Abstract effect on the tracked local along one kind of exit. -/
inductive Eff where
  /-- This exit cannot happen. -/
  | unreach
  /-- The local is unchanged. -/
  | keep
  /-- The local moved by exactly one step. -/
  | step
  /-- Anything may have happened. -/
  | bad
  deriving DecidableEq, Repr

/-- Effects on normal completion, on `continue`, and on `break`. -/
structure Effs where
  normal : Eff
  continued : Eff
  broke : Eff
  deriving DecidableEq, Repr

namespace Eff

/-- Effect of running something with effect `second` after effect `first`. -/
def comp : Eff → Eff → Eff
  | .unreach, _ => .unreach
  | _, .unreach => .unreach
  | .keep, e => e
  | .step, .keep => .step
  | _, _ => .bad

/-- Effect of an exit reachable in two ways. -/
def join : Eff → Eff → Eff
  | .unreach, e => e
  | e, .unreach => e
  | .keep, .keep => .keep
  | .step, .step => .step
  | _, _ => .bad

/-- Shadowing: any reachable exit restores the local. -/
def restore : Eff → Eff
  | .unreach => .unreach
  | _ => .keep

def quiet : Eff → Bool
  | .unreach | .keep => true
  | _ => false

end Eff

def Effs.keep : Effs := ⟨.keep, .unreach, .unreach⟩
def Effs.bad : Effs := ⟨.bad, .bad, .bad⟩

/-- `value` is `i + 1` (up) or `i - 1` (down). -/
def isStep (mode : Mode) (i : VarName) : Exp Word → Bool
  | .op .add [.var .local name, .const k] => mode == .up && name == i && k == 1
  | .op .sub [.var .local name, .const k] => mode == .down && name == i && k == 1
  | _ => false

/-- Abstract effect of a program on the local `i`. -/
def effect (mode : Mode) (i : VarName) : Prog Word → Effs
  | .skip | .tick | .annot _ _ | .store _ _ | .store32 _ _ | .storeByte _ _
  | .shMemStore _ _ _ | .extCall _ _ _ _ _ | .assign .global _ _ => Effs.keep
  | .assign .local name value =>
      if name == i then
        if isStep mode i value then ⟨.step, .unreach, .unreach⟩ else Effs.bad
      else Effs.keep
  | .primitive name _ _ => if name == i then Effs.bad else Effs.keep
  | .shMemLoad _ .local name _ => if name == i then Effs.bad else Effs.keep
  | .shMemLoad _ .global _ _ => Effs.keep
  | .break => ⟨.unreach, .unreach, .keep⟩
  | .continue => ⟨.unreach, .keep, .unreach⟩
  | .raise _ _ | .return _ => ⟨.unreach, .unreach, .unreach⟩
  | .seq first second =>
      let a := effect mode i first
      let b := effect mode i second
      ⟨a.normal.comp b.normal, a.continued.join (a.normal.comp b.continued),
        a.broke.join (a.normal.comp b.broke)⟩
  | .ite _ thenBranch elseBranch =>
      let a := effect mode i thenBranch
      let b := effect mode i elseBranch
      ⟨a.normal.join b.normal, a.continued.join b.continued, a.broke.join b.broke⟩
  | .while _ body =>
      let a := effect mode i body
      if a.normal.quiet && a.continued.quiet && a.broke.quiet then Effs.keep else Effs.bad
  | .dec name _ _ body =>
      let a := effect mode i body
      if name == i then ⟨a.normal.restore, a.continued.restore, a.broke.restore⟩ else a
  | .decCall name _ _ _ body =>
      let a := effect mode i body
      if name == i then ⟨a.normal.restore, a.continued.restore, a.broke.restore⟩ else a
  | .call (some (destination, some (_, handlerVar, handlerProgram))) _ _ =>
      let a := effect mode i handlerProgram
      if handlerVar == i || destination == some (.local, i) then Effs.bad
      else ⟨Eff.keep.join a.normal, a.continued, a.broke⟩
  | .call (some (destination, none)) _ _ =>
      if destination == some (.local, i) then Effs.bad else Effs.keep
  | .call none _ _ => Effs.keep

/-- How a guard bounds its counter. -/
inductive Kind where
  /-- `i <+ e`: unsigned, counting up. -/
  | upU
  /-- `i < e`: signed, counting up. -/
  | upS
  /-- `i >+ 0`, `i > 0` or `i != 0`: counting down to zero. -/
  | down
  deriving DecidableEq, Repr

def Kind.mode : Kind → Mode
  | .upU | .upS => .up
  | .down => .down

/-- The counter a guard tests, with the way the guard bounds it. -/
def guardKind : Exp Word → Option (Kind × VarName)
  | .cmp .lower (.var .local i) _ => some (.upU, i)
  | .cmp .less (.var .local i) _ => some (.upS, i)
  | .cmp .lower (.const k) (.var .local i) => if k == 0 then some (.down, i) else none
  | .cmp .less (.const k) (.var .local i) => if k == 0 then some (.down, i) else none
  | .cmp .notEqual (.var .local i) (.const k) => if k == 0 then some (.down, i) else none
  | _ => none

/-- Every way back to the loop head moves the counter by one step. -/
def stepsBack (e : Effs) : Bool :=
  (e.normal == .step || e.normal == .unreach) && (e.continued == .step || e.continued == .unreach)

/-- The loop is a recognised counter loop. -/
def counterLoop (c : Exp Word) (body : Prog Word) : Bool :=
  match guardKind c with
  | some (kind, i) => stepsBack (effect kind.mode i body)
  | none => false

end InitECandidate.Solver.GuestBound
