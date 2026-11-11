import InitECandidate.Solver.GuestBound.GuestShape
import Tools.GenGuestBoundStamp
import Std.Data.HashMap

/-!
Generator for the per-function cost theorems under
`submission/InitECandidate/Solver/GuestBound/Fns/`. Building this module runs
it: `lake build Tools.GenGuestBound`. It computes `staticCost` for every guest
function in call-graph order and writes one theorem per function, grouped by
call-graph level. Functions whose call tree contains a loop are skipped until
loop bounds are available.
-/

open Flapjack InitECandidate.Solver.GuestBound

namespace Tools.GenGuestBound

partial def callees : Prog (BitVec 64) → List String
  | .dec _ _ _ body => callees body
  | .seq a b => callees a ++ callees b
  | .ite _ a b => callees a ++ callees b
  | .while _ body => callees body
  | .call (some (_, some (_, _, h))) f _ => f :: callees h
  | .call _ f _ => [f]
  | .decCall _ _ f _ body => f :: callees body
  | _ => []

partial def loopCount : Prog (BitVec 64) → Nat
  | .dec _ _ _ body => loopCount body
  | .seq a b => loopCount a + loopCount b
  | .ite _ a b => loopCount a + loopCount b
  | .while _ body => 1 + loopCount body
  | .call (some (_, some (_, _, h))) _ _ => loopCount h
  | .decCall _ _ _ _ body => loopCount body
  | _ => 0

partial def loops : Prog (BitVec 64) → List (Exp (BitVec 64) × Prog (BitVec 64))
  | .dec _ _ _ body => loops body
  | .seq a b => loops a ++ loops b
  | .ite _ a b => loops a ++ loops b
  | .while c body => (c, body) :: loops body
  | .call (some (_, some (_, _, h))) _ _ => loops h
  | .decCall _ _ _ _ body => loops body
  | _ => []

/-- Hint and iteration bound of every loop in pre-order. Hints: `0` for
`loopOk`, `1` for `walkMLoop`, `2` for a hand-proved loop, `3` for `shapeLoop`
under the declarations in scope (`none` when they are not tracked). -/
partial def loopInfos (manual : Nat → Option Nat) :
    Prog (BitVec 64) → Option (List (String × Shape)) → StateM Nat (List (Option Nat × Nat))
  | .dec x sh _ body, D => loopInfos manual body (D.map ((x, sh) :: ·))
  | .decCall x sh _ _ body, D => loopInfos manual body (D.map ((x, sh) :: ·))
  | .seq a b, D => do
      let l₁ ← loopInfos manual a D
      let keep := shapeOk shapeCallee (loopVars a) a
      let l₂ ← loopInfos manual b (if keep then D else none)
      return l₁ ++ l₂
  | .ite _ a b, D => do
      let l₁ ← loopInfos manual a D
      let l₂ ← loopInfos manual b D
      return l₁ ++ l₂
  | .while c body, D => do
      let index ← get
      set (index + 1)
      let info : Option Nat × Nat :=
        match manual index with
        | some n => (some 2, n)
        | none =>
          if loopOk Guest.Software.guestAst c body then (some 0, 2 ^ 64)
          else if walkMLoop (quietFn Guest.Software.guestAst) body then
            (some 1, walkIters (assignedLocals body).length)
          else match D with
            | some d =>
                if shapeLoop shapeCallee d body then
                  (some 3, shapeIters (flatMax d (loopVars body)) (loopVars body).length)
                else (none, 0)
            | none => (none, 0)
      let inner ← loopInfos manual body (if info.1 == some 3 then D else none)
      return info :: inner
  | .call (some (_, some (_, _, h))) _ _, _ => loopInfos manual h none
  | _, _ => pure []

/-- A hand-proved loop, from `GuestBound/manual-loops.txt`: function, pre-order
loop index, iteration bound, and the module that proves `Manual.<fn>.loop<index>`. -/
structure ManualLoop where
  fn : String
  index : Nat
  iters : Nat
  module : String

def manualPath : String := "submission/InitECandidate/Solver/GuestBound/manual-loops.txt"

def readManual : IO (List ManualLoop) := do
  if !(← System.FilePath.pathExists manualPath) then return []
  let text ← IO.FS.readFile manualPath
  let mut out := []
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " " |>.filter (· ≠ "") with
    | [fn, index, iters, module] =>
        out := { fn, index := index.toNat!, iters := iters.toNat!, module } :: out
    | _ => throw (IO.userError s!"bad line in {manualPath}: {line}")
  return out.reverse

/-- A hand-proved function, from `GuestBound/manual-fns.txt`: function, step
bound, and the module that proves `Manual.<fn>.cost`. -/
structure ManualFn where
  fn : String
  bound : Nat
  module : String

def manualFnPath : String := "submission/InitECandidate/Solver/GuestBound/manual-fns.txt"

def readManualFns : IO (List ManualFn) := do
  if !(← System.FilePath.pathExists manualFnPath) then return []
  let text ← IO.FS.readFile manualFnPath
  let mut out := []
  for line in text.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty || line.startsWith "#" then continue
    match line.splitOn " " |>.filter (· ≠ "") with
    | [fn, bound, module] => out := { fn, bound := bound.toNat!, module } :: out
    | _ => throw (IO.userError s!"bad line in {manualFnPath}: {line}")
  return out.reverse

/-- `staticCost` with the loop's pre-order index available, for hand-proved loops. -/
partial def costWith (callee : String → Nat)
    (iters : Nat → Exp (BitVec 64) → Prog (BitVec 64) → Nat) :
    Prog (BitVec 64) → StateM Nat Nat
  | .skip | .break | .continue | .tick | .annot _ _ => pure 1
  | .dec _ _ value body => do
      return panValueExpStepCost value + (← costWith callee iters body) + 1
  | .assign _ _ value => pure (panValueExpStepCost value + 1)
  | .primitive _ _ arguments => pure (panValueExpsStepCost arguments + 1)
  | .store address value | .store32 address value | .storeByte address value =>
      pure (panValueExpStepCost address + panValueExpStepCost value + 1)
  | .seq first second => do
      let a ← costWith callee iters first
      let b ← costWith callee iters second
      return a + b + 1
  | .ite condition thenBranch elseBranch => do
      let a ← costWith callee iters thenBranch
      let b ← costWith callee iters elseBranch
      return panValueExpStepCost condition + max a b + 1
  | .while condition body => do
      let index ← get
      set (index + 1)
      let b ← costWith callee iters body
      return iters index condition body * (panValueExpStepCost condition + b + 1)
  | .call (some (_, some (_, _, handlerProgram))) function arguments => do
      let h ← costWith callee iters handlerProgram
      return panValueExpsStepCost arguments + callee function + h + 1
  | .call _ function arguments => pure (panValueExpsStepCost arguments + callee function + 0 + 1)
  | .decCall _ _ function arguments body => do
      let b ← costWith callee iters body
      return panValueExpsStepCost arguments + callee function + b + 1
  | .extCall _ configuration configurationLength array arrayLength =>
      pure (panValueExpsStepCost [configuration, configurationLength, array, arrayLength] + 1)
  | .raise _ value | .return value => pure (panValueExpStepCost value + 1)
  | .shMemLoad _ _ _ address => pure (panValueExpStepCost address + 1)
  | .shMemStore _ address value =>
      pure (panValueExpStepCost address + panValueExpStepCost value + 1)

structure Info where
  index : Nat
  name : String
  body : Prog (BitVec 64)

def functions : List Info := Id.run do
  let mut out := []
  let mut i := 0
  for d in Guest.Software.guestAst do
    match d with
    | .function f => out := { index := i, name := f.name, body := f.body } :: out
    | _ => pure ()
    i := i + 1
  return out.reverse

def chunkSize : Nat := 6

def run : IO Unit := do
  let fns := functions
  let manual ← readManual
  let manualFns ← readManualFns
  let manualFnFor (fn : String) : Option ManualFn := manualFns.find? fun m => m.fn == fn
  let manualFor (fn : String) (index : Nat) : Option ManualLoop :=
    manual.find? fun m => m.fn == fn && m.index == index
  let infosOf (f : Info) : List (Option Nat × Nat) :=
    (loopInfos (fun index => (manualFor f.name index).map (·.iters)) f.body (some [])).run' 0
  let hintsOf (f : Info) : List (Option Nat) := (infosOf f).map (·.1)
  let itersOf (f : Info) (index : Nat) (_ : Exp (BitVec 64)) (_ : Prog (BitVec 64)) : Nat :=
    ((infosOf f)[index]?.map (·.2)).getD (2 ^ 64)
  let byName : Std.HashMap String Info := fns.foldl (fun m f => m.insert f.name f) {}
  -- level and cost by iterating to a fixed point (the call graph is acyclic)
  let mut level : Std.HashMap String Nat := {}
  let mut cost : Std.HashMap String Nat := {}
  let mut skipped : Std.HashMap String Unit := {}
  let mut pending := fns
  let mut progress := true
  while progress do
    progress := false
    let mut rest := []
    for f in pending do
      let cs := callees f.body
      if ((manualFnFor f.name).isNone && (hintsOf f).any (·.isNone)) ||
          cs.any (fun c => skipped.contains c || !byName.contains c) then
        skipped := skipped.insert f.name ()
        progress := true
      else if cs.all (fun c => cost.contains c) then
        let lv := cs.foldl (fun acc c => max acc (level.getD c 0 + 1)) 0
        let callee := fun c => cost.getD c 0
        let n := match manualFnFor f.name with
          | some m => m.bound
          | none => (costWith callee (itersOf f) f.body).run' 0
        level := level.insert f.name lv
        cost := cost.insert f.name n
        progress := true
      else rest := f :: rest
    pending := rest.reverse
  let dir := "submission/InitECandidate/Solver/GuestBound/Fns"
  IO.FS.createDirAll dir
  let maxLevel := level.fold (fun acc _ lv => max acc lv) 0
  let mut total := 0
  for lv in [0:maxLevel + 1] do
    let here := fns.filter (fun f => level.get? f.name == some lv)
    let mut chunks : List (List Info) := []
    let mut current : List Info := []
    for f in here do
      current := f :: current
      if current.length == chunkSize then
        chunks := current.reverse :: chunks
        current := []
    if !current.isEmpty then chunks := current.reverse :: chunks
    chunks := chunks.reverse
    let mut j := 0
    let mut imports := ""
    for chunk in chunks do
      let prev := if lv == 0 then "import InitECandidate.Solver.GuestBound.GuestShape"
        else s!"import InitECandidate.Solver.GuestBound.Fns.L{lv - 1}"
      let modules := (manual.filter fun m => chunk.any fun f => f.name == m.fn).map (·.module) ++
        (manualFns.filter fun m => chunk.any fun f => f.name == m.fn).map (·.module)
      let extra := String.join (modules.eraseDups.map fun m => s!"\nimport {m}")
      let mut text := s!"{prev}{extra}\n\n/-! Generated by `Tools/GenGuestBound.lean`; do not edit. -/\n\nnamespace InitECandidate.Solver.GuestBound.Fn\nopen Flapjack\n\nvariable \{σ : Type} \{E : Env σ}\n"
      for f in chunk do
        let hints := (hintsOf f).map (·.getD 0)
        let hintText := if hints.all (· == 0) then "" else s!" {hints}"
        if (manualFnFor f.name).isSome then
          let arguments := String.join ((callees f.body).eraseDups.map fun c => s!" («{c}» hE)")
          text := text ++ s!"\ntheorem «{f.name}» (hE : GuestEnv E) : FunCost E \"{f.name}\" {cost.getD f.name 0} :=\n  FunCost.mono (InitECandidate.Solver.GuestBound.Manual.«{f.name}».cost hE{arguments}) (by decide +kernel)\n"
        else
          text := text ++ s!"\ntheorem «{f.name}» (hE : GuestEnv E) : FunCost E \"{f.name}\" {cost.getD f.name 0} := by\n  guest_cost {f.index}{hintText}\n"
        total := total + 1
      text := text ++ "\nend InitECandidate.Solver.GuestBound.Fn\n"
      IO.FS.writeFile s!"{dir}/L{lv}C{j}.lean" text
      imports := imports ++ s!"import InitECandidate.Solver.GuestBound.Fns.L{lv}C{j}\n"
      j := j + 1
    IO.FS.writeFile s!"{dir}/L{lv}.lean" imports
  IO.println s!"functions {fns.length}, generated {total}, skipped {skipped.size}, pending {pending.length}, levels {maxLevel + 1}"

/-- Hints of the loops of `f`, with hand-proved loops taken into account. -/
def hintsFor (manual : List ManualLoop) (manualFns : List ManualFn) (f : Info) :
    List (Option Nat) :=
  let whole := manualFns.any fun m => m.fn == f.name
  ((loopInfos (fun index => (manual.find? fun m => m.fn == f.name && m.index == index).map
    (·.iters)) f.body (some [])).run' 0).map fun info =>
      if whole && info.1.isNone then some 2 else info.1

def loopReport : IO Unit := do
  let manual ← readManual
  let manualFns ← readManualFns
  let mut counts : Std.HashMap Nat Nat := {}
  let mut rejected : List String := []
  for f in functions do
    for (hint, index) in (hintsFor manual manualFns f).zipIdx do
      match hint with
      | some h => counts := counts.insert h (counts.getD h 0 + 1)
      | none => rejected := s!"{f.name} loop {index}" :: rejected
  IO.println s!"loops by rule: counter {counts.getD 0 0}, walk {counts.getD 1 0}, manual {counts.getD 2 0}, shape {counts.getD 3 0}; rejected {rejected.length}"
  for r in rejected.reverse do IO.println r

/-- For each function with a rejected loop, how many functions call it transitively. -/
def blockerReport : IO Unit := do
  let manual ← readManual
  let manualFns ← readManualFns
  let fns := functions
  let direct : Std.HashMap String (List String) :=
    fns.foldl (fun m f => m.insert f.name (callees f.body)) {}
  let roots := fns.filter (fun f => (hintsFor manual manualFns f).any (·.isNone))
  let mut lines : List (Nat × String) := []
  for root in roots do
    let mut reach : Std.HashMap String Unit := ({} : Std.HashMap String Unit).insert root.name ()
    let mut changed := true
    while changed do
      changed := false
      for f in fns do
        if !reach.contains f.name && ((direct.getD f.name []).any fun c => reach.contains c) then
          reach := reach.insert f.name ()
          changed := true
    lines := (reach.size - 1, root.name) :: lines
  let sorted := lines.toArray.qsort (fun a b => a.1 > b.1)
  for (count, name) in sorted do IO.println s!"{count} {name}"

#eval run
#eval loopReport
#eval blockerReport

end Tools.GenGuestBound
