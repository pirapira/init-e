import InitECandidate.Solver.GuestBound.Runs
import InitECandidate.Solver.GuestBound.CallInv

/-!
# Evaluating expressions by rewriting

Equations giving the value of an expression from the values of its parts.
Together with the `Runs` lemmas they let `simp` execute straight-line code.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem evalF_local (s : St σ) (x : VarName) : E.eval s (.var .local x) = s.locals x := by
  simp [Env.eval, evalPanValueExp]

theorem evalF_rField (s : St σ) (i : Nat) (e : Exp Word) :
    E.eval s (.rField i e) =
      match E.eval s e with
      | some (.rStruct fields) => fields[i]?
      | _ => none := by
  simp only [Env.eval]
  rw [evalPanValueExp]
  cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord e E.memoryAccess with
  | none => rfl
  | some v => cases v <;> rfl

theorem evalArgs_nil (s : St σ) : E.evalArgs s [] = some [] := by
  simp [Env.evalArgs, evalPanValueExps, evalPanValueExp.evalPanValueExps]

theorem evalArgs_cons (s : St σ) (e : Exp Word) (es : List (Exp Word)) :
    E.evalArgs s (e :: es) =
      match E.eval s e with
      | some v => (E.evalArgs s es).map (v :: ·)
      | none => none := by
  simp only [Env.evalArgs, Env.eval, evalPanValueExps]
  rw [evalPanValueExp.evalPanValueExps]
  cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord e E.memoryAccess with
  | none => rfl
  | some v =>
    cases evalPanValueExp.evalPanValueExps E.structs s.locals s.globals s.memory E.baseAddress
        E.topAddress E.bytesInWord es E.memoryAccess with
    | none => rfl
    | some vs => rfl

theorem evalF_rStruct (s : St σ) (es : List (Exp Word)) :
    E.eval s (.rStruct es) = (E.evalArgs s es).map .rStruct := by
  simp only [Env.eval, Env.evalArgs, evalPanValueExps]
  rw [evalPanValueExp]

theorem evalF_cmp (hE : WordEnv E) (s : St σ) (operator : Cmp) (a b : Exp Word) :
    E.eval s (.cmp operator a b) =
      match E.eval s a, E.eval s b with
      | some (.word x), some (.word y) => some (.word (evalPanCmp operator x y))
      | _, _ => none := by
  obtain ⟨access, hacc, -, -, hcmp⟩ := hE.access
  simp only [Env.eval]
  rw [evalPanValueExp, hacc]
  cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord a (some access) with
  | none => rfl
  | some va =>
    cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord b (some access) with
    | none => cases va <;> rfl
    | some vb => cases va <;> cases vb <;> simp [hcmp]

theorem evalF_shift (hE : WordEnv E) (s : St σ) (operator : Shift) (a b : Exp Word) :
    E.eval s (.shift operator a b) =
      match E.eval s a, E.eval s b with
      | some (.word x), some (.word y) => (RiscV.panRiscVShift operator x y).map .word
      | _, _ => none := by
  obtain ⟨access, hacc, -, -, -⟩ := hE.access
  have hsh := hE.shift access hacc
  simp only [Env.eval]
  rw [evalPanValueExp, hacc]
  cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord a (some access) with
  | none => rfl
  | some va =>
    cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord b (some access) with
    | none => cases va <;> rfl
    | some vb => cases va <;> cases vb <;> simp [hsh]

theorem evalF_op (hE : WordEnv E) (s : St σ) (operator : BinOp) (es : List (Exp Word)) :
    E.eval s (.op operator es) =
      match E.evalArgs s es with
      | some values =>
          match values.mapM panValueWordProjection with
          | some words => (wordOp operator words).map .word
          | none => none
      | none => none := by
  obtain ⟨access, hacc, -, -, -⟩ := hE.access
  have hop := hE.wordOp access hacc
  simp only [Env.eval, Env.evalArgs, evalPanValueExps]
  rw [evalPanValueExp, hacc]
  cases evalPanValueExp.evalPanValueExps E.structs s.locals s.globals s.memory E.baseAddress
      E.topAddress E.bytesInWord es (some access) with
  | none => rfl
  | some values =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases values.mapM panValueWordProjection with
    | none => rfl
    | some words => simp [hop]

end InitECandidate.Solver.GuestBound
