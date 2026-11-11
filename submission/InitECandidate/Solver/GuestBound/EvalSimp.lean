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

theorem shape_word (structs : StructContext) (w : Word) :
    panValueShape structs (.word w) = .one := by
  simp [panValueShape]

theorem shape_rStruct (structs : StructContext) (fields : List (PanValue Word)) :
    panValueShape structs (.rStruct fields) = .comb (fields.map (panValueShape structs)) := by
  rw [panValueShape]

theorem shape_matches_self (sh : Shape) : panShapeMatches sh sh = true :=
  (panShapeMatches_eq_true _ _).mpr rfl

theorem wordsProj_nil :
    List.mapM panValueWordProjection ([] : List (PanValue Word)) = some [] := rfl

theorem wordsProj_cons (w : Word) (vs : List (PanValue Word)) :
    List.mapM panValueWordProjection (PanValue.word w :: vs) =
      (List.mapM panValueWordProjection vs).map (w :: ·) := by
  simp only [List.mapM_cons, panValueWordProjection, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  cases List.mapM panValueWordProjection vs <;> rfl

theorem update_lookup (locals : VarName → Option (PanValue Word)) (x y : VarName)
    (v : PanValue Word) :
    updatePanValueMap locals x v y = if y == x then some v else locals y := rfl

/-- `runs_primitive` with the arguments as `E.evalArgs`. -/
theorem runs_primitive' {s : St σ} {x : VarName} {operator : PrimOp}
    {arguments : List (Exp Word)} {r : Result σ} :
    Runs E s (.primitive x operator arguments) r ↔
      r = match E.evalArgs s arguments with
        | some values =>
            match E.primitive operator values with
            | some value =>
                match s.locals x with
                | some old =>
                    if panShapeMatches (panValueShape E.structs value)
                        (panValueShape E.structs old) then
                      .normal (updatePanValueMap s.locals x value) s.globals s.memory s.ffi
                    else s.err
                | none => s.err
            | none => s.err
        | none => s.err := runs_primitive

/-- A declaring call, in terms of `Runs`. -/
theorem runs_decCall_inv {f : FunName} {s : St σ} {x : VarName} {shape : Shape}
    {arguments : List (Exp Word)} {body : Prog Word} {r : Result σ}
    (h : Runs E s (.decCall x shape f arguments body) r) :
    r.isError = true ∨ ∃ parameters calleeBody values calleeLocals rb,
      lookupPanFunction f E.functions = some (parameters, calleeBody) ∧
      E.evalArgs s arguments = some values ∧
      bindPanValueParameters parameters values = some calleeLocals ∧
      Runs E ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ calleeBody rb ∧
      match rb with
      | .returned _ g m ffi [value] =>
          ∃ r', panShapeMatches (panValueShape E.structs value) shape = true ∧
            Runs E ⟨updatePanValueMap s.locals x value, g, m, ffi⟩ body r' ∧
            r = restorePanValueFfiLocal x (s.locals x) r'
      | .raised _ g m ffi exception value => r = .raised (fun _ => none) g m ffi exception value
      | .finalFfi _ g m ffi event => r = .finalFfi (fun _ => none) g m ffi event
      | _ => False := by
  obtain ⟨fuel, n, h⟩ := h
  rcases decCall_run_inv h with herr | ⟨fuel₁, parameters, calleeBody, values, calleeLocals, rb,
    nb, hlookup, hvalues, hbind, hcallee, hout⟩
  · exact Or.inl herr
  refine Or.inr ⟨parameters, calleeBody, values, calleeLocals, rb, hlookup, hvalues, hbind,
    ⟨fuel₁, nb, hcallee⟩, ?_⟩
  cases rb with
  | returned l g m ffi values' =>
    cases values' with
    | nil => exact hout
    | cons value rest =>
      cases rest with
      | nil =>
        obtain ⟨fuel₂, r', n', hshape, hrun', hr⟩ := hout
        exact ⟨r', hshape, ⟨fuel₂, n', hrun'⟩, hr⟩
      | cons value' rest' => exact hout
  | _ => exact hout

/-- A call statement without a handler, in terms of `Runs`. -/
theorem runs_call_inv {f : FunName} (destination : Option (Option (VarKind × VarName)))
    {s : St σ} {arguments : List (Exp Word)} {r : Result σ}
    (h : Runs E s (.call (destination.map fun dest => (dest, none)) f arguments) r) :
    r.isError = true ∨ ∃ parameters body values calleeLocals rb,
      lookupPanFunction f E.functions = some (parameters, body) ∧
      E.evalArgs s arguments = some values ∧
      bindPanValueParameters parameters values = some calleeLocals ∧
      Runs E ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body rb ∧
      CallOutcome E s destination rb r := by
  obtain ⟨fuel, n, h⟩ := h
  rcases call_run_inv destination h with herr | ⟨fuel', parameters, body, values, calleeLocals,
    rb, nb, hlookup, hvalues, hbind, hcallee, hout⟩
  · exact Or.inl herr
  · exact Or.inr ⟨parameters, body, values, calleeLocals, rb, hlookup, hvalues, hbind,
      ⟨fuel', nb, hcallee⟩, hout⟩

end InitECandidate.Solver.GuestBound
