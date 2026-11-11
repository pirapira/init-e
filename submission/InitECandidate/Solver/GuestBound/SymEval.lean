import InitECandidate.Solver.GuestBound.GlobalLoop

/-!
# Symbolic evaluation

Rewrite and inversion lemmas for evaluating expressions and single statements
under `WordEnv`, for hand proofs of function specifications.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Expression evaluation at the environment's parameters. -/
def Env.eval (E : Env σ) (s : St σ) (e : Exp Word) : Option (PanValue Word) :=
  evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
    E.bytesInWord e E.memoryAccess

@[simp] theorem eval_const (s : St σ) (k : Word) : E.eval s (.const k) = some (.word k) := by
  simp [Env.eval, evalPanValueExp]

@[simp] theorem eval_local (s : St σ) (x : VarName) : E.eval s (.var .local x) = s.locals x := by
  simp [Env.eval, evalPanValueExp]

@[simp] theorem eval_global (s : St σ) (x : VarName) :
    E.eval s (.var .global x) = s.globals x := by
  simp [Env.eval, evalPanValueExp]

/-- A binary word operation evaluates both operands to words. -/
theorem eval_op2_inv (hE : WordEnv E) {s : St σ} {operator : BinOp} {a b : Exp Word}
    {x : PanValue Word} (h : E.eval s (.op operator [a, b]) = some x) :
    ∃ va vb w, E.eval s a = some (.word va) ∧ E.eval s b = some (.word vb) ∧
      wordOp operator [va, vb] = some w ∧ x = .word w := by
  obtain ⟨access, hacc, -, -, -⟩ := hE.access
  have hop := hE.wordOp access hacc
  simp only [Env.eval] at h ⊢
  rw [hacc] at h ⊢
  cases ha : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord a (some access) with
  | none => simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, ha] at h
  | some av =>
    cases hb : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord b (some access) with
    | none => simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, ha, hb] at h
    | some bv =>
      cases av <;> cases bv <;>
        simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, ha, hb, panValueWordProjection,
          hop] at h
      rename_i va vb
      obtain ⟨w, hw, rfl⟩ := h
      exact ⟨va, vb, w, rfl, rfl, hw, rfl⟩

/-- A binary word operation on word operands. -/
theorem eval_op2 (hE : WordEnv E) {s : St σ} (operator : BinOp) {a b : Exp Word} {va vb : Word}
    (ha : E.eval s a = some (.word va)) (hb : E.eval s b = some (.word vb)) :
    E.eval s (.op operator [a, b]) = (wordOp operator [va, vb]).map .word := by
  obtain ⟨access, hacc, -, -, -⟩ := hE.access
  have hop := hE.wordOp access hacc
  simp only [Env.eval] at ha hb ⊢
  rw [hacc] at ha hb ⊢
  simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, ha, hb, hop]

/-- A comparison on word operands. -/
theorem eval_cmp (hE : WordEnv E) {s : St σ} (operator : Cmp) {a b : Exp Word} {va vb : Word}
    (ha : E.eval s a = some (.word va)) (hb : E.eval s b = some (.word vb)) :
    E.eval s (.cmp operator a b) = some (.word (evalPanCmp operator va vb)) := by
  obtain ⟨access, hacc, -, -, hcmp⟩ := hE.access
  simp only [Env.eval] at ha hb ⊢
  rw [hacc] at ha hb ⊢
  simp [evalPanValueExp, ha, hb, hcmp]

/-- A condition evaluates to the word its expression evaluates to. -/
theorem cond_of_eval {s : St σ} {c : Exp Word} {v : Word} {k : Nat}
    (h : E.cond s c = some (v, k)) : E.eval s c = some (.word v) := cond_eval h

/-- A declaration fails or runs its body with the declared value bound. -/
theorem dec_run_inv {fuel : Nat} {s : St σ} {x : VarName} {shape : Shape} {e : Exp Word}
    {body : Prog Word} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.dec x shape e body) = some (r, n)) :
    r.isError = true ∨ ∃ fuel' v rb nb, E.eval s e = some v ∧
      panShapeMatches (panValueShape E.structs v) shape = true ∧
      E.run fuel' ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body =
        some (rb, nb) ∧
      r = restorePanValueFfiLocal x (s.locals x) rb := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory e E.memoryAccess shape with
    | none =>
      rw [hacc] at h
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inl rfl
    | some accepted =>
      rw [hacc] at h
      simp only [Option.elim_some] at h
      cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel
          (updatePanValueMap s.locals x accepted.1) s.globals s.memory s.ffi body
          (memoryAccess := E.memoryAccess) (contracts := E.contracts)
          (memoryHandler := E.memoryHandler) with
      | none => rw [hb] at h; simp at h
      | some pair =>
        obtain ⟨rb, nb⟩ := pair
        rw [hb] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [panValueDecAccepted, evalPanValueExpCounted] at hacc
        cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
            E.topAddress E.bytesInWord e E.memoryAccess with
        | none => rw [hv] at hacc; simp at hacc
        | some v =>
          rw [hv] at hacc
          simp only [Option.map_some] at hacc
          split at hacc
          · rename_i hshape
            simp only [Option.some.injEq] at hacc
            subst hacc
            exact Or.inr ⟨fuel, v, rb, nb, hv, hshape, hb, rfl⟩
          · simp at hacc

/-- A conditional fails or runs the branch its condition selects. -/
theorem ite_run_inv {fuel : Nat} {s : St σ} {c : Exp Word} {thenBranch elseBranch : Prog Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.ite c thenBranch elseBranch) = some (r, n)) :
    r.isError = true ∨ ∃ fuel' v n', E.eval s c = some (.word v) ∧
      ((v ≠ 0 ∧ E.run fuel' s thenBranch = some (r, n')) ∨
        (v = 0 ∧ E.run fuel' s elseBranch = some (r, n'))) := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory c E.memoryAccess with
    | none =>
      rw [hcond] at h
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inl rfl
    | some pair =>
      obtain ⟨v, k⟩ := pair
      rw [hcond] at h
      have hev : E.eval s c = some (.word v) := cond_eval hcond
      simp only [Option.elim_some] at h
      by_cases hc : (v != 0) = true
      · rw [if_pos hc] at h
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi thenBranch (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at h; simp at h
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at h
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact Or.inr ⟨fuel, v, nb, hev, Or.inl ⟨by simpa using hc, hb⟩⟩
      · rw [if_neg hc] at h
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi elseBranch (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at h; simp at h
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at h
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact Or.inr ⟨fuel, v, nb, hev, Or.inr ⟨by simpa using hc, hb⟩⟩

/-- A global assignment fails or stores the value of its expression. -/
theorem assign_global_inv {fuel : Nat} {s : St σ} {x : VarName} {e : Exp Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.assign .global x e) = some (r, n)) :
    r.isError = true ∨ ∃ v, E.eval s e = some v ∧
      r = .normal s.locals (updatePanValueMap s.globals x v) s.memory s.ffi := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueAssignGlobalResult, evalPanValueExpCounted] at h
    cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord e E.memoryAccess with
    | none =>
      rw [hv] at h
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inl rfl
    | some v =>
      rw [hv] at h
      simp only [Option.map_some] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inr ⟨v, hv, rfl⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl rfl

/-- A `return` fails or returns the value of its expression with the current non-local state. -/
theorem return_inv {fuel : Nat} {s : St σ} {e : Exp Word} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.return e) = some (r, n)) :
    r.isError = true ∨ ∃ v, E.eval s e = some v ∧
      r = .returned (fun _ => none) s.globals s.memory s.ffi [v] := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueReturnResult, evalPanValueExpCounted] at h
    cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord e E.memoryAccess with
    | none =>
      rw [hv] at h
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inl rfl
    | some v =>
      rw [hv] at h
      simp only [Option.map_some] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inr ⟨v, hv, rfl⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl rfl

end InitECandidate.Solver.GuestBound
