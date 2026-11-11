import InitECandidate.Solver.GuestBound.SymEval
import InitECandidate.Solver.GuestBound.Orbit
import InitECandidate.Solver.GuestBound.HalvingLoop

/-!
# Fuel-free runs

`Runs E s p r`: some run of `p` from `s` ends in `r`. The lemmas below
characterise `Runs` by the syntax of `p`, so that straight-line code can be
executed symbolically by rewriting with them.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Some run of `p` from `s` ends in `r`. -/
def Runs (E : Env σ) (s : St σ) (p : Prog Word) (r : Result σ) : Prop :=
  ∃ fuel n, E.run fuel s p = some (r, n)

/-- The error result that leaves the state alone. -/
def St.err (s : St σ) : Result σ := .error s.locals s.globals s.memory s.ffi

theorem Runs.of_run {fuel : Nat} {s : St σ} {p : Prog Word} {r : Result σ} {n : Nat}
    (h : E.run fuel s p = some (r, n)) : Runs E s p r := ⟨fuel, n, h⟩

theorem runs_of_map {fuel : Nat} {s : St σ} {p : Prog Word} {r : Result σ}
    (h : (E.run fuel s p).map Prod.fst = some r) : Runs E s p r := by
  obtain ⟨⟨r', n⟩, h', rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨fuel, n, h'⟩

theorem runs_skip {s : St σ} {r : Result σ} :
    Runs E s .skip r ↔ r = .normal s.locals s.globals s.memory s.ffi := by
  constructor
  · rintro ⟨fuel, n, h⟩
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
    | succ fuel =>
      simp only [Env.run, evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  · rintro rfl
    exact runs_of_map (fuel := 1) (by simp [Env.run, evalPanValueFfiProgSteps])

theorem runs_seq {s : St σ} {first second : Prog Word} {r : Result σ} :
    Runs E s (.seq first second) r ↔ ∃ r₁, Runs E s first r₁ ∧
      match r₁ with
      | .normal l g m f => Runs E ⟨l, g, m, f⟩ second r
      | _ => r = r₁ := by
  constructor
  · rintro ⟨fuel, n, h⟩
    obtain ⟨fuel', r₁, n₁, h₁, hrest⟩ := seq_run_inv h
    refine ⟨r₁, ⟨fuel', n₁, h₁⟩, ?_⟩
    cases r₁ with
    | normal l g m f =>
      obtain ⟨n₂, h₂⟩ := hrest
      exact ⟨fuel', n₂, h₂⟩
    | _ => exact hrest
  · rintro ⟨r₁, ⟨f₁, n₁, h₁⟩, hrest⟩
    cases r₁ with
    | normal l g m f =>
      obtain ⟨f₂, n₂, h₂⟩ := hrest
      have h₁' := run_mono (Nat.le_max_left f₁ f₂) h₁
      have h₂' := run_mono (Nat.le_max_right f₁ f₂) h₂
      simp only [Env.run] at h₁' h₂'
      refine runs_of_map (fuel := max f₁ f₂ + 1) ?_
      simp only [Env.run]
      rw [evalPanValueFfiProgSteps, h₁']
      simp [h₂']
    | _ =>
      subst hrest
      simp only [Env.run] at h₁
      refine runs_of_map (fuel := f₁ + 1) ?_
      simp only [Env.run]
      rw [evalPanValueFfiProgSteps, h₁]
      simp

/-- The condition value, from the expression value. -/
theorem cond_eq (s : St σ) (c : Exp Word) :
    E.cond s c = match E.eval s c with
      | some (.word v) => some (v, panValueExpStepCost c)
      | _ => none := by
  simp only [Env.cond, Env.eval, panValueIteCondition, evalPanValueExpCounted]
  cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord c E.memoryAccess with
  | none => rfl
  | some v => cases v <;> rfl

theorem runs_ite {s : St σ} {c : Exp Word} {thenBranch elseBranch : Prog Word}
    {r : Result σ} :
    Runs E s (.ite c thenBranch elseBranch) r ↔
      match E.eval s c with
      | some (.word v) => if v = 0 then Runs E s elseBranch r else Runs E s thenBranch r
      | _ => r = s.err := by
  have hc := cond_eq (E := E) s c
  simp only [Env.cond] at hc
  constructor
  · rintro ⟨fuel, n, h⟩
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
    | succ fuel =>
      simp only [Env.run] at h
      rw [evalPanValueFfiProgSteps, hc] at h
      split
      · rename_i v hv
        rw [hv] at h
        simp only [Option.elim_some] at h
        by_cases hz : v = 0
        · rw [if_pos hz]
          subst hz
          simp only [bne_self_eq_false, Bool.false_eq_true, if_false] at h
          obtain ⟨⟨r', n'⟩, h', hr⟩ := Option.bind_eq_some_iff.mp h
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hr
          exact ⟨fuel, n', by rw [← hr.1]; exact h'⟩
        · rw [if_neg hz]
          have hne : (v != 0) = true := by simpa using hz
          simp only [hne, if_true] at h
          obtain ⟨⟨r', n'⟩, h', hr⟩ := Option.bind_eq_some_iff.mp h
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hr
          exact ⟨fuel, n', by rw [← hr.1]; exact h'⟩
      · rename_i hv
        have : (match E.eval s c with
            | some (.word v) => some (v, panValueExpStepCost c)
            | _ => (none : Option (Word × Nat))) = none := by
          split
          · rename_i v hv'
            exact absurd hv' (hv v)
          · rfl
        rw [this] at h
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at h
        exact h.1.symm
  · intro h
    split at h
    · rename_i v hv
      rw [hv] at hc
      by_cases hz : v = 0
      · rw [if_pos hz] at h
        subst hz
        obtain ⟨fuel, n, hrun⟩ := h
        simp only [Env.run] at hrun
        refine runs_of_map (fuel := fuel + 1) ?_
        simp only [Env.run]
        rw [evalPanValueFfiProgSteps, hc]
        simp [hrun]
      · rw [if_neg hz] at h
        obtain ⟨fuel, n, hrun⟩ := h
        simp only [Env.run] at hrun
        refine runs_of_map (fuel := fuel + 1) ?_
        simp only [Env.run]
        rw [evalPanValueFfiProgSteps, hc]
        have hz' : ¬ v = 0#64 := hz
        simp [hrun, hz']
    · rename_i hv
      subst h
      have : (match E.eval s c with
          | some (.word v) => some (v, panValueExpStepCost c)
          | _ => (none : Option (Word × Nat))) = none := by
        split
        · rename_i v hv'
          exact absurd hv' (hv v)
        · rfl
      rw [this] at hc
      refine runs_of_map (fuel := 1) ?_
      simp only [Env.run]
      rw [evalPanValueFfiProgSteps, hc]
      simp [St.err]

theorem runs_return {s : St σ} {e : Exp Word} {r : Result σ} :
    Runs E s (.return e) r ↔
      r = match E.eval s e with
        | some v =>
            if panValuePayloadWithinLimit E.structs v then
              .returned (fun _ => none) s.globals s.memory s.ffi [v]
            else s.err
        | none => s.err := by
  have hrun : ∀ fuel, (E.run (fuel + 1) s (.return e)).map Prod.fst = some
      (match E.eval s e with
        | some v =>
            if panValuePayloadWithinLimit E.structs v then
              .returned (fun _ => none) s.globals s.memory s.ffi [v]
            else s.err
        | none => s.err) := by
    intro fuel
    simp only [Env.run]
    rw [evalPanValueFfiProgSteps]
    simp only [panValueReturnResult, evalPanValueExpCounted, Env.eval, St.err]
    cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord e E.memoryAccess with
    | none => simp
    | some v =>
      simp only [Option.map_some]
      split <;> simp
  constructor
  · rintro ⟨fuel, n, h⟩
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
    | succ fuel =>
      have := hrun fuel
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact this
  · rintro rfl
    exact runs_of_map (hrun 0)

theorem runs_assign_local {s : St σ} {x : VarName} {e : Exp Word} {r : Result σ} :
    Runs E s (.assign .local x e) r ↔
      r = match E.eval s e with
        | some v =>
            if panValueAssignmentValid E.structs s.locals s.globals .local x v then
              .normal (updatePanValueMap s.locals x v) s.globals s.memory s.ffi
            else s.err
        | none => s.err := by
  have hrun : ∀ fuel, (E.run (fuel + 1) s (.assign .local x e)).map Prod.fst = some
      (match E.eval s e with
        | some v =>
            if panValueAssignmentValid E.structs s.locals s.globals .local x v then
              .normal (updatePanValueMap s.locals x v) s.globals s.memory s.ffi
            else s.err
        | none => s.err) := by
    intro fuel
    simp only [Env.run]
    rw [evalPanValueFfiProgSteps]
    simp only [panValueAssignLocalResult, evalPanValueExpCounted, Env.eval, St.err]
    cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord e E.memoryAccess with
    | none => simp
    | some v =>
      simp only [Option.map_some]
      split <;> simp
  constructor
  · rintro ⟨fuel, n, h⟩
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
    | succ fuel =>
      have := hrun fuel
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact this
  · rintro rfl
    exact runs_of_map (hrun 0)

theorem runs_dec {s : St σ} {x : VarName} {shape : Shape} {e : Exp Word} {body : Prog Word}
    {r : Result σ} :
    Runs E s (.dec x shape e body) r ↔
      match E.eval s e with
      | some v =>
          if panShapeMatches (panValueShape E.structs v) shape then
            ∃ rb, Runs E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body rb ∧
              r = restorePanValueFfiLocal x (s.locals x) rb
          else r = s.err
      | none => r = s.err := by
  have hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
      s.locals s.globals s.memory e E.memoryAccess shape =
        match E.eval s e with
        | some v =>
            if panShapeMatches (panValueShape E.structs v) shape then
              some (v, panValueExpStepCost e)
            else none
        | none => none := by
    simp only [panValueDecAccepted, evalPanValueExpCounted, Env.eval]
    cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord e E.memoryAccess with
    | none => rfl
    | some v => rfl
  constructor
  · rintro ⟨fuel, n, h⟩
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
    | succ fuel =>
      simp only [Env.run] at h
      rw [evalPanValueFfiProgSteps, hacc] at h
      cases hv : E.eval s e with
      | none =>
        rw [hv] at h
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at h
        exact h.1.symm
      | some v =>
        rw [hv] at h
        simp only at h ⊢
        by_cases hm : panShapeMatches (panValueShape E.structs v) shape = true
        · rw [if_pos hm] at h ⊢
          simp only [Option.elim_some] at h
          obtain ⟨⟨rb, nb⟩, hb, hr⟩ := Option.bind_eq_some_iff.mp h
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hr
          exact ⟨rb, ⟨fuel, nb, hb⟩, hr.1.symm⟩
        · rw [if_neg hm] at h ⊢
          simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at h
          exact h.1.symm
  · intro h
    cases hv : E.eval s e with
    | none =>
      rw [hv] at h hacc
      simp only at h
      subst h
      refine runs_of_map (fuel := 1) ?_
      simp only [Env.run]
      rw [evalPanValueFfiProgSteps, hacc]
      simp [St.err]
    | some v =>
      rw [hv] at h hacc
      simp only at h hacc
      by_cases hm : panShapeMatches (panValueShape E.structs v) shape = true
      · rw [if_pos hm] at h hacc
        obtain ⟨rb, ⟨fuel, nb, hb⟩, rfl⟩ := h
        simp only [Env.run] at hb
        refine runs_of_map (fuel := fuel + 1) ?_
        simp only [Env.run]
        rw [evalPanValueFfiProgSteps, hacc]
        simp [hb]
      · rw [if_neg hm] at h hacc
        subst h
        refine runs_of_map (fuel := 1) ?_
        simp only [Env.run]
        rw [evalPanValueFfiProgSteps, hacc]
        simp [St.err]

end InitECandidate.Solver.GuestBound
