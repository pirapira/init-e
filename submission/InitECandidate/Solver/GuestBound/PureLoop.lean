import InitECandidate.Solver.GuestBound.Orbit
import InitECandidate.Solver.GuestBound.OffsetLoopBound

/-!
# Pure counter loops

A loop body that changes nothing except one local `i`, by `i = i + k`
(no stores, no assignments to other variables, no calls). The loop-head state
is then a function of the iteration number with period `2^64`, so
`orbit_bound` applies whatever the guard is. This covers `memeq`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Statements that change nothing but the local `i`, and that only by `i = i + k`. -/
def frameOk (k : Word) (i : VarName) : Prog Word → Bool
  | .skip | .tick | .annot _ _ | .break | .continue | .return _ | .raise _ _ => true
  | .assign .local name value => name == i && isStep (.upBy k) i value
  | .seq first second => frameOk k i first && frameOk k i second
  | .ite _ thenBranch elseBranch => frameOk k i thenBranch && frameOk k i elseBranch
  | .dec name _ _ body => name != i && frameOk k i body
  | _ => false

/-- On exits that keep running, everything but `i` is as in `s`, and `i` is
unchanged unless it was a word. -/
def Frame (i : VarName) (s : St σ) : Result σ → Prop
  | .normal l g mem f | .continued l g mem f | .broke l g mem f =>
      g = s.globals ∧ mem = s.memory ∧ f = s.ffi ∧ (∀ x, x ≠ i → l x = s.locals x) ∧
        (l i = s.locals i ∨ ∃ w, s.locals i = some (.word w))
  | _ => True

theorem Frame.refl (i : VarName) (s : St σ) :
    (∀ x, x ≠ i → s.locals x = s.locals x) ∧
      (s.locals i = s.locals i ∨ ∃ w, s.locals i = some (.word w)) :=
  ⟨fun _ _ => rfl, Or.inl rfl⟩

theorem Frame.trans {i : VarName} {s : St σ} {l g : VarName → Option (PanValue Word)}
    {mem : Word → Option (PanValue Word)} {f : FfiState σ} {r : Result σ}
    (h₁ : Frame i s (.normal l g mem f : Result σ)) (h₂ : Frame i ⟨l, g, mem, f⟩ r) :
    Frame i s r := by
  obtain ⟨hg, hm, hf, hl, hi⟩ := h₁
  cases r <;> simp only [Frame] at h₂ ⊢
  all_goals
    obtain ⟨hg', hm', hf', hl', hi'⟩ := h₂
    refine ⟨hg'.trans hg, hm'.trans hm, hf'.trans hf, fun x hx => (hl' x hx).trans (hl x hx), ?_⟩
    rcases hi' with h | ⟨w, hw⟩
    · rcases hi with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr h'
    · rcases hi with h' | h'
      · exact Or.inr ⟨w, h' ▸ hw⟩
      · exact Or.inr h'

theorem Frame.restore {i name : VarName} {s : St σ} {value : PanValue Word} {r : Result σ}
    (hne : (name != i) = true)
    (h : Frame i ⟨updatePanValueMap s.locals name value, s.globals, s.memory, s.ffi⟩ r) :
    Frame i s (restorePanValueFfiLocal name (s.locals name) r) := by
  have hni : name ≠ i := by simpa using hne
  have hin : (i == name) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact fun h => hni h.symm
  cases r <;> simp only [Frame, restorePanValueFfiLocal] at h ⊢
  all_goals
    obtain ⟨hg, hm, hf, hl, hi⟩ := h
    refine ⟨hg, hm, hf, ?_, ?_⟩
    · intro x hx
      by_cases hxn : x = name
      · subst hxn
        simp [restorePanValueLocal]
      · have hxn' : (x == name) = false := by simpa using hxn
        simp only [restorePanValueLocal, hxn']
        rw [hl x hx]
        simp [updatePanValueMap, hxn']
    · simp only [restorePanValueLocal, hin, updatePanValueMap] at hi ⊢
      exact hi

set_option hygiene false in
/-- Finish a leaf whose keep-running results leave the state alone. -/
local macro "frame_same" : tactic => `(tactic| (
  simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  exact ⟨rfl, rfl, rfl, fun _ _ => rfl, Or.inl rfl⟩))

/-- `frameOk` statements leave everything but `i` alone. -/
theorem frame_sound (hE : WordEnv E) (k : Word) (i : VarName) :
    ∀ (fuel : Nat) (p : Prog Word) (s : St σ) (r : Result σ) (n : Nat),
      frameOk k i p = true → E.run fuel s p = some (r, n) → Frame i s r := by
  intro fuel
  induction fuel with
  | zero =>
    intro p s r n _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro p s r n hs hrun
    simp only [Env.run] at hrun
    cases p with
    | skip =>
      simp only [evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact ⟨rfl, rfl, rfl, fun _ _ => rfl, Or.inl rfl⟩
    | tick => frame_same
    | annot key text => frame_same
    | «break» => frame_same
    | «continue» => frame_same
    | «return» value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueReturnResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [Frame])
    | raise exception value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueRaiseResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [Frame])
    | assign kind name value =>
      cases kind with
      | global => simp [frameOk] at hs
      | «local» =>
        simp only [frameOk, Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨rfl, hstep⟩ := hs
        rw [evalPanValueFfiProgSteps] at hrun
        simp only [panValueAssignLocalResult, evalPanValueExpCounted] at hrun
        cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
            E.topAddress E.bytesInWord value E.memoryAccess with
        | none =>
          rw [hv] at hrun
          simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [Frame]
        | some evaluated =>
          rw [hv] at hrun
          simp only [Option.map_some] at hrun
          split at hrun
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            refine ⟨rfl, rfl, rfl, ?_, ?_⟩
            · intro x hx
              have hx' : (x == name) = false := by simpa using hx
              simp [updatePanValueMap, hx']
            · right
              unfold isStep at hstep
              split at hstep
              · rename_i name' k'
                simp only [Bool.and_eq_true, beq_iff_eq] at hstep
                obtain ⟨rfl, -⟩ := hstep
                obtain ⟨w, hw, -⟩ := add_eval hE hv
                exact ⟨w, hw⟩
              · simp at hstep
              · cases hstep
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            simp only [Frame]
    | seq first second =>
      simp only [frameOk, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases h₁ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi first (memoryAccess := E.memoryAccess) (contracts := E.contracts)
          (memoryHandler := E.memoryHandler) with
      | none => rw [h₁] at hrun; simp at hrun
      | some pair =>
        obtain ⟨r₁, n₁⟩ := pair
        rw [h₁] at hrun
        have p₁ := ih first s r₁ n₁ hs.1 h₁
        cases r₁ with
        | normal l g m f =>
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases h₂ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f second
              (memoryAccess := E.memoryAccess) (contracts := E.contracts)
              (memoryHandler := E.memoryHandler) with
          | none => rw [h₂] at hrun; simp at hrun
          | some pair₂ =>
            obtain ⟨r₂, n₂⟩ := pair₂
            rw [h₂] at hrun
            simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact Frame.trans p₁ (ih second ⟨l, g, m, f⟩ r₂ n₂ hs.2 h₂)
        | _ =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact p₁
    | ite condition thenBranch elseBranch =>
      simp only [frameOk, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [Frame]
      | some pair =>
        obtain ⟨c, kc⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hc : (c != 0) = true
        · rw [if_pos hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi thenBranch (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih thenBranch s rb nb hs.1 hb
        · rw [if_neg hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi elseBranch (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih elseBranch s rb nb hs.2 hb
    | dec name shape value body =>
      simp only [frameOk, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory value E.memoryAccess shape with
      | none =>
        rw [hacc] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [Frame]
      | some accepted =>
        rw [hacc] at hrun
        simp only [Option.elim_some] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel
            (updatePanValueMap s.locals name accepted.1) s.globals s.memory s.ffi body
            (memoryAccess := E.memoryAccess) (contracts := E.contracts)
            (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at hrun
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact Frame.restore hs.1 (ih body ⟨updatePanValueMap s.locals name accepted.1,
            s.globals, s.memory, s.ffi⟩ rb nb hs.2 hb)
    | _ => simp [frameOk] at hs

end InitECandidate.Solver.GuestBound
