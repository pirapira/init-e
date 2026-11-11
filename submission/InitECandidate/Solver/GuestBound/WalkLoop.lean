import Mathlib.Data.Fintype.Card
import InitECandidate.Solver.GuestBound.PureLoopBound

/-!
# Walk loops

A loop body that changes nothing except one local `i`, by arbitrary
assignments (no stores, no other assignments, no calls), with a guard that
evaluates only when `i` is a word. The loop-head state is then determined by
the word in `i`, and a returning run cannot visit the same word twice, so it
takes at most `2^64` iterations. This covers pointer walks such as
`htab_find_leaf`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Statements that change nothing but the local `i` (by any assignment). -/
def walkOk (i : VarName) : Prog Word → Bool
  | .skip | .tick | .annot _ _ | .break | .continue | .return _ | .raise _ _ => true
  | .assign .local name _ => name == i
  | .seq first second => walkOk i first && walkOk i second
  | .ite _ thenBranch elseBranch => walkOk i thenBranch && walkOk i elseBranch
  | .dec name _ _ body => name != i && walkOk i body
  | _ => false

/-- On exits that keep running, everything but `i` is as in `s`. -/
def Walk (i : VarName) (s : St σ) : Result σ → Prop
  | .normal l g mem f | .continued l g mem f | .broke l g mem f =>
      g = s.globals ∧ mem = s.memory ∧ f = s.ffi ∧ (∀ x, x ≠ i → l x = s.locals x)
  | _ => True

theorem Walk.trans {i : VarName} {s : St σ} {l g : VarName → Option (PanValue Word)}
    {mem : Word → Option (PanValue Word)} {f : FfiState σ} {r : Result σ}
    (h₁ : Walk i s (.normal l g mem f : Result σ)) (h₂ : Walk i ⟨l, g, mem, f⟩ r) :
    Walk i s r := by
  obtain ⟨hg, hm, hf, hl⟩ := h₁
  cases r <;> simp only [Walk] at h₂ ⊢
  all_goals
    obtain ⟨hg', hm', hf', hl'⟩ := h₂
    exact ⟨hg'.trans hg, hm'.trans hm, hf'.trans hf, fun x hx => (hl' x hx).trans (hl x hx)⟩

theorem Walk.restore {i name : VarName} {s : St σ} {value : PanValue Word} {r : Result σ}
    (hne : (name != i) = true)
    (h : Walk i ⟨updatePanValueMap s.locals name value, s.globals, s.memory, s.ffi⟩ r) :
    Walk i s (restorePanValueFfiLocal name (s.locals name) r) := by
  have hni : name ≠ i := by simpa using hne
  cases r <;> simp only [Walk, restorePanValueFfiLocal] at h ⊢
  all_goals
    obtain ⟨hg, hm, hf, hl⟩ := h
    refine ⟨hg, hm, hf, ?_⟩
    intro x hx
    by_cases hxn : x = name
    · subst hxn
      simp [restorePanValueLocal]
    · have hxn' : (x == name) = false := by simpa using hxn
      simp only [restorePanValueLocal, hxn']
      rw [hl x hx]
      simp [updatePanValueMap, hxn']

set_option hygiene false in
/-- Finish a leaf whose keep-running results leave the state alone. -/
local macro "walk_same" : tactic => `(tactic| (
  simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩))

/-- `walkOk` statements leave everything but `i` alone. -/
theorem walk_sound (i : VarName) :
    ∀ (fuel : Nat) (p : Prog Word) (s : St σ) (r : Result σ) (n : Nat),
      walkOk i p = true → E.run fuel s p = some (r, n) → Walk i s r := by
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
      exact ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
    | tick => walk_same
    | annot key text => walk_same
    | «break» => walk_same
    | «continue» => walk_same
    | «return» value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueReturnResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [Walk])
    | raise exception value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueRaiseResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [Walk])
    | assign kind name value =>
      cases kind with
      | global => simp [walkOk] at hs
      | «local» =>
        simp only [walkOk, beq_iff_eq] at hs
        subst hs
        rw [evalPanValueFfiProgSteps] at hrun
        simp only [panValueAssignLocalResult, evalPanValueExpCounted] at hrun
        cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
            E.topAddress E.bytesInWord value E.memoryAccess with
        | none =>
          rw [hv] at hrun
          simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [Walk]
        | some evaluated =>
          rw [hv] at hrun
          simp only [Option.map_some] at hrun
          split at hrun
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            refine ⟨rfl, rfl, rfl, ?_⟩
            intro x hx
            have hx' : (x == name) = false := by simpa using hx
            simp [updatePanValueMap, hx']
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            simp only [Walk]
    | seq first second =>
      simp only [walkOk, Bool.and_eq_true] at hs
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
            exact Walk.trans p₁ (ih second ⟨l, g, m, f⟩ r₂ n₂ hs.2 h₂)
        | _ =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact p₁
    | ite condition thenBranch elseBranch =>
      simp only [walkOk, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [Walk]
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
      simp only [walkOk, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory value E.memoryAccess shape with
      | none =>
        rw [hacc] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [Walk]
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
          exact Walk.restore hs.1 (ih body ⟨updatePanValueMap s.locals name accepted.1,
            s.globals, s.memory, s.ffi⟩ rb nb hs.2 hb)
    | _ => simp [walkOk] at hs

end InitECandidate.Solver.GuestBound
