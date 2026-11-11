import InitECandidate.Solver.GuestBound.Keeper

/-!
# Two keepers

`quietKeeper`: globals, memory and FFI state are unchanged (read-only code).
`globalKeeper g`: the global `g` is unchanged.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type}

/-- Leaves that change only locals. -/
def quietLeaf : Prog Word → Bool
  | .skip | .tick | .annot _ _ | .break | .continue | .return _ | .raise _ _
  | .assign .local _ _ | .primitive _ _ _ => true
  | _ => false

set_option hygiene false in
local macro "keeper_leaf" helper:ident finish:tacticSeq : tactic => `(tactic| (
  rw [evalPanValueFfiProgSteps] at hrun
  simp only [$helper:ident] at hrun
  repeat' split at hrun
  all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
  all_goals (obtain ⟨rfl, -⟩ := hrun)
  all_goals ($finish)))

set_option hygiene false in
local macro "keeper_same" finish:tacticSeq : tactic => `(tactic| (
  simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  ($finish)))

/-- Globals, memory and FFI state are unchanged. -/
def quietKeeper (E : Env σ) : Keeper E where
  rel s s' := s'.globals = s.globals ∧ s'.memory = s.memory ∧ s'.ffi = s.ffi
  refl _ := ⟨rfl, rfl, rfl⟩
  trans h₁ h₂ := ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩
  right_locals _ h := h
  left_locals _ h := h
  allow := quietLeaf
  leaf := by
    intro fuel p s r n hallow hrun
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
    | succ fuel =>
      simp only [Env.run] at hrun
      cases p with
      | skip =>
        simp only [evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact ⟨rfl, rfl, rfl⟩
      | tick => keeper_same (exact ⟨rfl, rfl, rfl⟩)
      | annot key text => keeper_same (exact ⟨rfl, rfl, rfl⟩)
      | «break» => keeper_same (exact ⟨rfl, rfl, rfl⟩)
      | «continue» => keeper_same (exact ⟨rfl, rfl, rfl⟩)
      | «return» value => keeper_leaf panValueReturnResult (exact ⟨rfl, rfl, rfl⟩)
      | raise exception value => keeper_leaf panValueRaiseResult (exact ⟨rfl, rfl, rfl⟩)
      | primitive name operator arguments =>
        keeper_leaf panValuePrimitiveResult (exact ⟨rfl, rfl, rfl⟩)
      | assign kind name value =>
        cases kind with
        | global => simp [quietLeaf] at hallow
        | «local» => keeper_leaf panValueAssignLocalResult (exact ⟨rfl, rfl, rfl⟩)
      | _ => simp [quietLeaf] at hallow

/-- Leaves that do not write the global `g`. -/
def globalLeaf (g : VarName) : Prog Word → Bool
  | .assign .global name _ => name != g
  | .shMemLoad _ .global name _ => name != g
  | .skip | .tick | .annot _ _ | .break | .continue | .return _ | .raise _ _
  | .assign .local _ _ | .primitive _ _ _ | .store _ _ | .store32 _ _ | .storeByte _ _
  | .shMemStore _ _ _ | .shMemLoad _ .local _ _ | .extCall _ _ _ _ _ => true
  | _ => false

/-- The global `g` is unchanged. -/
def globalKeeper (E : Env σ) (g : VarName) : Keeper E where
  rel s s' := s'.globals g = s.globals g
  refl _ := rfl
  trans h₁ h₂ := h₂.trans h₁
  right_locals _ h := h
  left_locals _ h := h
  allow := globalLeaf g
  leaf := by
    intro fuel p s r n hallow hrun
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
    | succ fuel =>
      simp only [Env.run] at hrun
      cases p with
      | skip =>
        simp only [evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rfl
      | tick => keeper_same rfl
      | annot key text => keeper_same rfl
      | «break» => keeper_same rfl
      | «continue» => keeper_same rfl
      | «return» value => keeper_leaf panValueReturnResult rfl
      | raise exception value => keeper_leaf panValueRaiseResult rfl
      | primitive name operator arguments => keeper_leaf panValuePrimitiveResult rfl
      | store address value => keeper_leaf panValueStoreResult rfl
      | store32 address value => keeper_leaf panValueStore32Result rfl
      | storeByte address value => keeper_leaf panValueStoreByteResult rfl
      | shMemStore size address value => keeper_leaf panValueShMemStoreResult rfl
      | assign kind name value =>
        cases kind with
        | «local» => keeper_leaf panValueAssignLocalResult rfl
        | global =>
          have hne : (g == name) = false := by
            simp only [globalLeaf, bne_iff_ne, ne_eq] at hallow
            simp only [beq_eq_false_iff_ne, ne_eq]
            exact fun h => hallow h.symm
          keeper_leaf panValueAssignGlobalResult
            (first | rfl | (show updatePanValueMap _ _ _ g = _; simp [updatePanValueMap, hne]))
      | shMemLoad size kind name address =>
        cases kind with
        | «local» => keeper_leaf panValueShMemLoadResult rfl
        | global =>
          have hne : (g == name) = false := by
            simp only [globalLeaf, bne_iff_ne, ne_eq] at hallow
            simp only [beq_eq_false_iff_ne, ne_eq]
            exact fun h => hallow h.symm
          keeper_leaf panValueShMemLoadResult
            (first | rfl | (show updatePanValueMap _ _ _ g = _; simp [updatePanValueMap, hne]))
      | extCall function configuration configurationLength array arrayLength =>
        rw [evalPanValueFfiProgSteps] at hrun
        simp only [panValueFfiExtCallSteps] at hrun
        repeat' split at hrun
        all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq, Option.pure_def,
          Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun))
        all_goals first
          | (obtain ⟨rfl, -⟩ := hrun; rfl)
          | (obtain ⟨_, _, rfl, -⟩ := hrun; rfl)
      | _ => simp [globalLeaf] at hallow

/-- Leaves that write no global. -/
def globalsLeaf : Prog Word → Bool
  | .skip | .tick | .annot _ _ | .break | .continue | .return _ | .raise _ _
  | .assign .local _ _ | .primitive _ _ _ | .store _ _ | .store32 _ _ | .storeByte _ _
  | .shMemStore _ _ _ | .shMemLoad _ .local _ _ | .extCall _ _ _ _ _ => true
  | _ => false

/-- All globals are unchanged. -/
def globalsKeeper (E : Env σ) : Keeper E where
  rel s s' := s'.globals = s.globals
  refl _ := rfl
  trans h₁ h₂ := h₂.trans h₁
  right_locals _ h := h
  left_locals _ h := h
  allow := globalsLeaf
  leaf := by
    intro fuel p s r n hallow hrun
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
    | succ fuel =>
      simp only [Env.run] at hrun
      cases p with
      | skip =>
        simp only [evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rfl
      | tick => keeper_same rfl
      | annot key text => keeper_same rfl
      | «break» => keeper_same rfl
      | «continue» => keeper_same rfl
      | «return» value => keeper_leaf panValueReturnResult rfl
      | raise exception value => keeper_leaf panValueRaiseResult rfl
      | primitive name operator arguments => keeper_leaf panValuePrimitiveResult rfl
      | store address value => keeper_leaf panValueStoreResult rfl
      | store32 address value => keeper_leaf panValueStore32Result rfl
      | storeByte address value => keeper_leaf panValueStoreByteResult rfl
      | shMemStore size address value => keeper_leaf panValueShMemStoreResult rfl
      | assign kind name value =>
        cases kind with
        | «local» => keeper_leaf panValueAssignLocalResult rfl
        | global => simp [globalsLeaf] at hallow
      | shMemLoad size kind name address =>
        cases kind with
        | «local» => keeper_leaf panValueShMemLoadResult rfl
        | global => simp [globalsLeaf] at hallow
      | extCall function configuration configurationLength array arrayLength =>
        rw [evalPanValueFfiProgSteps] at hrun
        simp only [panValueFfiExtCallSteps] at hrun
        repeat' split at hrun
        all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq, Option.pure_def,
          Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun))
        all_goals first
          | (obtain ⟨rfl, -⟩ := hrun; rfl)
          | (obtain ⟨_, _, rfl, -⟩ := hrun; rfl)
      | _ => simp [globalsLeaf] at hallow

end InitECandidate.Solver.GuestBound
