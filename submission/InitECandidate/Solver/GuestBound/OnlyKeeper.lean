import InitECandidate.Solver.GuestBound.MemKeep

/-!
# Functions that assign only some globals

`onlyKeeper E G` relates states whose globals agree outside the list `G`.
Its checker accepts stores and assignments to globals named in `G`, so
`only_sound` gives, for example, "`htab_set` changes no global other than
`heap_ptr`" by `decide`. This is the globals half of the frame of a
world-state operation; the memory half comes from the operation's own
specification.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type}

set_option hygiene false in
local macro "only_leaf" helper:ident finish:tacticSeq : tactic => `(tactic| (
  rw [evalPanValueFfiProgSteps] at hrun
  simp only [$helper:ident] at hrun
  repeat' split at hrun
  all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
  all_goals (obtain ⟨rfl, -⟩ := hrun)
  all_goals ($finish)))

set_option hygiene false in
local macro "only_same" finish:tacticSeq : tactic => `(tactic| (
  simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  ($finish)))

/-- Leaves that assign no global outside `G`. -/
def onlyLeaf (G : List VarName) : Prog Word → Bool
  | .assign .global name _ => G.contains name
  | .shMemLoad _ .global name _ => G.contains name
  | .skip | .tick | .annot _ _ | .break | .continue | .return _ | .raise _ _
  | .assign .local _ _ | .primitive _ _ _ | .store _ _ | .store32 _ _ | .storeByte _ _
  | .shMemStore _ _ _ | .shMemLoad _ .local _ _ | .extCall _ _ _ _ _ => true
  | _ => false

/-- The globals outside `G` are unchanged. -/
def onlyKeeper (E : Env σ) (G : List VarName) : Keeper E where
  rel s s' := ∀ x, G.contains x = false → s'.globals x = s.globals x
  refl _ := fun _ _ => rfl
  trans h₁ h₂ := fun x hx => (h₂ x hx).trans (h₁ x hx)
  right_locals _ h := h
  left_locals _ h := h
  allow := onlyLeaf G
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
        exact fun _ _ => rfl
      | tick => only_same (exact fun _ _ => rfl)
      | annot key text => only_same (exact fun _ _ => rfl)
      | «break» => only_same (exact fun _ _ => rfl)
      | «continue» => only_same (exact fun _ _ => rfl)
      | «return» value => only_leaf panValueReturnResult (exact fun _ _ => rfl)
      | raise exception value => only_leaf panValueRaiseResult (exact fun _ _ => rfl)
      | primitive name operator arguments =>
        only_leaf panValuePrimitiveResult (exact fun _ _ => rfl)
      | store address value => only_leaf panValueStoreResult (exact fun _ _ => rfl)
      | store32 address value => only_leaf panValueStore32Result (exact fun _ _ => rfl)
      | storeByte address value => only_leaf panValueStoreByteResult (exact fun _ _ => rfl)
      | shMemStore size address value => only_leaf panValueShMemStoreResult (exact fun _ _ => rfl)
      | assign kind name value =>
        cases kind with
        | «local» => only_leaf panValueAssignLocalResult (exact fun _ _ => rfl)
        | global =>
          have hin : G.contains name = true := by simpa only [onlyLeaf] using hallow
          have hne : ∀ x, G.contains x = false → (x == name) = false := by
            intro x hx
            simp only [beq_eq_false_iff_ne, ne_eq]
            rintro rfl
            rw [hin] at hx
            cases hx
          only_leaf panValueAssignGlobalResult
            (first
              | exact fun _ _ => rfl
              | (intro x hx; show updatePanValueMap _ _ _ x = _
                 simp [updatePanValueMap, hne x hx]))
      | shMemLoad size kind name address =>
        cases kind with
        | «local» => only_leaf panValueShMemLoadResult (exact fun _ _ => rfl)
        | global =>
          have hin : G.contains name = true := by simpa only [onlyLeaf] using hallow
          have hne : ∀ x, G.contains x = false → (x == name) = false := by
            intro x hx
            simp only [beq_eq_false_iff_ne, ne_eq]
            rintro rfl
            rw [hin] at hx
            cases hx
          only_leaf panValueShMemLoadResult
            (first
              | exact fun _ _ => rfl
              | (intro x hx; show updatePanValueMap _ _ _ x = _
                 simp [updatePanValueMap, hne x hx]))
      | extCall function configuration configurationLength array arrayLength =>
        rw [evalPanValueFfiProgSteps] at hrun
        simp only [panValueFfiExtCallSteps] at hrun
        repeat' split at hrun
        all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq, Option.pure_def,
          Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun))
        all_goals first
          | (obtain ⟨rfl, -⟩ := hrun; exact fun _ _ => rfl)
          | (obtain ⟨_, _, rfl, -⟩ := hrun; exact fun _ _ => rfl)
      | _ => simp [onlyLeaf] at hallow

variable {E : Env σ}

/-- A function accepted by the check changes no global outside `G`. -/
theorem only_sound (hE : GuestEnv E) (G : List VarName) (depth : Nat) (f : FunName)
    (h : keepFn (onlyLeaf G) Guest.Software.guestAst depth f = true) :
    FunKeeps (onlyKeeper E G) f :=
  keepFn_sound (onlyKeeper E G) hE.functions depth f h

/-- The hash-table operations change no global other than `heap_ptr`. -/
theorem htab_set_only (hE : GuestEnv E) : FunKeeps (onlyKeeper E ["heap_ptr"]) "htab_set" :=
  only_sound hE ["heap_ptr"] 6 "htab_set" (by decide +kernel)

theorem htab_del_only (hE : GuestEnv E) : FunKeeps (onlyKeeper E ["heap_ptr"]) "htab_del" :=
  only_sound hE ["heap_ptr"] 6 "htab_del" (by decide +kernel)

end InitECandidate.Solver.GuestBound
