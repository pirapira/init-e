import InitECandidate.Solver.GuestBound.WordExp

/-!
# Frame analysis for several walked locals

`walkOkM M` accepts statements that assign only locals in `M`, and only word
expressions or each other's values. The values of `M` then stay within words
and the values `M` had at entry, which is what bounds the number of distinct
loop-head states.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The value is a word. -/
def IsWordVal (v : Option (PanValue Word)) : Prop := ∃ w, v = some (.word w)

/-- A right-hand side that is a word expression or one of the tracked locals. -/
def walkRhs (M : List VarName) (value : Exp Word) : Bool :=
  wordExp value ||
    match value with
    | .var .local y => M.contains y
    | _ => false

/-- Statements that change nothing but the locals in `M`, assigning them only
word expressions or each other. -/
def walkOkM (M : List VarName) : Prog Word → Bool
  | .skip | .tick | .annot _ _ | .break | .continue | .return _ | .raise _ _ => true
  | .assign .local name value => M.contains name && walkRhs M value
  | .seq first second => walkOkM M first && walkOkM M second
  | .ite _ thenBranch elseBranch => walkOkM M thenBranch && walkOkM M elseBranch
  | .dec name _ _ body => !M.contains name && walkOkM M body
  | _ => false

/-- On exits that keep running, everything outside `M` is as in `s`, and each
local in `M` holds a word or the value some local in `M` had in `s`. -/
def WalkM (M : List VarName) (s : St σ) : Result σ → Prop
  | .normal l g mem f | .continued l g mem f | .broke l g mem f =>
      g = s.globals ∧ mem = s.memory ∧ f = s.ffi ∧ (∀ x, x ∉ M → l x = s.locals x) ∧
        (∀ x, x ∈ M → IsWordVal (l x) ∨ ∃ y, y ∈ M ∧ l x = s.locals y)
  | _ => True

theorem WalkM.same (M : List VarName) (s : St σ) :
    (∀ x, x ∉ M → s.locals x = s.locals x) ∧
      (∀ x, x ∈ M → IsWordVal (s.locals x) ∨ ∃ y, y ∈ M ∧ s.locals x = s.locals y) :=
  ⟨fun _ _ => rfl, fun x hx => Or.inr ⟨x, hx, rfl⟩⟩

theorem WalkM.trans {M : List VarName} {s : St σ} {l g : VarName → Option (PanValue Word)}
    {mem : Word → Option (PanValue Word)} {f : FfiState σ} {r : Result σ}
    (h₁ : WalkM M s (.normal l g mem f : Result σ)) (h₂ : WalkM M ⟨l, g, mem, f⟩ r) :
    WalkM M s r := by
  obtain ⟨hg, hm, hf, hl, hv⟩ := h₁
  cases r <;> simp only [WalkM] at h₂ ⊢
  all_goals
    obtain ⟨hg', hm', hf', hl', hv'⟩ := h₂
    refine ⟨hg'.trans hg, hm'.trans hm, hf'.trans hf, fun x hx => (hl' x hx).trans (hl x hx), ?_⟩
    intro x hx
    rcases hv' x hx with hw | ⟨y, hy, hxy⟩
    · exact Or.inl hw
    · rcases hv y hy with hw | ⟨z, hz, hyz⟩
      · exact Or.inl (hxy ▸ hw)
      · exact Or.inr ⟨z, hz, hxy.trans hyz⟩

theorem WalkM.restore {M : List VarName} {name : VarName} {s : St σ} {value : PanValue Word}
    {r : Result σ} (hne : (!M.contains name) = true)
    (h : WalkM M ⟨updatePanValueMap s.locals name value, s.globals, s.memory, s.ffi⟩ r) :
    WalkM M s (restorePanValueFfiLocal name (s.locals name) r) := by
  have hnot : name ∉ M := by simpa using hne
  cases r <;> simp only [WalkM, restorePanValueFfiLocal] at h ⊢
  all_goals
    obtain ⟨hg, hm, hf, hl, hv⟩ := h
    refine ⟨hg, hm, hf, ?_, ?_⟩
    · intro x hx
      by_cases hxn : x = name
      · subst hxn
        simp [restorePanValueLocal]
      · have hxn' : (x == name) = false := by simpa using hxn
        simp only [restorePanValueLocal, hxn']
        rw [hl x hx]
        simp [updatePanValueMap, hxn']
    · intro x hx
      have hxn : (x == name) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        exact fun h => hnot (h ▸ hx)
      simp only [restorePanValueLocal, hxn]
      rcases hv x hx with hw | ⟨y, hy, hxy⟩
      · exact Or.inl hw
      · have hyn : (y == name) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun h => hnot (h ▸ hy)
        refine Or.inr ⟨y, hy, ?_⟩
        rw [hxy]
        simp [updatePanValueMap, hyn]

set_option hygiene false in
/-- Finish a leaf whose keep-running results leave the state alone. -/
local macro "walk_same" : tactic => `(tactic| (
  simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun x hx => Or.inr ⟨x, hx, rfl⟩⟩))

/-- `walkOkM` statements leave everything outside `M` alone and keep `M` within words and entry values. -/
theorem walkM_sound (hE : WordEnv E) (M : List VarName) :
    ∀ (fuel : Nat) (p : Prog Word) (s : St σ) (r : Result σ) (n : Nat),
      walkOkM M p = true → E.run fuel s p = some (r, n) → WalkM M s r := by
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
      exact ⟨rfl, rfl, rfl, fun _ _ => rfl, fun x hx => Or.inr ⟨x, hx, rfl⟩⟩
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
      all_goals (simp only [WalkM])
    | raise exception value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueRaiseResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [WalkM])
    | assign kind name value =>
      cases kind with
      | global => simp [walkOkM] at hs
      | «local» =>
        simp only [walkOkM, Bool.and_eq_true] at hs
        obtain ⟨hname, hrhs⟩ := hs
        have hmem : name ∈ M := by simpa using hname
        rw [evalPanValueFfiProgSteps] at hrun
        simp only [panValueAssignLocalResult, evalPanValueExpCounted] at hrun
        cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
            E.topAddress E.bytesInWord value E.memoryAccess with
        | none =>
          rw [hv] at hrun
          simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [WalkM]
        | some evaluated =>
          rw [hv] at hrun
          simp only [Option.map_some] at hrun
          split at hrun
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            refine ⟨rfl, rfl, rfl, ?_, ?_⟩
            · intro x hx
              have hx' : (x == name) = false := by
                simp only [beq_eq_false_iff_ne, ne_eq]
                exact fun h => hx (h ▸ hmem)
              simp [updatePanValueMap, hx']
            · intro x hx
              by_cases hxn : x = name
              · subst hxn
                simp only [updatePanValueMap, beq_self_eq_true, if_true]
                simp only [walkRhs, Bool.or_eq_true] at hrhs
                rcases hrhs with hw | hvar
                · obtain ⟨w, rfl⟩ := wordExp_eval hE hw hv
                  exact Or.inl ⟨w, rfl⟩
                · split at hvar
                  · rename_i y
                    simp only [evalPanValueExp] at hv
                    exact Or.inr ⟨y, by simpa using hvar, hv.symm⟩
                  · cases hvar
              · have hxn' : (x == name) = false := by simpa using hxn
                refine Or.inr ⟨x, hx, ?_⟩
                simp [updatePanValueMap, hxn']
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            simp only [WalkM]
    | seq first second =>
      simp only [walkOkM, Bool.and_eq_true] at hs
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
            exact WalkM.trans p₁ (ih second ⟨l, g, m, f⟩ r₂ n₂ hs.2 h₂)
        | _ =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact p₁
    | ite condition thenBranch elseBranch =>
      simp only [walkOkM, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [WalkM]
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
      simp only [walkOkM, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory value E.memoryAccess shape with
      | none =>
        rw [hacc] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [WalkM]
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
          exact WalkM.restore hs.1 (ih body ⟨updatePanValueMap s.locals name accepted.1,
            s.globals, s.memory, s.ffi⟩ rb nb hs.2 hb)
    | _ => simp [walkOkM] at hs

end InitECandidate.Solver.GuestBound
