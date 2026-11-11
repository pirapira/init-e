import InitECandidate.Solver.GuestBound.RankedWalk
import InitECandidate.Solver.GuestBound.ScratchAlloc

/-!
# Composition rules for ranked walk steps

`StepOk M rank D p`: from any state in which the locals in `D` hold words,
every run of `p` that keeps the loop going has walked `M` or decreased the
rank. The rules below build this for a loop body from its statements.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The locals in `D` hold words. -/
def WordsAt (D : List VarName) (s : St σ) : Prop := ∀ y, y ∈ D → IsWordVal (s.locals y)

/-- Every run of `p` from a state with words in `D` satisfies `StepPost`. -/
def StepOk (E : Env σ) (M : List VarName) (rank : (VarName → Option (PanValue Word)) → Nat)
    (D : List VarName) (p : Prog Word) : Prop :=
  ∀ fuel (s : St σ) r n, WordsAt D s → E.run fuel s p = some (r, n) → StepPost M rank s r

variable {M D : List VarName} {rank : (VarName → Option (PanValue Word)) → Nat}

theorem StepPost.of_error {s : St σ} {r : Result σ} (h : r.isError = true) :
    StepPost M rank s r := by
  cases r <;> trivial

/-- Statements accepted by `walkOkM` walk `M`. -/
theorem StepOk.of_walk (hE : WordEnv E) (callee : FunName → Bool)
    (hcallee : ∀ f, callee f = true → FunKeeps (quietKeeper E) f) {p : Prog Word}
    (h : walkOkM callee M p = true) : StepOk E M rank D p := by
  intro fuel s r n _ hrun
  have hw := walkM_sound hE callee hcallee M fuel p s r n h hrun
  cases r <;> first | trivial | exact Or.inl hw

theorem StepOk.ite {c : Exp Word} {a b : Prog Word} (ha : StepOk E M rank D a)
    (hb : StepOk E M rank D b) : StepOk E M rank D (.ite c a b) := by
  intro fuel s r n hD hrun
  rcases ite_run_inv hrun with herr | ⟨fuel', v, n', -, hbranch⟩
  · exact StepPost.of_error herr
  · rcases hbranch with ⟨-, h⟩ | ⟨-, h⟩
    · exact ha fuel' s r n' hD h
    · exact hb fuel' s r n' hD h

theorem StepPost.restore {s : St σ} {x : VarName} {value : PanValue Word} {r : Result σ}
    (hx : (!M.contains x) = true)
    (h : StepPost M rank ⟨updatePanValueMap s.locals x value, s.globals, s.memory, s.ffi⟩ r) :
    StepPost M rank s (restorePanValueFfiLocal x (s.locals x) r) := by
  cases r with
  | normal l g m f =>
    rcases h with hw | hr
    · exact Or.inl (WalkM.restore (r := .normal l g m f) hx hw)
    · exact Or.inr hr
  | continued l g m f =>
    rcases h with hw | hr
    · exact Or.inl (WalkM.restore (r := .normal l g m f) hx hw)
    · exact Or.inr hr
  | _ => trivial

/-- A declared single-word local outside `M` may be used as a word in the body. -/
theorem StepOk.dec_word {x : VarName} {e : Exp Word} {body : Prog Word}
    (hx : (!M.contains x) = true) (h : StepOk E M rank (x :: D) body) :
    StepOk E M rank D (.dec x .one e body) := by
  intro fuel s r n hD hrun
  rcases dec_run_inv hrun with herr | ⟨fuel', v, rb, nb, -, hshape, hrun', rfl⟩
  · exact StepPost.of_error herr
  obtain ⟨w, rfl⟩ := word_of_shape_one hshape
  refine StepPost.restore hx (h fuel' _ rb nb ?_ hrun')
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    exact ⟨w, by simp [updatePanValueMap]⟩
  · have hy' : y ∈ D := by
      rcases List.mem_cons.mp hy with h | h
      · exact absurd h hyx
      · exact h
    have hyx' : (y == x) = false := by simpa using hyx
    show IsWordVal (updatePanValueMap s.locals x (PanValue.word w) y)
    simp only [updatePanValueMap, hyx']
    exact hD y hy'

/-- A declaring call to a read-only function, binding a local outside `M` and `D`. -/
theorem StepOk.decCall_quiet {x : VarName} {shape : Shape} {f : FunName}
    {arguments : List (Exp Word)} {body : Prog Word}
    (hf : FunKeeps (quietKeeper E) f) (hx : (!M.contains x) = true) (hxD : x ∉ D)
    (h : StepOk E M rank D body) : StepOk E M rank D (.decCall x shape f arguments body) := by
  intro fuel s r n hD hrun
  rcases decCall_run_inv hrun with herr | ⟨fuel₁, parameters, calleeBody, values, calleeLocals,
    rb, nb, hlookup, -, -, hcallee, hout⟩
  · exact StepPost.of_error herr
  have hq := hf parameters calleeBody hlookup fuel₁ _ rb nb hcallee
  cases rb with
  | returned l g m ffi values' =>
    obtain ⟨hg, hm, hffi⟩ := hq
    simp only [PanValueFfiControlResult.st] at hg hm hffi
    subst hg hm hffi
    cases values' with
    | nil => exact hout.elim
    | cons value rest =>
      cases rest with
      | cons value' rest' => exact hout.elim
      | nil =>
        obtain ⟨fuel₂, r', n', hrun', rfl⟩ := hout
        refine StepPost.restore hx (h fuel₂ _ r' n' ?_ hrun')
        intro y hy
        have hyx : (y == x) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun hh => hxD (hh ▸ hy)
        show IsWordVal (updatePanValueMap s.locals x value y)
        simp only [updatePanValueMap, hyx]
        exact hD y hy
  | raised l g m ffi exception value =>
    simp only at hout
    subst hout
    trivial
  | finalFfi l g m ffi event =>
    simp only at hout
    subst hout
    trivial
  | _ => exact hout.elim

/-- Assigning a known word local to a local in `M`. -/
theorem StepOk.assign_word {x y : VarName} (hx : x ∈ M) (hy : y ∈ D) :
    StepOk E M rank D (.assign .local x (.var .local y)) := by
  intro fuel s r n hD hrun
  rcases assign_local_inv hrun with herr | ⟨v, hv, rfl⟩
  · exact StepPost.of_error herr
  simp only [eval_local] at hv
  obtain ⟨w, hw⟩ := hD y hy
  rw [hw] at hv
  simp only [Option.some.injEq] at hv
  subst hv
  refine Or.inl ⟨rfl, rfl, rfl, ?_, ?_⟩
  · intro z hz
    have hzx : (z == x) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun hh => hz (hh ▸ hx)
    simp [updatePanValueMap, hzx]
  · intro z hz
    by_cases hzx : z = x
    · subst hzx
      exact Or.inl ⟨w, by simp [updatePanValueMap]⟩
    · have hzx' : (z == x) = false := by simpa using hzx
      exact Or.inr ⟨z, hz, by simp [updatePanValueMap, hzx']⟩

/-- `var x = scratch_alloc(k); rest` with `k ≥ 1` and `rest` writing no global
decreases the scratch rank whenever it keeps the loop going. -/
theorem StepOk.alloc_push (hE : GuestEnv E) {x : VarName} {k : Word} {rest : Prog Word}
    (hk : 1 ≤ k.toNat) (hrest : keepWith globalsLeaf (fun _ => false) rest = true) :
    StepOk E M scratchRank D (.decCall x .one "scratch_alloc" [.const k] rest) := by
  intro fuel s r n _ hrun
  rcases decCall_run_inv hrun with herr | ⟨fuel₁, parameters, calleeBody, values, calleeLocals,
    rb, nb, hlookup, hvalues, hbind, hcallee, hout⟩
  · exact StepPost.of_error herr
  have hparams := (fun_of_index 13 hE.functions (by guest_decl_at 13) (by decide +kernel)
    hlookup).2
  have hvals : values = [.word k] := by
    simp only [Env.evalArgs] at hvalues
    simp [evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp] at hvalues
    exact hvalues.symm
  subst hvals
  have hn : calleeLocals "n" = some (.word k) := by
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    rw [← hbind]
    simp [updatePanValueMap]
  have hspec := scratch_alloc_spec hE parameters calleeBody hlookup fuel₁
    ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb nb k hcallee hn hk
  cases rb with
  | returned l g m ffi values' =>
    obtain ⟨hrank, -, -, -⟩ := hspec
    cases values' with
    | nil => exact hout.elim
    | cons value restv =>
      cases restv with
      | cons value' rest' => exact hout.elim
      | nil =>
        obtain ⟨fuel₂, r', n', hrun', rfl⟩ := hout
        have hkeep := keepWith_sound (globalsKeeper E) (fun _ => false)
          (fun f hf => by cases hf) fuel₂ rest _ r' n' hrest hrun'
        have hg : r'.st.globals = g := hkeep
        cases r' with
        | normal l' g' m' f' =>
          have : g' = g := hg
          subst this
          exact Or.inr hrank
        | continued l' g' m' f' =>
          have : g' = g := hg
          subst this
          exact Or.inr hrank
        | _ => trivial
  | raised l g m ffi exception value =>
    simp only at hout
    subst hout
    trivial
  | finalFfi l g m ffi event =>
    simp only at hout
    subst hout
    trivial
  | _ => exact hout.elim

end InitECandidate.Solver.GuestBound
