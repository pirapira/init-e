import InitECandidate.Solver.GuestBound.CostLogic

/-!
# More loop rules

`Triple.while_exit` is `Triple.while` with the exit condition available for
the postcondition. `while_never` shows a loop has no non-error result from a
set of states that the body keeps and on which the guard stays true.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- `while_steps`, with the guard known to be zero at exit. -/
theorem while_steps_exit {I : St σ → Prop} {μ : St σ → Nat} {Q : Result σ → Prop}
    {c : Exp Word} {body : Prog Word} {e b : Nat}
    (hc : CondCost E I c e)
    (hexit : ∀ s, I s → (∃ k, E.cond s c = some (0, k)) →
      Q (.normal s.locals s.globals s.memory s.ffi))
    (hbody : ∀ k, Triple E (fun s => I s ∧ μ s = k ∧ CondTrue E s c) body b
      (loopBodyPost I μ k Q)) :
    ∀ (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat), I s →
      Env.run E fuel s (.while c body) = some (r, n) → r.isError = false →
      n ≤ (μ s + 1) * (e + b + 1) ∧ Q r := by
  intro fuel
  induction fuel with
  | zero =>
    intro s r n _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro s r n hI hrun hne
    have hpos : e + b + 1 ≤ (μ s + 1) * (e + b + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory c E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      cases hne
    | some pair =>
      obtain ⟨v, k⟩ := pair
      rw [hcond] at hrun
      have hk : k ≤ e := hc s v k hI hcond
      simp only [Option.elim_some] at hrun
      by_cases hv : (v == 0) = true
      · rw [if_pos hv] at hrun
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        have hv0 : v = 0 := by simpa using hv
        subst hv0
        exact ⟨by omega, hexit s hI ⟨k, hcond⟩⟩
      · rw [if_neg hv] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi body (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some bodyPair =>
          obtain ⟨rb, nb⟩ := bodyPair
          rw [hb] at hrun
          have hpre : I s ∧ μ s = μ s ∧ CondTrue E s c := ⟨hI, rfl, v, k, hcond, by simpa using hv⟩
          have again : ∀ l g m f, nb ≤ b → I ⟨l, g, m, f⟩ → μ ⟨l, g, m, f⟩ < μ s →
              ∀ (r : Result σ) (n : Nat), (do
                let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                  E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                  l g m f (.while c body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                pure (loopResult, k + nb + loopSteps + 1)) = some (r, n) →
              r.isError = false →
              n ≤ (μ s + 1) * (e + b + 1) ∧ Q r := by
            intro l g m f hnb hI' hμ r n hrun hne
            cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f
                (.while c body) (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                (memoryHandler := E.memoryHandler) with
            | none => rw [hloop] at hrun; simp at hrun
            | some loopPair =>
              obtain ⟨rl, nl⟩ := loopPair
              rw [hloop] at hrun
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              obtain ⟨hnl, hQ⟩ := ih ⟨l, g, m, f⟩ rl nl hI' hloop hne
              refine ⟨?_, hQ⟩
              have step : (μ (⟨l, g, m, f⟩ : St σ) + 1) * (e + b + 1) + (e + b + 1) ≤
                  (μ s + 1) * (e + b + 1) := by
                rw [← Nat.succ_mul]
                exact Nat.mul_le_mul_right _ (by omega)
              omega
          cases rb with
          | normal l g m f =>
            obtain ⟨hnb, hpost⟩ := hbody (μ s) fuel s _ nb hpre hb rfl
            exact again l g m f hnb hpost.1 hpost.2 r n hrun hne
          | continued l g m f =>
            obtain ⟨hnb, hpost⟩ := hbody (μ s) fuel s _ nb hpre hb rfl
            exact again l g m f hnb hpost.1 hpost.2 r n hrun hne
          | broke l g m f =>
            obtain ⟨hnb, hpost⟩ := hbody (μ s) fuel s _ nb hpre hb rfl
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            exact ⟨by omega, hpost⟩
          | _ =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            obtain ⟨hnb, hpost⟩ := hbody (μ s) fuel s _ nb hpre hb hne
            exact ⟨by omega, hpost⟩

/-- The while rule with the exit condition: a loop entered with variant at most
`M` takes at most `(M + 1) * (e + b + 1)` steps. -/
theorem Triple.while_exit {I : St σ → Prop} {μ : St σ → Nat} {Q : Result σ → Prop}
    {c : Exp Word} {body : Prog Word} {e b : Nat} (M : Nat)
    (hc : CondCost E I c e)
    (hexit : ∀ s, I s → (∃ k, E.cond s c = some (0, k)) →
      Q (.normal s.locals s.globals s.memory s.ffi))
    (hbody : ∀ k, Triple E (fun s => I s ∧ μ s = k ∧ CondTrue E s c) body b
      (loopBodyPost I μ k Q)) :
    Triple E (fun s => I s ∧ μ s ≤ M) (.while c body) ((M + 1) * (e + b + 1)) Q := by
  unfold Triple
  intro fuel s r n hP hrun hne
  obtain ⟨hn, hQ⟩ := while_steps_exit hc hexit hbody fuel s r n hP.1 hrun hne
  exact ⟨Nat.le_trans hn (Nat.mul_le_mul_right _ (by omega)), hQ⟩

/-- A loop does not return from a set of states `Z` that the body keeps, when
the guard is true on `Z` and the body can only end normally or in `.error`. -/
theorem while_never {Z : St σ → Prop} {c : Exp Word} {body : Prog Word}
    (hguard : ∀ s, Z s → ∀ v k, E.cond s c = some (v, k) → (v == 0) = false)
    (hbody : ∀ fuel s r n, Z s → E.run fuel s body = some (r, n) →
      r.isError = true ∨ ∃ l g m f, r = .normal l g m f ∧ Z ⟨l, g, m, f⟩) :
    ∀ (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat), Z s →
      E.run fuel s (.while c body) = some (r, n) → r.isError = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro s r n _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro s r n hZ hrun
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory c E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      rfl
    | some pair =>
      obtain ⟨v, k⟩ := pair
      rw [hcond] at hrun
      have hv := hguard s hZ v k hcond
      simp only [Option.elim_some] at hrun
      have hv' : ¬ (v == 0) = true := by rw [hv]; exact Bool.false_ne_true
      rw [if_neg hv'] at hrun
      cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
          s.memory s.ffi body (memoryAccess := E.memoryAccess)
          (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
      | none => rw [hb] at hrun; simp at hrun
      | some bodyPair =>
        obtain ⟨rb, nb⟩ := bodyPair
        rw [hb] at hrun
        rcases hbody fuel s rb nb hZ hb with herr | ⟨l, g, m, f, rfl, hZ'⟩
        · cases rb with
          | error l g m f =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            rfl
          | _ => cases herr
        · simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f
              (.while c body) (memoryAccess := E.memoryAccess) (contracts := E.contracts)
              (memoryHandler := E.memoryHandler) with
          | none => rw [hloop] at hrun; simp at hrun
          | some loopPair =>
            obtain ⟨rl, nl⟩ := loopPair
            rw [hloop] at hrun
            simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih ⟨l, g, m, f⟩ rl nl hZ' hloop

/-- The result is neither `continued` nor `broke`. -/
def NoEsc : Result σ → Prop
  | .continued _ _ _ _ | .broke _ _ _ _ => False
  | _ => True

/-- A loop never ends in `continued` or `broke`. -/
theorem while_not_escape {c : Exp Word} {body : Prog Word} :
    ∀ (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat),
      E.run fuel s (.while c body) = some (r, n) →
      NoEsc r := by
  intro fuel
  induction fuel with
  | zero =>
    intro s r n hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro s r n hrun
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory c E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      trivial
    | some pair =>
      obtain ⟨v, k⟩ := pair
      rw [hcond] at hrun
      simp only [Option.elim_some] at hrun
      by_cases hv : (v == 0) = true
      · rw [if_pos hv] at hrun
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        trivial
      · rw [if_neg hv] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi body (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some bodyPair =>
          obtain ⟨rb, nb⟩ := bodyPair
          rw [hb] at hrun
          have again : ∀ l g m f, (do
                let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                  E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                  l g m f (.while c body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                pure (loopResult, k + nb + loopSteps + 1)) = some (r, n) →
              NoEsc r := by
            intro l g m f hrun
            cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f
                (.while c body) (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                (memoryHandler := E.memoryHandler) with
            | none => rw [hloop] at hrun; simp at hrun
            | some loopPair =>
              obtain ⟨rl, nl⟩ := loopPair
              rw [hloop] at hrun
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact ih ⟨l, g, m, f⟩ rl nl hloop
          cases rb with
          | normal l g m f => exact again l g m f hrun
          | continued l g m f => exact again l g m f hrun
          | broke l g m f =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            trivial
          | _ =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            trivial

end InitECandidate.Solver.GuestBound
