import InitECandidate.Solver.GuestBound.ShapeLoop

/-!
# Loops whose state only moves forward

A pigeonhole bound for loops that also change memory, when memory only grows
in some order: a later state with the same code as an earlier one is that
state, so a returning run visits each code at most once.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The invariant holds again at the loop head, in a state later than `s`. -/
def KeepLe (I : St σ → Prop) (le : St σ → St σ → Prop) (s : St σ) : Result σ → Prop
  | .normal l g m f | .continued l g m f => I ⟨l, g, m, f⟩ ∧ le s ⟨l, g, m, f⟩
  | _ => True

open Classical in
/-- As `finite_core`, for states that only move forward in an order `le`:
two states with the same code are equal when one is later than the other. -/
theorem ordered_core {α : Type} [Fintype α] (I : St σ → Prop) (le : St σ → St σ → Prop)
    (htrans : ∀ a b c, le a b → le b c → le a c) (enc : St σ → α)
    (hinj : ∀ s s', I s → I s' → le s' s → enc s = enc s' → s = s') (N : Nat)
    (hcard : Fintype.card α ≤ N) {c : Exp Word} {body : Prog Word} {b : Nat}
    (hbody : ∀ fuel s r n, I s → CondTrue E s c → E.run fuel s body = some (r, n) →
      r.isError = false → n ≤ b ∧ KeepLe I le s r) (r : Result σ) (hne : r.isError = false) :
    ∀ (fuel : Nat) (V : Finset α) (s : St σ) (m : Nat),
      I s → E.run fuel s (.while c body) = some (r, m) →
      (∀ code ∈ V, ∃ s' fuel' m', I s' ∧ le s' s ∧ enc s' = code ∧ fuel ≤ fuel' ∧
        m < m' ∧ E.run fuel' s' (.while c body) = some (r, m')) →
      m + V.card * (panValueExpStepCost c + b + 1) ≤ N * (panValueExpStepCost c + b + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro V s m _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro V s m hok hrun0 hV
    have hrun := hrun0
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    have hnotV : enc s ∉ V := by
      intro hmem
      obtain ⟨s', fuel', m', hok', hle', henc, hfuel, hlt, hrun'⟩ := hV _ hmem
      have hs : s' = s := (hinj _ _ hok hok' hle' henc.symm).symm
      have hsame := run_mono hfuel hrun0
      rw [hs] at hrun'
      rw [hrun'] at hsame
      simp only [Option.some.injEq, Prod.mk.injEq] at hsame
      omega
    have hcard' : V.card + 1 ≤ N :=
      Nat.le_trans (Finset.card_lt_univ_of_notMem hnotV) hcard
    have hroom : V.card * (panValueExpStepCost c + b + 1) + (panValueExpStepCost c + b + 1) ≤
        N * (panValueExpStepCost c + b + 1) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hcard'
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory c E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact Bool.noConfusion hne
    | some pair =>
      obtain ⟨v, kc⟩ := pair
      rw [hcond] at hrun
      have hkc : kc ≤ panValueExpStepCost c :=
        condCost (E := E) (fun _ => True) c s v kc trivial hcond
      simp only [Option.elim_some] at hrun
      by_cases hv : (v == 0) = true
      · rw [if_pos hv] at hrun
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      · rw [if_neg hv] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi body (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at hrun
          have hct : CondTrue E s c := ⟨v, kc, hcond, by simpa using hv⟩
          have again : ∀ l g mem f, nb ≤ b → I ⟨l, g, mem, f⟩ → le s ⟨l, g, mem, f⟩ →
              (do
                let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                  E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                  l g mem f (.while c body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                pure (loopResult, kc + nb + loopSteps + 1)) = some (r, m) →
              m + V.card * (panValueExpStepCost c + b + 1) ≤
                N * (panValueExpStepCost c + b + 1) := by
            intro l g mem f hnb hok' hstep hrun
            cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g mem f
                (.while c body) (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                (memoryHandler := E.memoryHandler) with
            | none => rw [hloop] at hrun; simp at hrun
            | some pair =>
              obtain ⟨rl, nl⟩ := pair
              rw [hloop] at hrun
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              have hV' : ∀ code ∈ insert (enc s) V, ∃ s' fuel' m', I s' ∧
                  le s' ⟨l, g, mem, f⟩ ∧ enc s' = code ∧ fuel ≤ fuel' ∧ nl < m' ∧
                  E.run fuel' s' (.while c body) = some (rl, m') := by
                intro code hcode
                rcases Finset.mem_insert.mp hcode with rfl | hcode
                · exact ⟨s, fuel + 1, _, hok, hstep, rfl, Nat.le_succ _, by omega, hrun0⟩
                · obtain ⟨s', fuel', m', hok'', hle'', henc, hfuel, hlt, hrun'⟩ := hV code hcode
                  exact ⟨s', fuel', m', hok'', htrans _ _ _ hle'' hstep, henc, by omega, by omega,
                    hrun'⟩
              have hih := ih (insert (enc s) V) ⟨l, g, mem, f⟩ nl hok' hloop hV'
              rw [Finset.card_insert_of_notMem hnotV, Nat.succ_mul] at hih
              omega
          cases rb with
          | normal l g mem f =>
            obtain ⟨hnb, hI', hstep⟩ := hbody fuel s _ nb hok hct hb rfl
            exact again l g mem f hnb hI' hstep hrun
          | continued l g mem f =>
            obtain ⟨hnb, hI', hstep⟩ := hbody fuel s _ nb hok hct hb rfl
            exact again l g mem f hnb hI' hstep hrun
          | broke l g mem f =>
            have hnb : nb ≤ b := (hbody fuel s _ nb hok hct hb rfl).1
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            omega
          | _ =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            have hnb : nb ≤ b := (hbody fuel s _ nb hok hct hb hne).1
            omega

end InitECandidate.Solver.GuestBound
