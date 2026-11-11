import Flapjack.PanValueFfiFuel
import InitECandidate.Solver.GuestBound.CostLogic

/-!
# Loops whose state comes back

If the states at the loop head follow a sequence `S` with `S (2^64) = S 0`,
a returning run cannot go through `2^64` iterations: it would be a run from
the same state with less fuel and a smaller count, contradicting the fact
that the evaluator is a function with monotone fuel.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- More fuel does not change a result. -/
theorem run_mono {fuel fuel' : Nat} (h : fuel ≤ fuel') {s : St σ} {p : Prog Word}
    {x : Result σ × Nat} (hrun : E.run fuel s p = some x) : E.run fuel' s p = some x :=
  StepCalculus.progMono E.context E.primitive E.handler E.structs E.functions E.baseAddress E.topAddress
    E.bytesInWord fuel s.locals s.globals s.memory s.ffi p E.memoryAccess E.contracts
    E.memoryHandler fuel' x h hrun

section orbit
variable {c : Exp Word} {body : Prog Word} {e b : Nat} (S : Nat → St σ)
  (hc : CondCost E (fun _ => True) c e) (hbody : Costs E body b)
  (hnext : ∀ t fuel l g mem f nb,
    (E.run fuel (S t) body = some (.normal l g mem f, nb) ∨
      E.run fuel (S t) body = some (.continued l g mem f, nb)) →
    (⟨l, g, mem, f⟩ : St σ) = S (t + 1))

include hc hbody hnext in
/-- One iteration: the loop ends, or continues from the next state with less fuel. -/
theorem orbit_step (t fuel : Nat) (r : Result σ) (m : Nat)
    (hrun : E.run fuel (S t) (.while c body) = some (r, m)) (hne : r.isError = false) :
    m ≤ e + b + 1 ∨ ∃ fuel' m', fuel' < fuel ∧
      E.run fuel' (S (t + 1)) (.while c body) = some (r, m') ∧ m' + 1 ≤ m ∧
      m ≤ m' + (e + b + 1) := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        (S t).locals (S t).globals (S t).memory c E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact Bool.noConfusion hne
    | some pair =>
      obtain ⟨v, kc⟩ := pair
      rw [hcond] at hrun
      have hkc : kc ≤ e := hc (S t) v kc trivial hcond
      simp only [Option.elim_some] at hrun
      by_cases hv : (v == 0) = true
      · rw [if_pos hv] at hrun
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        left; omega
      · rw [if_neg hv] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel (S t).locals
            (S t).globals (S t).memory (S t).ffi body (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at hrun
          have again : ∀ l g mem f, nb ≤ b → (⟨l, g, mem, f⟩ : St σ) = S (t + 1) →
              (do
                let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                  E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                  l g mem f (.while c body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                pure (loopResult, kc + nb + loopSteps + 1)) = some (r, m) →
              ∃ fuel' m', fuel' < fuel + 1 ∧
                E.run fuel' (S (t + 1)) (.while c body) = some (r, m') ∧ m' + 1 ≤ m ∧
                m ≤ m' + (e + b + 1) := by
            intro l g mem f hnb hS hrun
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
              have hloop' : E.run fuel ⟨l, g, mem, f⟩ (.while c body) = some (rl, nl) := hloop
              rw [hS] at hloop'
              exact ⟨fuel, nl, Nat.lt_succ_self _, hloop', by omega, by omega⟩
          cases rb with
          | normal l g mem f =>
            have hnb : nb ≤ b := (hbody fuel (S t) _ nb trivial hb rfl).1
            right
            exact again l g mem f hnb (hnext t fuel l g mem f nb (Or.inl hb)) hrun
          | continued l g mem f =>
            have hnb : nb ≤ b := (hbody fuel (S t) _ nb trivial hb rfl).1
            right
            exact again l g mem f hnb (hnext t fuel l g mem f nb (Or.inr hb)) hrun
          | broke l g mem f =>
            have hnb : nb ≤ b := (hbody fuel (S t) _ nb trivial hb rfl).1
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            left; omega
          | _ =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            have hnb : nb ≤ b := (hbody fuel (S t) _ nb trivial hb hne).1
            left; omega

include hc hbody hnext in
/-- After `j` iterations the loop has ended, or is at `S (t + j)` with at least `j` steps spent. -/
theorem orbit_iter (r : Result σ) (hne : r.isError = false) :
    ∀ (j t fuel m : Nat), E.run fuel (S t) (.while c body) = some (r, m) →
      m ≤ j * (e + b + 1) ∨ ∃ fuel' m', fuel' ≤ fuel ∧
        E.run fuel' (S (t + j)) (.while c body) = some (r, m') ∧ m' + j ≤ m ∧
        m ≤ m' + j * (e + b + 1) := by
  intro j
  induction j with
  | zero =>
    intro t fuel m hrun
    exact Or.inr ⟨fuel, m, Nat.le_refl _, hrun, by omega, by omega⟩
  | succ j ih =>
    intro t fuel m hrun
    have hsucc : (j + 1) * (e + b + 1) = j * (e + b + 1) + (e + b + 1) := Nat.succ_mul _ _
    rcases ih t fuel m hrun with h | ⟨fuel', m', hfuel, hrun', hlow, hhigh⟩
    · left; omega
    · rcases orbit_step S hc hbody hnext (t + j) fuel' r m' hrun' hne with h |
        ⟨fuel'', m'', hfuel', hrun'', hlow', hhigh'⟩
      · left; omega
      · right
        exact ⟨fuel'', m'', by omega, hrun'', by omega, by omega⟩

include hc hbody hnext in
/-- A loop whose head state returns to the start after `2^64` iterations takes
fewer than `2^64` iterations in any run that returns. -/
theorem orbit_bound (hper : S (2 ^ 64) = S 0) (fuel : Nat) (r : Result σ) (m : Nat)
    (hrun : E.run fuel (S 0) (.while c body) = some (r, m)) (hne : r.isError = false) :
    m ≤ 2 ^ 64 * (e + b + 1) := by
  rcases orbit_iter S hc hbody hnext r hne (2 ^ 64) 0 fuel m hrun with h |
    ⟨fuel', m', hfuel, hrun', hlow, -⟩
  · exact h
  · rw [Nat.zero_add, hper] at hrun'
    have hsame := run_mono hfuel hrun'
    rw [hrun] at hsame
    simp only [Option.some.injEq, Prod.mk.injEq] at hsame
    have h64 : 0 < 2 ^ 64 := by decide
    omega

end orbit

end InitECandidate.Solver.GuestBound
