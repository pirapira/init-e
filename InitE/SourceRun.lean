import InitE.SourceSemantics
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitE
open Classical Flapjack Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

/-- Two clocked, non-timeout runs have identical observable results. -/
theorem source_run_observations {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (p : ProgHOL width)
    (k₁ k₂ : Nat) (r₁ r₂ : Option (PanSemResultExact width))
    (t₁ t₂ : PanSemStateFiniteExact width σ)
    (run₁ : evaluateHOLFiniteState { s with clock := k₁ } p = (r₁, t₁))
    (run₂ : evaluateHOLFiniteState { s with clock := k₂ } p = (r₂, t₂))
    (non₁ : r₁ ≠ some .timeOut) (non₂ : r₂ ≠ some .timeOut) :
    r₁ = r₂ ∧ t₁.ffi.ioEvents = t₂.ffi.ioEvents := by
  have a := panPropsEvaluateAddClockEq p { s with clock := k₁ } r₁ t₁ k₂ ⟨run₁, non₁⟩
  have b := panPropsEvaluateAddClockEq p { s with clock := k₂ } r₂ t₂ k₁ ⟨run₂, non₂⟩
  dsimp only at a b
  rw [Nat.add_comm k₂ k₁, a] at b
  exact ⟨congrArg Prod.fst b,
    congrArg (fun result => result.2.ffi.ioEvents) b⟩

/-- A concrete terminal FFI run determines the unclocked source semantics.
This bridge permits kernel computation of a single clocked run without
computing the classical behavior wrapper. -/
theorem source_semantics_of_final_run {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (start : MlS) (clock : Nat)
    (event : HolFinalEvent) (post : PanSemStateFiniteExact width σ)
    (run : evaluateHOLFiniteState { s with clock := clock } (.call none start []) =
      (some (.finalFfi event), post)) :
    semantics s start = .terminate (.ffiOutcome event) post.ffi.ioEvents := by
  have observations (k : Nat) (r : Option (PanSemResultExact width))
      (t : PanSemStateFiniteExact width σ)
      (other : evaluateHOLFiniteState { s with clock := k } (.call none start []) = (r, t))
      (non : r ≠ some .timeOut) :
      r = some (.finalFfi event) ∧ t.ffi.ioEvents = post.ffi.ioEvents :=
    source_run_observations s _ k clock r _ t post other run non (by simp)
  unfold semantics
  dsimp only
  have noFail : ¬ ∃ k, (match (evaluateHOLFiniteState
      { s with clock := k } (.call none start [])).1 with
      | some .timeOut => False
      | some (.finalFfi _) => False
      | some (.returned _) => False
      | _ => True) := by
    rintro ⟨k, bad⟩
    generalize h : evaluateHOLFiniteState { s with clock := k } (.call none start []) = pair at bad
    rcases pair with ⟨r, t⟩
    have non : r ≠ some .timeOut := by intro equal; simp [equal] at bad
    have equal := (observations k r t h non).1
    simp [equal] at bad
  split
  next bad => exact False.elim (noFail bad)
  next _ =>
    have choice : holOptionSome (fun res => ∃ k t r outcome,
        evaluateHOLFiniteState { s with clock := k } (.call none start []) = (r, t) ∧
        (match r with
         | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
         | some (.returned _) => outcome = HolOutcome.success
         | _ => False) ∧
        res = HolBehaviour.terminate outcome t.ffi.ioEvents) =
        some (.terminate (.ffiOutcome event) post.ffi.ioEvents) := by
      apply HolLList.holOptionSome_eq_some
      · exact ⟨clock, post, _, _, run, rfl, rfl⟩
      · rintro result ⟨k, t, r, outcome, other, terminal, rfl⟩
        have non : r ≠ some .timeOut := by intro equal; simp [equal] at terminal
        obtain ⟨equal, trace⟩ := observations k r t other non
        simp only [equal] at terminal
        rw [terminal, trace]
    split
    next result selected =>
      have equal : some result = some (.terminate (.ffiOutcome event) post.ffi.ioEvents) :=
        selected.symm.trans choice
      exact Option.some.inj equal
    next selected =>
      have equal : (none : Option HolBehaviour) =
          some (.terminate (.ffiOutcome event) post.ffi.ioEvents) := selected.symm.trans choice
      cases equal

end InitE
