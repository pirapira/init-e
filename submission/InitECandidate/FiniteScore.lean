import InitE.Challenge
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Order

/-!
# A finite score exists for every infinity certificate

`InitE.Certificate` reads its input only through `Guest.guestHostMemory input`:
the source run, the target's FFI state and initial memory, and the observed
output all start from it. That host memory is a function `BitVec 64 → Option UInt8`,
a finite type, so the input-dependent step counts of an infinity certificate take
finitely many values. Their maximum is a uniform finite score. Divergent source
runs are outside `Certificate`, so they need no bound.

The score is only shown to exist; nothing here computes it.
-/

namespace InitECandidate.FiniteScore
open InitE Flapjack

instance (n : Nat) : Finite (BitVec n) :=
  Finite.of_injective BitVec.toFin fun _ _ h => BitVec.eq_of_toFin_eq h

instance : Finite UInt8 :=
  Finite.of_injective UInt8.toBitVec fun _ _ h => UInt8.toBitVec_inj.mp h

instance : Finite Guest.HostMemory := Pi.finite

theorem sourceBehaviour_congr {i j : Guest.InputBlob}
    (same : Guest.guestHostMemory i = Guest.guestHostMemory j) :
    sourceBehaviour i = sourceBehaviour j := by
  simp only [sourceBehaviour, sourceInitialState, sourceFfi, same]

theorem matchingExecutionAt_congr (s : Submission) {i j : Guest.InputBlob}
    (same : Guest.guestHostMemory i = Guest.guestHostMemory j)
    (outcome : HolOutcome) (events : List HolIoEvent) (steps : Nat) :
    matchingExecutionAt s i outcome events steps ↔
      matchingExecutionAt s j outcome events steps := by
  have memory : s.initialMemory i = s.initialMemory j := by
    funext a
    simp only [Submission.initialMemory, same]
  have state : s.initialState i = s.initialState j := by
    simp only [Submission.initialState, memory]
  unfold matchingExecutionAt matchingResult acceptedOutput outputByte observedHost sourceFfi
  rw [state, same]

/-- One step count serves every covered input with the same host memory. -/
theorem uniform_steps (s : Submission) (cert : Certificate s .infinity)
    (memory : Guest.HostMemory) :
    ∃ steps, ∀ input, Guest.guestHostMemory input = memory →
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events, sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome → matchingExecutionAt s input outcome events steps := by
  by_cases witness : ∃ input outcome events, Guest.guestHostMemory input = memory ∧
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 ∧
      sourceBehaviour input = .terminate outcome events ∧ coveredOutcome outcome
  · obtain ⟨input₀, outcome₀, events₀, view₀, gas₀, source₀, covered₀⟩ := witness
    obtain ⟨steps, -, run⟩ := cert.correct input₀ gas₀ outcome₀ events₀ source₀ covered₀
    refine ⟨steps, fun input view _ outcome events source _ => ?_⟩
    have same : Guest.guestHostMemory input = Guest.guestHostMemory input₀ :=
      view.trans view₀.symm
    have terminate : HolBehaviour.terminate outcome events = .terminate outcome₀ events₀ := by
      rw [← source, ← source₀, sourceBehaviour_congr same]
    simp only [HolBehaviour.terminate.injEq] at terminate
    obtain ⟨rfl, rfl⟩ := terminate
    exact (matchingExecutionAt_congr s same outcome events steps).mpr run
  · exact ⟨0, fun input view gas outcome events source covered =>
      absurd ⟨input, outcome, events, view, gas, source, covered⟩ witness⟩

/-- An infinity certificate yields a finite one for the same ROM and metadata. -/
theorem finite_certificate_of_infinity (s : Submission) (cert : Certificate s .infinity) :
    ∃ bound : Nat, Certificate { s with K := .finite bound } (.finite bound) := by
  choose steps run using uniform_steps s cert
  obtain ⟨bound, below⟩ := Finite.bddAbove_range steps
  refine ⟨bound, rfl, { cert.admitted with }, ?_⟩
  intro input gas outcome events source covered
  exact ⟨steps (Guest.guestHostMemory input), below ⟨_, rfl⟩,
    run _ input rfl gas outcome events source covered⟩

end InitECandidate.FiniteScore
