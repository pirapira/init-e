import InitE.Challenge

/-! Lower bounds for accepting target runs. The certificate corollary takes an
accepted source witness explicitly; this module does not establish that such
a witness exists for the fixed source. -/

namespace InitE
open Classical Flapjack

/-- A halting evaluation with at most one unit of clock cannot record a
successful foreign call: a returning call still needs clock to halt. -/
theorem halt_one_preserves_events {width : Nat} [NeZero width]
    {State Projection σ : Type} (mc : MachineConfig width State Projection)
    (ffi : HolFfiState σ) (ms post : State) (finalFfi : HolFfiState σ)
    (outcome : HolOutcome)
    (run : evaluateTargetHOL mc ffi 1 ms = (.halt outcome, post, finalFfi)) :
    finalFfi.ioEvents = ffi.ioEvents := by
  simp only [evaluateTargetHOL] at run
  repeat' first
    | (solve | cases congrArg Prod.fst run)
    | (solve | simp_all only [Prod.mk.injEq])
    | split at run

/-- Admission forces the first clock tick to execute ordinary code. -/
theorem Submission.entry_is_program (s : Submission) (admitted : s.Admitted)
    (input : Guest.InputBlob) :
    s.machineConfig.progAddresses (s.machineConfig.target.getPc (s.initialState input)) ∧
      s.machineConfig.target.getPc (s.initialState input) ∉ s.machineConfig.ffiEntryPcs := by
  change s.programDomain (BitVec.ofNat 64 initialPc) ∧
    BitVec.ofNat 64 initialPc ∉ s.machineConfig.ffiEntryPcs
  constructor
  · constructor
    · change ((initialPc ≤ initialPc ∧ initialPc < initialPc + codeSizeLimit) ∨
        (ramStart ≤ initialPc ∧ initialPc < ramEnd)) ∧
        ¬ ((inputStart ≤ initialPc ∧ initialPc < inputEnd) ∨
          (outputStart ≤ initialPc ∧ initialPc < outputEnd))
      simp [initialPc, codeSizeLimit, ramStart, inputStart, inputEnd, inputSize,
        outputStart, outputEnd, outputSize]
    · intro i hi equal
      have loaded := (admitted.ordinary_slots_loaded ⟨i, hi⟩).1
      rw [← equal] at loaded
      change initialPc < initialPc at loaded
      omega
  · intro member
    have loaded := (admitted.entry_loaded _ member).1
    change initialPc < initialPc at loaded
    omega

/-- If evaluation starts in ordinary code, a halt in at most two clock ticks
cannot have recorded any successful foreign calls. -/
theorem halt_two_preserves_events {width : Nat} [NeZero width]
    {State Projection σ : Type} (mc : MachineConfig width State Projection)
    (ffi : HolFfiState σ) (ms post : State) (finalFfi : HolFfiState σ)
    (outcome : HolOutcome) (steps : Nat) (short : steps ≤ 2)
    (entry : mc.progAddresses (mc.target.getPc ms) ∧ mc.target.getPc ms ∉ mc.ffiEntryPcs)
    (run : evaluateTargetHOL mc ffi steps ms = (.halt outcome, post, finalFfi)) :
    finalFfi.ioEvents = ffi.ioEvents := by
  cases steps with
  | zero => simp [evaluateTargetHOL] at run
  | succ steps =>
    rw [evaluateTargetHOL, if_pos entry] at run
    split at run
    · dsimp only at run
      split at run
      · cases steps with
        | zero => simp [evaluateTargetHOL] at run
        | succ steps =>
          have : steps = 0 := by omega
          subst steps
          exact halt_one_preserves_events _ _ _ _ _ _ run
      · simp at run
    · simp at run

/-- An accepting target execution must change the initially clear success byte,
so it needs at least three ticks: ordinary entry, a returning call, and halt.
The explicit initial-byte premise also handles inputs whose framing overlaps
the output region in the total host-memory model. -/
theorem accepted_execution_steps (s : Submission) (admitted : s.Admitted)
    (input : Guest.InputBlob) (initial : outputByte input [] ⟨32, by decide⟩ ≠ 1)
    (steps : Nat) (outcome : HolOutcome) (post : Flapjack.RiscV.L3.riscv_state)
    (finalFfi : HolFfiState Guest.HostMemory)
    (run : evaluateTargetHOL s.machineConfig (sourceFfi input) steps
      (s.initialState input) = (.halt outcome, post, finalFfi))
    (accepted : acceptedOutput input outcome finalFfi.ioEvents) : 3 ≤ steps := by
  by_contra short
  have events := halt_two_preserves_events _ _ _ _ _ _ steps (by omega)
    (s.entry_is_program admitted input) run
  change finalFfi.ioEvents = [] at events
  exact initial (events ▸ accepted.2)

/-- A matching execution for an accepted source result needs at least three ticks. -/
theorem matchingExecutionAt_steps (s : Submission) (admitted : s.Admitted)
    (input : Guest.InputBlob) (initial : outputByte input [] ⟨32, by decide⟩ ≠ 1)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (accepted : acceptedOutput input outcome events) (steps : Nat)
    (execution : matchingExecutionAt s input outcome events steps) : 3 ≤ steps := by
  obtain ⟨targetOutcome, post, finalFfi, run, matching⟩ := execution
  rw [matchingResult, if_pos accepted] at matching
  exact accepted_execution_steps s admitted input initial steps targetOutcome post finalFfi
    run matching.1

/-- An accepted covered source witness rules out every certified score below 3.
Infinity is allowed and still requires finite executions, as in `Certificate`. -/
theorem Certificate.score_at_least_three_of_accepted {s : Submission} {claimed : NatE}
    (certificate : Certificate s claimed)
    (input : Guest.InputBlob) (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (initial : outputByte input [] ⟨32, by decide⟩ ≠ 1)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (covered : coveredOutcome outcome) (accepted : acceptedOutput input outcome events) :
    claimed.Allows 3 := by
  obtain ⟨steps, bound, execution⟩ := certificate.correct input gas outcome events source covered
  have lower := matchingExecutionAt_steps s certificate.admitted input initial outcome events
    accepted steps execution
  cases claimed with
  | finite k => change steps ≤ k at bound; exact Nat.le_trans lower bound
  | infinity => trivial

end InitE
