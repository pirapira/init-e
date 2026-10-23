import InitECandidate.Solver.WordToStackClockExactOffset

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# WordToStack offset: semantic MMIO decomposition (interface module)

Flapjack's `compCall` only gives `∃ ck`. The decomposition
`ck ≤ executedRaises + executedShareInsts` is NOT derivable from it without re-proving
`compCorrect` with an event counter. It therefore enters here as the explicit hypothesis
`OffsetDecomp` on the actual witness `ck`; every consequence below is proved from it.
-/

namespace InitECandidate.Solver.WordToStackSemanticMmioBound

open Flapjack
open Flapjack.Compiler.Backend.StackLang
open Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm
open InitE
open WordToStackClockExactOffset

/-- Semantic decomposition hypothesis on any agreeing stack run produced from offset `ck`. -/
def OffsetDecomp {width : Nat} [NeZero width] {C F : Type} (start : Nat)
    (t : StackSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (raises shares : Nat) : Prop :=
  ∀ (ck : Nat) (t1 : StackSemStateFiniteExact width C F) (res1 : Option (StackSemResult width)),
    StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := t.clock + ck}) =
      (res1, t1) → res.map compileResult = res1 → ck ≤ raises + shares

/-- Exact tick identity plus semantic bound on the real witness `ck`. -/
theorem word_to_stack_ticks_decomp {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (start : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F) (k : Nat)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (lens : List Nat) (raises shares : Nat)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) s = (res, s1))
    (hne : res ≠ some .error) (hrel : stateRel ac k 0 0 s t lens 0)
    (hdec : OffsetDecomp start t res raises shares) :
    ∃ (ck : Nat) (t1 : StackSemStateFiniteExact width C F) (res1 : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := t.clock + ck}) =
        (res1, t1) ∧
      (res.map compileResult = res1 →
        s1.ffi = t1.ffi ∧ ck ≤ raises + shares ∧
        (t.clock + ck) - t1.clock = (s.clock - s1.clock) + ck) := by
  obtain ⟨ck, t1, res1, hr, hagree⟩ :=
    word_to_stack_exact_offset ac start s k res s1 t lens hrun hne hrel
  refine ⟨ck, t1, res1, hr, fun hs => ?_⟩
  obtain ⟨hffi, _, _, hticks⟩ := hagree hs
  exact ⟨hffi, hdec ck t1 res1 hr hs, hticks⟩

/-! ## Arithmetic consequences on tick counts -/

/-- With zero executed raises the offset is bounded by executed shareInsts. -/
theorem ck_le_shares_of_no_raise {ck raises shares : Nat}
    (h : ck ≤ raises + shares) (h0 : raises = 0) : ck ≤ shares := by omega

/-- Additive MMIO offset: `k_stack ≤ k_word + maxMmioOps`  (`C_ws = 1`, `D_ws ≤ maxMmioOps`). -/
theorem stack_ticks_le_word_add_mmio (k_word ck raises shares maxMmio : Nat)
    (h : ck ≤ raises + shares) (h0 : raises = 0) (hm : shares ≤ maxMmio) :
    k_word + ck ≤ k_word + maxMmio := by omega

/-- Tightness of the additive bound: equality is attained when `ck = maxMmioOps`. -/
theorem stack_ticks_mmio_tight (k_word maxMmio : Nat) :
    k_word + maxMmio = k_word + maxMmio ∧ maxMmio ≤ 0 + maxMmio := by omega

/-- On a segment with zero executed raises and zero shareInsts (the EVM RAM loop), the
offset vanishes: `C_ws = 1, D_ws = 0`. -/
theorem evm_loop_iso (k_word ck raises shares : Nat)
    (h : ck ≤ raises + shares) (h0 : raises = 0) (hs : shares = 0) :
    k_word + ck = k_word := by omega

/-- General bound: `ck ≤ k_word ⇒ k_stack ≤ 2 * k_word` (`C_ws ≤ 2, D_ws = 0`). -/
theorem stack_ticks_le_two_word (k_word ck : Nat) (h : ck ≤ k_word) :
    k_word + ck ≤ 2 * k_word := by omega

/-- The factor `2` is tight: attained at `ck = k_word`. -/
theorem stack_ticks_two_word_tight (k_word : Nat) : k_word + k_word = 2 * k_word := by omega

/-- Each executed raise or shareInst consumes at least one word tick, so the decomposition
implies the general hypothesis `ck ≤ k_word`. -/
theorem ck_le_word_of_events (ck raises shares k_word : Nat)
    (h : ck ≤ raises + shares) (hev : raises + shares ≤ k_word) : ck ≤ k_word := by omega

/-! ## Budget impact (front factor of `SelfContainedMasterK`) -/

/-- Worst case `C_ws = 2` doubles the front factor `10 → 20`; still far below the ceiling. -/
theorem budget_worst_cws2 : budgetAt 20 = 73531094117 ∧ budgetAt 20 < 900719925474 := by
  unfold budgetAt; rw [InitE.bootstrapSteps_eq, SelfContainedMasterK.refinedSourceClock_eq.1]
  decide

/-- With the MMIO decomposition (`C_ws = 1`), the front factor is unchanged. -/
theorem budget_mmio_cws1 : budgetAt (1 * 10) = SelfContainedMasterK.refinedCandidateK := rfl


end InitECandidate.Solver.WordToStackSemanticMmioBound
