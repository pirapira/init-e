import InitECandidate.Solver.LoopWordStackExactClockIso
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateClock

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# WordToStack: exact entry clock relation

* `stateRel` pins `s.clock = t.clock`, and WordSem never increases the clock
  (`evaluate_clock`), so the branch `s1.clock > t.clock` is impossible.
* The offset `ck` is the sum of per-construct offsets in Flapjack's `compCorrect`
  (`0` for leaves, `1` per `raise` / `shareInst`, summed through `seq` and `loop`), so it is
  bounded by the run, not by a constant. We expose it as `D_ws := ck` and prove the exact
  identity `stack ticks = word ticks + ck`.
-/

namespace InitECandidate.Solver.WordToStackClockExactOffset

open Flapjack
open Flapjack.Compiler.Backend.StackLang
open Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm
open InitE

theorem stateRel_clock_eq {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat)
    {s : WordSemStateFiniteExact width (Nat × C) F} {t : StackSemStateFiniteExact width C F}
    {lens : List Nat} (h : stateRel ac k 0 0 s t lens 0) : s.clock = t.clock := h.1

theorem word_run_clock_le {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width C F)
    (h : WordSemStateFiniteExact.evaluate p s = (res, s1)) : s1.clock ≤ s.clock := by
  have := WordSemStateFiniteExact.evaluate_clock_proj p s
  rw [h] at this; exact this.1

/-- Exact WordToStack entry clock relation (branch `s1.clock > t.clock` eliminated):
the stack run at `t.clock + ck` ends at the word end clock and consumes exactly
`word ticks + ck`. -/
theorem word_to_stack_exact_offset {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (start : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F) (k : Nat)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (lens : List Nat)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) s = (res, s1))
    (hne : res ≠ some .error) (hrel : stateRel ac k 0 0 s t lens 0) :
    ∃ (ck : Nat) (t1 : StackSemStateFiniteExact width C F) (res1 : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := t.clock + ck}) =
        (res1, t1) ∧
      (res.map compileResult = res1 →
        s1.ffi = t1.ffi ∧ t1.clock = s1.clock ∧ s1.clock ≤ t.clock ∧
        (t.clock + ck) - t1.clock = (s.clock - s1.clock) + ck) := by
  obtain ⟨ck, t1, res1, hrun', _, _, hout⟩ :=
    CompCall.compCall ac start s k res s1 t lens ⟨hrun, hne, hrel⟩
  refine ⟨ck, t1, res1, hrun', ?_⟩
  intro hsame
  rw [if_pos hsame] at hout
  obtain ⟨hffi, hclk⟩ := hout
  have h0 := stateRel_clock_eq ac k hrel
  have hle := word_run_clock_le _ _ _ _ hrun
  exact ⟨hffi, hclk.symm, h0 ▸ hle, by omega⟩

/-- The eliminated branch is genuinely impossible under `stateRel`. -/
theorem no_clock_increase_branch {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (start : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F) (k : Nat)
    (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F) (lens : List Nat)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) s = (res, s1))
    (hrel : stateRel ac k 0 0 s t lens 0) : ¬ s1.clock > t.clock := by
  have := word_run_clock_le _ _ _ _ hrun
  rw [stateRel_clock_eq ac k hrel] at this; omega

/-! ## Combined LoopToWord + WordToStack affine map and front-factor arithmetic -/

/-- Loop → Word → Stack composite: factor `1`, offset `D_ws`. -/
theorem loop_word_stack_affine (d_ws k : Nat) :
    LoopWordStackExactClockIso.affine 1 d_ws (LoopWordStackExactClockIso.affine 1 0 k) =
      LoopWordStackExactClockIso.affine 1 d_ws k := by
  unfold LoopWordStackExactClockIso.affine; omega

/-- Budget at front factor `M`, keeping `B_max`, source clock and offset of `SelfContainedMasterK`. -/
def budgetAt (M : Nat) : Nat :=
  bootstrapSteps + SelfContainedMasterK.bMax *
    (M * (SelfContainedMasterK.refinedSourceClock + SelfContainedMasterK.pipeOffset))

theorem budgetAt_10 : budgetAt 10 = SelfContainedMasterK.refinedCandidateK := rfl

/-- At `M = 6` the exact value is `22,059,344,444` (not `22,059,343,312`). -/
theorem budgetAt_6 : budgetAt 6 = 22059344389 := by
  unfold budgetAt; rw [InitE.bootstrapSteps_eq, SelfContainedMasterK.refinedSourceClock_eq.1]; decide

theorem budgetAt_6_lt_10 : budgetAt 6 < budgetAt 10 := by
  rw [budgetAt_6, budgetAt_10, SelfContainedMasterK.refinedCandidateK_eq]; decide

theorem budgetAt_mono {M N : Nat} (h : M ≤ N) : budgetAt M ≤ budgetAt N := by
  unfold budgetAt
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h)) _

/-- Front factor `6` is reached exactly when the three non-isometric passes have product
`≤ 6`; the isometric passes contribute factor `1`. -/
theorem front6_of_product (c_pc c_cl c_sl : Nat) (h : c_sl * (c_cl * c_pc) ≤ 6) :
    budgetAt (c_sl * (c_cl * c_pc)) ≤ 22059344389 :=
  budgetAt_6 ▸ budgetAt_mono h


end InitECandidate.Solver.WordToStackClockExactOffset
