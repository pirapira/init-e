import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Assembly
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCall
import InitECandidate.Solver.SelfContainedMasterK

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# Exact clock behaviour of `LoopToWord` and `WordToStack`

* `LoopToWord` is a clock isometry for every program (all constructors at once, via the
  structural `compileCorrect`): equal start clocks, equal end clocks on every non-`timeOut`,
  non-`finalFfi` result, and source `timeOut` ↦ target `timeOut`. So `C_lw = 1, D_lw = 0`.
* `WordToStack` (entry call) is a clock isometry up to an additive entry offset `ck`:
  the stack run starts at `t.clock + ck` and ends at the source end clock. So `C_ws = 1`,
  `D_ws = ck`; `ck` is existential in Flapjack (no numeric bound is proved here).
-/

namespace InitECandidate.Solver.LoopWordStackExactClockIso

open Flapjack
open Flapjack.LoopToWord
open Flapjack.LoopToWord.CompileCorrect
open Flapjack.Compiler.Backend.StackLang
open Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm
open InitE

/-- The `LoopToWord` state relation pins the target clock to the source clock. -/
theorem loopToWord_stateRel_clock {width : Nat} [NeZero width] {C F : Type}
    {s : LoopSemStateFiniteExact width F} {t : WordSemStateFiniteExact width C F}
    (h : loopToWordStateRelHOLExact s t) : t.clock = s.clock := by
  obtain ⟨_, _, _, _, hc, _⟩ := h
  exact hc

/-- Ending clocks agree on every result that carries a state relation. -/
theorem resultCase_clock {width : Nat} [NeZero width] {C F : Type}
    (ctxt : Spt Nat) (retv : WordLocW width) (t : WordSemStateFiniteExact width C F)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F) (res1 : Option (WordSemResult width))
    (t1 : WordSemStateFiniteExact width C F)
    (hrc : resultCase ctxt retv t res s1 res1 t1)
    (hto : res ≠ some .timeOut) (hff : ∀ f, res ≠ some (.finalFfi f)) :
    t1.clock = s1.clock := by
  rcases res with _ | ((v | v | n | n | _ | f | _))
  · exact loopToWord_stateRel_clock hrc.1
  · exact loopToWord_stateRel_clock hrc.1
  · exact loopToWord_stateRel_clock hrc.1
  · exact loopToWord_stateRel_clock hrc.1
  · exact loopToWord_stateRel_clock hrc.1
  · exact absurd rfl hto
  · exact absurd rfl (hff f)
  · exact hrc.elim

/-- `LoopToWord` clock isometry (`C_lw = 1`, `D_lw = 0`) for every `LoopLang` program
(`Seq`, `If`, `Loop`, `Call`, `Tick`, assignments, memory, FFI: one structural statement). -/
theorem loop_to_word_clock_iso {width : Nat} [NeZero width] {C F : Type}
    (prog : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (ctxt : Spt Nat) (retv : WordLocW width) (l : Nat × Nat)
    (hyp : LoopSemStateFiniteExact.evaluate prog s = (res, s1) ∧ res ≠ some .error ∧
        loopToWordStateRelHOLExact s t ∧ LoopToWord.localsRelHOL ctxt s.locals t.locals ∧
        sptLookup 0 t.locals = some retv ∧ goodDimindex width ∧
        ¬ wordSemIsWordLoc retv = true ∧
        (∀ k, sptMem k (accVarsHOL prog .ln) → sptMem k ctxt)) :
    ∃ t1 res1,
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt prog l).1 t = (res1, t1) ∧
      t.clock = s.clock ∧ t1.ffi = s1.ffi ∧
      (res = some .timeOut → res1 = some .timeOut) ∧
      (res ≠ some .timeOut → (∀ f, res ≠ some (.finalFfi f)) →
        t1.clock = s1.clock ∧ t.clock - t1.clock = s.clock - s1.clock) := by
  obtain ⟨t1, res1, hrun, hffi, hrc⟩ := compileCorrect (C := C) prog s res s1 t ctxt retv l hyp
  have h0 := loopToWord_stateRel_clock hyp.2.2.1
  refine ⟨t1, res1, hrun, h0, hffi, ?_, ?_⟩
  · intro h; subst h; exact hrc
  · intro hto hff
    have h1 := resultCase_clock ctxt retv t res s1 res1 t1 hrc hto hff
    exact ⟨h1, by rw [h0, h1]⟩

/-- `LoopToWord` never turns a non-`timeOut` source into a target `timeOut`. -/
theorem loop_to_word_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (ctxt : Spt Nat) (retv : WordLocW width) (t : WordSemStateFiniteExact width C F)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F) (res1 : Option (WordSemResult width))
    (t1 : WordSemStateFiniteExact width C F)
    (hrc : resultCase ctxt retv t res s1 res1 t1) (hto : res ≠ some .timeOut) :
    res1 ≠ some .timeOut := by
  rcases res with _ | ((v | v | n | n | _ | f | _))
  · rw [hrc.2.1]; simp
  · rw [hrc.2.1]; simp
  · intro h
    obtain ⟨u1, u2, hu⟩ := hrc.2.1 (by rw [h]; simp)
    rw [h] at hu; cases hu
  · rw [hrc.2.1]; simp
  · rw [hrc.2.1]; simp
  · exact absurd rfl hto
  · rw [hrc]; simp
  · exact hrc.elim

/-- `WordToStack` entry clock relation: `C_ws = 1`, additive entry offset `ck`.
On agreeing results the stack run started at `t.clock + ck` ends at the word end clock,
so stack ticks consumed = word ticks consumed + `ck`. -/
theorem word_to_stack_clock_affine {width : Nat} [NeZero width] {C F : Type}
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
        s1.ffi = t1.ffi ∧ t1.clock = s1.clock ∧
        (t.clock + ck) - t1.clock = (t.clock - s1.clock) + ck ∨ s1.clock > t.clock) := by
  obtain ⟨ck, t1, res1, hrun', _, _, hout⟩ :=
    CompCall.compCall ac start s k res s1 t lens ⟨hrun, hne, hrel⟩
  refine ⟨ck, t1, res1, hrun', ?_⟩
  intro hsame
  rw [if_pos hsame] at hout
  obtain ⟨hffi, hclk⟩ := hout
  by_cases hle : s1.clock ≤ t.clock
  · exact Or.inl ⟨hffi, hclk.symm, by omega⟩
  · exact Or.inr (by omega)

/-! ## Arithmetic impact on the front factor of `SelfContainedMasterK` -/

/-- Affine clock map of one pass. -/
def affine (c d k : Nat) : Nat := c * k + d

/-- Composition of two affine passes is affine with factor `c₂ * c₁` and offset `c₂ * d₁ + d₂`. -/
theorem affine_comp (c₁ d₁ c₂ d₂ k : Nat) :
    affine c₂ d₂ (affine c₁ d₁ k) = affine (c₂ * c₁) (c₂ * d₁ + d₂) k := by
  unfold affine; rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- An isometric pass (`C = 1, D = 0`) is the identity on clocks. -/
theorem affine_iso (k : Nat) : affine 1 0 k = k := by unfold affine; omega

/-- Inserting `LoopToWord` (`1,0`) and `WordToStack` (`1,d_ws`) leaves the multiplicative
front factor unchanged: it is the product of the remaining pass factors only. -/
theorem front_factor_after_iso (c_pc d_pc c_cl d_cl c_sl d_sl d_ws k : Nat) :
    affine c_sl d_sl (affine 1 d_ws (affine 1 0 (affine c_cl d_cl (affine c_pc d_pc k)))) =
      affine (c_sl * (c_cl * c_pc)) (c_sl * (c_cl * d_pc + d_cl + d_ws) + d_sl) k := by
  unfold affine; ring

/-- Concretely: with the two isometric passes, the front factor `10` of
`SelfContainedMasterK` must be covered by `PanToCrep × CrepToLoop × StackToLab` alone; any
split with product ≤ 108 keeps `refinedCandidateK`-style budget under 400B. -/
theorem iso_front_budget_lt_400B (c_pc c_cl c_sl : Nat) (h : c_sl * (c_cl * c_pc) ≤ 108) :
    bootstrapSteps + SelfContainedMasterK.bMax *
      ((c_sl * (c_cl * c_pc)) * (SelfContainedMasterK.refinedSourceClock +
        SelfContainedMasterK.pipeOffset)) < 400000000000 :=
  (SelfContainedMasterK.front_factor_threshold _).2 h


end InitECandidate.Solver.LoopWordStackExactClockIso
