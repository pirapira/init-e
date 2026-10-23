import InitECandidate.Solver.WordSimpPreservesNoStoreConsts
import Flapjack.Compiler.Backend.WordToWord.Compile

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.WordToWordFullCompileNoStoreConsts

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts
open InitECandidate.Solver.WordSimpPreservesNoStoreConsts

variable {width : Nat} [NeZero width]

/-- Colouring renames registers; it never adds or removes a `storeConsts`. -/
theorem applyColour_NoSt_iff (f : Nat → Nat) :
    ∀ p : WordLangProgHOL (BitVec width), NoSt (Flapjack.WordAlloc.applyColour f p) = NoSt p
  | .seq a b => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NoSt]
      rw [applyColour_NoSt_iff f a, applyColour_NoSt_iff f b]
  | .ite c r ri a b => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NoSt]
      rw [applyColour_NoSt_iff f a, applyColour_NoSt_iff f b]
  | .mustTerminate a => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NoSt]; exact applyColour_NoSt_iff f a
  | .loop x a y => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NoSt]; exact applyColour_NoSt_iff f a
  | .call none d args none => by rw [Flapjack.WordAlloc.applyColour]; rfl
  | .call none d args (some (v, q, l1, l2)) => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NoSt]; rw [applyColour_NoSt_iff f q]
  | .call (some (vs, cs, r, l1, l2)) d args none => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NoSt]; rw [applyColour_NoSt_iff f r]
  | .call (some (vs, cs, r, l1, l2)) d args (some (v, q, m1, m2)) => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NoSt]
      rw [applyColour_NoSt_iff f r, applyColour_NoSt_iff f q]
  | .skip | .move .. | .inst .. | .assign .. | .get .. | .set .. | .store .. | .alloc ..
  | .storeConsts .. | .raise .. | .return .. | .break .. | .continue .. | .tick
  | .opCurrHeap .. | .locValue .. | .install .. | .codeBufferWrite .. | .dataBufferWrite ..
  | .ffi .. | .shareInst .. => by
      rw [Flapjack.WordAlloc.applyColour] <;> first | rfl | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_applyColour (f : Nat → Nat) (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true) :
    NoSt (Flapjack.WordAlloc.applyColour f p) = true := by
  rw [applyColour_NoSt_iff]; exact h

theorem t_oracleColourOk (k : Nat) (co : Option (Spt Nat)) (tree : RegAlloc.ClashTree)
    (p q : WordLangProgHOL (BitVec width)) (forced : List (Nat × Nat)) (h : NoSt p = true)
    (e : Flapjack.WordAlloc.oracleColourOk k co tree p forced = some q) : NoSt q = true := by
  unfold Flapjack.WordAlloc.oracleColourOk at e
  split at e
  · simp at e
  · dsimp only at e
    split at e
    · split at e
      · simp only [Option.some.injEq] at e; subst e; exact t_applyColour _ _ h
      · simp at e
    · simp at e

theorem t_wordAlloc (fc : Nat) (c : AsmConfigExact width) (alg k : Nat)
    (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat)) (h : NoSt p = true) :
    NoSt (Flapjack.WordAlloc.wordAlloc fc c alg k p co) = true := by
  unfold Flapjack.WordAlloc.wordAlloc; dsimp only
  split
  · split
    · exact t_applyColour _ _ h
    · exact h
  · rename_i q e; exact t_oracleColourOk _ _ _ _ _ _ h e

/-- Master: every function body accepted by `fullCompileSingle` with `NoSt` input
yields `NoSt` output (all 11 calls of the HOL pipeline). -/
theorem t_fullCompileSingle (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (nm ac : Nat) (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat))
    (h : NoSt p = true) :
    NoSt (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.2 = true := by
  unfold WordToWord.fullCompileSingle WordToWord.compileSingle; dsimp only
  apply t_removeMustTerminate
  apply t_wordAlloc
  exact t_ssa_cse_mid_tail_chain c _ ac b _ (t_compileExp _ h)

theorem fullCompileSingle_preserves_meta (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (nm ac : Nat) (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat)) :
    (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).1 = nm ∧
    (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.1 = ac := by
  unfold WordToWord.fullCompileSingle WordToWord.compileSingle; exact ⟨rfl, rfl⟩

/-- Unconditional master theorem: LoopToWord output through `fullCompileSingle`. -/
theorem loopToWord_fullCompileSingle_NoSt (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac : Nat)
    (co : Option (Spt Nat)) :
    NoSt (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true :=
  t_fullCompileSingle b rc alg c nm ac _ co (loopToWord_NoSt ctx q l)

theorem loopToWord_fullCompileSingle_allowance_zero (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac : Nat)
    (co : Option (Spt Nat)) :
    storeConstsAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 := by
  simp [storeConstsAllowance, loopToWord_fullCompileSingle_NoSt ctx q l b rc alg c nm ac co]

/-- Whole-program lift over any list of `NoSt` functions. -/
theorem t_fullCompile_list (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (ps : List ((Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)))
    (h : ∀ x ∈ ps, NoSt x.1.2.2 = true) :
    ∀ y ∈ ps.map (WordToWord.fullCompileSingle b rc alg c), NoSt y.2.2 = true := by
  intro y hy
  obtain ⟨⟨⟨nm, ac, p⟩, co⟩, hx, rfl⟩ := List.mem_map.1 hy
  exact t_fullCompileSingle b rc alg c nm ac p co (h _ hx)

/-- Colouring is not a source of `storeConsts` but keeps an existing one. -/
theorem applyColour_keeps_storeConsts (f : Nat → Nat) :
    NoSt (Flapjack.WordAlloc.applyColour f
      (WordLangProgHOL.storeConsts (α := BitVec width) 0 2 4 6 [])) = false := by
  rw [applyColour_NoSt_iff]; rfl

theorem fullCompileSingle_needs_hyp_counterexample :
    NoSt (WordLangProgHOL.mustTerminate (α := BitVec width)
      (.storeConsts 0 2 4 6 [])) = false := rfl


end InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
