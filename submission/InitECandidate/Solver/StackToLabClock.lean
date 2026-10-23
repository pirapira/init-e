import InitECandidate.Solver.StackRemoveToStackNamesStateRelAndClockBridge
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# `InitECandidate.Solver.StackToLabClock` — Quantitative Clocked Simulation for `StackToLab`

Replaces the unbounded existential `∃ ck` in `StackToLab.Proofs.FlattenCorrect.FlattenConcl` and
`FlattenCallCorrect.flattenCallCorrect` with the quantitative bounded simulation relation
`LabSimulationResultB`, tracing the exact `LabSem` tick cost of every `StackToLab.flattenHOL`
constructor and composing with `StackRemoveToStackNamesStateRelAndClockBridge` to obtain the
explicit linear bound `targetLabClock ≤ 4 * source.clock + C`.
-/

namespace InitECandidate.Solver.StackToLabClock

open Flapjack hiding flattenHOL findLabHOL
open Flapjack.Compiler Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCallCorrect
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt)

variable {width : Nat} [NeZero width]

/-! ## 1. Single-Pass `LabSem` Extra-Tick Cost and Code-Table Bound -/

/-- Single-pass (uniterated, uncalled) extra `LabSem` tick cost of a `StackLang` program
under `StackToLab.flattenHOL`. Every leaf constructor has `stepCost ≤ 2 ≤ 3`. -/
def stepCost : HolProg width → Nat
  | .skip => 0
  | .halt _ => 1
  | .inst _ => 1
  | .tick => 1
  | .ret _ => 1
  | .raise _ => 1
  | .break _ => 1
  | .continue _ => 0
  | .locValue _ _ _ => 1
  | .codeBufferWrite _ _ => 1
  | .ffi _ _ _ _ _ _ => 2
  | .install _ _ _ _ _ => 2
  | .shMemOp _ _ _ => 0
  | .seq c1 c2 => stepCost c1 + stepCost c2
  | .ite _ _ _ c1 c2 => 2 + stepCost c1 + stepCost c2
  | .loop body => stepCost body
  | .jumpLower _ _ _ => 1
  | .rawCall _ => 0
  | .call none _ _ => 0
  | .call (some (rp, _, _, _)) _ none => 2 + stepCost rp
  | .call (some (rp, _, _, _)) _ (some (hp, _, _)) => 2 + stepCost rp + stepCost hp
  | _ => 0

/-- `StackNames.progCompHOL` is a pure register renaming and preserves `stepCost` identically. -/
theorem stepCost_progCompHOL (names : Spt Nat) :
    ∀ (p : HolProg width), stepCost (StackNames.progCompHOL names p) = stepCost p
  | .skip => rfl
  | .halt _ => rfl
  | .inst _ => rfl
  | .tick => rfl
  | .ret _ => rfl
  | .raise _ => rfl
  | .break _ => rfl
  | .continue _ => rfl
  | .locValue _ _ _ => rfl
  | .codeBufferWrite _ _ => rfl
  | .ffi _ _ _ _ _ _ => rfl
  | .install _ _ _ _ _ => rfl
  | .shMemOp _ _ (.addr _ _) => rfl
  | .seq c1 c2 => by
      simp only [StackNames.progCompHOL, stepCost,
        stepCost_progCompHOL names c1, stepCost_progCompHOL names c2]
  | .ite _ _ _ c1 c2 => by
      simp only [StackNames.progCompHOL, stepCost,
        stepCost_progCompHOL names c1, stepCost_progCompHOL names c2]
  | .loop body => by
      simp only [StackNames.progCompHOL, stepCost, stepCost_progCompHOL names body]
  | .jumpLower _ _ _ => rfl
  | .rawCall _ => rfl
  | .call none _ none => rfl
  | .call none _ (some (_, _, _)) => rfl
  | .call (some (rp, _, _, _)) _ none => by
      simp only [StackNames.progCompHOL, stepCost, stepCost_progCompHOL names rp]
  | .call (some (rp, _, _, _)) _ (some (hp, _, _)) => by
      simp only [StackNames.progCompHOL, stepCost,
        stepCost_progCompHOL names rp, stepCost_progCompHOL names hp]
  | .get _ _ | .set _ _ | .opCurrHeap _ _ _ | .alloc _ | .storeConsts _ _ _
  | .stackAlloc _ | .stackFree _ | .stackStore _ _ | .stackStoreAny _ _
  | .stackLoad _ _ | .stackLoadAny _ _ | .stackGetSize _ | .stackSetSize _
  | .bitmapLoad _ _ | .dataBufferWrite _ _ => rfl
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

/-- State invariant: every installed procedure in `s.code` and every installable oracle entry
in `s.compileOracle` has single-pass extra `LabSem` cost at most `M`. -/
def CodeStepBounded {C F : Type} (M : Nat) (s : StackSemStateFiniteExact width C F) : Prop :=
  (∀ k p, sptLookup k s.code = some p → stepCost p ≤ M) ∧
  (∀ i, ∀ e ∈ (s.compileOracle i).2.1, stepCost e.2 ≤ M)

/-- `CodeStepBounded M` is preserved by every `StackSemEvaluate.evaluate` transition
(including `.install`), via Flapjack's `evaluateCodeBitmaps` evolution law. -/
theorem codeStepBounded_evaluate {C F : Type} (M : Nat)
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (run : StackSemEvaluate.evaluate (program, source) = (result, post))
    (h : CodeStepBounded M source) : CodeStepBounded M post := by
  obtain ⟨count, hor, hcode, _⟩ :=
    StackProps.EvaluateCodeBitmaps.evaluateCodeBitmaps program source result post run
  refine ⟨fun k p hk => ?_, fun i e he => ?_⟩
  · rw [hcode] at hk
    rcases lookup_foldl_sptUnion k p _ _ hk with h0 | ⟨t, ht, hl⟩
    · exact h.1 k p h0
    · rcases List.mem_map.1 ht with ⟨idx, _, rfl⟩
      rw [sptLookup_sptFromAList] at hl
      exact h.2 idx (k, p) (sptAListLookup_mem _ _ _ hl)
  · rw [hor] at he
    exact h.2 (i + count) e he

/-- `CodeStepBounded` is monotonic in the bound `M`. -/
theorem CodeStepBounded.mono {C F : Type} {M1 M2 : Nat}
    {s : StackSemStateFiniteExact width C F} (hle : M1 ≤ M2) (h : CodeStepBounded M1 s) :
    CodeStepBounded M2 s :=
  ⟨fun k p hk => Nat.le_trans (h.1 k p hk) hle,
   fun i e he => Nat.le_trans (h.2 i e he) hle⟩

/-- `StackNames.renameState` preserves `CodeStepBounded M` because `progCompHOL` preserves `stepCost`. -/
theorem codeStepBounded_renameState {C F : Type} (M : Nat)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (f : Spt Nat)
    (s : StackSemStateFiniteExact width C F) (h : CodeStepBounded M s) :
    CodeStepBounded M (StackNames.renameState c f s) := by
  refine ⟨fun k p hk => ?_, fun i e he => ?_⟩
  · simp only [StackNames.renameState] at hk
    rw [Flapjack.sptLookup_sptFromAList, StackNames.sptAListLookup_compileHOL,
      ← Flapjack.sptLookup_sptFromAList, Flapjack.sptLookup_sptFromAList_sptToAList] at hk
    rcases hp0 : sptLookup k s.code with _ | p0
    · rw [hp0] at hk; simp at hk
    · rw [hp0] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      subst hk
      rw [stepCost_progCompHOL]
      exact h.1 k p0 hp0
  · have he' : e ∈ List.map (StackNames.progCompEntryHOL f) (s.compileOracle i).2.1 := he
    rcases List.mem_map.mp he' with ⟨e0, he0, rfl⟩
    simp only [StackNames.progCompEntryHOL, stepCost_progCompHOL]
    exact h.2 i e0 he0

/-- Telescoping identity for clock differences across sequential composition. -/
theorem telescope_clock_mul {a b c M : Nat} (h1 : c ≤ b) (h2 : b ≤ a) :
    (a - b) * M + (b - c) * M = (a - c) * M := by
  rw [← Nat.add_mul, show a - b + (b - c) = a - c by omega]

/-- Telescoping inequality across a `decClock` step (`b ≠ 0`, `c ≤ b - 1`, `b ≤ a`, `d ≤ M`). -/
theorem telescope_decClock_mul {a b c d M : Nat} (hb : b ≠ 0) (h1 : c ≤ b - 1) (h2 : b ≤ a)
    (hd : d ≤ M) :
    (a - b) * M + d + (b - 1 - c) * M ≤ (a - c) * M := by
  have h3 : (a - b) * M + 1 * M + (b - 1 - c) * M = (a - c) * M := by
    rw [← Nat.add_mul, ← Nat.add_mul, show a - b + 1 + (b - 1 - c) = a - c by omega]
  omega

/-- Entry of a returning call with the `sptLookup d s1.code = some prog` witness exposed. -/
theorem callEnter_with_lookup {C F : Type} {s1 : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {link l1 l2 : Nat}
    {dest : Nat ⊕ Nat} {prog : HolProg width} (rel : stateRel s1 t1) (h0 : s1.clock ≠ 0)
    (fetchA : asmFetchAux t1.pc t1.code =
      some (.labAsm (.locValue link (.lab l1 l2)) 0 [] 0))
    (fetchB : asmFetchAux (t1.pc + 1) t1.code = some (compileJumpHOL dest))
    (locL : locToPc l1 l2 t1.code = some (t1.pc + 2))
    (hfind : StackSemControl.findCode dest (s1.regs.eraseEq link) s1.code = some prog) :
    ∃ (d pc' : Nat) (tE : Flapjack.Compiler.Backend.LabSem.State width C F),
      sptLookup d s1.code = some prog ∧
      (∀ ck1, evaluate { t1 with clock := t1.clock + 1 + ck1 } =
        evaluate { tE with clock := tE.clock + ck1 }) ∧
      tE.lenReg = t1.lenReg ∧ tE.ptrReg = t1.ptrReg ∧ tE.len2Reg = t1.len2Reg ∧
      tE.ptr2Reg = t1.ptr2Reg ∧ tE.linkReg = t1.linkReg ∧ tE.code = t1.code ∧ tE.pc = pc' ∧
      stateRel (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) s1)) tE ∧
      locToPc d 0 t1.code = some pc' ∧
      StackProps.callArgs prog t1.ptrReg t1.lenReg t1.ptr2Reg t1.len2Reg t1.linkReg ∧
      codeInstalled pc' (appListAppend (flattenHOL true prog d
        (StackAlloc.nextLabHOL prog 2) [] []).1) t1.code := by
  have clk := relClock rel
  let tB : Flapjack.Compiler.Backend.LabSem.State width C F :=
    { t1 with
      regs := fun key => if key = link then .loc l1 l2 else t1.regs key
      pc := t1.pc + 1 }
  have relB : stateRel (StackSemStateOps.setVar link (.loc l1 l2) s1) tB :=
    StateRel.setVarUpdReg rel
  have hregs : ∀ r v, (s1.regs.eraseEq link).lookup r = some v → tB.regs r = v := by
    intro r v h
    simp only [HolFiniteMapExact.eraseEq, Flapjack.FDOMSUB_HOL] at h
    split_ifs at h with e
    simp only [tB, e, if_false]
    exact InstCorrect.regOfLookup rel h
  obtain ⟨d, pc', hlook, entry, caP, instP, stepB⟩ :=
    compileJumpEnter (t1 := tB) (s := StackSemStateOps.setVar link (.loc l1 l2) s1) hregs relB
      fetchB hfind
  refine ⟨d, pc', { tB with pc := pc', clock := t1.clock - 1 }, hlook, fun ck1 => ?_, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, StateRel.stateRelDecClock relB, entry, caP, instP⟩
  rw [show t1.clock + 1 + ck1 = (t1.clock - 1 + ck1 + 1) + 1 by omega,
    locValueStep _ fetchA locL]
  exact stepB (t1.clock - 1 + ck1)

/-! ## 2. Clocked Simulation Relations `LabSimAt` and `LabSimulationResultB` -/

/-- Exact clocked simulation witness at a concrete extra clock `ck` for `StackToLab.flattenHOL`.
This is the matrix of `FlattenConcl` at an explicit `ck`. -/
def LabSimAt {C F : Type}
    (prog : HolProg width) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : Flapjack.Compiler.Backend.LabSem.State width C F) (ck : Nat) : Prop :=
  ∃ (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
    match haltView r with
    | some res => evaluate { t1 with clock := t1.clock + ck } = (res, t2) ∧ t2.ffi = s2.ffi
    | none =>
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      match r.map (fun w => resultView w n cs bs) with
      | none =>
        t2.pc = t1.pc + ((appListAppend (flattenHOL t prog n l cs bs).1).filter
          (fun x => !isLabelHOL x)).length ∧ stateRel s2 t2
      | some (.vloc n1 n2) =>
        (∀ k, (sptLookup k s2.code).isSome → (locToPc k 0 t2.code).isSome) ∧
          ∀ w, locToPc n1 n2 t2.code = some w → w = t2.pc ∧ stateRel s2 t2
      | some (.vcont n1 n2) =>
        stateRel s2 t2 ∧ codeInstalled t2.pc [.labAsm (.jump (.lab n1 n2)) 0 [] 0] t2.code
      | some .vtimeout => t2.ffi = s2.ffi ∧ t2.clock = 0
      | some .verr => False

/-- Bounded clocked simulation result `LabSimulationResultB`: replaces the unbounded existential
`∃ ck` of `FlattenConcl` with an explicit upper bound `ck ≤ bound` on the extra `LabSem` ticks. -/
def LabSimulationResultB {C F : Type}
    (prog : HolProg width) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : Flapjack.Compiler.Backend.LabSem.State width C F) (bound : Nat) : Prop :=
  ∃ ck ≤ bound, LabSimAt prog t r s2 n l cs bs t1 ck

theorem LabSimulationResultB.of_at {C F : Type}
    {prog : HolProg width} {t : Bool} {r : Option (StackSemResult width)}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {ck bound : Nat}
    (hck : ck ≤ bound) (h : LabSimAt prog t r s2 n l cs bs t1 ck) :
    LabSimulationResultB prog t r s2 n l cs bs t1 bound :=
  ⟨ck, hck, h⟩

theorem LabSimulationResultB.mono {C F : Type}
    {prog : HolProg width} {t : Bool} {r : Option (StackSemResult width)}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {b1 b2 : Nat}
    (hle : b1 ≤ b2) (h : LabSimulationResultB prog t r s2 n l cs bs t1 b1) :
    LabSimulationResultB prog t r s2 n l cs bs t1 b2 := by
  obtain ⟨ck, hck, hsim⟩ := h
  exact ⟨ck, Nat.le_trans hck hle, hsim⟩

theorem LabSimulationResultB.toFlattenConcl {C F : Type}
    {prog : HolProg width} {t : Bool} {r : Option (StackSemResult width)}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {bound : Nat}
    (h : LabSimulationResultB prog t r s2 n l cs bs t1 bound) :
    FlattenConcl prog t r s2 n l cs bs t1 := by
  obtain ⟨ck, _, hsim⟩ := h
  exact ⟨ck, hsim⟩

/-! ## 3. Structural Composition Combinators for `LabSimAt` and `LabSimulationResultB` -/

section Combinators
variable {C F : Type}

theorem labSimAt_stay {prog : HolProg width} {t : Bool}
    {s : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (rel : stateRel s t1)
    (empty : ((appListAppend (flattenHOL t prog n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length = 0) :
    LabSimAt prog t none s n l cs bs t1 0 := by
  refine ⟨t1, ?_⟩
  simp only [haltView, Option.map_none, true_and]
  exact ⟨fun ck1 => by simp, List.prefix_refl _, by omega, rel⟩

theorem labSimAt_some {p p' : HolProg width} {t t' : Bool} {x : StackSemResult width}
    {s2 : StackSemStateFiniteExact width C F} {n l l' : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {ck : Nat}
    (h : LabSimAt p t (some x) s2 n l cs bs t1 ck) :
    LabSimAt p' t' (some x) s2 n l' cs bs t1 ck := by
  obtain ⟨t2, h⟩ := h
  refine ⟨t2, ?_⟩
  revert h
  cases haltView (some x) with
  | some res => exact id
  | none =>
    simp only [Option.map_some]
    cases resultView x n cs bs <;> exact id

theorem labSimB_some {p p' : HolProg width} {t t' : Bool} {x : StackSemResult width}
    {s2 : StackSemStateFiniteExact width C F} {n l l' : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {b : Nat}
    (h : LabSimulationResultB p t (some x) s2 n l cs bs t1 b) :
    LabSimulationResultB p' t' (some x) s2 n l' cs bs t1 b := by
  obtain ⟨ck, hck, hsim⟩ := h
  exact ⟨ck, hck, labSimAt_some hsim⟩

theorem labSimAt_result {p p' : HolProg width} {t t' : Bool} {x y : StackSemResult width}
    {s2 : StackSemStateFiniteExact width C F} {n n' l l' : Nat} {cs bs cs' bs' : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {ck : Nat}
    (hh : haltView (some x) = haltView (some y))
    (hr : resultView x n cs bs = resultView y n' cs' bs')
    (h : LabSimAt p t (some x) s2 n l cs bs t1 ck) :
    LabSimAt p' t' (some y) s2 n' l' cs' bs' t1 ck := by
  obtain ⟨t2, h⟩ := h
  refine ⟨t2, ?_⟩
  revert h
  rw [hh]
  cases haltView (some y) with
  | some res => exact id
  | none =>
    simp only [Option.map_some, hr]
    cases resultView y n' cs' bs' <;> exact id

theorem labSimB_result {p p' : HolProg width} {t t' : Bool} {x y : StackSemResult width}
    {s2 : StackSemStateFiniteExact width C F} {n n' l l' : Nat} {cs bs cs' bs' : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {b : Nat}
    (hh : haltView (some x) = haltView (some y))
    (hr : resultView x n cs bs = resultView y n' cs' bs')
    (h : LabSimulationResultB p t (some x) s2 n l cs bs t1 b) :
    LabSimulationResultB p' t' (some y) s2 n' l' cs' bs' t1 b := by
  obtain ⟨ck, hck, hsim⟩ := h
  exact ⟨ck, hck, labSimAt_result hh hr hsim⟩

theorem labSimAt_compose {p p' : HolProg width} {t t' : Bool}
    {r : Option (StackSemResult width)} {s2 : StackSemStateFiniteExact width C F}
    {n l l' : Nat} {cs bs : List Nat} {ck ck' : Nat}
    {t1 t2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (run : ∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
      evaluate { t2 with clock := t2.clock + ck1 })
    (e1 : t2.lenReg = t1.lenReg) (e2 : t2.ptrReg = t1.ptrReg) (e3 : t2.len2Reg = t1.len2Reg)
    (e4 : t2.ptr2Reg = t1.ptr2Reg) (e5 : t2.linkReg = t1.linkReg) (pre : t1.code <+: t2.code)
    (hlen : t1.pc + ((appListAppend (flattenHOL t p n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length =
      t2.pc + ((appListAppend (flattenHOL t' p' n l' cs bs).1).filter
        (fun x => !isLabelHOL x)).length)
    (h : LabSimAt p' t' r s2 n l' cs bs t2 ck') :
    LabSimAt p t r s2 n l cs bs t1 (ck + ck') := by
  obtain ⟨t3, h⟩ := h
  refine ⟨t3, ?_⟩
  revert h
  cases haltView r with
  | some res =>
    rintro ⟨ev, ffi⟩
    exact ⟨by rw [← Nat.add_assoc, run ck', ev], ffi⟩
  | none =>
    rintro ⟨run2, f1, f2, f3, f4, f5, pre2, rest⟩
    refine ⟨fun ck1 => ?_, by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], by rw [f4, e4],
      by rw [f5, e5], pre.trans pre2, ?_⟩
    · rw [show t1.clock + (ck + ck') + ck1 = t1.clock + ck + (ck' + ck1) by omega, run,
        ← run2 ck1, Nat.add_assoc]
    · revert rest
      cases r.map (fun w => resultView w n cs bs) with
      | none => rintro ⟨hpc, rel⟩; exact ⟨by omega, rel⟩
      | some v => cases v <;> exact id

theorem labSimB_compose {p p' : HolProg width} {t t' : Bool}
    {r : Option (StackSemResult width)} {s2 : StackSemStateFiniteExact width C F}
    {n l l' : Nat} {cs bs : List Nat} {ck b : Nat}
    {t1 t2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (run : ∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
      evaluate { t2 with clock := t2.clock + ck1 })
    (e1 : t2.lenReg = t1.lenReg) (e2 : t2.ptrReg = t1.ptrReg) (e3 : t2.len2Reg = t1.len2Reg)
    (e4 : t2.ptr2Reg = t1.ptr2Reg) (e5 : t2.linkReg = t1.linkReg) (pre : t1.code <+: t2.code)
    (hlen : t1.pc + ((appListAppend (flattenHOL t p n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length =
      t2.pc + ((appListAppend (flattenHOL t' p' n l' cs bs).1).filter
        (fun x => !isLabelHOL x)).length)
    (h : LabSimulationResultB p' t' r s2 n l' cs bs t2 b) :
    LabSimulationResultB p t r s2 n l cs bs t1 (ck + b) := by
  obtain ⟨ck', hck', hsim⟩ := h
  exact ⟨ck + ck', by omega, labSimAt_compose run e1 e2 e3 e4 e5 pre hlen hsim⟩

theorem labSimAt_composeSome {p p' : HolProg width} {t t' : Bool}
    {x : StackSemResult width} {s2 : StackSemStateFiniteExact width C F}
    {n l l' : Nat} {cs bs : List Nat} {ck ck' : Nat}
    {t1 t2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (run : ∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
      evaluate { t2 with clock := t2.clock + ck1 })
    (e1 : t2.lenReg = t1.lenReg) (e2 : t2.ptrReg = t1.ptrReg) (e3 : t2.len2Reg = t1.len2Reg)
    (e4 : t2.ptr2Reg = t1.ptr2Reg) (e5 : t2.linkReg = t1.linkReg) (pre : t1.code <+: t2.code)
    (h : LabSimAt p' t' (some x) s2 n l' cs bs t2 ck') :
    LabSimAt p t (some x) s2 n l cs bs t1 (ck + ck') := by
  obtain ⟨t3, h⟩ := h
  refine ⟨t3, ?_⟩
  revert h
  cases haltView (some x) with
  | some res =>
    rintro ⟨ev, ffi⟩
    exact ⟨by rw [← Nat.add_assoc, run ck', ev], ffi⟩
  | none =>
    rintro ⟨run2, f1, f2, f3, f4, f5, pre2, rest⟩
    refine ⟨fun ck1 => ?_, by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], by rw [f4, e4],
      by rw [f5, e5], pre.trans pre2, ?_⟩
    · rw [show t1.clock + (ck + ck') + ck1 = t1.clock + ck + (ck' + ck1) by omega, run,
        ← run2 ck1, Nat.add_assoc]
    · revert rest
      simp only [Option.map_some]
      cases resultView x n cs bs <;> exact id

theorem labSimB_composeSome {p p' : HolProg width} {t t' : Bool}
    {x : StackSemResult width} {s2 : StackSemStateFiniteExact width C F}
    {n l l' : Nat} {cs bs : List Nat} {ck b : Nat}
    {t1 t2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (run : ∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
      evaluate { t2 with clock := t2.clock + ck1 })
    (e1 : t2.lenReg = t1.lenReg) (e2 : t2.ptrReg = t1.ptrReg) (e3 : t2.len2Reg = t1.len2Reg)
    (e4 : t2.ptr2Reg = t1.ptr2Reg) (e5 : t2.linkReg = t1.linkReg) (pre : t1.code <+: t2.code)
    (h : LabSimulationResultB p' t' (some x) s2 n l' cs bs t2 b) :
    LabSimulationResultB p t (some x) s2 n l cs bs t1 (ck + b) := by
  obtain ⟨ck', hck', hsim⟩ := h
  exact ⟨ck + ck', by omega, labSimAt_composeSome run e1 e2 e3 e4 e5 pre hsim⟩

theorem labSimB_none {p : HolProg width} {t : Bool} {s2 : StackSemStateFiniteExact width C F}
    {n l : Nat} {cs bs : List Nat} {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    {b : Nat} (h : LabSimulationResultB p t none s2 n l cs bs t1 b) :
    ∃ ck ≤ b, ∃ (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      t2.pc = t1.pc + ((appListAppend (flattenHOL t p n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length ∧ stateRel s2 t2 := h

theorem labSimB_vloc {p : HolProg width} {t : Bool} {x : StackSemResult width}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {n1 n2 b : Nat}
    (hh : haltView (some x) = none) (hr : resultView x n cs bs = .vloc n1 n2)
    (h : LabSimulationResultB p t (some x) s2 n l cs bs t1 b) :
    ∃ ck ≤ b, ∃ (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      ∀ w, locToPc n1 n2 t2.code = some w → w = t2.pc ∧ stateRel s2 t2 := by
  obtain ⟨ck, hck, t2, h⟩ := h
  refine ⟨ck, hck, t2, ?_⟩
  revert h
  rw [hh]
  simp only [Option.map_some, hr]
  rintro ⟨a, b0, c, d, e, f, g, -, w⟩
  exact ⟨a, b0, c, d, e, f, g, w⟩

end Combinators

/-! ## 4. Exact Leaf Clock Simulation (`≤ 2 ≤ 3` `LabSem` Ticks per `StackSem` Step) -/

section LeavesB
variable {C F : Type}

/-- `Skip` leaf: `0` extra `LabSem` ticks (`ck = 0 ≤ 3`). -/
theorem flattenCorrectSkipB
    (s1 : StackSemStateFiniteExact width C F) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.skip : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.skip : HolProg width) t r s2 n l cs bs t1 0 := by
  obtain ⟨ev, -, rel, -, -, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_skip] at ev
  cases ev
  exact ⟨0, Nat.le_refl 0, labSimAt_stay rel (by simp [flattenHOL, appListAppendList])⟩

/-- `Halt` leaf: `1` extra `LabSem` tick (`ck = 1 ≤ 3`). -/
theorem flattenCorrectHaltB
    (s1 : StackSemStateFiniteExact width C F) (v : Nat) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.halt v : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.halt v : HolProg width) t r s2 n l cs bs t1 1 := by
  obtain ⟨ev, nerr, rel, ca, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_halt] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.labAsm .halt 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  simp only [StackProps.callArgs] at ca
  split at ev
  · rename_i w hw
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have hreg : t1.regs t1.ptrReg = w := by
      rw [← ca]; exact InstCorrect.regOfLookup rel hw
    refine ⟨1, Nat.le_refl 1, { t1 with clock := t1.clock + 1 }, ?_, ?_⟩
    · rw [evaluate]
      simp only [Nat.add_one_ne_zero, if_false, asmFetch, fetch, hreg]
      cases w with
      | word value =>
        by_cases hv : value = 0#width <;> simp [haltWordView, hv]
      | loc a b => simp [haltWordView]
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Inst` leaf: `1` extra `LabSem` tick (`ck = 1 ≤ 3`). -/
theorem flattenCorrectInstB
    (s1 : StackSemStateFiniteExact width C F) (i : HolInst width) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.inst i : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.inst i : HolProg width) t r s2 n l cs bs t1 1 := by
  obtain ⟨ev, nerr, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_inst] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.inst i)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  split at ev
  · rename_i s1' hi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have rel2 := InstCorrect.instCorrect ⟨hi, rel⟩
    obtain ⟨cpc, ccode, cclock, -, -, -, -, -, cptr, clen, cptr2, clen2, clink⟩ :=
      asmInstConsts i t1
    have nf := InstCorrect.notFailed rel2
    refine ⟨1, Nat.le_refl 1, incPc (asmInst i t1), fun ck1 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rel2⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch,
        LabProps.asmInstWithClock, nf, Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock, cclock, cpc]
      congr 1 <;> first | omega | exact nf.symm
    all_goals simp [incPc, cptr, clen, cptr2, clen2, clink, ccode, cpc, flattenHOL,
      appListAppendList, isLabelHOL]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Tick` leaf: `0` extra `LabSem` ticks when `s1.clock ≠ 0` (the 1 `LabSem` skip instruction
is matched 1:1 by `decClock`), and `1` extra tick on timeout (`s1.clock = 0`). -/
theorem flattenCorrectTickB
    (s1 : StackSemStateFiniteExact width C F) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.tick : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.tick : HolProg width) t r s2 n l cs bs t1
      (if s1.clock = 0 then 1 else 0) := by
  obtain ⟨ev, nerr, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_tick] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.inst .skip)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  have nf := InstCorrect.notFailed rel
  have clk := relClock rel
  split_ifs at ev with h0
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    rw [if_pos h0]
    refine ⟨1, Nat.le_refl 1, incPc t1, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, ?_, ?_⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, asmInst, nf,
        Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock]
      congr 1 <;> first | omega | exact nf.symm
    · simp [incPc, StackSemStateOps.emptyEnv, relFfi rel]
    · simp [incPc]; omega
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    rw [if_neg h0]
    refine ⟨0, Nat.le_refl 0, incPc (decClock t1), fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, ?_, StateRel.stateRelDecClock rel⟩
    · rw [evaluate]
      simp only [show t1.clock + 0 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, asmInst, nf,
        Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock]
      congr 1 <;> first | omega | exact nf.symm
    · simp [incPc, decClock, flattenHOL, appListAppendList, isLabelHOL]

/-- Shared register-jump step of `Return` and `Raise` with explicit extra clock `ck = 1`. -/
theorem jumpRegLocB {p : HolProg width} {t : Bool} {x : StackSemResult width}
    {s : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    {n l : Nat} {cs bs : List Nat} {reg l1 l2 : Nat}
    (hh : haltView (some x) = none) (hr : resultView x n cs bs = .vloc l1 l2)
    (rel : stateRel s t1)
    (fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg reg)) [] 0))
    (hreg : t1.regs reg = .loc l1 l2) :
    LabSimulationResultB p t (some x) s n l cs bs t1 1 := by
  refine ⟨1, Nat.le_refl 1, ?_⟩
  unfold LabSimAt
  rw [hh]
  simp only [Option.map_some, hr]
  cases hpc : locToPc l1 l2 t1.code with
  | none =>
    refine ⟨{ t1 with clock := t1.clock + 1 }, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, fun k hk => codeLookupLocToPc rel k hk, ?_⟩
    · simp only [Nat.add_assoc]
    · intro w hw; simp [hpc] at hw
  | some pc =>
    refine ⟨updPc pc t1, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
      codeLookupLocToPc rel, fun w hw => ?_⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, hreg, hpc]
      congr 1
      simp only [updPc, decClock]
      congr 1
      omega
    · simp only [updPc] at hw ⊢
      rw [hpc] at hw
      exact ⟨(Option.some.inj hw).symm, rel⟩

/-- `Return` leaf: `1` extra `LabSem` tick (`ck = 1 ≤ 3`). -/
theorem flattenCorrectRetB
    (s1 : StackSemStateFiniteExact width C F) (v : Nat) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.ret v : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.ret v : HolProg width) t r s2 n l cs bs t1 1 := by
  obtain ⟨ev, nerr, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_ret] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg v)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  split at ev
  · rename_i l1 l2 hv
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    exact jumpRegLocB rfl rfl rel fetch (InstCorrect.regOfLookup rel hv)
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Raise` leaf: `1` extra `LabSem` tick (`ck = 1 ≤ 3`). -/
theorem flattenCorrectRaiseB
    (s1 : StackSemStateFiniteExact width C F) (v : Nat) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.raise v : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.raise v : HolProg width) t r s2 n l cs bs t1 1 := by
  obtain ⟨ev, nerr, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_raise] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg v)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  split at ev
  · rename_i l1 l2 hv
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    exact jumpRegLocB rfl rfl rel fetch (InstCorrect.regOfLookup rel hv)
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Break` leaf: `1` extra `LabSem` tick (`ck = 1 ≤ 3`). -/
theorem flattenCorrectBreakB
    (s1 : StackSemStateFiniteExact width C F) (k : Nat) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.break k : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.break k : HolProg width) t r s2 n l cs bs t1 1 := by
  obtain ⟨ev, -, rel, -, inst, labs⟩ := hyps
  rw [StackSemEvaluate.evaluate_break] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.jump (.lab n (findLabHOL k bs))) 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  have some_ : (locToPc n (findLabHOL k bs) t1.code).isSome := by
    by_cases hm : findLabHOL k bs ∈ bs
    · exact labs _ (by simp [hm])
    · rw [notMemFindLabImp bs k hm]; exact labs 0 (by simp)
  obtain ⟨pc, hpc⟩ := Option.isSome_iff_exists.mp some_
  refine ⟨1, Nat.le_refl 1, updPc pc t1, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
    List.prefix_refl _, codeLookupLocToPc rel, fun w hw => ?_⟩
  · rw [evaluate]
    simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, getPcValue, hpc]
    congr 1
    simp only [updPc, decClock]
    congr 1
    omega
  · simp only [updPc] at hw ⊢
    rw [hpc] at hw
    exact ⟨(Option.some.inj hw).symm, rel⟩

/-- `LocValue` leaf: `1` extra `LabSem` tick (`ck = 1 ≤ 3`). -/
theorem flattenCorrectLocValueB
    (s1 : StackSemStateFiniteExact width C F) (reg l1 l2 : Nat) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.locValue reg l1 l2 : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.locValue reg l1 l2 : HolProg width) t r s2 n l cs bs t1 1 := by
  obtain ⟨ev, nerr, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_locValue] at ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.locValue reg (.lab l1 l2)) 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  split_ifs at ev with check
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    obtain ⟨pc, hpc⟩ := StateRel.locCheckImpLocToPc ⟨check, rel⟩
    refine ⟨1, Nat.le_refl 1, incPc (updReg reg (.loc l1 l2) t1), fun ck1 => ?_,
      rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, StateRel.setVarUpdReg rel⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, getPcValue,
        hpc, reduceCtorEq]
      congr 1
      simp only [incPc, decClock, updReg, labToLoc]
      congr 1
      omega
    · simp [incPc, updReg, flattenHOL, appListAppendList, isLabelHOL]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `CodeBufferWrite` leaf: `1` extra `LabSem` tick (`ck = 1 ≤ 3`). -/
theorem flattenCorrectCodeBufferWriteB
    (s1 : StackSemStateFiniteExact width C F) (r1 r2 : Nat) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.codeBufferWrite r1 r2 : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.codeBufferWrite r1 r2 : HolProg width) t r s2 n l cs bs t1 1 := by
  obtain ⟨ev, nerr, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_codeBufferWrite] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.cbw r1 r2) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  have cbEq : s1.codeBuffer = t1.codeBuffer := rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  split at ev
  · rename_i w1 w2 h1 h2
    split at ev
    · rename_i cb hcb
      simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨1, Nat.le_refl 1, incPc { t1 with codeBuffer := cb }, fun ck1 => ?_,
        rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, stateRelWithCodeBuffer rel cb⟩
      · rw [evaluate]
        simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch,
          InstCorrect.regOfLookup rel h1, InstCorrect.regOfLookup rel h2, ← cbEq, hcb]
        congr 1
        simp only [incPc, decClock]
        congr 1
        omega
      · simp [incPc, flattenHOL, appListAppendList, isLabelHOL]
    · simp only [Prod.mk.injEq] at ev
      exact absurd ev.1.symm nerr
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Continue` leaf: `0` extra `LabSem` ticks (`ck = 0 ≤ 3`). -/
theorem flattenCorrectContinueB
    (s1 : StackSemStateFiniteExact width C F) (k : Nat) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.continue k : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.continue k : HolProg width) t r s2 n l cs bs t1 0 := by
  obtain ⟨ev, -, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_continue] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  refine ⟨0, Nat.le_refl 0, t1, fun ck1 => rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
    rel, ?_⟩
  simpa [flattenHOL, appListAppendList] using inst

/-- `FFI` leaf: `2` extra `LabSem` ticks (`locValue` + `callFFI`, `ck = 2 ≤ 3`). -/
theorem flattenCorrectFfiB
    (s1 : StackSemStateFiniteExact width C F) (f : Basis.Pure.MlString.MlString)
    (ptr len ptr2 len2 ret : Nat) (t : Bool) (r : Option (StackSemResult width))
    (s2 : StackSemStateFiniteExact width C F) (n l : Nat) (cs bs : List Nat)
    (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.ffi f ptr len ptr2 len2 ret : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.ffi f ptr len ptr2 len2 ret : HolProg width) t r s2 n l cs bs t1 2 := by
  obtain ⟨ev, nerr, rel, ca, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_ffi] at ev
  simp only [StackProps.callArgs] at ca
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ca
  have hinst : codeInstalled t1.pc [.labAsm (.locValue t1.linkReg (.lab n l)) 0 [] 0,
      .labAsm (.callFFI f) 0 [] 0, .label n l 0] t1.code := by
    simpa [flattenHOL, appListAppendList] using inst
  simp only [isLabelHOL, Bool.false_eq_true, if_false, if_true, codeInstalled] at hinst
  obtain ⟨fetch0, fetch1, locL, -⟩ := hinst
  obtain ⟨-, -, hmem, hdom, -, hbe, hffiEq, hclk, -, -, -, hnf, d13, d14, d15, d16, -⟩ := id rel
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  split at ev
  · rename_i w w2 w3 w4 hlen hptr hlen2 hptr2
    have rlen := InstCorrect.regOfLookup rel hlen
    have rptr := InstCorrect.regOfLookup rel hptr
    have rlen2 := InstCorrect.regOfLookup rel hlen2
    have rptr2 := InstCorrect.regOfLookup rel hptr2
    split at ev
    · rename_i cfg bytes hcfg hbytes
      rw [← hmem, ← hdom, ← hbe] at hcfg hbytes
      have step : ∀ c, evaluate { t1 with clock := c + 2 } =
          match callFFIHOL t1.ffi (.extCall f) cfg bytes with
          | .final outcome => (.halt (.ffiOutcome outcome),
              incPc (decClock (updReg t1.linkReg (.loc n l) { t1 with clock := c + 2 })))
          | .ret newFfi returned => evaluate { t1 with
              memory := writeBytearrayExact w4 returned t1.memory t1.memDomain t1.be
              ffi := newFfi
              ioRegs := holShiftSeq 1 t1.ioRegs
              ioFpRegs := holShiftSeq 1 t1.ioFpRegs
              regs := fun r => getRegValue (t1.ioRegs 0 (.extCall f) r)
                ((fun x => if x = t1.linkReg then WordLocW.loc n l else t1.regs x) r)
                WordLocW.word
              fpRegs := fun r => t1.ioFpRegs 0 r
              pc := t1.pc + 2
              clock := c } := by
        intro c
        rw [evaluate]
        simp only [show c + 2 ≠ 0 by omega, if_false, asmFetch, fetch0, getPcValue, locL,
          reduceCtorEq]
        rw [evaluate]
        simp only [incPc, decClock, updReg, labToLoc, show c + 2 - 1 ≠ 0 by omega, if_false,
          asmFetch, fetch1, Ne.symm d13, Ne.symm d14, Ne.symm d15, Ne.symm d16, if_true,
          rlen, rptr, rlen2, rptr2, hcfg, hbytes, locL]
        cases callFFIHOL t1.ffi (.extCall f) cfg bytes with
        | final o => rfl
        | ret newFfi returned => simp only; congr 1
      rw [← hffiEq] at ev
      split at ev
      · rename_i outcome hffi
        simp only [Prod.mk.injEq] at ev
        obtain ⟨rfl, rfl⟩ := ev
        refine ⟨2, Nat.le_refl 2, incPc (decClock (updReg t1.linkReg (.loc n l)
          { t1 with clock := t1.clock + 2 })), ?_, ?_⟩
        · rw [step, hffi]
        · simp [incPc, decClock, updReg, hffiEq]
      · rename_i newFfi returned hffi
        simp only [Prod.mk.injEq] at ev
        obtain ⟨rfl, rfl⟩ := ev
        refine ⟨2, Nat.le_refl 2, { t1 with
              memory := writeBytearrayExact w4 returned t1.memory t1.memDomain t1.be
              ffi := newFfi
              ioRegs := holShiftSeq 1 t1.ioRegs
              ioFpRegs := holShiftSeq 1 t1.ioFpRegs
              regs := fun r => getRegValue (t1.ioRegs 0 (.extCall f) r)
                ((fun x => if x = t1.linkReg then WordLocW.loc n l else t1.regs x) r)
                WordLocW.word
              fpRegs := fun r => t1.ioFpRegs 0 r
              pc := t1.pc + 2 }, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
          ?_, ?_⟩
        · rw [show t1.clock + 2 + ck1 = (t1.clock + ck1) + 2 by omega, step, hffi]
        · simp [flattenHOL, appListAppendList, isLabelHOL]
        · have := stateRelFfiRet rel f t1.linkReg rfl (.loc n l)
            (writeBytearrayExact w4 returned t1.memory t1.memDomain t1.be) newFfi (t1.pc + 2)
          simpa [hmem, hdom, hbe] using this
    · exact (err ev).elim
  · exact (err ev).elim

/-- `Install` leaf: `2` extra `LabSem` ticks (`locValue` + `install`, `ck = 2 ≤ 3`). -/
theorem flattenCorrectInstallB
    (s1 : StackSemStateFiniteExact width C F) (ptr len dptr dlen ret : Nat) (t : Bool)
    (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.install ptr len dptr dlen ret : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.install ptr len dptr dlen ret : HolProg width) t r s2 n l cs bs t1 2 := by
  obtain ⟨ev, nerr, rel, ca, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_install] at ev
  simp only [StackProps.callArgs] at ca
  obtain ⟨rfl, rfl, rfl⟩ := ca
  have hinst : codeInstalled t1.pc [.labAsm (.locValue t1.linkReg (.lab n l)) 0 [] 0,
      .labAsm .install 0 [] 0, .label n l 0] t1.code := by
    simpa [flattenHOL, appListAppendList] using inst
  obtain ⟨fetch0, i2⟩ := lineAt rfl hinst
  obtain ⟨fetch1, i3⟩ := lineAt rfl i2
  obtain ⟨locL, -⟩ := labelAt i3
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, d13, d14, -, -, -, -, -, -, -, h22, h23, h24, -⟩ :=
    id rel
  have hus := (relNoStack rel).1
  rcases hx : StackSemStateOps.getVar t1.ptrReg s1 with _ | ⟨w1 | ⟨_, _⟩⟩ <;>
    rcases hy : StackSemStateOps.getVar t1.lenReg s1 with _ | ⟨w2 | ⟨_, _⟩⟩ <;>
    rcases hz : StackSemStateOps.getVar dptr s1 with _ | ⟨w3 | ⟨_, _⟩⟩ <;>
    rcases hw : StackSemStateOps.getVar dlen s1 with _ | ⟨w4 | ⟨_, _⟩⟩ <;>
    simp only [hx, hy, hz, hw] at ev <;> try exact (err ev).elim
  rcases ho : s1.compileOracle 0 with ⟨cfg, progs, bm⟩
  have hprogs : (s1.compileOracle 0).2.1 = progs := by rw [ho]
  simp only [ho, hus, Bool.false_eq_true, if_false] at ev
  rcases hfl : wordSemBufferFlush s1.codeBuffer w1 w2 with _ | ⟨bytes, cb⟩
  · simp only [hfl] at ev; exact (err ev).elim
  simp only [hfl] at ev
  rcases hc : s1.compile cfg progs with _ | ⟨bytes', cfg'⟩
  · simp only [hc] at ev; exact (err ev).elim
  simp only [hc] at ev
  rcases hpr : progs with _ | ⟨⟨k, p0⟩, rest⟩
  · rw [hpr] at ev; exact (err ev).elim
  rw [hpr] at ev
  simp only at ev
  split at ev
  swap; · exact (err ev).elim
  rename_i hv
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  rw [← hpr]
  have ho' : t1.compileOracle 0 = (cfg, progs.map progToSectionHOL) := by
    rw [h24]; simp [ho]
  have hc' : t1.compile cfg (progs.map progToSectionHOL) = some (bytes, cfg') := by
    have := congrFun (congrFun h23 cfg) progs
    rw [← this, hc, hv.1]
  have hcfg : (t1.compileOracle 1).1 = cfg' := by
    rw [h24]; simpa [holShiftSeq] using hv.2.2
  have hmap : progs.map progToSectionHOL = ⟨k, (progToSectionHOL (k, p0)).lines⟩ ::
      rest.map progToSectionHOL := by
    rw [hpr]; simp [progToSection_eq]
  refine ⟨2, Nat.le_refl 2, { t1 with
      pc := t1.pc + 1 + 1
      codeBuffer := cb
      code := t1.code ++ progs.map progToSectionHOL
      ccRegs := holShiftSeq 1 t1.ccRegs
      ccFpRegs := holShiftSeq 1 t1.ccFpRegs
      regs := fun r => if r = t1.ptrReg then .loc k 0 else
        getRegValue (t1.ccRegs 0 r) (if r = t1.linkReg then .loc n l else t1.regs r)
          WordLocW.word
      fpRegs := fun r => t1.ccFpRegs 0 r
      compileOracle := holShiftSeq 1 t1.compileOracle }, fun ck1 => ?_, rfl, rfl, rfl, rfl,
    rfl, List.prefix_append _ _, ?_, ?_⟩
  · rw [show t1.clock + 2 + ck1 = (t1.clock + ck1 + 1) + 1 by omega, locValueStep _ fetch0 locL]
    refine (installStep (t := { t1 with
        regs := fun key => if key = t1.linkReg then .loc n l else t1.regs key
        pc := t1.pc + 1 }) (w1 := w1) (w2 := w2) (t1.clock + ck1) fetch1
      (by simp [Ne.symm d14, InstCorrect.regOfLookup rel hx])
      (by simp [Ne.symm d13, InstCorrect.regOfLookup rel hy])
      (by simp) (by simpa [← h22] using hfl) locL ho' hc' hmap hcfg).trans ?_
    rfl
  · simp [flattenHOL, appListAppendList, isLabelHOL]
  · rw [hpr] at hprogs
    have := stateRelInstall rel hprogs bm cb s1.dataBuffer k n l (t1.pc + 1 + 1)
    rw [← hpr] at this
    rwa [hus] at this

private theorem shMemLoadSimB {s1 : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {op : HolMemop} {reg a : Nat}
    {w addr : BitVec width} {k : Nat} {t : Bool} {r : Option (StackSemResult width)}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    (rel : stateRel s1 t1)
    (fetch : asmFetchAux t1.pc t1.code = some (.asm (.shareMem op reg (.addr a w)) [] 0))
    (cnz : t1.clock ≠ 0) (haddr : addrValue (.addr a w) t1 = some addr)
    (hop : ∀ c, shareMemOp op reg (.addr a w) { t1 with clock := c } =
      shareMemLoad reg (.addr a w) { t1 with clock := c } k)
    (hdom : (if k = 0 then addr.toNat % (width / 8) == 0 && t1.sharedMemDomain addr
      else t1.sharedMemDomain (riscvByteAlignHOL addr)) = true)
    (hlen : ((appListAppend (flattenHOL t (.shMemOp op reg (.addr a w)) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length = 1)
    (ev : (match callFFIHOL (StackSemStateOps.decClock s1).ffi (.sharedMem .mappedRead)
        [BitVec.ofNat 8 k] (panWordToBytesHOL addr false) with
      | .final outcome => (some (.finalFFI outcome), StackSemStateOps.decClock s1)
      | .ret newFfi newBytes => (none, { StackSemStateOps.decClock s1 with
          regs := (StackSemStateOps.decClock s1).regs.updateEq
            (reg, .word (panWordOfBytesHOL false 0 newBytes))
          ffi := newFfi })) = (r, s2)) :
    LabSimulationResultB (.shMemOp op reg (.addr a w) : HolProg width) t r s2 n l cs bs t1 0 := by
  have ffiEq := relFfi rel
  have lab : ∀ c, shareMemLoad reg (.addr a w) { t1 with clock := c } k =
      match callFFIHOL t1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 k]
          (sharedMemoryWordBytes addr) with
      | .final outcome => some (.final outcome, { t1 with clock := c })
      | .ret f bytes => some (.ret f bytes, { t1 with
          clock := c - 1
          ffi := f
          regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r
          pc := t1.pc + 1 }) := by
    intro c
    simp only [shareMemLoad]
    rw [show addrValue (.addr a w) { t1 with clock := c } = some addr from haddr]
    simp only [hdom, if_true]
    cases callFFIHOL t1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 k]
      (sharedMemoryWordBytes addr) <;> rfl
  rw [panWordToBytes_eq_shared,
    show (StackSemStateOps.decClock s1).ffi = t1.ffi from ffiEq.symm] at ev
  split at ev
  · rename_i outcome hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, Nat.le_refl 0, { t1 with clock := t1.clock + 0 }, ?_, ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 }) (res := .final outcome)
        (t' := { t1 with clock := t1.clock + 0 }) (by simpa using cnz) fetch]
      rw [hop, lab, hffi]
    · simp [ffiEq, StackSemStateOps.decClock]
  · rename_i ffi' bytes hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, Nat.le_refl 0, { t1 with
        ffi := ffi'
        regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r
        pc := t1.pc + 1
        clock := t1.clock - 1
        ioRegs := holShiftSeq 1 t1.ioRegs
        ioFpRegs := holShiftSeq 1 t1.ioFpRegs }, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, by simp [hlen], ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 + ck1 })
        (res := .ret ffi' bytes)
        (t' := { t1 with
          clock := t1.clock + 0 + ck1 - 1
          ffi := ffi'
          regs := fun r => if r = reg then .word (wordOfBytesHOL8 false 0 bytes) else t1.regs r
          pc := t1.pc + 1 }) (by simp; omega) fetch]
      · dsimp only
        congr 1
        simp only [Flapjack.Compiler.Backend.LabSem.State.mk.injEq, and_true, true_and]
        omega
      · rw [hop, lab, hffi]
    · have := stateRelShMemRet rel ffi' (t1.pc + 1)
        (some (reg, .word (wordOfBytesHOL8 false 0 bytes)))
      simpa [panWordOfBytes_eq_wordOfBytesHOL8, StackSemStateOps.decClock] using this

private theorem shMemStoreSimB {s1 : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {op : HolMemop} {reg a : Nat}
    {w addr v : BitVec width} {k : Nat} {t : Bool} {r : Option (StackSemResult width)}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {payload : List (BitVec 8)}
    (rel : stateRel s1 t1)
    (fetch : asmFetchAux t1.pc t1.code = some (.asm (.shareMem op reg (.addr a w)) [] 0))
    (cnz : t1.clock ≠ 0) (haddr : addrValue (.addr a w) t1 = some addr)
    (hv : t1.regs reg = .word v)
    (hop : ∀ c, shareMemOp op reg (.addr a w) { t1 with clock := c } =
      shareMemStore reg (.addr a w) { t1 with clock := c } k)
    (hdom : (if k = 0 then addr.toNat % (width / 8) == 0 && t1.sharedMemDomain addr
      else t1.sharedMemDomain (riscvByteAlignHOL addr)) = true)
    (hpay : payload = (if k = 0 then sharedMemoryWordBytes v
      else (sharedMemoryWordBytes v).take k) ++ sharedMemoryWordBytes addr)
    (hlen : ((appListAppend (flattenHOL t (.shMemOp op reg (.addr a w)) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length = 1)
    (ev : (match callFFIHOL (StackSemStateOps.decClock s1).ffi (.sharedMem .mappedWrite)
        [BitVec.ofNat 8 k] payload with
      | .final outcome => (some (.finalFFI outcome), StackSemStateOps.decClock s1)
      | .ret newFfi _ => (none, { StackSemStateOps.decClock s1 with ffi := newFfi })) =
        (r, s2)) :
    LabSimulationResultB (.shMemOp op reg (.addr a w) : HolProg width) t r s2 n l cs bs t1 0 := by
  have ffiEq := relFfi rel
  have lab : ∀ c, shareMemStore reg (.addr a w) { t1 with clock := c } k =
      match callFFIHOL t1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 k] payload with
      | .final outcome => some (.final outcome, { t1 with clock := c })
      | .ret f bytes => some (.ret f bytes, { t1 with
          clock := c - 1
          ffi := f
          pc := t1.pc + 1 }) := by
    intro c
    simp only [shareMemStore]
    rw [show ({ t1 with clock := c } : Flapjack.Compiler.Backend.LabSem.State width C F).regs reg
      = .word v from hv]
    simp only
    rw [show addrValue (.addr a w) { t1 with clock := c } = some addr from haddr]
    simp only [hdom, if_true, ← hpay]
    cases callFFIHOL t1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 k] payload <;> rfl
  rw [show (StackSemStateOps.decClock s1).ffi = t1.ffi from ffiEq.symm] at ev
  split at ev
  · rename_i outcome hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, Nat.le_refl 0, { t1 with clock := t1.clock + 0 }, ?_, ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 }) (res := .final outcome)
        (t' := { t1 with clock := t1.clock + 0 }) (by simpa using cnz) fetch]
      rw [hop, lab, hffi]
    · simp [ffiEq, StackSemStateOps.decClock]
  · rename_i ffi' bytes hffi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, Nat.le_refl 0, { t1 with
        ffi := ffi'
        pc := t1.pc + 1
        clock := t1.clock - 1
        ioRegs := holShiftSeq 1 t1.ioRegs
        ioFpRegs := holShiftSeq 1 t1.ioFpRegs }, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, by simp [hlen], ?_⟩
    · rw [evaluateShareMemStep (t := { t1 with clock := t1.clock + 0 + ck1 })
        (res := .ret ffi' bytes)
        (t' := { t1 with clock := t1.clock + 0 + ck1 - 1, ffi := ffi', pc := t1.pc + 1 })
        (by simp; omega) fetch]
      · dsimp only
        congr 1
        simp only [Flapjack.Compiler.Backend.LabSem.State.mk.injEq, and_true, true_and]
        omega
      · rw [hop, lab, hffi]
    · have := stateRelShMemRet rel ffi' (t1.pc + 1) none
      simpa [StackSemStateOps.decClock] using this

/-- `ShMemOp` leaf: `0` extra `LabSem` ticks (`ck = 0 ≤ 3`, 1:1 with `decClock`). -/
theorem flattenCorrectShMemOpB
    (s1 : StackSemStateFiniteExact width C F) (op : HolMemop) (reg a : Nat) (w : BitVec width)
    (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps (.shMemOp op reg (.addr a w) : HolProg width) s1 t r s2 n l cs bs t1) :
    LabSimulationResultB (.shMemOp op reg (.addr a w) : HolProg width) t r s2 n l cs bs t1 0 := by
  obtain ⟨ev, nerr, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_shMemOp] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.shareMem op reg (.addr a w)) [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  have clk := relClock rel
  have ffiEq := relFfi rel
  split at ev
  · rename_i addr hexp
    have haddr : addrValue (.addr a w) t1 = some addr := InstCorrect.addrOfWordExp rel hexp
    split_ifs at ev with h0
    · simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨0, Nat.le_refl 0, t1, fun ck1 => by simp, rfl, rfl, rfl, rfl, rfl,
        List.prefix_refl _, ?_, ?_⟩
      · simp [StackSemStateOps.emptyEnv, ffiEq]
      · omega
    · have cnz : t1.clock ≠ 0 := by omega
      have hlen : ((appListAppend (flattenHOL t (.shMemOp op reg (.addr a w)) n l cs bs).1).filter
          (fun x => !isLabelHOL x)).length = 1 := by
        simp [flattenHOL, appListAppendList, isLabelHOL]
      have good : goodDimindex width := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, g⟩ := rel
        exact g
      have pos : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
      have err : ∀ {x : StackSemStateFiniteExact width C F},
          (some StackSemResult.error, x) = (r, s2) → False := fun e => by
        simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
      cases op
      case load =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad] at ev
        split_ifs at ev with dom
        · exact shMemLoadSimB (k := 0) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom, relShAligned rel dom]) hlen ev
        · exact (err ev).elim
      case load8 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoadByte] at ev
        split_ifs at ev with dom
        · exact shMemLoadSimB (k := 1) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) hlen ev
        · exact (err ev).elim
      case load16 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad16] at ev
        split_ifs at ev with dom
        · exact shMemLoadSimB (k := 2) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) hlen ev
        · exact (err ev).elim
      case load32 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad32] at ev
        split_ifs at ev with dom
        · exact shMemLoadSimB (k := 4) rel fetch cnz haddr (fun c => rfl)
            (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom]) hlen ev
        · exact (err ev).elim
      case store =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSimB (k := 0) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom, relShAligned rel dom])
              (by simp [panWordToBytes_eq_shared]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
      case store8 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStoreByte] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSimB (k := 1) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom])
              (by simp [panWordToBytes_eq_shared, sharedBytesTakeOne v pos]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
      case store16 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore16] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSimB (k := 2) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom])
              (by simp [panWordToBytes_eq_shared]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
      case store32 =>
        simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore32] at ev
        split at ev
        · rename_i v hv
          split_ifs at ev with dom
          · exact shMemStoreSimB (k := 4) rel fetch cnz haddr (InstCorrect.regOfLookup rel hv)
              (fun c => rfl) (by simp only [StackSemStateOps.decClock] at dom; simp [relShMdomain rel, dom])
              (by simp [panWordToBytes_eq_shared]) hlen ev
          · exact (err ev).elim
        · exact (err ev).elim
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- Guarded leaves (`Get`, `Set`, `OpCurrHeap`, `Alloc`, `StoreConsts`, stack-frame operations,
`BitmapLoad`, `DataBufferWrite`) return `some .error` under `stateRel`, so `LabSimulationResultB`
holds at bound `0`. -/
private theorem guardedB {prog : HolProg width} {s1 : StackSemStateFiniteExact width C F}
    (h : ∀ (t : Flapjack.Compiler.Backend.LabSem.State width C F), stateRel s1 t →
      (StackSemEvaluate.evaluate (prog, s1)).1 = some .error)
    (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hyps : FlattenHyps prog s1 t r s2 n l cs bs t1) :
    LabSimulationResultB prog t r s2 n l cs bs t1 0 := by
  obtain ⟨ev, nerr, rel, -⟩ := hyps
  have := h t1 rel
  rw [ev] at this
  exact absurd this nerr

end LeavesB

/-! ## 5. Control-Flow & Call Constructors (`Seq`, `If`, `Loop`, `JumpLower`, `RawCall`, `Call`) -/

section ControlAndCallsB
variable {C F : Type}

/-- `Seq c1 c2`: exact additivity of extra `LabSem` clocks (`b1 + b2`). -/
theorem flattenCorrectSeqB_add
    (s1 : StackSemStateFiniteExact width C F) (c1 c2 : HolProg width)
    (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (b1 b2 : Nat)
    (hyps : FlattenHyps (.seq c1 c2) s1 t r s2 n l cs bs t1)
    (ih1 : ∀ r1 s1',
      FlattenHyps c1 s1 false r1 s1' n l cs bs t1 →
      LabSimulationResultB c1 false r1 s1' n l cs bs t1 b1)
    (ih2 : ∀ s1' t2,
      StackSemEvaluate.evaluate (c1, s1) = (none, s1') →
      FlattenHyps c2 s1' false r s2 n (flattenHOL false c1 n l cs bs).2.2 cs bs t2 →
      LabSimulationResultB c2 false r s2 n (flattenHOL false c1 n l cs bs).2.2 cs bs t2 b2) :
    LabSimulationResultB (.seq c1 c2) t r s2 n l cs bs t1 (b1 + b2) := by
  obtain ⟨ev, nerr, rel, ca, inst, labs⟩ := hyps
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at ev
  simp only [StackProps.callArgs] at ca
  rcases h1 : flattenHOL false c1 n l cs bs with ⟨xs, nr1, l1⟩
  rcases h2 : flattenHOL false c2 n l1 cs bs with ⟨ys, nr2, l2⟩
  have hflat : appListAppend (flattenHOL t (.seq c1 c2) n l cs bs).1 =
      appListAppend xs ++ ((if t then [.label n 1 0] else []) ++ appListAppend ys) := by
    rw [flattenHOL]
    cases t <;> simp [h1, h2, appListAppendAppend, appListAppendList]
  rw [hflat] at inst
  obtain ⟨instXs, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst
  have instYs : codeInstalled (t1.pc + ((appListAppend xs).filter
      (fun x => !isLabelHOL x)).length) (appListAppend ys) t1.code := by
    cases t
    · simpa using instRest
    · simp only [if_true, List.singleton_append, codeInstalled_cons, isLabelHOL] at instRest
      exact instRest.2
  have lenFlat : ((appListAppend (flattenHOL t (.seq c1 c2) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length =
      ((appListAppend xs).filter (fun x => !isLabelHOL x)).length +
        ((appListAppend ys).filter (fun x => !isLabelHOL x)).length := by
    rw [hflat]; cases t <;> simp [List.filter_append, isLabelHOL]
  rcases e1 : StackSemEvaluate.evaluate (c1, s1) with ⟨r1, s1'⟩
  rw [e1] at ev
  cases r1 with
  | some x =>
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have c1h := ih1 (some x) s1' ⟨e1, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩
    exact (labSimB_some c1h).mono (by omega)
  | none =>
    simp only at ev
    have c1h := ih1 none s1' ⟨e1, by simp, rel, ca.1, by rw [h1]; exact instXs, labs⟩
    obtain ⟨ck1, hck1, t2, run, f1, f2, f3, f4, f5, pre, hpc, rel2⟩ := labSimB_none c1h
    rw [h1] at hpc
    have c2h : LabSimulationResultB c2 false r s2 n l1 cs bs t2 b2 := by
      have := ih2 s1' t2 e1
      rw [h1] at this
      exact this (flattenHypsMid ev nerr rel2 ca.2 f1 f2 f3 f4 f5 pre
        (by rw [h2, hpc]; exact instYs) labs)
    refine (labSimB_compose run f1 f2 f3 f4 f5 pre ?_ c2h).mono (by omega)
    simp only [lenFlat, hpc, h2]
    omega

/-- `If cmp reg ri c1 c2`: conditional jump + optional join jump adds at most `2` ticks (`+ 1` or `+ 2`)
to the taken branch's clock bound (`b_branch + 2`). -/
theorem flattenCorrectIfB_branch
    (s1 : StackSemStateFiniteExact width C F) (cmp : HolCmp) (reg : Nat)
    (ri : HolRegImm width) (c1 c2 : HolProg width)
    (t : Bool) (res : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (b1 b2 : Nat)
    (hyps : FlattenHyps (.ite cmp reg ri c1 c2) s1 t res s2 n l cs bs t1)
    (ih1 : ∀ t1',
      FlattenHyps c1 s1 false res s2 n l cs bs t1' →
      LabSimulationResultB c1 false res s2 n l cs bs t1' b1)
    (ih2 : ∀ t1',
      FlattenHyps c2 s1 false res s2 n (flattenHOL false c1 n l cs bs).2.2 cs bs t1' →
      LabSimulationResultB c2 false res s2 n (flattenHOL false c1 n l cs bs).2.2 cs bs t1' b2) :
    LabSimulationResultB (.ite cmp reg ri c1 c2) t res s2 n l cs bs t1 (2 + max b1 b2) := by
  obtain ⟨ev, nerr, rel, ca, inst, labs⟩ := hyps
  rw [StackSemEvaluate.evaluate_ite] at ev
  simp only [StackProps.callArgs] at ca
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (res, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  split at ev
  swap; · exact (err ev).elim
  rename_i x y hx hy
  have rx : t1.regs reg = x := InstCorrect.regOfLookup rel hx
  have ry : regImm ri t1 = y := StateRel.stateRelGetVarImm ⟨rel, hy⟩
  rcases hc : wordSemWordCmp cmp x y with _ | b
  · rw [hc] at ev; exact (err ev).elim
  have hcmp : wordSemWordCmp cmp (t1.regs reg) (regImm ri t1) = some b := by rw [rx, ry, hc]
  have hneg : wordSemWordCmp (negateHOL cmp) (t1.regs reg) (regImm ri t1) = some (!b) := by
    rw [Prelude.wordCmpNegate, hcmp]; rfl
  have evb : StackSemEvaluate.evaluate (if b then c1 else c2, s1) = (res, s2) := by
    rw [hc] at ev; cases b <;> exact ev
  rcases h1 : flattenHOL false c1 n l cs bs with ⟨xs, nr1, l1⟩
  rcases h2 : flattenHOL false c2 n l1 cs bs with ⟨ys, nr2, l2⟩
  have ih2' : ∀ t1',
      FlattenHyps c2 s1 false res s2 n l1 cs bs t1' →
      LabSimulationResultB c2 false res s2 n l1 cs bs t1' b2 := by
    intro t1' h; have := ih2 t1'; rw [h1] at this; exact this h
  have unfold := (show flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs =
      flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs from rfl)
  conv at unfold => rhs; rw [flattenHOL]
  simp only [h1, h2] at unfold
  have nolab : ∀ (a : AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString),
      isLabelHOL (Line.labAsm a 0 [] 0 : LabLineHOL width) = false := fun _ => rfl
  have hlenOf : ∀ (L : List (LabLineHOL width)),
      appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 = L →
      ((appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length = (L.filter (fun x => !isLabelHOL x)).length :=
    fun L h => by rw [h]
  split_ifs at unfold with k1 k2 k3 k4 k5
  · -- both branches `Skip`
    simp only [Bool.and_eq_true] at k1
    rw [isSkipEq k1.1, isSkipEq k1.2] at evb
    have : (if b then (StackLang.Prog.skip : HolProg width) else .skip) = .skip := by cases b <;> rfl
    rw [this, StackSemEvaluate.evaluate_skip] at evb
    simp only [Prod.mk.injEq] at evb
    obtain ⟨rfl, rfl⟩ := evb
    exact ⟨0, by omega, labSimAt_stay rel (by rw [unfold]; simp [appListAppendList])⟩
  · -- then-branch `Skip`
    have hflat : appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp cmp reg ri (.lab n l2)) 0 [] 0 :: (appListAppend ys ++
          [.label n l2 0]) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instYs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, -⟩ := labelAt instLab
    cases b
    · have step := fun c => (jumpCmpStep (b := false) c fetch0 hcmp)
      simp only [Bool.false_eq_true, if_false] at step
      refine (labSimB_compose (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) ?_
        (ih2' { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩)).mono (by omega)
      rw [hlenOf _ hflat, h2]
      simp [List.filter_append, isLabelHOL]
      omega
    · simp only [if_true] at evb
      rw [isSkipEq k2, StackSemEvaluate.evaluate_skip] at evb
      simp only [Prod.mk.injEq] at evb
      obtain ⟨rfl, rfl⟩ := evb
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hcmp)
      simp only [if_true, locL] at step
      refine ⟨1, by omega, { t1 with pc := t1.pc + 1 + ((appListAppend ys).filter
          (fun x => !isLabelHOL x)).length }, runToPc step, rfl, rfl, rfl, rfl, rfl,
        List.prefix_refl _, ?_, rel⟩
      rw [hlenOf _ hflat]
      simp [List.filter_append, isLabelHOL]
      omega
  · -- else-branch `Skip`
    have hflat : appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp (negateHOL cmp) reg ri (.lab n l2)) 0 [] 0 :: (appListAppend xs ++
          [.label n l2 0]) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instXs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, -⟩ := labelAt instLab
    cases b
    · simp only [Bool.false_eq_true, if_false] at evb
      rw [isSkipEq k3, StackSemEvaluate.evaluate_skip] at evb
      simp only [Prod.mk.injEq] at evb
      obtain ⟨rfl, rfl⟩ := evb
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hneg)
      simp only [if_true, locL] at step
      refine ⟨1, by omega, { t1 with pc := t1.pc + 1 + ((appListAppend xs).filter
          (fun x => !isLabelHOL x)).length }, runToPc step, rfl, rfl, rfl, rfl, rfl,
        List.prefix_refl _, ?_, rel⟩
      rw [hlenOf _ hflat]
      simp [List.filter_append, isLabelHOL]
      omega
    · have step := fun c => (jumpCmpStep (b := false) c fetch0 hneg)
      simp only [Bool.false_eq_true, if_false] at step
      refine (labSimB_compose (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) ?_
        (ih1 { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)).mono (by omega)
      rw [hlenOf _ hflat, h1]
      simp [List.filter_append, isLabelHOL]
      omega
  · -- then-branch never returns: placed first
    have hflat : appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp (negateHOL cmp) reg ri (.lab n l2)) 0 [] 0 :: (appListAppend xs ++
          (.label n l2 0 :: appListAppend ys)) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instXs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, instYs⟩ := labelAt instLab
    cases b
    · have step := fun c => (jumpCmpStep (b := true) c fetch0 hneg)
      simp only [if_true, locL] at step
      refine (labSimB_compose (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) ?_
        (ih2' _ ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩)).mono (by omega)
      rw [hlenOf _ hflat, h2]
      simp [List.filter_append, isLabelHOL]
      omega
    · have some_ := FlattenHelpers.noRetCorrect false c1 n l cs bs (by rw [h1]; exact k4) s1
      simp only [if_true] at evb
      rw [evb] at some_
      obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp some_
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hneg)
      simp only [Bool.false_eq_true, if_false] at step
      exact (labSimB_composeSome (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _)
        (ih1 { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)).mono (by omega)
  · -- else-branch never returns: placed first
    have hflat : appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp cmp reg ri (.lab n l2)) 0 [] 0 :: (appListAppend ys ++
          (.label n l2 0 :: appListAppend xs)) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instYs, instLab⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨locL, instXs⟩ := labelAt instLab
    cases b
    · have some_ := FlattenHelpers.noRetCorrect false c2 n l1 cs bs (by rw [h2]; exact k5) s1
      simp only [Bool.false_eq_true, if_false] at evb
      rw [evb] at some_
      obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.mp some_
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hcmp)
      simp only [Bool.false_eq_true, if_false] at step
      exact (labSimB_composeSome (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _)
        (ih2' { t1 with pc := t1.pc + 1 }
          ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩)).mono (by omega)
    · have step := fun c => (jumpCmpStep (b := true) c fetch0 hcmp)
      simp only [if_true, locL] at step
      refine (labSimB_compose (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) ?_
        (ih1 _ ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)).mono (by omega)
      rw [hlenOf _ hflat, h1]
      simp [List.filter_append, isLabelHOL]
      omega
  · -- general shape with a join jump
    have hflat : appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1 =
        .labAsm (.jumpCmp cmp reg ri (.lab n l2)) 0 [] 0 :: (appListAppend ys ++
          (.labAsm (.jump (.lab n (l2 + 1))) 0 [] 0 :: .label n l2 0 ::
            (appListAppend xs ++ [.label n (l2 + 1) 0]))) := by
      rw [unfold]; simp [appListAppendAppend, appListAppendList]
    rw [hflat] at inst
    obtain ⟨fetch0, instRest⟩ := lineAt (nolab _) inst
    obtain ⟨instYs, instRest2⟩ := codeInstalledAppendImp _ _ _ _ instRest
    obtain ⟨fetchJ, instRest3⟩ := lineAt (nolab _) instRest2
    obtain ⟨locL, instRest4⟩ := labelAt instRest3
    obtain ⟨instXs, instLab2⟩ := codeInstalledAppendImp _ _ _ _ instRest4
    obtain ⟨locL2, -⟩ := labelAt instLab2
    have total : ((appListAppend (flattenHOL t (.ite cmp reg ri c1 c2) n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length =
        ((appListAppend ys).filter (fun x => !isLabelHOL x)).length +
          ((appListAppend xs).filter (fun x => !isLabelHOL x)).length + 2 := by
      rw [hflat]; simp [List.filter_append, isLabelHOL]; omega
    cases b
    · simp only [Bool.false_eq_true, if_false] at evb
      have step := fun c => (jumpCmpStep (b := false) c fetch0 hcmp)
      simp only [Bool.false_eq_true, if_false] at step
      have c2h := ih2' { t1 with pc := t1.pc + 1 }
        ⟨evb, nerr, rel, ca.2, by rw [h2]; exact instYs, labs⟩
      cases res with
      | some x =>
        exact (labSimB_composeSome (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _)
          c2h).mono (by omega)
      | none =>
        obtain ⟨ck2, hck2, t3, run2, f1, f2, f3, f4, f5, pre2, hpc2, rel3⟩ := labSimB_none c2h
        rw [h2] at hpc2
        simp only at hpc2 f1 f2 f3 f4 f5 pre2
        have fetchJ3 : asmFetchAux t3.pc t3.code =
            some (.labAsm (.jump (.lab n (l2 + 1))) 0 [] 0) := by
          rw [hpc2]; exact asmFetchAuxSomeIsPrefix _ _ _ _ ⟨fetchJ, pre2⟩
        have locL23 := locToPcIsPrefix _ _ _ _ _ ⟨locL2, pre2⟩
        refine ⟨1 + ck2 + 1, by omega, { t3 with pc := t1.pc + 1 +
            ((appListAppend ys).filter (fun x => !isLabelHOL x)).length + 1 +
            ((appListAppend xs).filter (fun x => !isLabelHOL x)).length },
          fun ck1 => ?_, f1, f2, f3, f4, f5, pre2, ?_, rel3⟩
        · rw [show t1.clock + (1 + ck2 + 1) + ck1 = t1.clock + 1 + (ck2 + (ck1 + 1)) by omega,
            runToPc step, show t1.clock + (ck2 + (ck1 + 1)) = t1.clock + ck2 + (ck1 + 1) by omega,
            run2, show t3.clock + (ck1 + 1) = (t3.clock + ck1) + 1 by omega,
            jumpStep (t3.clock + ck1) fetchJ3 locL23]
        · simp only [total]; omega
    · simp only [if_true] at evb
      have step := fun c => (jumpCmpStep (b := true) c fetch0 hcmp)
      simp only [if_true, locL] at step
      refine (labSimB_compose (runToPc step) rfl rfl rfl rfl rfl (List.prefix_refl _) ?_
        (ih1 _ ⟨evb, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩)).mono (by omega)
      rw [total, h1]
      simp
      omega

/-- Loop re-entry helper with explicit clock bound `b`. -/
theorem loopReentryB {body : HolProg width} {s1' : StackSemStateFiniteExact width C F}
    {res : Option (StackSemResult width)} {n l l1 : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    {xs : AppList (LabLineHOL width)} {nr : Bool} {b : Nat}
    (h1 : flattenHOL false body n (l + 2) (l :: cs) ((l + 1) :: bs) = (xs, nr, l1))
    (fetchJ : asmFetchAux (t1.pc + ((appListAppend xs).filter (fun x => !isLabelHOL x)).length)
      t1.code = some (.labAsm (.jump (.lab n l)) 0 [] 0))
    (hc : StackSemControl.contLoop res = true)
    (bh : LabSimulationResultB body false res s1' n (l + 2) (l :: cs) ((l + 1) :: bs) t1 b) :
    ∃ ck ≤ b, ∃ (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      stateRel s1' t2 ∧ asmFetchAux t2.pc t2.code = some (.labAsm (.jump (.lab n l)) 0 [] 0) := by
  cases res with
  | none =>
    obtain ⟨ck, hck, t2, run, f1, f2, f3, f4, f5, pre, hpc, rel2⟩ := labSimB_none bh
    rw [h1] at hpc
    exact ⟨ck, hck, t2, run, f1, f2, f3, f4, f5, pre, rel2, by
      rw [hpc]; exact asmFetchAuxSomeIsPrefix _ _ _ _ ⟨fetchJ, pre⟩⟩
  | some x =>
    rcases x with _ | _ | _ | k | _ | _ | _ | _
    case «continue» =>
      simp only [StackSemControl.contLoop, decide_eq_true_eq] at hc
      subst hc
      obtain ⟨ck, hck, t2, h⟩ := bh
      simp only [haltView, Option.map_some, resultView, findLabHOL] at h
      obtain ⟨run, f1, f2, f3, f4, f5, pre, rel2, inst2⟩ := h
      exact ⟨ck, hck, t2, run, f1, f2, f3, f4, f5, pre, rel2, fetchSingle rfl inst2⟩
    all_goals simp [StackSemControl.contLoop] at hc

/-- `Loop body`: each continuing iteration of `.loop body` decrements the `StackSem` clock by at
least `1` (`(decClock s1').clock = s1'.clock - 1 < s1.clock`), executes the `LabSem` back-jump in
`1` tick matched by `t2.clock - 1`, and adds the body's extra clock `b_body` to the remaining
iterations' extra clock `b_rest`. -/
theorem flattenCorrectLoopB_step
    (s1 : StackSemStateFiniteExact width C F) (body : HolProg width)
    (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (b_body : StackSemStateFiniteExact width C F → Nat)
    (b_rest : StackSemStateFiniteExact width C F → Nat)
    (b_total : Nat)
    (hyps : FlattenHyps (.loop body) s1 t r s2 n l cs bs t1)
    (ihBody : ∀ res s1',
      StackSemEvaluate.evaluate (body, s1) = (res, s1') →
      FlattenHyps body s1 false res s1' n (l + 2) (l :: cs) ((l + 1) :: bs) t1 →
      LabSimulationResultB body false res s1' n (l + 2) (l :: cs) ((l + 1) :: bs) t1
        (b_body s1'))
    (ihLoop : ∀ res s1' (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      StackSemEvaluate.evaluate (body, s1) = (res, s1') →
      StackSemControl.contLoop res = true →
      s1'.clock ≠ 0 →
      (StackSemStateOps.decClock s1').clock < s1.clock →
      FlattenHyps (.loop body) (StackSemStateOps.decClock s1') t r s2 n l cs bs
        { t2 with pc := t1.pc, clock := t2.clock - 1 } →
      LabSimulationResultB (.loop body) t r s2 n l cs bs
        { t2 with pc := t1.pc, clock := t2.clock - 1 } (b_rest s1'))
    (hExitBound : ∀ res s1',
      StackSemEvaluate.evaluate (body, s1) = (res, s1') →
      (StackSemControl.contLoop res = false ∨ s1'.clock = 0) →
      r = (if StackSemControl.contLoop res then some .timeOut else StackSemControl.exitLoop res) →
      s2 = (if StackSemControl.contLoop res then StackSemStateOps.emptyEnv s1' else s1') →
      b_body s1' ≤ b_total)
    (hContBound : ∀ res s1',
      StackSemEvaluate.evaluate (body, s1) = (res, s1') →
      StackSemControl.contLoop res = true →
      s1'.clock ≠ 0 →
      StackSemEvaluate.evaluate (.loop body, StackSemStateOps.decClock s1') = (r, s2) →
      b_body s1' + b_rest s1' ≤ b_total) :
    LabSimulationResultB (.loop body) t r s2 n l cs bs t1 b_total := by
  obtain ⟨ev, nerr, rel, ca, inst, labs⟩ := hyps
  rw [StackSemEvaluate.evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at ev
  simp only [StackProps.callArgs] at ca
  have tf : flattenHOL t (.loop body) n l cs bs = flattenHOL false (.loop body) n l cs bs := by
    cases t
    · rfl
    · exact flattenTF (by simp [isSeqHOL])
  rcases h1 : flattenHOL false body n (l + 2) (l :: cs) ((l + 1) :: bs) with ⟨xs, nr1, l1⟩
  have hflat : appListAppend (flattenHOL t (.loop body) n l cs bs).1 =
      .label n l 0 :: (appListAppend xs ++
        [.labAsm (.jump (.lab n l)) 0 [] 0, .label n (l + 1) 0]) := by
    rw [tf, flattenHOL]; simp [h1, appListAppendAppend, appListAppendList]
  have total : ((appListAppend (flattenHOL t (.loop body) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length =
      ((appListAppend xs).filter (fun x => !isLabelHOL x)).length + 1 := by
    rw [hflat]; simp [List.filter_append, isLabelHOL]
  have inst0 := inst
  rw [hflat] at inst
  obtain ⟨locL, inst1⟩ := labelAt inst
  obtain ⟨instXs, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst1
  obtain ⟨fetchJ, instRest2⟩ := lineAt rfl instRest
  obtain ⟨locL1, -⟩ := labelAt instRest2
  rcases e1 : StackSemEvaluate.evaluate (body, s1) with ⟨res, s1'⟩
  rw [e1] at ev
  simp only at ev
  have labs' : ∀ k ∈ (l :: cs) ++ ((l + 1) :: bs) ++ [0], (locToPc n k t1.code).isSome := by
    intro k hk
    by_cases e : k = l
    · subst e; simp [locL]
    by_cases e' : k = l + 1
    · subst e'; simp [locL1]
    apply labs k
    simp only [List.cons_append, List.mem_cons, List.mem_append] at hk ⊢
    tauto
  have nerrBody : res ≠ some .error := by
    rintro rfl
    simp [StackSemControl.contLoop, StackSemControl.exitLoop] at ev
    exact nerr ev.1.symm
  have bh := ihBody res s1' e1 ⟨e1, nerrBody, rel, ca, by rw [h1]; exact instXs, labs'⟩
  by_cases hc : StackSemControl.contLoop res = true
  · rw [if_pos hc] at ev
    obtain ⟨ck, hck, t2, run, f1, f2, f3, f4, f5, pre, rel2, fetch2⟩ :=
      loopReentryB h1 fetchJ hc bh
    split_ifs at ev with hz
    · simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      have hb := hExitBound res s1' e1 (.inr hz) (by simp [hc]) (by simp [hc])
      refine ⟨ck, Nat.le_trans hck hb, t2, run, f1, f2, f3, f4, f5, pre, ?_, ?_⟩
      · simp [StackSemStateOps.emptyEnv, relFfi rel2]
      · rw [relClock rel2]; exact hz
    · have hlt : (StackSemStateOps.decClock s1').clock < s1.clock := by
        have := StackSemEvaluateClock.evaluateClock _ _ _ _ e1
        simp only [StackSemStateOps.decClock]
        omega
      have locL2 := locToPcIsPrefix _ _ _ _ _ ⟨locL, pre⟩
      have rel3 : stateRel (StackSemStateOps.decClock s1')
          { t2 with pc := t1.pc, clock := t2.clock - 1 } := StateRel.stateRelDecClock rel2
      have lh := ihLoop res s1' t2 e1 hc hz hlt
        ⟨ev, nerr, rel3, by rw [f1, f2, f3, f4, f5]; exact ca,
          codeInstalledIsPrefix _ _ _ _ ⟨inst0, pre⟩,
          fun k hk => isSomeLocToPcPrefix ⟨labs k hk, pre⟩⟩
      have hb := hContBound res s1' e1 hc hz ev
      have hclk2 := relClock rel2
      refine (labSimB_compose (ck := ck) (t2 := { t2 with pc := t1.pc, clock := t2.clock - 1 })
        (fun ck1 => ?_) f1 f2 f3 f4 f5 pre rfl lh).mono (by omega)
      rw [run, show t2.clock + ck1 = (t2.clock - 1 + ck1) + 1 by omega,
        jumpStep (t2.clock - 1 + ck1) fetch2 locL2]
  · have hcF : StackSemControl.contLoop res = false := by simpa using hc
    rw [if_neg hc] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have hb := hExitBound res s1' e1 (.inl hcF) (by simp [hcF]) (by simp [hcF])
    have bh' := bh.mono hb
    rcases res with _ | x
    · simp [StackSemControl.contLoop] at hc
    rcases x with v | v | k | k | v | _ | o | _
    · exact labSimB_result rfl (by cases v <;> rfl) bh'
    · exact labSimB_result rfl (by cases v <;> rfl) bh'
    · rcases k with _ | k
      · simp only [StackSemControl.exitLoop, if_true]
        obtain ⟨ck, hck, t2, h⟩ := bh'
        simp only [haltView, Option.map_some, resultView, findLabHOL] at h
        obtain ⟨run, f1, f2, f3, f4, f5, pre, -, hw⟩ := h
        obtain ⟨hpc, rel2⟩ := hw _ (locToPcIsPrefix _ _ _ _ _ ⟨locL1, pre⟩)
        refine ⟨ck, hck, t2, run, f1, f2, f3, f4, f5, pre, ?_, rel2⟩
        rw [← hpc, total]
        omega
      · simp only [StackSemControl.exitLoop, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        exact labSimB_result (by simp [haltView]) (by simp [resultView, findLabHOL]) bh'
    · rcases k with _ | k
      · simp [StackSemControl.contLoop] at hc
      · simp only [StackSemControl.exitLoop, Nat.add_sub_cancel]
        exact labSimB_result (by simp [haltView]) (by simp [resultView, findLabHOL]) bh'
    all_goals exact labSimB_result rfl (by simp [resultView]) bh'

/-- `JumpLower r1 r2 dest`: when not taken costs `1` extra tick (`ck = 1`); when taken and
`s1.clock ≠ 0` costs `0` extra jump ticks (`1` `LabSem` jump tick matched by `decClock`) plus the
callee bound `b_callee`. -/
theorem flattenCorrectJumpLowerB_step
    (s1 : StackSemStateFiniteExact width C F) (r1 r2 dest : Nat)
    (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (b_callee : Nat)
    (hyps : FlattenHyps (.jumpLower r1 r2 dest) s1 t r s2 n l cs bs t1)
    (ihCallee : ∀ prog (x' : StackSemResult width) pc',
      sptLookup dest s1.code = some prog →
      s1.clock ≠ 0 →
      r = some x' →
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) = (some x', s2) →
      FlattenHyps prog (StackSemStateOps.decClock s1) true (some x') s2 dest
        (StackAlloc.nextLabHOL prog 2) [] [] { t1 with pc := pc', clock := t1.clock - 1 } →
      LabSimulationResultB prog true (some x') s2 dest (StackAlloc.nextLabHOL prog 2) [] []
        { t1 with pc := pc', clock := t1.clock - 1 } b_callee) :
    LabSimulationResultB (.jumpLower r1 r2 dest) t r s2 n l cs bs t1 (1 + b_callee) := by
  obtain ⟨ev, nerr, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_jumpLower] at ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.jumpCmp .lower r1 (.reg r2) (.lab dest 0)) 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  rcases hx : StackSemStateOps.getVar r1 s1 with _ | ⟨x | ⟨_, _⟩⟩ <;>
    rcases hy : StackSemStateOps.getVar r2 s1 with _ | ⟨y | ⟨_, _⟩⟩ <;>
    simp only [hx, hy] at ev <;> try exact (err ev).elim
  have hcmp : wordSemWordCmp .lower (t1.regs r1) (regImm (.reg r2) t1) =
      some (wordCmpHOL .lower x y) := by
    simp [regImm, InstCorrect.regOfLookup rel hx, InstCorrect.regOfLookup rel hy, wordSemWordCmp]
  have clk := relClock rel
  by_cases hlow : wordCmpHOL .lower x y = true
  · rw [if_pos hlow] at ev
    rw [hlow] at hcmp
    split at ev
    · exact (err ev).elim
    rename_i prog hfind
    have hlook : sptLookup dest s1.code = some prog := by
      simpa [StackSemControl.findCode] using hfind
    obtain ⟨caP, pc', instP, entry⟩ := relCode rel hlook
    by_cases h0 : s1.clock = 0
    · rw [if_pos h0] at ev
      simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨0, by omega, t1, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
        ?_, ?_⟩
      · simp [StackSemStateOps.emptyEnv, relFfi rel]
      · omega
    · rw [if_neg h0] at ev
      rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) with ⟨res, s'⟩
      rw [e2] at ev
      simp only at ev
      by_cases hbad : StackSemControl.badFunReturn res = true
      · rw [if_pos hbad] at ev; exact (err ev).elim
      rw [if_neg hbad] at ev
      simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      obtain ⟨x', rfl⟩ := notBadFunReturnImpSome _ hbad
      have rel' : stateRel (StackSemStateOps.decClock s1)
          { t1 with pc := pc', clock := t1.clock - 1 } := StateRel.stateRelDecClock rel
      have ph := ihCallee prog x' pc' hlook h0 rfl e2
        ⟨e2, nerr, rel', caP, instP, by simp [entry]⟩
      have step := fun c => (jumpCmpStep (b := true) c fetch hcmp)
      simp only [if_true, entry] at step
      exact (labSimB_composeSome (runEnter (by omega) step) rfl rfl rfl rfl rfl
        (List.prefix_refl _)
        (labSimB_result (p' := prog) (t' := true) (l' := 0) rfl
          (resultViewIndep hbad _ _ _ _ _ _) ph)).mono (by omega)
  · have hlow' : wordCmpHOL .lower x y = false := by simpa using hlow
    rw [if_neg hlow] at ev
    rw [hlow'] at hcmp
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have step := fun c => (jumpCmpStep (b := false) c fetch hcmp)
    simp only [Bool.false_eq_true, if_false] at step
    refine ⟨1, by omega, { t1 with pc := t1.pc + 1 }, runToPc step, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, ?_, rel⟩
    simp [flattenHOL, appListAppendList, isLabelHOL]

/-- `RawCall dest`: `0` extra jump ticks (`1` `LabSem` jump tick matched by `decClock`) plus the
callee body bound `b_body`. -/
theorem flattenCorrectRawCallB_step
    (s1 : StackSemStateFiniteExact width C F) (dest : Nat)
    (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (b_body : Nat)
    (hyps : FlattenHyps (.rawCall dest) s1 t r s2 n l cs bs t1)
    (ihBody : ∀ p1 body (x' : StackSemResult width) l1 pc',
      sptLookup dest s1.code = some (.seq p1 body) →
      s1.clock ≠ 0 →
      r = some x' →
      StackSemEvaluate.evaluate (body, StackSemStateOps.decClock s1) = (some x', s2) →
      FlattenHyps body (StackSemStateOps.decClock s1) false (some x') s2 dest l1 [] []
        { t1 with pc := pc', clock := t1.clock - 1 } →
      LabSimulationResultB body false (some x') s2 dest l1 [] []
        { t1 with pc := pc', clock := t1.clock - 1 } b_body) :
    LabSimulationResultB (.rawCall dest) t r s2 n l cs bs t1 b_body := by
  obtain ⟨ev, nerr, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_rawCall] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.labAsm (.jump (.lab dest 1)) 0 [] 0) :=
    fetchSingle rfl (by simpa [flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  rcases hlook : sptLookup dest s1.code with _ | prog
  · rw [hlook] at ev; exact (err ev).elim
  rw [hlook] at ev
  simp only at ev
  rcases prog with _ | _ | _ | _ | _ | _ | ⟨p1, body⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals try (simp only [StackSemControl.destSeq] at ev; exact (err ev).elim)
  simp only [StackSemControl.destSeq] at ev
  obtain ⟨caP, pc', instP, entry⟩ := relCode rel hlook
  simp only [StackProps.callArgs] at caP
  rcases h1 : flattenHOL false p1 dest (StackAlloc.nextLabHOL (.seq p1 body) 2) [] [] with
    ⟨xs, nr1, l1⟩
  rcases h2 : flattenHOL false body dest l1 [] [] with ⟨ys, nr2, l2⟩
  have hflat : appListAppend (flattenHOL true (.seq p1 body) dest
      (StackAlloc.nextLabHOL (.seq p1 body) 2) [] []).1 =
      appListAppend xs ++ (.label dest 1 0 :: appListAppend ys) := by
    rw [flattenHOL]; simp [h1, h2, appListAppendAppend, appListAppendList]
  rw [hflat] at instP
  obtain ⟨-, instRest⟩ := codeInstalledAppendImp _ _ _ _ instP
  obtain ⟨loc1, instYs⟩ := labelAt instRest
  set lenXs := ((appListAppend xs).filter (fun x => !isLabelHOL x)).length with hLenXs
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, by omega, t1, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
      ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0] at ev
  rcases e2 : StackSemEvaluate.evaluate (body, StackSemStateOps.decClock s1) with ⟨res, s'⟩
  rw [e2] at ev
  simp only at ev
  by_cases hbad : StackSemControl.badFunReturn res = true
  · rw [if_pos hbad] at ev; exact (err ev).elim
  rw [if_neg hbad] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  obtain ⟨x', rfl⟩ := notBadFunReturnImpSome _ hbad
  have rel' : stateRel (StackSemStateOps.decClock s1)
      { t1 with pc := pc' + lenXs, clock := t1.clock - 1 } := StateRel.stateRelDecClock rel
  have ph := ihBody p1 body x' l1 (pc' + lenXs) hlook h0 rfl e2
    ⟨e2, nerr, rel', caP.2, by rw [h2]; exact instYs, by simp [entry]⟩
  have step := fun c => jumpStep c fetch loc1
  exact (labSimB_composeSome (runEnter (by omega) step) rfl rfl rfl rfl rfl
    (List.prefix_refl _)
    (labSimB_result (p' := body) (t' := false) (l' := 0) rfl
      (resultViewIndep hbad _ _ _ _ _ _) ph)).mono (by omega)

/-- `TailCall` (`Call none dest handler`): `0` extra jump ticks (`1` `LabSem` jump tick matched by
`decClock`) plus the callee bound `b_callee`. -/
theorem flattenCorrectCallTailB_step
    (s1 : StackSemStateFiniteExact width C F) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (b_callee : Nat)
    (hyps : FlattenHyps (.call none dest handler) s1 t r s2 n l cs bs t1)
    (ihCallee : ∀ d prog (x' : StackSemResult width) pc',
      sptLookup d s1.code = some prog →
      s1.clock ≠ 0 →
      r = some x' →
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) = (some x', s2) →
      FlattenHyps prog (StackSemStateOps.decClock s1) true (some x') s2 d
        (StackAlloc.nextLabHOL prog 2) [] [] { t1 with pc := pc', clock := t1.clock - 1 } →
      LabSimulationResultB prog true (some x') s2 d (StackAlloc.nextLabHOL prog 2) [] []
        { t1 with pc := pc', clock := t1.clock - 1 } b_callee) :
    LabSimulationResultB (.call none dest handler) t r s2 n l cs bs t1 b_callee := by
  obtain ⟨ev, nerr, rel, -, inst, -⟩ := hyps
  rw [StackSemEvaluate.evaluate_call] at ev
  simp only at ev
  have fetch : asmFetchAux t1.pc t1.code = some (compileJumpHOL dest) :=
    fetchSingle (Prelude.notIsLabelCompileJump dest)
      (by simpa [flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  rcases hfind : StackSemControl.findCode dest s1.regs s1.code with _ | prog
  · rw [hfind] at ev; exact (err ev).elim
  rw [hfind] at ev
  simp only at ev
  rcases handler with _ | hd
  swap; · exact (err ev).elim
  simp only at ev
  obtain ⟨d, pc', hlook, entry, caP, instP, step⟩ :=
    compileJumpEnter (fun r v h => InstCorrect.regOfLookup rel h) rel fetch hfind
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, by omega, t1, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
      ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0, StackSemEvaluateClock.fixClockEvaluate] at ev
  rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) with ⟨res, s'⟩
  rw [e2] at ev
  simp only at ev
  by_cases hbad : StackSemControl.badFunReturn res = true
  · rw [if_pos hbad] at ev; exact (err ev).elim
  rw [if_neg hbad] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  obtain ⟨x', rfl⟩ := notBadFunReturnImpSome _ hbad
  have rel' : stateRel (StackSemStateOps.decClock s1)
      { t1 with pc := pc', clock := t1.clock - 1 } := StateRel.stateRelDecClock rel
  have ph := ihCallee d prog x' pc' hlook h0 rfl e2
    ⟨e2, nerr, rel', caP, instP, by simp [entry]⟩
  exact (labSimB_composeSome (runEnter (by omega) step) rfl rfl rfl rfl rfl
    (List.prefix_refl _)
    (labSimB_result (p' := prog) (t' := true) (l' := 0) rfl
      (resultViewIndep hbad _ _ _ _ _ _) ph)).mono (by omega)

/-- Returning `Call` (`Call (some (rp, link, l1, l2)) dest handler`): entry `locValue` +
`compileJumpHOL` (`1` extra tick beyond `decClock`) plus callee bound `b_callee` plus return/handler
continuation bound and optional join jump (`≤ 2 + b_callee + b_cont`). -/
theorem flattenCorrectCallRetB_step
    (s1 : StackSemStateFiniteExact width C F) (rp : HolProg width)
    (link l1 l2 : Nat) (dest : Nat ⊕ Nat) (handler : Option (HolProg width × Nat × Nat))
    (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (b_callee : StackSemStateFiniteExact width C F → Nat)
    (b_ret : StackSemStateFiniteExact width C F → Nat)
    (b_hand : StackSemStateFiniteExact width C F → Nat)
    (b_total : Nat)
    (hyps : FlattenHyps (.call (some (rp, link, l1, l2)) dest handler) s1 t r s2 n l cs bs t1)
    (ihCallee : ∀ d prog res0 s2' (tE : Flapjack.Compiler.Backend.LabSem.State width C F),
      sptLookup d s1.code = some prog →
      s1.clock ≠ 0 →
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1)) = (res0, s2') →
      FlattenHyps prog (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) s1))
        true res0 s2' d (StackAlloc.nextLabHOL prog 2) [] [] tE →
      LabSimulationResultB prog true res0 s2' d (StackAlloc.nextLabHOL prog 2) [] [] tE
        (b_callee s2'))
    (ihRet : ∀ d prog s2' (t3 : Flapjack.Compiler.Backend.LabSem.State width C F),
      sptLookup d s1.code = some prog →
      s1.clock ≠ 0 →
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1)) = (some (.result (.loc l1 l2)), s2') →
      StackSemEvaluate.evaluate (rp, s2') = (r, s2) →
      FlattenHyps rp s2' false r s2 n l cs bs t3 →
      LabSimulationResultB rp false r s2 n l cs bs t3 (b_ret s2'))
    (ihHand : ∀ d prog hp hs hl s2' (t3 : Flapjack.Compiler.Backend.LabSem.State width C F),
      handler = some (hp, hs, hl) →
      sptLookup d s1.code = some prog →
      s1.clock ≠ 0 →
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1)) = (some (.exception (.loc hs hl)), s2') →
      StackSemEvaluate.evaluate (hp, s2') = (r, s2) →
      FlattenHyps hp s2' false r s2 n (flattenHOL false rp n l cs bs).2.2 cs bs t3 →
      LabSimulationResultB hp false r s2 n (flattenHOL false rp n l cs bs).2.2 cs bs t3
        (b_hand s2'))
    (hPropBound : ∀ d prog res0,
      sptLookup d s1.code = some prog →
      s1.clock ≠ 0 →
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1)) = (res0, s2) →
      1 + b_callee s2 ≤ b_total)
    (hRetBound : ∀ d prog s2',
      sptLookup d s1.code = some prog →
      s1.clock ≠ 0 →
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1)) = (some (.result (.loc l1 l2)), s2') →
      StackSemEvaluate.evaluate (rp, s2') = (r, s2) →
      2 + b_callee s2' + b_ret s2' ≤ b_total)
    (hHandBound : ∀ d prog hp hs hl s2',
      handler = some (hp, hs, hl) →
      sptLookup d s1.code = some prog →
      s1.clock ≠ 0 →
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1)) = (some (.exception (.loc hs hl)), s2') →
      StackSemEvaluate.evaluate (hp, s2') = (r, s2) →
      1 + b_callee s2' + b_hand s2' ≤ b_total) :
    LabSimulationResultB (.call (some (rp, link, l1, l2)) dest handler) t r s2 n l cs bs t1
      b_total := by
  obtain ⟨ev, nerr, rel, ca, inst, labs⟩ := hyps
  rw [StackSemEvaluate.evaluate_call] at ev
  simp only at ev
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  unfold StackProps.callArgs at ca
  simp only at ca
  have caR := ca.1
  have caH := ca.2.2
  rcases h1 : flattenHOL false rp n l cs bs with ⟨xs, nr1, m1⟩
  obtain ⟨rest, hflat, hrest⟩ := callRetPrelude (t := t) (link := link) (l1 := l1) (l2 := l2)
    (dest := dest) (handler := handler) h1
  have inst0 := inst
  rw [hflat] at inst
  obtain ⟨fetchA, inst2⟩ := lineAt rfl inst
  obtain ⟨fetchB, inst3⟩ := lineAt (Prelude.notIsLabelCompileJump dest) inst2
  obtain ⟨locL, inst4⟩ := labelAt inst3
  obtain ⟨instXs, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst4
  rcases hfind : StackSemControl.findCode dest (s1.regs.eraseEq link) s1.code with _ | prog
  · rw [hfind] at ev; exact (err ev).elim
  rw [hfind] at ev
  simp only at ev
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, by omega, t1, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
      ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0] at ev
  rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
    (StackSemStateOps.setVar link (.loc l1 l2) s1)) with ⟨res0, s2'⟩
  have ev' := callRetEval e2 ev
  obtain ⟨d, pc', tE, hlook, run1, f1, f2, f3, f4, f5, fcode, fpc, relE, entry, caP, instP⟩ :=
    callEnter_with_lookup rel h0 fetchA fetchB (by simpa using locL) hfind
  have nerr0 : res0 ≠ some .error := by
    rintro rfl; exact err ev'
  have ph := ihCallee d prog res0 s2' tE hlook h0 e2
    ⟨e2, nerr0, relE, by rw [f1, f2, f3, f4, f5]; exact caP, by rw [fcode, fpc]; exact instP,
      by simp [fcode, entry]⟩
  have prop : ∀ (x : StackSemResult width)
      (hind : ∀ cs bs cs' bs' : List Nat, ∀ m m', resultView x m cs bs = resultView x m' cs' bs')
      (he2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1)) = (some x, s2))
      (phx : LabSimulationResultB prog true (some x) s2 d (StackAlloc.nextLabHOL prog 2) [] [] tE
        (b_callee s2)),
      LabSimulationResultB (.call (some (rp, link, l1, l2)) dest handler) t (some x) s2 n l cs bs t1
        b_total := by
    intro x hind he2 phx
    exact (labSimB_composeSome (ck := 1) run1 f1 f2 f3 f4 f5 (fcode ▸ List.prefix_refl _)
      (labSimB_result (p' := prog) (t' := true) (l' := 0) rfl (hind _ _ _ _ _ _) phx)).mono
      (hPropBound d prog (some x) hlook h0 he2)
  rcases res0 with _ | x
  · exact (err ev').elim
  rcases x with v | v | k | k | v | _ | o | _
  · -- the callee returned
    simp only at ev'
    by_cases hv : v = .loc l1 l2
    swap; · rw [if_pos hv] at ev'; exact (err ev').elim
    rw [if_neg (not_not.mpr hv)] at ev'
    subst hv
    obtain ⟨ck', hck', t3, run3, g1, g2, g3, g4, g5, pre3, hw⟩ :=
      labSimB_vloc (n1 := l1) (n2 := l2) rfl rfl ph
    rw [fcode] at pre3
    obtain ⟨hpc3, rel3⟩ := hw (t1.pc + 1 + 1) (locToPcIsPrefix _ _ _ _ _ ⟨locL, pre3⟩)
    have rh := ihRet d prog s2' t3 hlook h0 e2 ev'
      ⟨ev', nerr, rel3, by rw [g1, g2, g3, g4, g5, f1, f2, f3, f4, f5]; exact caR,
        by rw [← hpc3, h1]; exact codeInstalledIsPrefix _ _ _ _ ⟨instXs, pre3⟩,
        fun k hk => isSomeLocToPcPrefix ⟨labs k hk, pre3⟩⟩
    have hbRet := hRetBound d prog s2' hlook h0 e2 ev'
    have run13 := chainRun run1 run3
    rcases handler with _ | ⟨hp, hs, hl⟩
    · rw [hrest rfl] at hflat
      refine (labSimB_compose run13 (by rw [g1, f1]) (by rw [g2, f2]) (by rw [g3, f3])
        (by rw [g4, f4]) (by rw [g5, f5]) pre3 ?_ rh).mono (by omega)
      rw [hflat, ← hpc3, h1]
      cases dest <;> simp [isLabelHOL, compileJumpHOL] <;> omega
    · obtain ⟨ys, m2, fetchJ, locH, instYs, locEnd, total, -⟩ := callHandlerCode h1 inst0
      cases r with
      | some x =>
        exact (labSimB_composeSome run13 (by rw [g1, f1]) (by rw [g2, f2])
          (by rw [g3, f3]) (by rw [g4, f4]) (by rw [g5, f5]) pre3 rh).mono (by omega)
      | none =>
        obtain ⟨ck2, hck2, t4, run4, k1, k2, k3, k4, k5, pre4, hpc4, rel4⟩ := labSimB_none rh
        rw [h1] at hpc4
        have pre34 := pre3.trans pre4
        have fetchJ4 : asmFetchAux t4.pc t4.code =
            some (.labAsm (.jump (.lab n m2)) 0 [] 0) := by
          rw [hpc4, ← hpc3]; exact asmFetchAuxSomeIsPrefix _ _ _ _ ⟨fetchJ, pre34⟩
        have locEnd4 := locToPcIsPrefix _ _ _ _ _ ⟨locEnd, pre34⟩
        refine ⟨(1 + ck') + ck2 + 1, by omega, { t4 with pc := t1.pc + 1 + 1 +
            ((appListAppend xs).filter (fun x => !isLabelHOL x)).length + 1 +
            ((appListAppend ys).filter (fun x => !isLabelHOL x)).length }, fun ck1 => ?_,
          by rw [k1, g1, f1], by rw [k2, g2, f2], by rw [k3, g3, f3], by rw [k4, g4, f4],
          by rw [k5, g5, f5], pre34, ?_, rel4⟩
        · rw [show t1.clock + ((1 + ck') + ck2 + 1) + ck1 =
              t1.clock + ((1 + ck') + ck2) + (ck1 + 1) by omega, chainRun run13 run4,
            show t4.clock + (ck1 + 1) = (t4.clock + ck1) + 1 by omega,
            jumpStep (t4.clock + ck1) fetchJ4 locEnd4]
        · simp only [total]; omega
  · -- the callee raised
    rcases handler with _ | ⟨hp, hs, hl⟩
    · simp only at ev'
      simp only [Prod.mk.injEq] at ev'
      obtain ⟨rfl, rfl⟩ := ev'
      exact prop _ (fun _ _ _ _ _ _ => by cases v <;> rfl) e2 ph
    · simp only at ev'
      by_cases hv : v = .loc hs hl
      swap; · rw [if_pos hv] at ev'; exact (err ev').elim
      rw [if_neg (not_not.mpr hv)] at ev'
      subst hv
      obtain ⟨ys, m2, -, locH, instYs, -, total, h2⟩ := callHandlerCode h1 inst0
      obtain ⟨ck', hck', t3, run3, g1, g2, g3, g4, g5, pre3, hw⟩ :=
        labSimB_vloc (n1 := hs) (n2 := hl) rfl rfl ph
      rw [fcode] at pre3
      obtain ⟨hpc3, rel3⟩ := hw _ (locToPcIsPrefix _ _ _ _ _ ⟨locH, pre3⟩)
      simp only at caH
      have rh : LabSimulationResultB hp false r s2 n m1 cs bs t3 (b_hand s2') := by
        have := ihHand d prog hp hs hl s2' t3 rfl hlook h0 e2 ev'
        rw [h1] at this
        exact this ⟨ev', nerr, rel3, by rw [g1, g2, g3, g4, g5, f1, f2, f3, f4, f5]; exact caH,
          by rw [← hpc3, h2]; exact codeInstalledIsPrefix _ _ _ _ ⟨instYs, pre3⟩,
          fun k hk => isSomeLocToPcPrefix ⟨labs k hk, pre3⟩⟩
      have hbHand := hHandBound d prog hp hs hl s2' rfl hlook h0 e2 ev'
      refine (labSimB_compose (chainRun run1 run3) (by rw [g1, f1]) (by rw [g2, f2])
        (by rw [g3, f3]) (by rw [g4, f4]) (by rw [g5, f5]) pre3 ?_ rh).mono (by omega)
      rw [total, ← hpc3, h2]
      omega
  · exact (err ev').elim
  · exact (err ev').elim
  all_goals
    simp only [Prod.mk.injEq] at ev'
    obtain ⟨rfl, rfl⟩ := ev'
    exact prop _ (fun _ _ _ _ _ _ => rfl) e2 ph

end ControlAndCallsB

/-! ## 6. Canonical Clocked Simulation of `StackToLab` (`stackToLab_flatten_clock_simulation`) -/

section MainSimulation
variable {C F : Type}

/-- Clocked `flatten_correct` predicate at per-tick body bound `M`:
under `FlattenHyps`, `stepCost prog ≤ M`, and `CodeStepBounded M s1`, the flattened `LabSem`
execution requires at most `stepCost prog + (s1.clock - s2.clock) * M` extra ticks. -/
def FlattenPropB (M : Nat) (prog : HolProg width)
    (s1 : StackSemStateFiniteExact width C F) : Prop :=
  stepCost prog ≤ M → CodeStepBounded M s1 →
  ∀ (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F),
    FlattenHyps prog s1 t r s2 n l cs bs t1 →
    LabSimulationResultB prog t r s2 n l cs bs t1
      (stepCost prog + (s1.clock - s2.clock) * M)

/-- Induction hypothesis available to a constructor case under `MeasureLt`. -/
def FlattenIHB (M : Nat) (p : HolProg width)
    (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (p' : HolProg width) (s' : StackSemStateFiniteExact width C F),
    MeasureLt p' s' p s → FlattenPropB M p' s'

/-- Every constructor of `HolProg width` satisfies `FlattenPropB M` given `FlattenIHB M`. -/
theorem flattenPropBOfIH (M : Nat) (prog : HolProg width)
    (s1 : StackSemStateFiniteExact width C F) (ih : FlattenIHB M prog s1) :
    FlattenPropB M prog s1 := by
  intro hcost hcode t r s2 n l cs bs t1 hyps
  cases prog with
  | skip =>
    exact (flattenCorrectSkipB s1 t r s2 n l cs bs t1 hyps).mono (by simp [stepCost])
  | halt v =>
    exact (flattenCorrectHaltB s1 v t r s2 n l cs bs t1 hyps).mono (by simp [stepCost])
  | inst i =>
    exact (flattenCorrectInstB s1 i t r s2 n l cs bs t1 hyps).mono (by simp [stepCost])
  | tick =>
    exact (flattenCorrectTickB s1 t r s2 n l cs bs t1 hyps).mono (by split <;> simp [stepCost])
  | ret v =>
    exact (flattenCorrectRetB s1 v t r s2 n l cs bs t1 hyps).mono (by simp [stepCost])
  | raise v =>
    exact (flattenCorrectRaiseB s1 v t r s2 n l cs bs t1 hyps).mono (by simp [stepCost])
  | «break» k =>
    exact (flattenCorrectBreakB s1 k t r s2 n l cs bs t1 hyps).mono (by simp [stepCost])
  | «continue» k =>
    exact (flattenCorrectContinueB s1 k t r s2 n l cs bs t1 hyps).mono (by simp [stepCost])
  | locValue reg l1 l2 =>
    exact (flattenCorrectLocValueB s1 reg l1 l2 t r s2 n l cs bs t1 hyps).mono (by simp [stepCost])
  | codeBufferWrite r1 r2 =>
    exact (flattenCorrectCodeBufferWriteB s1 r1 r2 t r s2 n l cs bs t1 hyps).mono
      (by simp [stepCost])
  | ffi f ptr len ptr2 len2 ret =>
    exact (flattenCorrectFfiB s1 f ptr len ptr2 len2 ret t r s2 n l cs bs t1 hyps).mono
      (by simp [stepCost])
  | install ptr len dptr dlen ret =>
    exact (flattenCorrectInstallB s1 ptr len dptr dlen ret t r s2 n l cs bs t1 hyps).mono
      (by simp [stepCost])
  | shMemOp op reg addr =>
    rcases addr with ⟨a, w⟩
    exact (flattenCorrectShMemOpB s1 op reg a w t r s2 n l cs bs t1 hyps).mono
      (by simp [stepCost])
  | get v name =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_get]; simp [(relNoStack rel).2.1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | set name v =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_set]; simp [(relNoStack rel).2.1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | opCurrHeap op v src =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_opCurrHeap]; simp [(relNoStack rel).2.1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | alloc k =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_alloc]; simp [(relNoStack rel).2.2])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | storeConsts a b stub =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_storeConsts]; simp [(relNoStack rel).2.1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | stackAlloc k =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_stackAlloc]; simp [(relNoStack rel).1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | stackFree k =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_stackFree]; simp [(relNoStack rel).1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | stackStore r0 k =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_stackStore]; simp [(relNoStack rel).1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | stackStoreAny r0 rn =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_stackStoreAny]; simp [(relNoStack rel).1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | stackLoad r0 k =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_stackLoad]; simp [(relNoStack rel).1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | stackLoadAny r0 rn =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_stackLoadAny]; simp [(relNoStack rel).1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | stackGetSize r0 =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_stackGetSize]; simp [(relNoStack rel).1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | stackSetSize r0 =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_stackSetSize]; simp [(relNoStack rel).1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | bitmapLoad r0 v =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_bitmapLoad]; simp [(relNoStack rel).1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | dataBufferWrite r1 r2 =>
    exact (guardedB (fun t rel => by
      rw [StackSemEvaluate.evaluate_dataBufferWrite]; simp [(relNoStack rel).1])
      t r s2 n l cs bs t1 hyps).mono (by omega)
  | seq c1 c2 =>
    simp only [stepCost] at hcost ⊢
    have lt1 : MeasureLt c1 s1 (.seq c1 c2) s1 :=
      .inr ⟨rfl, StackSemMeasure.seq_first_size_lt c1 c2⟩
    have ev := hyps.1
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at ev
    rcases e1 : StackSemEvaluate.evaluate (c1, s1) with ⟨r1, sMid⟩
    rw [e1] at ev
    cases r1 with
    | some x =>
      simp only [Prod.mk.injEq] at ev
      rcases ev with ⟨h_r, h_s⟩
      subst h_r; subst h_s
      refine (flattenCorrectSeqB_add s1 c1 c2 t (some x) sMid n l cs bs t1
        (stepCost c1 + (s1.clock - sMid.clock) * M) 0 hyps
        (fun r1' s1'' h1 => ?_) (fun s1'' _ he1 _ => by rw [e1] at he1; cases he1)).mono (by omega)
      have heq : r1' = some x ∧ s1'' = sMid := Prod.mk.inj (h1.1.symm.trans e1)
      rcases heq with ⟨rfl, h_eq⟩
      subst h_eq
      exact ih c1 s1 lt1 (by omega) hcode false (some x) s1'' n l cs bs t1 h1
    | none =>
      simp only at ev
      have hsMid := StackSemEvaluateClock.evaluateClock _ _ _ _ e1
      have hs2 := StackSemEvaluateClock.evaluateClock _ _ _ _ ev
      have hcode' := codeStepBounded_evaluate M c1 s1 none sMid e1 hcode
      have lt2 : MeasureLt c2 sMid (.seq c1 c2) s1 :=
        measureLtOfClockLe hsMid (StackSemMeasure.seq_second_size_lt c1 c2)
      have htele := telescope_clock_mul (M := M) hs2 hsMid
      refine (flattenCorrectSeqB_add s1 c1 c2 t r s2 n l cs bs t1
        (stepCost c1 + (s1.clock - sMid.clock) * M)
        (stepCost c2 + (sMid.clock - s2.clock) * M) hyps
        (fun r1' s1'' h1 => ?_) (fun s1'' t2 he1 h2 => ?_)).mono (by omega)
      · have heq : r1' = none ∧ s1'' = sMid := Prod.mk.inj (h1.1.symm.trans e1)
        rcases heq with ⟨rfl, h_eq⟩
        subst h_eq
        exact ih c1 s1 lt1 (by omega) hcode false none s1'' n l cs bs t1 h1
      · have heq : s1'' = sMid := (Prod.mk.inj (he1.symm.trans e1)).2
        subst heq
        exact ih c2 s1'' lt2 (by omega) hcode' false r s2 _ _ cs bs t2 h2
  | ite cmp reg ri c1 c2 =>
    simp only [stepCost] at hcost ⊢
    have lt1 : MeasureLt c1 s1 (.ite cmp reg ri c1 c2) s1 :=
      .inr ⟨rfl, StackSemMeasure.if_first_size_lt cmp reg ri c1 c2⟩
    have lt2 : MeasureLt c2 s1 (.ite cmp reg ri c1 c2) s1 :=
      .inr ⟨rfl, StackSemMeasure.if_second_size_lt cmp reg ri c1 c2⟩
    refine (flattenCorrectIfB_branch s1 cmp reg ri c1 c2 t r s2 n l cs bs t1
      (stepCost c1 + (s1.clock - s2.clock) * M)
      (stepCost c2 + (s1.clock - s2.clock) * M) hyps
      (fun t1' h1 => ih c1 s1 lt1 (by omega) hcode false r s2 n l cs bs t1' h1)
      (fun t1' h2 => ih c2 s1 lt2 (by omega) hcode false r s2 n _ cs bs t1' h2)).mono (by omega)
  | loop body =>
    simp only [stepCost] at hcost ⊢
    refine flattenCorrectLoopB_step s1 body t r s2 n l cs bs t1
      (fun s1' => stepCost body + (s1.clock - s1'.clock) * M)
      (fun s1' => stepCost body + ((StackSemStateOps.decClock s1').clock - s2.clock) * M)
      (stepCost body + (s1.clock - s2.clock) * M) hyps
      (fun res s1' _ hBody => ?_)
      (fun res s1' t2 e1 _ _ hlt hLoop => ?_)
      (fun res s1' e1 _ _ hs2 => ?_)
      (fun res s1' e1 _ hz evLoop => ?_)
    · have ltBody : MeasureLt body s1 (.loop body) s1 :=
        .inr ⟨rfl, StackSemMeasure.loop_body_size_lt body⟩
      exact ih body s1 ltBody hcost hcode false res s1' n (l + 2) (l :: cs) ((l + 1) :: bs) t1 hBody
    · have hcode' := codeStepBounded_evaluate M body s1 res s1' e1 hcode
      have hcode'' : CodeStepBounded M (StackSemStateOps.decClock s1') := hcode'
      exact ih (.loop body) (StackSemStateOps.decClock s1') (.inl hlt) hcost hcode''
        t r s2 n l cs bs _ hLoop
    · have hs2_clk : s2.clock = s1'.clock := by
        rw [hs2]; split <;> rfl
      rw [hs2_clk]
    · have hs1' := StackSemEvaluateClock.evaluateClock _ _ _ _ e1
      have hs2 := StackSemEvaluateClock.evaluateClock _ _ _ _ evLoop
      simp only [StackSemStateOps.decClock] at hs2 ⊢
      have htele := telescope_decClock_mul (M := M) hz hs2 hs1' hcost
      omega
  | jumpLower r1 r2 dest =>
    simp only [stepCost] at hcost ⊢
    refine (flattenCorrectJumpLowerB_step s1 r1 r2 dest t r s2 n l cs bs t1
      ((s1.clock - s2.clock) * M) hyps
      (fun prog x' pc' hlook h0 _ e2 hCallee => ?_)).mono (by omega)
    have hlt : (StackSemStateOps.decClock s1).clock < s1.clock := by
      simp [StackSemStateOps.decClock]; omega
    have hcostP : stepCost prog ≤ M := hcode.1 dest prog hlook
    have hcode' : CodeStepBounded M (StackSemStateOps.decClock s1) := hcode
    have hs2 := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
    simp only [StackSemStateOps.decClock] at hs2
    have htele := telescope_decClock_mul (a := s1.clock) (b := s1.clock) (c := s2.clock)
      (d := stepCost prog) (M := M) h0 hs2 (Nat.le_refl _) hcostP
    exact (ih prog (StackSemStateOps.decClock s1) (.inl hlt) hcostP hcode'
      true (some x') s2 dest (StackAlloc.nextLabHOL prog 2) [] [] _ hCallee).mono
      (by simp only [StackSemStateOps.decClock]; omega)
  | rawCall dest =>
    simp only [stepCost] at hcost ⊢
    refine (flattenCorrectRawCallB_step s1 dest t r s2 n l cs bs t1
      ((s1.clock - s2.clock) * M) hyps
      (fun p1 body x' l1 pc' hlook h0 _ e2 hBody => ?_)).mono (by omega)
    have hlt : (StackSemStateOps.decClock s1).clock < s1.clock := by
      simp [StackSemStateOps.decClock]; omega
    have hcostSeq : stepCost (.seq p1 body) ≤ M := hcode.1 dest (.seq p1 body) hlook
    simp only [stepCost] at hcostSeq
    have hcostB : stepCost body ≤ M := by omega
    have hcode' : CodeStepBounded M (StackSemStateOps.decClock s1) := hcode
    have hs2 := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
    simp only [StackSemStateOps.decClock] at hs2
    have htele := telescope_decClock_mul (a := s1.clock) (b := s1.clock) (c := s2.clock)
      (d := stepCost body) (M := M) h0 hs2 (Nat.le_refl _) hcostB
    exact (ih body (StackSemStateOps.decClock s1) (.inl hlt) hcostB hcode'
      false (some x') s2 dest l1 [] [] _ hBody).mono
      (by simp only [StackSemStateOps.decClock]; omega)
  | call ret dest handler =>
    cases ret with
    | none =>
      simp only [stepCost] at hcost ⊢
      refine (flattenCorrectCallTailB_step s1 dest handler t r s2 n l cs bs t1
        ((s1.clock - s2.clock) * M) hyps
        (fun d prog x' pc' hlook h0 _ e2 hCallee => ?_)).mono (by omega)
      have hlt : (StackSemStateOps.decClock s1).clock < s1.clock := by
        simp [StackSemStateOps.decClock]; omega
      have hcostP : stepCost prog ≤ M := hcode.1 d prog hlook
      have hcode' : CodeStepBounded M (StackSemStateOps.decClock s1) := hcode
      have hs2 := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
      simp only [StackSemStateOps.decClock] at hs2
      have htele := telescope_decClock_mul (a := s1.clock) (b := s1.clock) (c := s2.clock)
        (d := stepCost prog) (M := M) h0 hs2 (Nat.le_refl _) hcostP
      exact (ih prog (StackSemStateOps.decClock s1) (.inl hlt) hcostP hcode'
        true (some x') s2 d (StackAlloc.nextLabHOL prog 2) [] [] _ hCallee).mono
        (by simp only [StackSemStateOps.decClock]; omega)
    | some retInfo =>
      rcases retInfo with ⟨rp, link, l1, l2⟩
      let s1_set := StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) s1)
      have hcode_set : CodeStepBounded M s1_set := hcode
      have hcost_rp : stepCost rp ≤ stepCost (.call (some (rp, link, l1, l2)) dest handler) := by
        cases handler with
        | none => simp [stepCost]
        | some h => rcases h with ⟨hp, hs, hl⟩; simp [stepCost]; omega
      have hcost_call : 2 + stepCost rp ≤ stepCost (.call (some (rp, link, l1, l2)) dest handler) := by
        cases handler with
        | none => simp [stepCost]
        | some h => rcases h with ⟨hp, hs, hl⟩; simp [stepCost]
      refine flattenCorrectCallRetB_step s1 rp link l1 l2 dest handler t r s2 n l cs bs t1
        (fun s2' => M + (s1_set.clock - s2'.clock) * M)
        (fun s2' => stepCost rp + (s2'.clock - s2.clock) * M)
        (fun s2' => (match handler with
          | none => 0
          | some (hp, _, _) => stepCost hp) + (s2'.clock - s2.clock) * M)
        (stepCost (.call (some (rp, link, l1, l2)) dest handler) + (s1.clock - s2.clock) * M)
        hyps
        (fun d prog res0 s2' tE hlook h0 _ hCallee => ?_)
        (fun d prog s2' t3 hlook h0 e2 _ hRet => ?_)
        (fun d prog hp hs hl s2' t3 hhand hlook h0 e2 _ hHand => ?_)
        (fun d prog res0 hlook h0 e2 => ?_)
        (fun d prog s2' hlook h0 e2 evRet => ?_)
        (fun d prog hp hs hl s2' hhand hlook h0 e2 evHand => ?_)
      · have hlt : s1_set.clock < s1.clock := setVarDecClockLt h0
        have hcostP : stepCost prog ≤ M := hcode.1 d prog hlook
        exact (ih prog s1_set (.inl hlt) hcostP hcode_set
          true res0 s2' d (StackAlloc.nextLabHOL prog 2) [] [] tE hCallee).mono (by omega)
      · have hs2' := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
        have hlt : s2'.clock < s1.clock := Nat.lt_of_le_of_lt hs2' (setVarDecClockLt h0)
        have hcode2' := codeStepBounded_evaluate M prog s1_set _ s2' e2 hcode_set
        exact ih rp s2' (.inl hlt) (Nat.le_trans hcost_rp hcost) hcode2'
          false r s2 n l cs bs t3 hRet
      · subst hhand
        have hs2' := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
        have hlt : s2'.clock < s1.clock := Nat.lt_of_le_of_lt hs2' (setVarDecClockLt h0)
        have hcode2' := codeStepBounded_evaluate M prog s1_set _ s2' e2 hcode_set
        have hcost_hp : stepCost hp ≤ M := by
          simp only [stepCost] at hcost; omega
        exact ih hp s2' (.inl hlt) hcost_hp hcode2' false r s2 n _ cs bs t3 hHand
      · have hs2 := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
        have hclk_set : s1_set.clock = s1.clock - 1 := rfl
        rw [hclk_set] at hs2 ⊢
        have htele := telescope_decClock_mul (a := s1.clock) (b := s1.clock) (c := s2.clock)
          (d := M) (M := M) h0 hs2 (Nat.le_refl _) (Nat.le_refl M)
        omega
      · have hs2' := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
        have hs2 := StackSemEvaluateClock.evaluateClock _ _ _ _ evRet
        have hclk_set : s1_set.clock = s1.clock - 1 := rfl
        rw [hclk_set] at hs2' ⊢
        have htele1 := telescope_decClock_mul (a := s1.clock) (b := s1.clock) (c := s2'.clock)
          (d := M) (M := M) h0 hs2' (Nat.le_refl _) (Nat.le_refl M)
        have htele2 := telescope_clock_mul (M := M) hs2 (show s2'.clock ≤ s1.clock by omega)
        omega
      · subst hhand
        simp only [stepCost] at hcost ⊢
        have hs2' := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
        have hs2 := StackSemEvaluateClock.evaluateClock _ _ _ _ evHand
        have hclk_set : s1_set.clock = s1.clock - 1 := rfl
        rw [hclk_set] at hs2' ⊢
        have htele1 := telescope_decClock_mul (a := s1.clock) (b := s1.clock) (c := s2'.clock)
          (d := M) (M := M) h0 hs2' (Nat.le_refl _) (Nat.le_refl M)
        have htele2 := telescope_clock_mul (M := M) hs2 (show s2'.clock ≤ s1.clock by omega)
        omega

/-- **Canonical Clocked `StackToLab.flattenHOL` Simulation Theorem**
(`stackToLab_flatten_clock_simulation`):
Replaces the unbounded existential `∃ ck` in `StackToLab.Proofs.FlattenCorrect.flattenCorrect`
with the explicit quantitative bound `ck ≤ stepCost prog + (s1.clock - s2.clock) * M`
whenever `stepCost prog ≤ M` and `CodeStepBounded M s1`. -/
theorem stackToLab_flatten_clock_simulation
    (M : Nat) (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F) :
    FlattenPropB M prog s1 := by
  have wf := measureLtWf (width := width) (C := C) (F := F)
  suffices ∀ (x : HolProg width × StackSemStateFiniteExact width C F),
      FlattenPropB M x.1 x.2 from this (prog, s1)
  intro x
  refine @WellFounded.induction _ _ wf (fun x => FlattenPropB M x.1 x.2) x ?_
  rintro ⟨p, s⟩ ih
  exact flattenPropBOfIH M p s (fun p' s' hlt => ih (p', s') hlt)

/-- **Four-Clock Target Bound for `StackToLab.flattenHOL`**
(`stackToLab_flatten_four_clock_bound`):
When every procedure body in `s1.code` (and `s1.compileOracle`) has `stepCost ≤ 3`
(`CodeStepBounded 3 s1`) and `stepCost prog ≤ 3`, the flattened `LabSem` execution requires at
most `ck ≤ 3 * s1.clock + stepCost prog` extra ticks beyond `t1.clock = s1.clock`, so the total
`LabSem` clock `t1.clock + ck` is bounded by `4 * s1.clock + stepCost prog`. -/
theorem stackToLab_flatten_four_clock_bound
    (prog : HolProg width) (s1 : StackSemStateFiniteExact width C F)
    (t : Bool) (r : Option (StackSemResult width)) (s2 : StackSemStateFiniteExact width C F)
    (n l : Nat) (cs bs : List Nat) (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (M : Nat) (hM : M ≤ 3)
    (hcost : stepCost prog ≤ M) (hcode : CodeStepBounded M s1)
    (hyps : FlattenHyps prog s1 t r s2 n l cs bs t1) :
    ∃ ck ≤ 3 * s1.clock + stepCost prog,
      t1.clock + ck ≤ 4 * s1.clock + stepCost prog ∧
      LabSimAt prog t r s2 n l cs bs t1 ck := by
  have hcost3 : stepCost prog ≤ 3 := Nat.le_trans hcost hM
  have hcode3 : CodeStepBounded 3 s1 := hcode.mono hM
  obtain ⟨ck, hck, hsim⟩ :=
    stackToLab_flatten_clock_simulation 3 prog s1 hcost3 hcode3 t r s2 n l cs bs t1 hyps
  have hclk : t1.clock = s1.clock := relClock hyps.2.2.1
  have hle : (s1.clock - s2.clock) * 3 ≤ 3 * s1.clock := by omega
  exact ⟨ck, by omega, by omega, hsim⟩

/-- **Clocked `flattenCallCorrect` Simulation Theorem**
(`stackToLab_call_clock_simulation`):
Quantitative version of `Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCallCorrect.flattenCallCorrect`
at entry point `start`: replaces the unbounded existential `∃ ck` with
`ck ≤ (s1.clock - s2.clock) * M + M` (and `t1.clock - 1 + ck ≤ (M + 1) * s1.clock + M`)
under `CodeStepBounded M s1`. -/
theorem stackToLab_call_clock_simulation
    (M start : Nat) (s1 s2 : StackSemStateFiniteExact width C F)
    (res : Option (StackSemResult width))
    (t1 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hcode : CodeStepBounded M s1)
    (ev : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width), s1) =
      (res, s2))
    (rel : stateRel s1 t1)
    (hpc : locToPc start 0 t1.code = some t1.pc)
    (nerr : res ≠ some .error)
    (hres : res ≠ some .timeOut →
      (∃ w : BitVec width, res = some (.halt (.word w))) ∨
      (∃ f, res = some (.finalFFI f)) ∨
      (∃ n, res = some (.result (.loc n 0)) ∧
        ∀ s : StackSemStateFiniteExact width C F, sptSubspt s1.code s.code ∧ s.clock ≠ 0 →
          ∃ t, StackSemEvaluate.evaluate ((.call none (.inl n) none : HolProg width), s) =
              (some (.halt (.word 0)), t) ∧
            t.ffi = s.ffi ∧ t.clock = s.clock - 1)) :
    ∃ (ck : Nat) (r2 : MachineResult) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      ck ≤ (s1.clock - s2.clock) * M + M ∧
      t1.clock - 1 + ck ≤ s1.clock + (s1.clock - s2.clock) * M + M ∧
      evaluate { t1 with clock := t1.clock - 1 + ck } = (r2, t2) ∧
      (∀ f, res = some (.finalFFI f) → r2 = .halt (.ffiOutcome f)) ∧
      (∀ w, res = some (.halt w) → r2 =
        match w with
        | .word w => if w = 0 then .halt .success else .halt .resourceLimitHit
        | _ => .error) ∧
      (∀ n, res = some (.result (.loc n 0)) → r2 = .halt .success) ∧
      t2.ffi = s2.ffi ∧
      r2 ≠ .error ∧ (res = some .timeOut → r2 = .timeOut) := by
  have clk := relClock rel
  obtain ⟨prog, hlook, ⟨h0, rfl, rfl⟩ | ⟨h0, x, rfl, hbad, e2⟩⟩ := callNoneInlCases ev nerr
  · -- clock zero: both sides time out at once (`ck = 0`)
    refine ⟨0, .timeOut, { t1 with clock := t1.clock - 1 + 0 }, by omega, by omega, ?_,
      by simp, by simp, by simp, ?_, by simp, fun _ => rfl⟩
    · rw [evaluate, if_pos (by simp; omega)]
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
  obtain ⟨caP, pc', instP, entry⟩ := relCode rel hlook
  rw [hpc] at entry
  cases entry
  have rel' : stateRel (StackSemStateOps.decClock s1) { t1 with clock := t1.clock - 1 } :=
    StateRel.stateRelDecClock rel
  have hcostP : stepCost prog ≤ M := hcode.1 start prog hlook
  have hcode' : CodeStepBounded M (StackSemStateOps.decClock s1) := hcode
  have hs2 := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
  simp only [StackSemStateOps.decClock] at hs2
  have htele1 := telescope_decClock_mul (a := s1.clock) (b := s1.clock) (c := s2.clock)
    (d := stepCost prog) (M := M) h0 hs2 (Nat.le_refl _) hcostP
  obtain ⟨ck, hck, t2, h⟩ := stackToLab_flatten_clock_simulation M prog
    (StackSemStateOps.decClock s1) hcostP hcode' true (some x) s2
    start (StackAlloc.nextLabHOL prog 2) [] [] { t1 with clock := t1.clock - 1 }
    ⟨e2, nerr, rel', caP, instP, by simp [hpc]⟩
  simp only [StackSemStateOps.decClock] at hck
  have hck_le : ck ≤ (s1.clock - s2.clock) * M := by omega
  rcases x with v | v | k | k | v | _ | f | _
  · -- `Result v`: only `Loc n 0` is allowed, and procedure `n` halts
    obtain ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, hh⟩ := hres (by simp)
    · simp at hw
    · simp at hf
    simp only [Option.some.injEq, StackSemResult.result.injEq] at hn
    subst hn
    simp only [haltView, Option.map_some, resultView] at h
    obtain ⟨run, -, -, -, -, -, -, hcover, hw⟩ := h
    have hsub : sptSubspt s1.code s2.code := by
      simpa [StackSemStateOps.decClock] using (StackProps.EvaluateMono.evaluateMono _ _ _ _ e2).2
    obtain ⟨t, evh, tffi, tclk⟩ := hh { s2 with clock := s2.clock + 1 } ⟨hsub, by simp⟩
    obtain ⟨prog2, hlook2, ⟨h0', -⟩ | ⟨-, x2, hx2, -, e3⟩⟩ := callNoneInlCases evh (by simp)
    · simp at h0'
    simp only [Option.some.injEq] at hx2
    subst hx2
    have hdc : StackSemStateOps.decClock { s2 with clock := s2.clock + 1 } = s2 := by
      simp [StackSemStateOps.decClock]
    rw [hdc] at e3
    simp only at hlook2
    have hcode2 : CodeStepBounded M s2 :=
      codeStepBounded_evaluate M prog (StackSemStateOps.decClock s1) _ s2 e2 hcode'
    have hcostP2 : stepCost prog2 ≤ M := hcode2.1 n prog2 hlook2
    have ht_clk : t.clock = s2.clock := by
      change t.clock = (s2.clock + 1) - 1 at tclk
      omega
    obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.mp (hcover n (by simp [hlook2]))
    obtain ⟨rfl, rel2⟩ := hw w hw'
    obtain ⟨caP2, pc2, instP2, entry2⟩ := relCode rel2 hlook2
    rw [hw'] at entry2
    cases entry2
    obtain ⟨ck', hck', t3, h3⟩ := stackToLab_flatten_clock_simulation M prog2 s2 hcostP2 hcode2
      true (some (.halt (.word 0))) t n
      (StackAlloc.nextLabHOL prog2 2) [] [] t2 ⟨e3, by simp, rel2, caP2, instP2, by simp [hw']⟩
    have hck'_le : ck' ≤ M := by
      rw [ht_clk, Nat.sub_self, Nat.zero_mul, Nat.add_zero] at hck'
      exact Nat.le_trans hck' hcostP2
    simp only [haltView, haltWordView, if_true] at h3
    refine ⟨ck + ck', .halt .success, t3, by omega, by omega, ?_,
      by simp, by simp, fun _ _ => rfl, ?_, by simp, by simp⟩
    · have r1 := run ck'
      rw [show t1.clock - 1 + (ck + ck') = t1.clock - 1 + ck + ck' by omega, r1]
      exact h3.1
    · rw [h3.2, tffi]
  · -- `Exception`: excluded by `hres`
    rcases hres (by simp) with ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, -⟩
    · simp at hw
    · simp at hf
    · simp at hn
  · simp [StackSemControl.badFunReturn] at hbad
  · simp [StackSemControl.badFunReturn] at hbad
  · -- `Halt v`
    obtain ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, -⟩ := hres (by simp)
    · simp only [Option.some.injEq, StackSemResult.halt.injEq] at hw
      subst hw
      simp only [haltView] at h
      refine ⟨ck, haltWordView (.word w), t2, by omega, by omega, h.1, by simp, ?_, by simp,
        h.2, ?_, by simp⟩
      · intro w' hw'
        simp only [Option.some.injEq, StackSemResult.halt.injEq] at hw'
        subst hw'
        rfl
      · simp only [haltWordView]; split <;> simp
    · simp at hf
    · simp at hn
  · -- `TimeOut`
    simp only [haltView, Option.map_some, resultView] at h
    obtain ⟨run, -, -, -, -, -, -, hffi, hclk2⟩ := h
    refine ⟨ck, .timeOut, { t2 with clock := t2.clock + 0 }, by omega, by omega, ?_,
      by simp, by simp, by simp, hffi, by simp, fun _ => rfl⟩
    have r0 := run 0
    simp only [Nat.add_zero] at r0 ⊢
    rw [r0, evaluate, if_pos (by simp [hclk2])]
  · -- `FinalFFI f`
    simp only [haltView] at h
    exact ⟨ck, _, t2, by omega, by omega, h.1,
      fun f' hf' => by simp only [Option.some.injEq, StackSemResult.finalFFI.injEq] at hf'; rw [hf'],
      by simp, by simp, h.2, by simp, by simp⟩
  · exact (nerr rfl).elim

/-! ## 7. End-to-End Composition: `StackRemove` → `StackNames` → `StackToLab` -/

/-- **End-to-End `StackRemove → StackNames → StackToLab` Clocked Bridge**
(`stackRemove_stackNames_stackToLab_clock`):
Composes `StackRemoveToStackNamesStateRelAndClockBridge.stackRemove_then_stackNames_clock`
(`clock + target.clock ≤ source.clock + 1` with `ClockOk clock result`) and
`stackToLab_flatten_clock_simulation` (`ck ≤ C_prog + (clock + target.clock - postTarget.clock) * M`).

When `stepCost (StackRemove.comp jump bounds pointer program) ≤ C_prog ≤ M` and
`CodeStepBounded M target`, any `LabSem` state `t1` related by
`stateRel (StackNames.renameState c f {target with clock := clock + target.clock}) t1`
simulates `StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program)` in at most
`ck ≤ C_prog + (source.clock + 1 - postTarget.clock) * M` extra ticks, and for `M ≤ 3` the total
`LabSem` clock is bounded by `t1.clock + ck ≤ 4 * source.clock + (C_prog + 4)`. -/
theorem stackRemove_stackNames_stackToLab_clock
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (t : Bool) (n l : Nat) (cs bs : List Nat)
    (M C_prog : Nat)
    (hnost : StackNoSt program = true) (hcodeNoSt : CodeNoSt source)
    (run : StackSemEvaluate.evaluate (program, source) = (result, postSource))
    (nonError : result ≠ some .error)
    (relation : StackRemove.stateRelHOL jump bounds pointer source target)
    (bound : StackProps.regBound program pointer)
    (hc : target.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f))
    (hcost : stepCost (StackRemove.comp jump bounds pointer program) ≤ C_prog)
    (hC_le_M : C_prog ≤ M)
    (hcode : CodeStepBounded M target) :
    ∃ clock postTarget,
      ClockOk clock result ∧
      clock + target.clock ≤ source.clock + 1 ∧
      StackSemEvaluate.evaluate
        (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program),
          StackNames.renameState c f {target with clock := clock + target.clock}) =
        (result, StackNames.renameState c f postTarget) ∧
      (StackNames.renameState c f postTarget).clock = postTarget.clock ∧
      ∀ (t1 : Flapjack.Compiler.Backend.LabSem.State width C F),
        stateRel (StackNames.renameState c f {target with clock := clock + target.clock}) t1 →
        StackProps.callArgs
          (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program))
          t1.ptrReg t1.lenReg t1.ptr2Reg t1.len2Reg t1.linkReg →
        codeInstalled t1.pc
          (appListAppend (flattenHOL t
            (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program)) n l cs bs).1)
          t1.code →
        (∀ k ∈ cs ++ bs ++ [0], (locToPc n k t1.code).isSome) →
        ∃ ck ≤ C_prog + (clock + source.clock - postTarget.clock) * M,
          t1.clock + ck ≤ (source.clock + 1) + C_prog + (source.clock + 1 - postTarget.clock) * M ∧
          (M ≤ 3 → t1.clock + ck ≤ 4 * source.clock + (C_prog + 4)) ∧
          LabSimAt
            (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program))
            t result (StackNames.renameState c f postTarget) n l cs bs t1 ck := by
  obtain ⟨clock, postTarget, hok, hclk_le, hEvalRen, hPostClk⟩ :=
    InitECandidate.Solver.StackRemoveToStackNamesStateRelAndClockBridge.stackRemove_then_stackNames_clock
      c f hf program source result postSource target pointer bounds jump
      hnost hcodeNoSt run nonError relation bound hc
  have hTgtClk : target.clock = source.clock :=
    (InitECandidate.Solver.StackRemoveToStackNamesStateRelAndClockBridge.stateRelHOL_compile_and_clock
      relation).2
  refine ⟨clock, postTarget, hok, hclk_le, hEvalRen, hPostClk,
    fun t1 hrel hca hinst hlabs => ?_⟩
  have hcostRen :
      stepCost (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program)) ≤ C_prog := by
    rw [stepCost_progCompHOL]
    exact hcost
  have hcodeTgtClk : CodeStepBounded M {target with clock := clock + target.clock} := hcode
  have hcodeRen : CodeStepBounded M
      (StackNames.renameState c f {target with clock := clock + target.clock}) :=
    codeStepBounded_renameState M c f {target with clock := clock + target.clock} hcodeTgtClk
  have hyps : FlattenHyps
      (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program))
      (StackNames.renameState c f {target with clock := clock + target.clock})
      t result (StackNames.renameState c f postTarget) n l cs bs t1 :=
    ⟨hEvalRen, nonError, hrel, hca, hinst, hlabs⟩
  obtain ⟨ck, hck, hsim⟩ :=
    stackToLab_flatten_clock_simulation M
      (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program))
      (StackNames.renameState c f {target with clock := clock + target.clock})
      (Nat.le_trans hcostRen hC_le_M) hcodeRen
      t result (StackNames.renameState c f postTarget) n l cs bs t1 hyps
  have hclk_t1 : t1.clock = clock + source.clock := by
    have := relClock hrel
    simpa [StackNames.renameState, hTgtClk] using this
  have hck_bound : ck ≤ C_prog + (clock + source.clock - postTarget.clock) * M := by
    have := stepCost_progCompHOL f (StackRemove.comp jump bounds pointer program)
    simp only [StackNames.renameState, hTgtClk] at hck
    omega
  have hdiff_le : (clock + source.clock - postTarget.clock) * M ≤
      (source.clock + 1 - postTarget.clock) * M :=
    Nat.mul_le_mul_right M (by omega)
  refine ⟨ck, hck_bound, by omega, fun hM3 => ?_, hsim⟩
  have hmul3 : (source.clock + 1 - postTarget.clock) * M ≤ (source.clock + 1) * 3 := by
    have h1 : (source.clock + 1 - postTarget.clock) * M ≤ (source.clock + 1) * M :=
      Nat.mul_le_mul_right M (by omega)
    have h2 : (source.clock + 1) * M ≤ (source.clock + 1) * 3 :=
      Nat.mul_le_mul_left _ hM3
    omega
  omega

/-- **Non-`Halt` Specialization of `StackRemove → StackNames → StackToLab`**
(`stackRemove_stackNames_stackToLab_noHalt_clock`):
When `result` is not `some (.halt _)`, `StackRemove` and `StackNames` add zero extra clock
(`clock = 0`), so the `LabSem` clock is bounded directly by
`t1.clock + ck ≤ 4 * source.clock + C_prog` for `M ≤ 3`. -/
theorem stackRemove_stackNames_stackToLab_noHalt_clock
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (program : HolProg width)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (t : Bool) (n l : Nat) (cs bs : List Nat)
    (M C_prog : Nat)
    (hnost : StackNoSt program = true) (hcodeNoSt : CodeNoSt source)
    (run : StackSemEvaluate.evaluate (program, source) = (result, postSource))
    (nonError : result ≠ some .error)
    (noHalt : ∀ w, result ≠ some (.halt w))
    (relation : StackRemove.stateRelHOL jump bounds pointer source target)
    (bound : StackProps.regBound program pointer)
    (hc : target.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f))
    (hcost : stepCost (StackRemove.comp jump bounds pointer program) ≤ C_prog)
    (hC_le_M : C_prog ≤ M)
    (hcode : CodeStepBounded M target) :
    ∃ postTarget,
      StackSemEvaluate.evaluate
        (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program),
          StackNames.renameState c f {target with clock := source.clock}) =
        (result, StackNames.renameState c f postTarget) ∧
      (StackNames.renameState c f postTarget).clock = postTarget.clock ∧
      ∀ (t1 : Flapjack.Compiler.Backend.LabSem.State width C F),
        stateRel (StackNames.renameState c f {target with clock := source.clock}) t1 →
        StackProps.callArgs
          (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program))
          t1.ptrReg t1.lenReg t1.ptr2Reg t1.len2Reg t1.linkReg →
        codeInstalled t1.pc
          (appListAppend (flattenHOL t
            (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program)) n l cs bs).1)
          t1.code →
        (∀ k ∈ cs ++ bs ++ [0], (locToPc n k t1.code).isSome) →
        ∃ ck ≤ C_prog + (source.clock - postTarget.clock) * M,
          t1.clock + ck ≤ source.clock + C_prog + (source.clock - postTarget.clock) * M ∧
          (M ≤ 3 → t1.clock + ck ≤ 4 * source.clock + C_prog) ∧
          LabSimAt
            (StackNames.progCompHOL f (StackRemove.comp jump bounds pointer program))
            t result (StackNames.renameState c f postTarget) n l cs bs t1 ck := by
  obtain ⟨clock, postTarget, hok, _, hEvalRen, hPostClk, hLab⟩ :=
    stackRemove_stackNames_stackToLab_clock c f hf program source result postSource target
      pointer bounds jump t n l cs bs M C_prog hnost hcodeNoSt run nonError relation bound hc
      hcost hC_le_M hcode
  have h0 : clock = 0 := by
    rcases hok with h | ⟨-, w, hw⟩
    · exact h
    · exact absurd hw (noHalt w)
  have hTgtClk : target.clock = source.clock :=
    (InitECandidate.Solver.StackRemoveToStackNamesStateRelAndClockBridge.stateRelHOL_compile_and_clock
      relation).2
  subst h0
  rw [Nat.zero_add, hTgtClk] at hEvalRen hLab
  refine ⟨postTarget, hEvalRen, hPostClk, fun t1 hrel hca hinst hlabs => ?_⟩
  obtain ⟨ck, hck, _, _, hsim⟩ := hLab t1 hrel hca hinst hlabs
  rw [Nat.zero_add] at hck
  have hclk_t1 : t1.clock = source.clock := by
    have := relClock hrel
    simpa [StackNames.renameState] using this
  refine ⟨ck, hck, by omega, fun hM3 => ?_, hsim⟩
  have hmul3 : (source.clock - postTarget.clock) * M ≤ source.clock * 3 := by
    have h1 : (source.clock - postTarget.clock) * M ≤ source.clock * M :=
      Nat.mul_le_mul_right M (by omega)
    have h2 : source.clock * M ≤ source.clock * 3 :=
      Nat.mul_le_mul_left _ hM3
    omega
  omega

end MainSimulation

end InitECandidate.Solver.StackToLabClock
