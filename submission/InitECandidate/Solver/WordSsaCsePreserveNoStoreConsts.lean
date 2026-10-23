import InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
import Flapjack.Compiler.Backend.WordToWord.Compile

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts

theorem t_listNextVarRenameMove {width : Nat} [NeZero width] (ssa : Spt Nat) (n : Nat)
    (ls : List Nat) : NoSt (listNextVarRenameMove (width := width) ssa n ls).1 = true := by
  unfold listNextVarRenameMove; rfl

theorem t_ssaReconcile {width : Nat} [NeZero width] {β : Type} (a b : Spt Nat) (ns : Spt β) :
    NoSt (ssaReconcile (width := width) a b ns) = true := by
  unfold ssaReconcile; dsimp only; split <;> rfl

theorem t_fakeMoveFold {width : Nat} [NeZero width] (l : List Nat) :
    NoSt ((l.map fun r => fakeMove (width := width) r).foldr .seq .skip) = true := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.foldr_cons, NoSt, Bool.and_eq_true]; exact ⟨rfl, ih⟩

theorem t_loopSetup {width : Nat} [NeZero width] (names exitNames : Spt Unit) (ssa : Spt Nat)
    (na : Nat) : NoSt (loopSetup (width := width) names exitNames ssa na).1 = true := by
  unfold loopSetup
  simp only [NoSt, Bool.and_eq_true]
  exact ⟨t_fakeMoveFold _, t_listNextVarRenameMove _ _ _⟩

theorem t_fakeMoves {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit)) :
    ∀ (l : List Nat) (sl sr : Spt Nat) (na : Nat),
      NoSt (fakeMoves (width := width) prio l sl sr na).1 = true ∧
      NoSt (fakeMoves (width := width) prio l sl sr na).2.1 = true
  | [], _, _, _ => ⟨rfl, rfl⟩
  | x :: xs, sl, sr, na => by
      have ih := t_fakeMoves (width := width) prio xs sl sr na
      rw [fakeMoves]; dsimp only
      split <;> simp_all [NoSt, fakeMove]

theorem t_fixInconsistencies {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit))
    (sl sr : Spt Nat) (na : Nat) :
    NoSt (fixInconsistencies (width := width) prio sl sr na).1 = true ∧
    NoSt (fixInconsistencies (width := width) prio sl sr na).2.1 = true := by
  unfold fixInconsistencies; dsimp only
  have := t_fakeMoves (width := width) prio
  simp_all [NoSt]

theorem t_ssaCcTransInst {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (ssa : Spt Nat) (na : Nat) : NoSt (ssaCcTransInst i ssa na).1 = true := by
  unfold ssaCcTransInst; (repeat' split) <;> simp_all [NoSt]

theorem t_ssaCcTrans {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (na : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      NoSt p = true → NoSt (ssaCcTrans p ssa na lt).1 = true
  | .seq a b, ssa, na, lt, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_ssaCcTrans a _ _ _ h.1, t_ssaCcTrans b _ _ _ h.2⟩
  | .ite cm r ri a b, ssa, na, lt, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; simp only [NoSt, Bool.and_eq_true]
      have hf := t_fixInconsistencies (width := width)
      exact ⟨⟨t_ssaCcTrans a _ _ _ h.1, (hf _ _ _ _).1⟩, ⟨t_ssaCcTrans b _ _ _ h.2, (hf _ _ _ _).2⟩⟩
  | .mustTerminate a, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; exact t_ssaCcTrans a _ _ _ h
  | .loop names body ex, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; dsimp only
      simp only [NoSt, Bool.and_eq_true]
      refine ⟨t_loopSetup _ _ _ _, ?_⟩
      split
      · exact t_ssaCcTrans body _ _ _ h
      · simp only [NoSt, Bool.and_eq_true]; exact ⟨t_ssaCcTrans body _ _ _ h, t_ssaReconcile _ _ _⟩
  | .call none d args hd, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; dsimp only
      rcases hd with _ | ⟨h1, q, h2, h3⟩ <;> simp_all [NoSt]
  | .call (some (r1, r2, r, r3, r4)) d args none, ssa, na, lt, h => by
      simp only [NoSt, Bool.and_true] at h
      rw [ssaCcTrans.eq_def]; dsimp only
      simp only [NoSt, Bool.and_eq_true, Bool.and_true, t_listNextVarRenameMove, true_and]
      exact t_ssaCcTrans r _ _ _ h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), ssa, na, lt, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; dsimp only
      have hf := t_fixInconsistencies (width := width)
      simp only [NoSt, Bool.and_eq_true, t_listNextVarRenameMove, true_and, and_true]
      exact ⟨⟨t_ssaCcTrans r _ _ _ h.1, (hf _ _ _ _).1⟩, ⟨t_ssaCcTrans q _ _ _ h.2, (hf _ _ _ _).2⟩⟩
  | .inst i, ssa, na, lt, h => by rw [ssaCcTrans.eq_def]; exact t_ssaCcTransInst i ssa na
  | .storeConsts .., _, _, _, h => by simp [NoSt] at h
  | .skip, _, _, _, h | .move .., _, _, _, h | .get .., _, _, _, h
  | .set .., _, _, _, h | .assign .., _, _, _, h | .store .., _, _, _, h | .alloc .., _, _, _, h
  | .raise .., _, _, _, h | .return .., _, _, _, h
  | .break .., _, _, _, h | .continue .., _, _, _, h | .tick, _, _, _, h
  | .opCurrHeap .., _, _, _, h | .locValue .., _, _, _, h | .install .., _, _, _, h
  | .codeBufferWrite .., _, _, _, h | .dataBufferWrite .., _, _, _, h | .ffi .., _, _, _, h
  | .shareInst .., _, _, _, h => by
      rw [ssaCcTrans.eq_def] <;> (try dsimp only) <;> (repeat' (first | split_ifs | split)) <;>
        simp_all [NoSt, t_listNextVarRenameMove, t_ssaReconcile]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_fullSsaCcTrans {width : Nat} [NeZero width] (n : Nat)
    (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true) :
    NoSt (fullSsaCcTrans n p) = true := by
  unfold fullSsaCcTrans setupSSA; dsimp only
  simp only [NoSt, Bool.true_and]; exact t_ssaCcTrans p _ _ _ h

theorem t_addToDataAux {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (key : List Nat) (o : WordLangProgHOL (BitVec width)) (h : NoSt o = true) :
    NoSt (WordCse.addToDataAux data d key o).2 = true := by
  unfold WordCse.addToDataAux; (repeat' (first | split_ifs | split)) <;> simp_all [NoSt]

theorem t_addToLoadAux {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (key : List Nat) (o : WordLangProgHOL (BitVec width)) (h : NoSt o = true) :
    NoSt (WordCse.addToLoadAux data d key o).2 = true := by
  unfold WordCse.addToLoadAux; (repeat' (first | split_ifs | split)) <;> simp_all [NoSt]

theorem t_addToDataConst {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (w : BitVec width) : NoSt (WordCse.addToDataConst data d w).2 = true := by
  unfold WordCse.addToDataConst; dsimp only; split <;> rfl

theorem t_wordCseInst {width : Nat} [NeZero width] (data : WordCse.Knowledge)
    (i : HolInst width) : NoSt (WordCse.wordCseInst data i).2 = true := by
  cases i with
  | skip => rfl
  | const r w =>
      unfold WordCse.wordCseInst; dsimp only; split
      · rfl
      · exact t_addToDataConst _ _ _
  | arith a =>
      unfold WordCse.wordCseInst; dsimp only; split
      · unfold WordCse.addToData; exact t_addToDataAux _ _ _ _ rfl
      · rfl
  | mem op r ad =>
      cases ad with
      | addr a ofs =>
        unfold WordCse.wordCseInst; dsimp only
        (repeat' (first | split_ifs | split)) <;>
          first | rfl | exact t_addToLoadAux _ _ _ _ rfl

theorem t_wordCse {width : Nat} [NeZero width] :
    ∀ (data : WordCse.Knowledge) (p : WordLangProgHOL (BitVec width)),
      NoSt p = true → NoSt (WordCse.wordCse data p).2 = true
  | data, .seq a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordCse.wordCse.eq_def]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_wordCse _ a h.1, t_wordCse _ b h.2⟩
  | data, .ite cm r ri a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordCse.wordCse.eq_def]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_wordCse _ a h.1, t_wordCse _ b h.2⟩
  | data, .mustTerminate a, h => by rw [WordCse.wordCse.eq_def]; exact t_wordCse _ a h
  | data, .loop x a y, h => by rw [WordCse.wordCse.eq_def]; exact t_wordCse _ a h
  | data, .inst i, h => by rw [WordCse.wordCse.eq_def]; exact t_wordCseInst _ _
  | data, .get r x, h => by
      rw [WordCse.wordCse.eq_def]; unfold WordCse.getClause; dsimp only
      (repeat' (first | split_ifs | split)) <;> rfl
  | data, .set x e, h => by
      rw [WordCse.wordCse.eq_def]; unfold WordCse.setClause; dsimp only
      (repeat' (first | split_ifs | split)) <;> rfl
  | data, .opCurrHeap .., h => by
      rw [WordCse.wordCse.eq_def]; dsimp only; split_ifs
      · rfl
      · exact t_addToDataAux _ _ _ _ rfl
  | data, .locValue .., h => by
      rw [WordCse.wordCse.eq_def]; exact t_addToDataAux _ _ _ _ rfl
  | data, .call .., h | data, .skip, h | data, .move .., h
  | data, .assign .., h | data, .store .., h | data, .alloc .., h
  | data, .storeConsts .., h | data, .raise .., h | data, .return .., h
  | data, .break .., h | data, .continue .., h | data, .tick, h
  | data, .install .., h | data, .codeBufferWrite .., h | data, .dataBufferWrite .., h
  | data, .ffi .., h | data, .shareInst .., h => by
      rw [WordCse.wordCse.eq_def] <;> first | exact h | (intros; simp_all) | skip
termination_by _ p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_wordCommonSubexpElim {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : NoSt p = true) : NoSt (WordCse.wordCommonSubexpElim p) = true := by
  unfold WordCse.wordCommonSubexpElim; exact t_wordCse _ p h

/-- Exact post-`instSelect` segment of `compileSingle` (before `wordAlloc`), then
`removeMustTerminate`: ssa → removeDead → cse → copyProp → threeToTwo → removeUnreach
→ removeDead. Plus the compiled-order mid/tail chain. -/
theorem t_ssa_cse_mid_tail_chain {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp argc : Nat) (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true) :
    NoSt (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
      (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
        (fullSsaCcTrans argc (WordInst.instSelect c temp p)))))))) = true :=
  t_removeDeadProg _ (t_removeUnreach _ (t_threeToTwo b _ (t_copyProp _
    (t_wordCommonSubexpElim _ (t_removeDeadProg _ (t_fullSsaCcTrans argc _
      (t_instSelect c temp p h)))))))

/-- Corollary: no `storeConsts` instruction anywhere, hence no StackRemove
allowance source (the only non-zero allowance in `CompCorrect` is `StoreConsts`). -/
def storeConstsAllowance {α : Type} (p : WordLangProgHOL α) : Nat := if NoSt p then 0 else 1

theorem storeConstsAllowance_chain_zero {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp argc : Nat) (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true) :
    storeConstsAllowance (WordAlloc.removeDeadProg (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordCse.wordCommonSubexpElim
        (WordAlloc.removeDeadProg (fullSsaCcTrans argc (WordInst.instSelect c temp p)))))))) = 0 := by
  simp [storeConstsAllowance, t_ssa_cse_mid_tail_chain c temp argc b p h]

theorem storeConstsAllowance_tight {α : Type} :
    storeConstsAllowance (WordLangProgHOL.storeConsts (α := α) 0 2 4 6 []) = 1 := rfl


end InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts
