import InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts
import Flapjack.Compiler.Backend.WordToWord.Compile

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.WordSimpPreservesNoStoreConsts

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordSsaCsePreserveNoStoreConsts

variable {width : Nat} [NeZero width]

theorem t_smartSeq (a b : WordLangProgHOL (BitVec width)) (ha : NoSt a = true)
    (hb : NoSt b = true) : NoSt (WordSimp.smartSeqHOL a b) = true := by
  unfold WordSimp.smartSeqHOL; split <;> simp_all [NoSt]

theorem t_dropConsts (cs : Spt (BitVec width)) :
    ∀ l : List Nat, NoSt (WordSimp.dropConsts cs l) = true
  | [] => rfl
  | n :: ns => by
      rw [WordSimp.dropConsts]; split
      · exact t_dropConsts cs ns
      · exact t_smartSeq _ _ (t_dropConsts cs ns) rfl

theorem t_seqAssoc :
    ∀ (p1 q : WordLangProgHOL (BitVec width)), NoSt p1 = true → NoSt q = true →
      NoSt (WordSimp.seqAssoc p1 q) = true
  | p1, .skip, h1, _ => by rw [WordSimp.seqAssoc]; exact h1
  | p1, .seq a b, h1, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; exact t_seqAssoc _ b (t_seqAssoc p1 a h1 h.1) h.2
  | p1, .ite v n r a b, h1, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_seqAssoc _ a rfl h.1, t_seqAssoc _ b rfl h.2⟩
  | p1, .mustTerminate a, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 (t_seqAssoc _ a rfl h)
  | p1, .loop x a y, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 (t_seqAssoc _ a rfl h)
  | p1, .call none d args none, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 rfl
  | p1, .call none d args (some (y1, q, y2, y3)), h1, h => by
      simp only [NoSt, Bool.true_and] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NoSt, Bool.true_and]; exact t_seqAssoc _ q rfl h
  | p1, .call (some (x1, x2, r, x3, x4)) d args none, h1, h => by
      simp only [NoSt, Bool.and_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NoSt, Bool.and_true]; exact t_seqAssoc _ r rfl h
  | p1, .call (some (x1, x2, r, x3, x4)) d args (some (y1, q, y2, y3)), h1, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_seqAssoc _ r rfl h.1, t_seqAssoc _ q rfl h.2⟩
  | p1, .move .., h1, h | p1, .inst .., h1, h | p1, .assign .., h1, h | p1, .get .., h1, h
  | p1, .set .., h1, h | p1, .store .., h1, h | p1, .alloc .., h1, h
  | p1, .storeConsts .., h1, h | p1, .raise .., h1, h | p1, .return .., h1, h
  | p1, .break .., h1, h | p1, .continue .., h1, h | p1, .tick, h1, h
  | p1, .opCurrHeap .., h1, h | p1, .locValue .., h1, h | p1, .install .., h1, h
  | p1, .codeBufferWrite .., h1, h | p1, .dataBufferWrite .., h1, h | p1, .ffi .., h1, h
  | p1, .shareInst .., h1, h => by
      rw [WordSimp.seqAssoc] <;> first | exact t_smartSeq _ _ h1 h | (intros; simp_all) | skip
termination_by _ q => sizeOf q
decreasing_by all_goals (simp_wf; try omega)

theorem t_constFpLoop :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width)),
      NoSt p = true → NoSt (WordSimp.constFpLoop p cs).1 = true
  | .seq a b, cs, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordSimp.constFpLoop]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_constFpLoop a _ h.1, t_constFpLoop b _ h.2⟩
  | .ite c l r a b, cs, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordSimp.constFpLoop]; dsimp only
      split
      · split
        · exact t_constFpLoop a _ h.1
        · exact t_constFpLoop b _ h.2
      · simp only [NoSt, Bool.and_eq_true]
        exact ⟨t_constFpLoop a _ h.1, t_constFpLoop b _ h.2⟩
  | .mustTerminate a, cs, h => by rw [WordSimp.constFpLoop]; exact t_constFpLoop a _ h
  | .loop x a y, cs, h => by rw [WordSimp.constFpLoop]; exact t_constFpLoop a _ h
  | .call none d args hd, cs, h => by
      rw [WordSimp.constFpLoop]; exact t_smartSeq _ _ (t_dropConsts _ _) h
  | .call (some (n, nm, r, l1, l2)) d args none, cs, h => by
      simp only [NoSt, Bool.and_true] at h
      rw [WordSimp.constFpLoop]; dsimp only
      apply t_smartSeq _ _ (t_dropConsts _ _)
      simp only [NoSt, Bool.and_true]; exact t_constFpLoop r _ h
  | .call (some (n, nm, r, l1, l2)) d args (some hh), cs, h => by
      rw [WordSimp.constFpLoop]; exact t_smartSeq _ _ (t_dropConsts _ _) h
  | .ffi .., cs, h | .alloc .., cs, h | .install .., cs, h => by
      rw [WordSimp.constFpLoop]; exact t_smartSeq _ _ (t_dropConsts _ _) rfl
  | .storeConsts .., _, h => by simp [NoSt] at h
  | .shareInst op v e, cs, h => by
      cases op <;> (rw [WordSimp.constFpLoop]) <;> rfl
  | .assign v e, cs, h => by
      rw [WordSimp.constFpLoop]; split <;> rfl
  | .skip, _, h | .move .., _, h | .inst .., _, h | .get .., _, h
  | .set .., _, h | .store .., _, h | .raise .., _, h | .return .., _, h
  | .break .., _, h | .continue .., _, h | .tick, _, h
  | .opCurrHeap .., _, h | .locValue .., _, h
  | .codeBufferWrite .., _, h | .dataBufferWrite .., _, h => by
      rw [WordSimp.constFpLoop] <;> first | rfl | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_constFp (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true) :
    NoSt (WordSimp.constFp p) = true := t_constFpLoop p _ h

theorem t_destIf (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true)
    (c : Cmp) (l : Nat) (r : WordRegImm (BitVec width)) (b1 b2 : WordLangProgHOL (BitVec width))
    (e : WordSimp.destIf p = some (c, l, r, b1, b2)) : NoSt b1 = true ∧ NoSt b2 = true := by
  unfold WordSimp.destIf at e; split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, -, -, rfl, rfl⟩ := e
    simpa [NoSt] using h
  · simp at e

theorem t_tryIfHoist2 : ∀ (n : Nat) (p1 interm dummy p2 r : WordLangProgHOL (BitVec width)),
    NoSt p1 = true → NoSt interm = true → NoSt p2 = true →
      WordSimp.tryIfHoist2 n p1 interm dummy p2 = some r → NoSt r = true
  | 0, _, _, _, _, _, _, _, _, e => by simp [WordSimp.tryIfHoist2] at e
  | n + 1, p1, interm, dummy, p2, r, h1, hi, h2, e => by
      unfold WordSimp.tryIfHoist2 at e
      split at e
      · rename_i c l rr b1 b2
        simp only [NoSt, Bool.and_eq_true] at h1
        dsimp only at e
        split at e; · simp at e
        split at e; · simp at e
        simp only [Option.some.injEq] at e; subst e
        apply t_constFp; simp_all [NoSt]
      · rename_i p3 p4
        simp only [NoSt, Bool.and_eq_true] at h1
        split at e
        · rename_i c l rr b1 b2 hd
          have hb := t_destIf p4 h1.2 _ _ _ _ _ hd
          dsimp only at e
          split at e; · simp at e
          split at e; · simp at e
          simp only [Option.some.injEq] at e; subst e
          simp only [NoSt, Bool.and_eq_true]
          refine ⟨h1.1, t_constFp _ ?_⟩
          simp_all [NoSt]
        · split at e
          · exact t_tryIfHoist2 n p3 _ dummy p2 r h1.1 (by simp_all [NoSt]) h2 e
          · simp at e
      · simp at e

theorem t_tryIfHoist1 (p1 p2 r : WordLangProgHOL (BitVec width)) (h1 : NoSt p1 = true)
    (h2 : NoSt p2 = true) (e : WordSimp.tryIfHoist1 p1 p2 = some r) : NoSt r = true := by
  unfold WordSimp.tryIfHoist1 at e; split at e
  · simp at e
  · exact t_tryIfHoist2 _ _ _ _ _ _ h1 rfl h2 e

theorem t_simpDuplicateIf :
    ∀ (p : WordLangProgHOL (BitVec width)), NoSt p = true → NoSt (WordSimp.simpDuplicateIf p) = true
  | .seq a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      have ha := t_simpDuplicateIf a h.1
      have hb := t_simpDuplicateIf b h.2
      rw [WordSimp.simpDuplicateIf]
      split
      · simp only [NoSt, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · rename_i p3 e
        exact t_seqAssoc _ _ rfl (t_tryIfHoist1 _ _ _ ha hb e)
  | .ite c l r a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordSimp.simpDuplicateIf]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_simpDuplicateIf a h.1, t_simpDuplicateIf b h.2⟩
  | .mustTerminate a, h => by rw [WordSimp.simpDuplicateIf]; exact t_simpDuplicateIf a h
  | .loop x a y, h => by rw [WordSimp.simpDuplicateIf]; exact t_simpDuplicateIf a h
  | .call none d args none, h => by rw [WordSimp.simpDuplicateIf]; rfl
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordSimp.simpDuplicateIf]; simp only [NoSt, Bool.true_and] at h ⊢; exact t_simpDuplicateIf q h
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordSimp.simpDuplicateIf]; simp only [NoSt, Bool.and_true] at h ⊢; exact t_simpDuplicateIf r h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordSimp.simpDuplicateIf]; simp only [NoSt, Bool.and_eq_true] at h ⊢
      exact ⟨t_simpDuplicateIf r h.1, t_simpDuplicateIf q h.2⟩
  | .skip, h | .move .., h | .inst .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .opCurrHeap .., h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by
      rw [WordSimp.simpDuplicateIf] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_pushOutIfAux :
    ∀ (p : WordLangProgHOL (BitVec width)), NoSt p = true → NoSt (WordSimp.pushOutIfAux p).1 = true
  | .seq a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      have ha := t_pushOutIfAux a h.1
      have hb := t_pushOutIfAux b h.2
      rw [WordSimp.pushOutIfAux]
      split
      · rename_i c1 e; rw [e] at ha; simp_all [NoSt]
      · rename_i c1 e; rw [e] at ha; split
        rename_i c2 bb e2; rw [e2] at hb; simp_all [NoSt]
  | .ite c l r a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      have ha := t_pushOutIfAux a h.1
      have hb := t_pushOutIfAux b h.2
      rw [WordSimp.pushOutIfAux]
      split <;> (rename_i e1 e2; rw [e1] at ha; rw [e2] at hb; simp_all [NoSt])
  | .mustTerminate a, h => by
      have ha := t_pushOutIfAux a h
      rw [WordSimp.pushOutIfAux]; split; rename_i c b e; rw [e] at ha; exact ha
  | .loop x a y, h => by rw [WordSimp.pushOutIfAux]; exact t_pushOutIfAux a h
  | .call none .., h => by rw [WordSimp.pushOutIfAux]; exact h
  | .call (some _) d args hd, h => by
      rw [WordSimp.pushOutIfAux] <;> first | exact h | (intros; simp_all) | skip
  | .skip, h | .move .., h | .inst .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .opCurrHeap .., h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by
      rw [WordSimp.pushOutIfAux] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_pushOutIf (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true) :
    NoSt (WordSimp.pushOutIf p) = true := t_pushOutIfAux p h

theorem t_compileExp (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true) :
    NoSt (WordSimp.compileExp p) = true := by
  unfold WordSimp.compileExp
  exact t_pushOutIf _ (t_simpDuplicateIf _ (t_constFp _ (t_seqAssoc _ _ rfl h)))

/-- LoopToWord output, then WordSimp, then every pass of `compileSingle` up to
(but excluding) `wordAlloc`, in the exact source order. -/
theorem t_loopToWord_simp_chain (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (c : AsmConfigExact width) (temp argc : Nat) (b : Bool) :
    NoSt (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
      (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
        (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp
          (WordSimp.compileExp (LoopToWord.compHOL ctx q l).1))))))))) = true :=
  t_ssa_cse_mid_tail_chain c temp argc b _ (t_compileExp _ (loopToWord_NoSt ctx q l))

theorem allowance_zero_through_simp (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (c : AsmConfigExact width) (temp argc : Nat) (b : Bool) :
    storeConstsAllowance (WordAlloc.removeDeadProg (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordCse.wordCommonSubexpElim
        (WordAlloc.removeDeadProg (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp
          (WordSimp.compileExp (LoopToWord.compHOL ctx q l).1))))))))) = 0 := by
  simp [storeConstsAllowance, t_loopToWord_simp_chain ctx q l c temp argc b]

/-- `WordSimp.compileExp` keeps an existing `storeConsts`: the invariant is not vacuous. -/
theorem compileExp_keeps_storeConsts :
    NoSt (WordSimp.compileExp (WordLangProgHOL.storeConsts (α := BitVec width) 0 2 4 6 [])) = false := by
  simp [WordSimp.compileExp, WordSimp.seqAssoc, WordSimp.smartSeqHOL, WordSimp.constFp,
    WordSimp.constFpLoop, WordSimp.simpDuplicateIf, WordSimp.pushOutIf, WordSimp.pushOutIfAux, NoSt]


end InitECandidate.Solver.WordSimpPreservesNoStoreConsts
