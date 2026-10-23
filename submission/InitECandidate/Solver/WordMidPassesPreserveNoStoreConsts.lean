import InitECandidate.Solver.WordPassesPreserveNoStoreConsts
import Flapjack.Compiler.Backend.WordToWord.Compile

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts

open Flapjack
open Flapjack.Compiler.Backend
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open Flapjack.Compiler.Encoders.Asm

theorem t_instSelectExp {width : Nat} [NeZero width] (c : AsmConfigExact width) :
    ∀ (n : Nat) (tar temp : Nat) (e : WordLangExpHOL (BitVec width)), sizeOf e = n →
      NoSt (WordInst.instSelectExp c tar temp e) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro tar temp e hn
    rw [WordInst.instSelectExp.eq_def]
    dsimp only
    (repeat' (first | split_ifs | split)) <;> simp only [NoSt, Bool.and_eq_true, Bool.and_true, Bool.true_and, and_true, true_and] <;>
      (repeat' constructor) <;>
      (try (exact ih _ (by subst hn; simp only [WordLangExpHOL.load.sizeOf_spec, WordLangExpHOL.op.sizeOf_spec, WordLangExpHOL.shift.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega) _ _ _ rfl))

theorem t_ise {width : Nat} [NeZero width] (c : AsmConfigExact width) (tar temp : Nat)
    (e : WordLangExpHOL (BitVec width)) : NoSt (WordInst.instSelectExp c tar temp e) = true :=
  t_instSelectExp c _ tar temp e rfl

theorem t_copyPropInst {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (cs : WordCopy.CopyState) : NoSt (WordCopy.copyPropInst i cs).1 = true := by
  unfold WordCopy.copyPropInst; (repeat' split) <;> simp_all [NoSt]

theorem t_instSelect {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)), NoSt p = true → NoSt (WordInst.instSelect c temp p) = true
  | .seq a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordInst.instSelect.eq_def]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_instSelect c temp a h.1, t_instSelect c temp b h.2⟩
  | .ite cm r ri a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordInst.instSelect.eq_def]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_instSelect c temp a h.1, t_instSelect c temp b h.2⟩
  | .mustTerminate a, h => by rw [WordInst.instSelect.eq_def]; exact t_instSelect c temp a h
  | .loop x a y, h => by rw [WordInst.instSelect.eq_def]; exact t_instSelect c temp a h
  | .call none d args none, h => by rw [WordInst.instSelect.eq_def]; rfl
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.instSelect.eq_def]; simp only [NoSt, Bool.true_and] at h ⊢; exact t_instSelect c temp q h
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordInst.instSelect.eq_def]; simp only [NoSt, Bool.and_true] at h ⊢; exact t_instSelect c temp r h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.instSelect.eq_def]; simp only [NoSt, Bool.and_eq_true] at h ⊢
      exact ⟨t_instSelect c temp r h.1, t_instSelect c temp q h.2⟩
  | .assign .., h | .set .., h | .store .., h | .shareInst .., h => by
      rw [WordInst.instSelect.eq_def]; dsimp only
      (repeat' (first | split_ifs | split)) <;> simp_all [NoSt, t_ise]
  | .skip, h | .move .., h | .inst .., h | .get .., h | .alloc .., h | .storeConsts .., h
  | .raise .., h | .return .., h | .break .., h | .continue .., h | .tick, h
  | .opCurrHeap .., h | .locValue .., h | .install .., h | .codeBufferWrite .., h
  | .dataBufferWrite .., h | .ffi .., h => by
      rw [WordInst.instSelect.eq_def] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_removeDead {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
      (lt : List (NumSet × NumSet)), NoSt p = true → NoSt (WordAlloc.removeDead p live nlive lt).1 = true
  | .seq a b, live, nlive, lt, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordAlloc.removeDead.eq_def]; dsimp only
      have h2 := t_removeDead b live nlive lt h.2
      have h1 := t_removeDead a (WordAlloc.removeDead b live nlive lt).2.1 (WordAlloc.removeDead b live nlive lt).2.2 lt h.1
      split <;> simp_all [NoSt]
  | .ite cm r ri a b, live, nlive, lt, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordAlloc.removeDead.eq_def]; dsimp only
      have h1 := t_removeDead a live nlive lt h.1
      have h2 := t_removeDead b live nlive lt h.2
      (repeat' split) <;> simp_all [NoSt]
  | .mustTerminate a, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; exact t_removeDead a live nlive lt h
  | .loop x a y, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; exact t_removeDead a _ _ _ h
  | .call none d args hd, live, nlive, lt, h => by rw [WordAlloc.removeDead.eq_def]; exact h
  | .call (some (r1, r2, r, r3, r4)) d args none, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; simp only [NoSt, Bool.and_true] at h ⊢; exact t_removeDead r _ _ _ h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; simp only [NoSt, Bool.and_eq_true] at h ⊢
      exact ⟨t_removeDead r _ _ _ h.1, t_removeDead q _ _ _ h.2⟩
  | .skip, _, _, _, h | .move .., _, _, _, h | .inst .., _, _, _, h | .get .., _, _, _, h
  | .set .., _, _, _, h | .assign .., _, _, _, h | .store .., _, _, _, h | .alloc .., _, _, _, h
  | .storeConsts .., _, _, _, h | .raise .., _, _, _, h | .return .., _, _, _, h
  | .break .., _, _, _, h | .continue .., _, _, _, h | .tick, _, _, _, h
  | .opCurrHeap .., _, _, _, h | .locValue .., _, _, _, h | .install .., _, _, _, h
  | .codeBufferWrite .., _, _, _, h | .dataBufferWrite .., _, _, _, h | .ffi .., _, _, _, h
  | .shareInst .., _, _, _, h => by
      rw [WordAlloc.removeDead.eq_def] <;> (try dsimp only) <;> (repeat' (first | split_ifs | split)) <;>
        first | exact h | rfl | (intros; simp_all) | simp_all [NoSt]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_removeDeadProg {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : NoSt p = true) : NoSt (WordAlloc.removeDeadProg p) = true :=
  t_removeDead p _ _ _ h

theorem t_copyPropProg {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : WordCopy.CopyState),
      NoSt p = true → NoSt (WordCopy.copyPropProg p cs).1 = true
  | .seq a b, cs, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordCopy.copyPropProg.eq_def]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_copyPropProg a cs h.1, t_copyPropProg b _ h.2⟩
  | .ite cm r ri a b, cs, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordCopy.copyPropProg.eq_def]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_copyPropProg a cs h.1, t_copyPropProg b cs h.2⟩
  | .mustTerminate a, cs, h => by rw [WordCopy.copyPropProg.eq_def]; exact t_copyPropProg a cs h
  | .loop x a y, cs, h => by rw [WordCopy.copyPropProg.eq_def]; exact t_copyPropProg a _ h
  | .inst i, cs, h => by rw [WordCopy.copyPropProg.eq_def]; exact t_copyPropInst i cs
  | .call .., cs, h | .skip, cs, h | .move .., cs, h | .get .., cs, h
  | .set .., cs, h | .assign .., cs, h | .store .., cs, h | .alloc .., cs, h
  | .storeConsts .., cs, h | .raise .., cs, h | .return .., cs, h
  | .break .., cs, h | .continue .., cs, h | .tick, cs, h
  | .opCurrHeap .., cs, h | .locValue .., cs, h | .install .., cs, h
  | .codeBufferWrite .., cs, h | .dataBufferWrite .., cs, h | .ffi .., cs, h
  | .shareInst .., cs, h => by
      rw [WordCopy.copyPropProg.eq_def] <;> (try dsimp only) <;> (repeat' (first | split_ifs | split)) <;>
        first | exact h | rfl | simp_all [NoSt]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_copyProp {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : NoSt p = true) : NoSt (WordCopy.copyProp p) = true :=
  t_copyPropProg p _ h

/-- Proven segment of `fullCompileSingle` (SSA, CSE, WordSimp, wordAlloc still open):
instSelect → removeDeadProg → copyProp → threeToTwo → removeUnreach → removeMustTerminate. -/
theorem t_mid_tail_chain {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat)
    (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : NoSt p = true) :
    NoSt (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordAlloc.removeDeadProg
        (WordInst.instSelect c temp p)))))) = true :=
  t_tail_chain b _ (t_copyProp _ (t_removeDeadProg _ (t_instSelect c temp p h)))

/-- `instSelect` keeps an existing `storeConsts` (no erasure, no creation). -/
theorem instSelect_keeps_storeConsts {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp : Nat) : NoSt (WordInst.instSelect c temp
      (WordLangProgHOL.storeConsts (α := BitVec width) 0 2 4 6 [])) = false := by
  rw [WordInst.instSelect.eq_def]; rfl


end InitECandidate.Solver.WordMidPassesPreserveNoStoreConsts
