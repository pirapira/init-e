import InitECandidate.Solver.PanToWordNoStubCall
import InitECandidate.Solver.WordToWordFullCompileNoStoreConsts

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# The 10 WordToWord passes keep `WordNoStubCall`

Same pass decomposition as modules 298–302 (`NoSt` chain), with the predicate replaced by
"no call targets `storeConstsStubLocation`". Closes `hcall` of
`StackRemoveAndNamesNoStoreConsts.panToStackNames_bodies_NoSt_and_NoStubCall`.
-/

namespace InitECandidate.Solver.WordToWordNoStubCall

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Encoders.Asm

/-- Local copy of `WordNoStubCall` with the `NoSt`-chain recursion shape. -/
def NSC {α : Type} : WordLangProgHOL α → Bool
  | .mustTerminate b => NSC b
  | .seq a b => NSC a && NSC b
  | .ite _ _ _ a b => NSC a && NSC b
  | .loop _ b _ => NSC b
  | .call ret d _ h =>
      (d != some storeConstsStubLocation) &&
      (match ret with | none => true | some (_, _, r, _, _) => NSC r) &&
      (match h with | none => true | some (_, p, _, _) => NSC p)
  | _ => true

theorem NSC_eq {α : Type} : ∀ p : WordLangProgHOL α,
    NSC p = StackRemoveAndNamesNoStoreConsts.WordNoStubCall p
  | .mustTerminate b => by simp only [NSC, StackRemoveAndNamesNoStoreConsts.WordNoStubCall, NSC_eq b]
  | .seq a b => by simp only [NSC, StackRemoveAndNamesNoStoreConsts.WordNoStubCall, NSC_eq a, NSC_eq b]
  | .ite _ _ _ a b => by simp only [NSC, StackRemoveAndNamesNoStoreConsts.WordNoStubCall, NSC_eq a, NSC_eq b]
  | .loop _ b _ => by simp only [NSC, StackRemoveAndNamesNoStoreConsts.WordNoStubCall, NSC_eq b]
  | .call none _ _ none => rfl
  | .call none _ _ (some (_, p, _, _)) => by
      simp only [NSC, StackRemoveAndNamesNoStoreConsts.WordNoStubCall, NSC_eq p]
  | .call (some (_, _, r, _, _)) _ _ none => by
      simp only [NSC, StackRemoveAndNamesNoStoreConsts.WordNoStubCall, NSC_eq r]
  | .call (some (_, _, r, _, _)) _ _ (some (_, p, _, _)) => by
      simp only [NSC, StackRemoveAndNamesNoStoreConsts.WordNoStubCall, NSC_eq r, NSC_eq p]
  | .skip | .move .. | .inst .. | .assign .. | .get .. | .set .. | .store .. | .alloc ..
  | .storeConsts .. | .raise .. | .return .. | .break .. | .continue .. | .tick
  | .opCurrHeap .. | .locValue .. | .install .. | .codeBufferWrite .. | .dataBufferWrite ..
  | .ffi .. | .shareInst .. => rfl

section
variable {width : Nat} [NeZero width]

/-! ## from WordPassesPreserveNSCoreConsts -/



theorem t_removeMustTerminate {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)), NSC p = true → NSC (WordRemove.removeMustTerminate p) = true
  | .seq a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordRemove.removeMustTerminate]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_removeMustTerminate a h.1, t_removeMustTerminate b h.2⟩
  | .ite c r ri a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordRemove.removeMustTerminate]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_removeMustTerminate a h.1, t_removeMustTerminate b h.2⟩
  | .mustTerminate a, h => by
      rw [WordRemove.removeMustTerminate]; exact t_removeMustTerminate a h
  | .loop x a y, h => by
      rw [WordRemove.removeMustTerminate]; exact t_removeMustTerminate a h
  | .call none d args none, h => by rw [WordRemove.removeMustTerminate.eq_def]; first | exact h | rfl | simpa [NSC] using h
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_removeMustTerminate q h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_removeMustTerminate r h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [NSC, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, t_removeMustTerminate r h.1.2⟩, t_removeMustTerminate q h.2⟩
  | .skip, h | .move .., h | .inst .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .opCurrHeap .., h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by simp_all [WordRemove.removeMustTerminate, NSC]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_threeToTwoReg {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)), NSC p = true → NSC (WordInst.threeToTwoReg p) = true
  | .seq a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordInst.threeToTwoReg]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_threeToTwoReg a h.1, t_threeToTwoReg b h.2⟩
  | .ite c r ri a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordInst.threeToTwoReg]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_threeToTwoReg a h.1, t_threeToTwoReg b h.2⟩
  | .mustTerminate a, h => by
      rw [WordInst.threeToTwoReg]; exact t_threeToTwoReg a h
  | .loop x a y, h => by
      rw [WordInst.threeToTwoReg]; exact t_threeToTwoReg a h
  | .call none d args none, h => by rw [WordInst.threeToTwoReg.eq_def]; first | exact h | rfl | simpa [NSC] using h
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_threeToTwoReg q h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_threeToTwoReg r h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [NSC, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, t_threeToTwoReg r h.1.2⟩, t_threeToTwoReg q h.2⟩
  | .opCurrHeap .., h => by rw [WordInst.threeToTwoReg]; rfl
  | .inst i, h => by
      rw [WordInst.threeToTwoReg.eq_def]; split <;> simp_all [NSC]
  | .skip, h | .move .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by rw [WordInst.threeToTwoReg]; all_goals first | exact h | (intros; contradiction) | simp_all
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_threeToTwo {width : Nat} [NeZero width] (b : Bool) (p : WordLangProgHOL (BitVec width))
    (h : NSC p = true) : NSC (WordInst.threeToTwoRegProg b p) = true := by
  unfold WordInst.threeToTwoRegProg; split
  · exact t_threeToTwoReg p h
  · exact h

theorem t_destSeqMove {width : Nat} [NeZero width] (q : WordLangProgHOL (BitVec width))
    (hq : NSC q = true) (n : Nat) (l : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (h : WordUnreach.destSeqMove q = some (n, l, rest)) : NSC rest = true := by
  unfold WordUnreach.destSeqMove at h
  split at h <;> simp_all [NSC]
  all_goals (obtain ⟨-, -, rfl⟩ := h; simp_all [NSC])

theorem t_simpSeq {width : Nat} [NeZero width] (p q : WordLangProgHOL (BitVec width))
    (hp : NSC p = true) (hq : NSC q = true) : NSC (WordUnreach.simpSeq p q) = true := by
  unfold WordUnreach.simpSeq
  split
  · exact hp
  · split <;> (try exact hp) <;> (try exact hq) <;> (try simp_all [NSC])
    all_goals (split <;> (try simp_all [NSC]) <;> (try split) <;> (try simp_all [NSC]))
    all_goals (rename_i heq _; exact t_destSeqMove _ hq _ _ _ heq)

theorem t_seqAssocRight {width : Nat} [NeZero width] :
    ∀ (p acc : WordLangProgHOL (BitVec width)), NSC p = true → NSC acc = true →
      NSC (WordUnreach.seqAssocRight p acc) = true
  | .skip, acc, _, ha => by rw [WordUnreach.seqAssocRight]; exact ha
  | .seq a b, acc, hp, ha => by
      simp only [NSC, Bool.and_eq_true] at hp
      rw [WordUnreach.seqAssocRight]
      exact t_seqAssocRight a _ hp.1 (t_seqAssocRight b acc hp.2 ha)
  | .ite v n r a b, acc, hp, ha => by
      simp only [NSC, Bool.and_eq_true] at hp
      rw [WordUnreach.seqAssocRight]
      apply t_simpSeq _ _ _ ha
      simp only [NSC, Bool.and_eq_true]
      exact ⟨t_seqAssocRight a _ hp.1 rfl, t_seqAssocRight b _ hp.2 rfl⟩
  | .mustTerminate a, acc, hp, ha => by
      rw [WordUnreach.seqAssocRight]
      exact t_simpSeq _ _ (t_seqAssocRight a _ hp rfl) ha
  | .loop x a y, acc, hp, ha => by
      rw [WordUnreach.seqAssocRight]
      exact t_simpSeq _ _ (t_seqAssocRight a _ hp rfl) ha
  | .call none d args hd, acc, hp, ha => by rw [WordUnreach.seqAssocRight]; exact hp
  | .call (some (x1, x2, q1, x3, x4)) d args none, acc, hp, ha => by
      rw [WordUnreach.seqAssocRight]
      simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at hp
      apply t_simpSeq _ _ _ ha
      simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true]; exact ⟨hp.1, t_seqAssocRight q1 _ hp.2 rfl⟩
  | .call (some (x1, x2, q1, x3, x4)) d args (some (y1, q2, y2, y3)), acc, hp, ha => by
      rw [WordUnreach.seqAssocRight]
      simp only [NSC, Bool.and_eq_true] at hp
      apply t_simpSeq _ _ _ ha
      simp only [NSC, Bool.and_eq_true]
      exact ⟨⟨hp.1.1, t_seqAssocRight q1 _ hp.1.2 rfl⟩, t_seqAssocRight q2 _ hp.2 rfl⟩
  | .move .., acc, hp, ha | .inst .., acc, hp, ha | .assign .., acc, hp, ha | .get .., acc, hp, ha
  | .set .., acc, hp, ha | .store .., acc, hp, ha | .alloc .., acc, hp, ha
  | .storeConsts .., acc, hp, ha | .raise .., acc, hp, ha | .return .., acc, hp, ha
  | .break .., acc, hp, ha | .continue .., acc, hp, ha | .tick, acc, hp, ha
  | .opCurrHeap .., acc, hp, ha | .locValue .., acc, hp, ha | .install .., acc, hp, ha
  | .codeBufferWrite .., acc, hp, ha | .dataBufferWrite .., acc, hp, ha | .ffi .., acc, hp, ha
  | .shareInst .., acc, hp, ha => by
      rw [WordUnreach.seqAssocRight] <;> first | exact t_simpSeq _ _ hp ha | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_removeUnreach {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : NSC p = true) : NSC (WordUnreach.removeUnreach p) = true :=
  t_seqAssocRight p _ h rfl

/-- The tail `threeToTwo ∘ removeUnreach ∘ removeMustTerminate`-shaped fragment preserves `NSC`. -/
theorem t_tail_chain {width : Nat} [NeZero width] (b : Bool) (p : WordLangProgHOL (BitVec width))
    (h : NSC p = true) :
    NSC (WordRemove.removeMustTerminate (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b p))) = true :=
  t_removeMustTerminate _ (t_removeUnreach _ (t_threeToTwo b p h))

/-! ## from WordMidPassesPreserveNSCoreConsts -/


theorem t_instSelectExp {width : Nat} [NeZero width] (c : AsmConfigExact width) :
    ∀ (n : Nat) (tar temp : Nat) (e : WordLangExpHOL (BitVec width)), sizeOf e = n →
      NSC (WordInst.instSelectExp c tar temp e) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro tar temp e hn
    rw [WordInst.instSelectExp.eq_def]
    dsimp only
    (repeat' (first | split_ifs | split)) <;> simp only [NSC, Bool.and_eq_true, Bool.and_true, Bool.true_and, and_true, true_and] <;>
      (repeat' constructor) <;>
      (try (exact ih _ (by subst hn; simp only [WordLangExpHOL.load.sizeOf_spec, WordLangExpHOL.op.sizeOf_spec, WordLangExpHOL.shift.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega) _ _ _ rfl))

theorem t_ise {width : Nat} [NeZero width] (c : AsmConfigExact width) (tar temp : Nat)
    (e : WordLangExpHOL (BitVec width)) : NSC (WordInst.instSelectExp c tar temp e) = true :=
  t_instSelectExp c _ tar temp e rfl

theorem t_copyPropInst {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (cs : WordCopy.CopyState) : NSC (WordCopy.copyPropInst i cs).1 = true := by
  unfold WordCopy.copyPropInst; (repeat' split) <;> simp_all [NSC]

theorem t_instSelect {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)), NSC p = true → NSC (WordInst.instSelect c temp p) = true
  | .seq a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordInst.instSelect.eq_def]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_instSelect c temp a h.1, t_instSelect c temp b h.2⟩
  | .ite cm r ri a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordInst.instSelect.eq_def]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_instSelect c temp a h.1, t_instSelect c temp b h.2⟩
  | .mustTerminate a, h => by rw [WordInst.instSelect.eq_def]; exact t_instSelect c temp a h
  | .loop x a y, h => by rw [WordInst.instSelect.eq_def]; exact t_instSelect c temp a h
  | .call none d args none, h => by rw [WordInst.instSelect.eq_def]; first | exact h | rfl | simpa [NSC] using h
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.instSelect.eq_def]; simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_instSelect c temp q h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordInst.instSelect.eq_def]; simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_instSelect c temp r h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.instSelect.eq_def]; simp only [NSC, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, t_instSelect c temp r h.1.2⟩, t_instSelect c temp q h.2⟩
  | .assign .., h | .set .., h | .store .., h | .shareInst .., h => by
      rw [WordInst.instSelect.eq_def]; dsimp only
      (repeat' (first | split_ifs | split)) <;> simp_all [NSC, t_ise]
  | .skip, h | .move .., h | .inst .., h | .get .., h | .alloc .., h | .storeConsts .., h
  | .raise .., h | .return .., h | .break .., h | .continue .., h | .tick, h
  | .opCurrHeap .., h | .locValue .., h | .install .., h | .codeBufferWrite .., h
  | .dataBufferWrite .., h | .ffi .., h => by
      rw [WordInst.instSelect.eq_def] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_removeDead {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
      (lt : List (NumSet × NumSet)), NSC p = true → NSC (WordAlloc.removeDead p live nlive lt).1 = true
  | .seq a b, live, nlive, lt, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordAlloc.removeDead.eq_def]; dsimp only
      have h2 := t_removeDead b live nlive lt h.2
      have h1 := t_removeDead a (WordAlloc.removeDead b live nlive lt).2.1 (WordAlloc.removeDead b live nlive lt).2.2 lt h.1
      split <;> simp_all [NSC]
  | .ite cm r ri a b, live, nlive, lt, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordAlloc.removeDead.eq_def]; dsimp only
      have h1 := t_removeDead a live nlive lt h.1
      have h2 := t_removeDead b live nlive lt h.2
      (repeat' split) <;> simp_all [NSC]
  | .mustTerminate a, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; exact t_removeDead a live nlive lt h
  | .loop x a y, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; exact t_removeDead a _ _ _ h
  | .call none d args hd, live, nlive, lt, h => by rw [WordAlloc.removeDead.eq_def]; exact h
  | .call (some (r1, r2, r, r3, r4)) d args none, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_removeDead r _ _ _ h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; simp only [NSC, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, t_removeDead r _ _ _ h.1.2⟩, t_removeDead q _ _ _ h.2⟩
  | .skip, _, _, _, h | .move .., _, _, _, h | .inst .., _, _, _, h | .get .., _, _, _, h
  | .set .., _, _, _, h | .assign .., _, _, _, h | .store .., _, _, _, h | .alloc .., _, _, _, h
  | .storeConsts .., _, _, _, h | .raise .., _, _, _, h | .return .., _, _, _, h
  | .break .., _, _, _, h | .continue .., _, _, _, h | .tick, _, _, _, h
  | .opCurrHeap .., _, _, _, h | .locValue .., _, _, _, h | .install .., _, _, _, h
  | .codeBufferWrite .., _, _, _, h | .dataBufferWrite .., _, _, _, h | .ffi .., _, _, _, h
  | .shareInst .., _, _, _, h => by
      rw [WordAlloc.removeDead.eq_def] <;> (try dsimp only) <;> (repeat' (first | split_ifs | split)) <;>
        first | exact h | rfl | (intros; simp_all) | simp_all [NSC]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_removeDeadProg {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : NSC p = true) : NSC (WordAlloc.removeDeadProg p) = true :=
  t_removeDead p _ _ _ h

theorem t_copyPropProg {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : WordCopy.CopyState),
      NSC p = true → NSC (WordCopy.copyPropProg p cs).1 = true
  | .seq a b, cs, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordCopy.copyPropProg.eq_def]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_copyPropProg a cs h.1, t_copyPropProg b _ h.2⟩
  | .ite cm r ri a b, cs, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordCopy.copyPropProg.eq_def]; simp only [NSC, Bool.and_eq_true]
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
        first | exact h | rfl | simp_all [NSC]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_copyProp {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : NSC p = true) : NSC (WordCopy.copyProp p) = true :=
  t_copyPropProg p _ h

/-- Proven segment of `fullCompileSingle` (SSA, CSE, WordSimp, wordAlloc still open):
instSelect → removeDeadProg → copyProp → threeToTwo → removeUnreach → removeMustTerminate. -/
theorem t_mid_tail_chain {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat)
    (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : NSC p = true) :
    NSC (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordAlloc.removeDeadProg
        (WordInst.instSelect c temp p)))))) = true :=
  t_tail_chain b _ (t_copyProp _ (t_removeDeadProg _ (t_instSelect c temp p h)))


/-! ## from WordSsaCsePreserveNSCoreConsts -/


theorem t_listNextVarRenameMove {width : Nat} [NeZero width] (ssa : Spt Nat) (n : Nat)
    (ls : List Nat) : NSC (listNextVarRenameMove (width := width) ssa n ls).1 = true := by
  unfold listNextVarRenameMove; rfl

theorem t_ssaReconcile {width : Nat} [NeZero width] {β : Type} (a b : Spt Nat) (ns : Spt β) :
    NSC (ssaReconcile (width := width) a b ns) = true := by
  unfold ssaReconcile; dsimp only; split <;> rfl

theorem t_fakeMoveFold {width : Nat} [NeZero width] (l : List Nat) :
    NSC ((l.map fun r => fakeMove (width := width) r).foldr .seq .skip) = true := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.foldr_cons, NSC, Bool.and_eq_true]; exact ⟨rfl, ih⟩

theorem t_loopSetup {width : Nat} [NeZero width] (names exitNames : Spt Unit) (ssa : Spt Nat)
    (na : Nat) : NSC (loopSetup (width := width) names exitNames ssa na).1 = true := by
  unfold loopSetup
  simp only [NSC, Bool.and_eq_true]
  exact ⟨t_fakeMoveFold _, t_listNextVarRenameMove _ _ _⟩

theorem t_fakeMoves {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit)) :
    ∀ (l : List Nat) (sl sr : Spt Nat) (na : Nat),
      NSC (fakeMoves (width := width) prio l sl sr na).1 = true ∧
      NSC (fakeMoves (width := width) prio l sl sr na).2.1 = true
  | [], _, _, _ => ⟨rfl, rfl⟩
  | x :: xs, sl, sr, na => by
      have ih := t_fakeMoves (width := width) prio xs sl sr na
      rw [fakeMoves]; dsimp only
      split <;> simp_all [NSC, fakeMove]

theorem t_fixInconsistencies {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit))
    (sl sr : Spt Nat) (na : Nat) :
    NSC (fixInconsistencies (width := width) prio sl sr na).1 = true ∧
    NSC (fixInconsistencies (width := width) prio sl sr na).2.1 = true := by
  unfold fixInconsistencies; dsimp only
  have := t_fakeMoves (width := width) prio
  simp_all [NSC]

theorem t_ssaCcTransInst {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (ssa : Spt Nat) (na : Nat) : NSC (ssaCcTransInst i ssa na).1 = true := by
  unfold ssaCcTransInst; (repeat' split) <;> simp_all [NSC]

theorem t_ssaCcTrans {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (na : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      NSC p = true → NSC (ssaCcTrans p ssa na lt).1 = true
  | .seq a b, ssa, na, lt, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_ssaCcTrans a _ _ _ h.1, t_ssaCcTrans b _ _ _ h.2⟩
  | .ite cm r ri a b, ssa, na, lt, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; simp only [NSC, Bool.and_eq_true]
      have hf := t_fixInconsistencies (width := width)
      exact ⟨⟨t_ssaCcTrans a _ _ _ h.1, (hf _ _ _ _).1⟩, ⟨t_ssaCcTrans b _ _ _ h.2, (hf _ _ _ _).2⟩⟩
  | .mustTerminate a, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; exact t_ssaCcTrans a _ _ _ h
  | .loop names body ex, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; dsimp only
      simp only [NSC, Bool.and_eq_true]
      refine ⟨t_loopSetup _ _ _ _, ?_⟩
      split
      · exact t_ssaCcTrans body _ _ _ h
      · simp only [NSC, Bool.and_eq_true]; exact ⟨t_ssaCcTrans body _ _ _ h, t_ssaReconcile _ _ _⟩
  | .call none d args hd, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; dsimp only
      rcases hd with _ | ⟨h1, q, h2, h3⟩ <;> simp_all [NSC]
  | .call (some (r1, r2, r, r3, r4)) d args none, ssa, na, lt, h => by
      simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h
      rw [ssaCcTrans.eq_def]; dsimp only
      simp only [NSC, Bool.and_eq_true, Bool.and_true, t_listNextVarRenameMove, true_and]
      exact ⟨h.1, t_ssaCcTrans r _ _ _ h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), ssa, na, lt, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; dsimp only
      have hf := t_fixInconsistencies (width := width)
      simp only [NSC, Bool.and_eq_true, t_listNextVarRenameMove, true_and, and_true]
      exact ⟨⟨h.1.1, t_ssaCcTrans r _ _ _ h.1.2, (hf _ _ _ _).1⟩, ⟨t_ssaCcTrans q _ _ _ h.2, (hf _ _ _ _).2⟩⟩
  | .inst i, ssa, na, lt, h => by rw [ssaCcTrans.eq_def]; exact t_ssaCcTransInst i ssa na
  | .storeConsts .., ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; dsimp only; simp [NSC]
  | .skip, _, _, _, h | .move .., _, _, _, h | .get .., _, _, _, h
  | .set .., _, _, _, h | .assign .., _, _, _, h | .store .., _, _, _, h | .alloc .., _, _, _, h
  | .raise .., _, _, _, h | .return .., _, _, _, h
  | .break .., _, _, _, h | .continue .., _, _, _, h | .tick, _, _, _, h
  | .opCurrHeap .., _, _, _, h | .locValue .., _, _, _, h | .install .., _, _, _, h
  | .codeBufferWrite .., _, _, _, h | .dataBufferWrite .., _, _, _, h | .ffi .., _, _, _, h
  | .shareInst .., _, _, _, h => by
      rw [ssaCcTrans.eq_def] <;> (try dsimp only) <;> (repeat' (first | split_ifs | split)) <;>
        simp_all [NSC, t_listNextVarRenameMove, t_ssaReconcile]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_fullSsaCcTrans {width : Nat} [NeZero width] (n : Nat)
    (p : WordLangProgHOL (BitVec width)) (h : NSC p = true) :
    NSC (fullSsaCcTrans n p) = true := by
  unfold fullSsaCcTrans setupSSA; dsimp only
  simp only [NSC, Bool.true_and]; exact t_ssaCcTrans p _ _ _ h

theorem t_addToDataAux {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (key : List Nat) (o : WordLangProgHOL (BitVec width)) (h : NSC o = true) :
    NSC (WordCse.addToDataAux data d key o).2 = true := by
  unfold WordCse.addToDataAux; (repeat' (first | split_ifs | split)) <;> simp_all [NSC]

theorem t_addToLoadAux {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (key : List Nat) (o : WordLangProgHOL (BitVec width)) (h : NSC o = true) :
    NSC (WordCse.addToLoadAux data d key o).2 = true := by
  unfold WordCse.addToLoadAux; (repeat' (first | split_ifs | split)) <;> simp_all [NSC]

theorem t_addToDataConst {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (w : BitVec width) : NSC (WordCse.addToDataConst data d w).2 = true := by
  unfold WordCse.addToDataConst; dsimp only; split <;> rfl

theorem t_wordCseInst {width : Nat} [NeZero width] (data : WordCse.Knowledge)
    (i : HolInst width) : NSC (WordCse.wordCseInst data i).2 = true := by
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
      NSC p = true → NSC (WordCse.wordCse data p).2 = true
  | data, .seq a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordCse.wordCse.eq_def]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_wordCse _ a h.1, t_wordCse _ b h.2⟩
  | data, .ite cm r ri a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordCse.wordCse.eq_def]; simp only [NSC, Bool.and_eq_true]
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
    (h : NSC p = true) : NSC (WordCse.wordCommonSubexpElim p) = true := by
  unfold WordCse.wordCommonSubexpElim; exact t_wordCse _ p h

/-- Exact post-`instSelect` segment of `compileSingle` (before `wordAlloc`), then
`removeMustTerminate`: ssa → removeDead → cse → copyProp → threeToTwo → removeUnreach
→ removeDead. Plus the compiled-order mid/tail chain. -/
theorem t_ssa_cse_mid_tail_chain {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp argc : Nat) (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : NSC p = true) :
    NSC (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
      (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
        (fullSsaCcTrans argc (WordInst.instSelect c temp p)))))))) = true :=
  t_removeDeadProg _ (t_removeUnreach _ (t_threeToTwo b _ (t_copyProp _
    (t_wordCommonSubexpElim _ (t_removeDeadProg _ (t_fullSsaCcTrans argc _
      (t_instSelect c temp p h)))))))

def storeConstsAllowance {α : Type} (p : WordLangProgHOL α) : Nat := if NSC p then 0 else 1

/-! ## from WordSimpPreservesNSCoreConsts -/



theorem t_smartSeq (a b : WordLangProgHOL (BitVec width)) (ha : NSC a = true)
    (hb : NSC b = true) : NSC (WordSimp.smartSeqHOL a b) = true := by
  unfold WordSimp.smartSeqHOL; split <;> simp_all [NSC]

theorem t_dropConsts (cs : Spt (BitVec width)) :
    ∀ l : List Nat, NSC (WordSimp.dropConsts cs l) = true
  | [] => rfl
  | n :: ns => by
      rw [WordSimp.dropConsts]; split
      · exact t_dropConsts cs ns
      · exact t_smartSeq _ _ (t_dropConsts cs ns) rfl

theorem t_seqAssoc :
    ∀ (p1 q : WordLangProgHOL (BitVec width)), NSC p1 = true → NSC q = true →
      NSC (WordSimp.seqAssoc p1 q) = true
  | p1, .skip, h1, _ => by rw [WordSimp.seqAssoc]; exact h1
  | p1, .seq a b, h1, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; exact t_seqAssoc _ b (t_seqAssoc p1 a h1 h.1) h.2
  | p1, .ite v n r a b, h1, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NSC, Bool.and_eq_true]
      exact ⟨t_seqAssoc _ a rfl h.1, t_seqAssoc _ b rfl h.2⟩
  | p1, .mustTerminate a, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 (t_seqAssoc _ a rfl h)
  | p1, .loop x a y, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 (t_seqAssoc _ a rfl h)
  | p1, .call none d args none, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 h
  | p1, .call none d args (some (y1, q, y2, y3)), h1, h => by
      simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true]; exact ⟨h.1, t_seqAssoc _ q rfl h.2⟩
  | p1, .call (some (x1, x2, r, x3, x4)) d args none, h1, h => by
      simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true]; exact ⟨h.1, t_seqAssoc _ r rfl h.2⟩
  | p1, .call (some (x1, x2, r, x3, x4)) d args (some (y1, q, y2, y3)), h1, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NSC, Bool.and_eq_true]
      exact ⟨⟨h.1.1, t_seqAssoc _ r rfl h.1.2⟩, t_seqAssoc _ q rfl h.2⟩
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
      NSC p = true → NSC (WordSimp.constFpLoop p cs).1 = true
  | .seq a b, cs, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordSimp.constFpLoop]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_constFpLoop a _ h.1, t_constFpLoop b _ h.2⟩
  | .ite c l r a b, cs, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordSimp.constFpLoop]; dsimp only
      split
      · split
        · exact t_constFpLoop a _ h.1
        · exact t_constFpLoop b _ h.2
      · simp only [NSC, Bool.and_eq_true]
        exact ⟨t_constFpLoop a _ h.1, t_constFpLoop b _ h.2⟩
  | .mustTerminate a, cs, h => by rw [WordSimp.constFpLoop]; exact t_constFpLoop a _ h
  | .loop x a y, cs, h => by rw [WordSimp.constFpLoop]; exact t_constFpLoop a _ h
  | .call none d args hd, cs, h => by
      rw [WordSimp.constFpLoop]; exact t_smartSeq _ _ (t_dropConsts _ _) h
  | .call (some (n, nm, r, l1, l2)) d args none, cs, h => by
      simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h
      rw [WordSimp.constFpLoop]; dsimp only
      apply t_smartSeq _ _ (t_dropConsts _ _)
      simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true]; exact ⟨h.1, t_constFpLoop r _ h.2⟩
  | .call (some (n, nm, r, l1, l2)) d args (some hh), cs, h => by
      rw [WordSimp.constFpLoop]; exact t_smartSeq _ _ (t_dropConsts _ _) h
  | .ffi .., cs, h | .alloc .., cs, h | .install .., cs, h => by
      rw [WordSimp.constFpLoop]; exact t_smartSeq _ _ (t_dropConsts _ _) rfl
  | .storeConsts .., cs, h => by rw [WordSimp.constFpLoop]; rfl
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

theorem t_constFp (p : WordLangProgHOL (BitVec width)) (h : NSC p = true) :
    NSC (WordSimp.constFp p) = true := t_constFpLoop p _ h

theorem t_destIf (p : WordLangProgHOL (BitVec width)) (h : NSC p = true)
    (c : Cmp) (l : Nat) (r : WordRegImm (BitVec width)) (b1 b2 : WordLangProgHOL (BitVec width))
    (e : WordSimp.destIf p = some (c, l, r, b1, b2)) : NSC b1 = true ∧ NSC b2 = true := by
  unfold WordSimp.destIf at e; split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, -, -, rfl, rfl⟩ := e
    simpa [NSC] using h
  · simp at e

theorem t_tryIfHoist2 : ∀ (n : Nat) (p1 interm dummy p2 r : WordLangProgHOL (BitVec width)),
    NSC p1 = true → NSC interm = true → NSC p2 = true →
      WordSimp.tryIfHoist2 n p1 interm dummy p2 = some r → NSC r = true
  | 0, _, _, _, _, _, _, _, _, e => by simp [WordSimp.tryIfHoist2] at e
  | n + 1, p1, interm, dummy, p2, r, h1, hi, h2, e => by
      unfold WordSimp.tryIfHoist2 at e
      split at e
      · rename_i c l rr b1 b2
        simp only [NSC, Bool.and_eq_true] at h1
        dsimp only at e
        split at e; · simp at e
        split at e; · simp at e
        simp only [Option.some.injEq] at e; subst e
        apply t_constFp; simp_all [NSC]
      · rename_i p3 p4
        simp only [NSC, Bool.and_eq_true] at h1
        split at e
        · rename_i c l rr b1 b2 hd
          have hb := t_destIf p4 h1.2 _ _ _ _ _ hd
          dsimp only at e
          split at e; · simp at e
          split at e; · simp at e
          simp only [Option.some.injEq] at e; subst e
          simp only [NSC, Bool.and_eq_true]
          refine ⟨h1.1, t_constFp _ ?_⟩
          simp_all [NSC]
        · split at e
          · exact t_tryIfHoist2 n p3 _ dummy p2 r h1.1 (by simp_all [NSC]) h2 e
          · simp at e
      · simp at e

theorem t_tryIfHoist1 (p1 p2 r : WordLangProgHOL (BitVec width)) (h1 : NSC p1 = true)
    (h2 : NSC p2 = true) (e : WordSimp.tryIfHoist1 p1 p2 = some r) : NSC r = true := by
  unfold WordSimp.tryIfHoist1 at e; split at e
  · simp at e
  · exact t_tryIfHoist2 _ _ _ _ _ _ h1 rfl h2 e

theorem t_simpDuplicateIf :
    ∀ (p : WordLangProgHOL (BitVec width)), NSC p = true → NSC (WordSimp.simpDuplicateIf p) = true
  | .seq a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      have ha := t_simpDuplicateIf a h.1
      have hb := t_simpDuplicateIf b h.2
      rw [WordSimp.simpDuplicateIf]
      split
      · simp only [NSC, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · rename_i p3 e
        exact t_seqAssoc _ _ rfl (t_tryIfHoist1 _ _ _ ha hb e)
  | .ite c l r a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      rw [WordSimp.simpDuplicateIf]; simp only [NSC, Bool.and_eq_true]
      exact ⟨t_simpDuplicateIf a h.1, t_simpDuplicateIf b h.2⟩
  | .mustTerminate a, h => by rw [WordSimp.simpDuplicateIf]; exact t_simpDuplicateIf a h
  | .loop x a y, h => by rw [WordSimp.simpDuplicateIf]; exact t_simpDuplicateIf a h
  | .call none d args none, h => by rw [WordSimp.simpDuplicateIf]; first | exact h | rfl | simpa [NSC] using h
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordSimp.simpDuplicateIf]; simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_simpDuplicateIf q h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordSimp.simpDuplicateIf]; simp only [NSC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_simpDuplicateIf r h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordSimp.simpDuplicateIf]; simp only [NSC, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, t_simpDuplicateIf r h.1.2⟩, t_simpDuplicateIf q h.2⟩
  | .skip, h | .move .., h | .inst .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .opCurrHeap .., h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by
      rw [WordSimp.simpDuplicateIf] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_pushOutIfAux :
    ∀ (p : WordLangProgHOL (BitVec width)), NSC p = true → NSC (WordSimp.pushOutIfAux p).1 = true
  | .seq a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      have ha := t_pushOutIfAux a h.1
      have hb := t_pushOutIfAux b h.2
      rw [WordSimp.pushOutIfAux]
      split
      · rename_i c1 e; rw [e] at ha; simp_all [NSC]
      · rename_i c1 e; rw [e] at ha; split
        rename_i c2 bb e2; rw [e2] at hb; simp_all [NSC]
  | .ite c l r a b, h => by
      simp only [NSC, Bool.and_eq_true] at h
      have ha := t_pushOutIfAux a h.1
      have hb := t_pushOutIfAux b h.2
      rw [WordSimp.pushOutIfAux]
      split <;> (rename_i e1 e2; rw [e1] at ha; rw [e2] at hb; simp_all [NSC])
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

theorem t_pushOutIf (p : WordLangProgHOL (BitVec width)) (h : NSC p = true) :
    NSC (WordSimp.pushOutIf p) = true := t_pushOutIfAux p h

theorem t_compileExp (p : WordLangProgHOL (BitVec width)) (h : NSC p = true) :
    NSC (WordSimp.compileExp p) = true := by
  unfold WordSimp.compileExp
  exact t_pushOutIf _ (t_simpDuplicateIf _ (t_constFp _ (t_seqAssoc _ _ rfl h)))


/-! ## from WordToWordFullCompileNSCoreConsts -/



/-- Colouring renames registers; it never adds or removes a `storeConsts`. -/
theorem applyColour_NSC_iff (f : Nat → Nat) :
    ∀ p : WordLangProgHOL (BitVec width), NSC (Flapjack.WordAlloc.applyColour f p) = NSC p
  | .seq a b => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSC]
      rw [applyColour_NSC_iff f a, applyColour_NSC_iff f b]
  | .ite c r ri a b => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSC]
      rw [applyColour_NSC_iff f a, applyColour_NSC_iff f b]
  | .mustTerminate a => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSC]; exact applyColour_NSC_iff f a
  | .loop x a y => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSC]; exact applyColour_NSC_iff f a
  | .call none d args none => by rw [Flapjack.WordAlloc.applyColour]; first | exact h | rfl | simpa [NSC] using h
  | .call none d args (some (v, q, l1, l2)) => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSC]; rw [applyColour_NSC_iff f q]
  | .call (some (vs, cs, r, l1, l2)) d args none => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSC]; rw [applyColour_NSC_iff f r]
  | .call (some (vs, cs, r, l1, l2)) d args (some (v, q, m1, m2)) => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSC]
      rw [applyColour_NSC_iff f r, applyColour_NSC_iff f q]
  | .skip | .move .. | .inst .. | .assign .. | .get .. | .set .. | .store .. | .alloc ..
  | .storeConsts .. | .raise .. | .return .. | .break .. | .continue .. | .tick
  | .opCurrHeap .. | .locValue .. | .install .. | .codeBufferWrite .. | .dataBufferWrite ..
  | .ffi .. | .shareInst .. => by
      rw [Flapjack.WordAlloc.applyColour] <;> first | rfl | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_applyColour (f : Nat → Nat) (p : WordLangProgHOL (BitVec width)) (h : NSC p = true) :
    NSC (Flapjack.WordAlloc.applyColour f p) = true := by
  rw [applyColour_NSC_iff]; exact h

theorem t_oracleColourOk (k : Nat) (co : Option (Spt Nat)) (tree : RegAlloc.ClashTree)
    (p q : WordLangProgHOL (BitVec width)) (forced : List (Nat × Nat)) (h : NSC p = true)
    (e : Flapjack.WordAlloc.oracleColourOk k co tree p forced = some q) : NSC q = true := by
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
    (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat)) (h : NSC p = true) :
    NSC (Flapjack.WordAlloc.wordAlloc fc c alg k p co) = true := by
  unfold Flapjack.WordAlloc.wordAlloc; dsimp only
  split
  · split
    · exact t_applyColour _ _ h
    · exact h
  · rename_i q e; exact t_oracleColourOk _ _ _ _ _ _ h e

/-- Master: every function body accepted by `fullCompileSingle` with `NSC` input
yields `NSC` output (all 11 calls of the HOL pipeline). -/
theorem t_fullCompileSingle (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (nm ac : Nat) (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat))
    (h : NSC p = true) :
    NSC (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.2 = true := by
  unfold WordToWord.fullCompileSingle WordToWord.compileSingle; dsimp only
  apply t_removeMustTerminate
  apply t_wordAlloc
  exact t_ssa_cse_mid_tail_chain c _ ac b _ (t_compileExp _ h)

theorem fullCompileSingle_preserves_meta (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (nm ac : Nat) (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat)) :
    (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).1 = nm ∧
    (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.1 = ac := by
  unfold WordToWord.fullCompileSingle WordToWord.compileSingle; exact ⟨rfl, rfl⟩


/-- Whole-program lift over any list of `NSC` functions. -/
theorem t_fullCompile_list (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (ps : List ((Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)))
    (h : ∀ x ∈ ps, NSC x.1.2.2 = true) :
    ∀ y ∈ ps.map (WordToWord.fullCompileSingle b rc alg c), NSC y.2.2 = true := by
  intro y hy
  obtain ⟨⟨⟨nm, ac, p⟩, co⟩, hx, rfl⟩ := List.mem_map.1 hy
  exact t_fullCompileSingle b rc alg c nm ac p co (h _ hx)


end

/-! ## End to end: Pancake → WordToWord, no hypothesis -/

theorem wordToWordCompile_NSC {width : Nat} [NeZero width] (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, NSC x.2.2 = true) :
    ∀ y ∈ (WordToWord.compile wc ac progs).2, NSC y.2.2 = true := by
  unfold WordToWord.compile; dsimp only
  apply t_fullCompile_list
  intro x hx
  exact h _ (List.of_mem_zip hx).1

/-- `hcall` discharged: for every Pancake program, no function leaving WordToWord calls the
`storeConsts` stub. -/
theorem panToWordToWord_NoStubCall {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) :
    ∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      StackRemoveAndNamesNoStoreConsts.WordNoStubCall y.2.2 = true := by
  intro y hy
  rw [← NSC_eq]
  exact wordToWordCompile_NSC wc ac _
    (fun x hx => by rw [NSC_eq]; exact PanToWordNoStubCall.panToWord_NoStubCall arch prog x hx) y hy

/-- Unconditional version of `panToStackNames_bodies_NoSt_and_NoStubCall`: Pancake →
WordToWord → WordToStack → raw call → StackAlloc → StackRemove → StackNames, every non-stub body
has no `storeConsts` **and** no call to the `storeConsts` stub. No `hcall` premise. -/
theorem panToStackNames_NoSt_and_NoStubCall_unconditional {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (WordToStack.Native.compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (PanToStackNoStoreConsts.StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       StackRemoveAndNamesNoStoreConsts.NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) :=
  StackRemoveAndNamesNoStoreConsts.panToStackNames_bodies_NoSt_and_NoStubCall arch prog wc ac perf
    (panToWordToWord_NoStubCall arch prog wc ac) info j bd ptr f

/-! ## Witnesses -/

theorem NSC_rejects_stub_call {α : Type} :
    NSC (WordLangProgHOL.seq (α := α) .skip
      (.call none (some storeConstsStubLocation) [] none)) = false := by
  simp [NSC, storeConstsStubLocation, wordNumStubs, stackNumStubs]

theorem NSC_accepts_user_call {α : Type} :
    NSC (WordLangProgHOL.call (α := α) none (some 64) [] none) = true := by
  simp [NSC, storeConstsStubLocation, wordNumStubs, stackNumStubs]

theorem NSC_allows_storeConsts {α : Type} :
    NSC (WordLangProgHOL.storeConsts (α := α) 0 1 2 3 []) = true := rfl


end InitECandidate.Solver.WordToWordNoStubCall
