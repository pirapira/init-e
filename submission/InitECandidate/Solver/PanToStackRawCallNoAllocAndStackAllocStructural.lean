import Flapjack.Compiler.Backend.StackAlloc.Compile
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.WordToWord.Compile
import Flapjack.Pancake.PanToWord
import InitECandidate.Solver.PanToWordNoStoreConsts
import InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false



namespace InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordPassesPreserveNoAlloc

open Flapjack
open Flapjack.Compiler.Backend

/-- No `storeConsts` anywhere (StackRemove's only offset source). -/
def WordNoAlloc {α : Type} : WordLangProgHOL α → Bool
  | .alloc .. => false
  | .mustTerminate b => WordNoAlloc b
  | .seq a b => WordNoAlloc a && WordNoAlloc b
  | .ite _ _ _ a b => WordNoAlloc a && WordNoAlloc b
  | .loop _ b _ => WordNoAlloc b
  | .call ret _ _ h =>
      (match ret with | none => true | some (_, _, r, _, _) => WordNoAlloc r) &&
      (match h with | none => true | some (_, p, _, _) => WordNoAlloc p)
  | _ => true

theorem t_removeMustTerminate {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)), WordNoAlloc p = true → WordNoAlloc (WordRemove.removeMustTerminate p) = true
  | .seq a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordRemove.removeMustTerminate]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_removeMustTerminate a h.1, t_removeMustTerminate b h.2⟩
  | .ite c r ri a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordRemove.removeMustTerminate]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_removeMustTerminate a h.1, t_removeMustTerminate b h.2⟩
  | .mustTerminate a, h => by
      rw [WordRemove.removeMustTerminate]; exact t_removeMustTerminate a h
  | .loop x a y, h => by
      rw [WordRemove.removeMustTerminate]; exact t_removeMustTerminate a h
  | .call none d args none, h => by rw [WordRemove.removeMustTerminate.eq_def]; rfl
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [WordNoAlloc, Bool.true_and] at h ⊢; exact t_removeMustTerminate q h
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [WordNoAlloc, Bool.and_true] at h ⊢; exact t_removeMustTerminate r h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true] at h ⊢
      exact ⟨t_removeMustTerminate r h.1, t_removeMustTerminate q h.2⟩
  | .skip, h | .move .., h | .inst .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .storeConsts .., h | .alloc .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .opCurrHeap .., h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by simp_all [WordRemove.removeMustTerminate, WordNoAlloc]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_threeToTwoReg {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)), WordNoAlloc p = true → WordNoAlloc (WordInst.threeToTwoReg p) = true
  | .seq a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordInst.threeToTwoReg]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_threeToTwoReg a h.1, t_threeToTwoReg b h.2⟩
  | .ite c r ri a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordInst.threeToTwoReg]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_threeToTwoReg a h.1, t_threeToTwoReg b h.2⟩
  | .mustTerminate a, h => by
      rw [WordInst.threeToTwoReg]; exact t_threeToTwoReg a h
  | .loop x a y, h => by
      rw [WordInst.threeToTwoReg]; exact t_threeToTwoReg a h
  | .call none d args none, h => by rw [WordInst.threeToTwoReg.eq_def]; rfl
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [WordNoAlloc, Bool.true_and] at h ⊢; exact t_threeToTwoReg q h
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [WordNoAlloc, Bool.and_true] at h ⊢; exact t_threeToTwoReg r h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true] at h ⊢
      exact ⟨t_threeToTwoReg r h.1, t_threeToTwoReg q h.2⟩
  | .opCurrHeap .., h => by rw [WordInst.threeToTwoReg]; rfl
  | .inst i, h => by
      rw [WordInst.threeToTwoReg.eq_def]; split <;> simp_all [WordNoAlloc]
  | .skip, h | .move .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .storeConsts .., h | .alloc .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by rw [WordInst.threeToTwoReg]; all_goals first | exact h | (intros; contradiction) | simp_all
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_threeToTwo {width : Nat} [NeZero width] (b : Bool) (p : WordLangProgHOL (BitVec width))
    (h : WordNoAlloc p = true) : WordNoAlloc (WordInst.threeToTwoRegProg b p) = true := by
  unfold WordInst.threeToTwoRegProg; split
  · exact t_threeToTwoReg p h
  · exact h

theorem t_destSeqMove {width : Nat} [NeZero width] (q : WordLangProgHOL (BitVec width))
    (hq : WordNoAlloc q = true) (n : Nat) (l : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (h : WordUnreach.destSeqMove q = some (n, l, rest)) : WordNoAlloc rest = true := by
  unfold WordUnreach.destSeqMove at h
  split at h <;> simp_all [WordNoAlloc]
  all_goals (obtain ⟨-, -, rfl⟩ := h; simp_all [WordNoAlloc])

theorem t_simpSeq {width : Nat} [NeZero width] (p q : WordLangProgHOL (BitVec width))
    (hp : WordNoAlloc p = true) (hq : WordNoAlloc q = true) : WordNoAlloc (WordUnreach.simpSeq p q) = true := by
  unfold WordUnreach.simpSeq
  split
  · exact hp
  · split <;> (try exact hp) <;> (try exact hq) <;> (try simp_all [WordNoAlloc])
    all_goals (split <;> (try simp_all [WordNoAlloc]) <;> (try split) <;> (try simp_all [WordNoAlloc]))
    all_goals (rename_i heq _; exact t_destSeqMove _ hq _ _ _ heq)

theorem t_seqAssocRight {width : Nat} [NeZero width] :
    ∀ (p acc : WordLangProgHOL (BitVec width)), WordNoAlloc p = true → WordNoAlloc acc = true →
      WordNoAlloc (WordUnreach.seqAssocRight p acc) = true
  | .skip, acc, _, ha => by rw [WordUnreach.seqAssocRight]; exact ha
  | .seq a b, acc, hp, ha => by
      simp only [WordNoAlloc, Bool.and_eq_true] at hp
      rw [WordUnreach.seqAssocRight]
      exact t_seqAssocRight a _ hp.1 (t_seqAssocRight b acc hp.2 ha)
  | .ite v n r a b, acc, hp, ha => by
      simp only [WordNoAlloc, Bool.and_eq_true] at hp
      rw [WordUnreach.seqAssocRight]
      apply t_simpSeq _ _ _ ha
      simp only [WordNoAlloc, Bool.and_eq_true]
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
      simp only [WordNoAlloc, Bool.and_true] at hp
      apply t_simpSeq _ _ _ ha
      simp only [WordNoAlloc, Bool.and_true]; exact t_seqAssocRight q1 _ hp rfl
  | .call (some (x1, x2, q1, x3, x4)) d args (some (y1, q2, y2, y3)), acc, hp, ha => by
      rw [WordUnreach.seqAssocRight]
      simp only [WordNoAlloc, Bool.and_eq_true] at hp
      apply t_simpSeq _ _ _ ha
      simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_seqAssocRight q1 _ hp.1 rfl, t_seqAssocRight q2 _ hp.2 rfl⟩
  | .move .., acc, hp, ha | .inst .., acc, hp, ha | .assign .., acc, hp, ha | .get .., acc, hp, ha
  | .set .., acc, hp, ha | .store .., acc, hp, ha | .storeConsts .., acc, hp, ha
  | .alloc .., acc, hp, ha | .raise .., acc, hp, ha | .return .., acc, hp, ha
  | .break .., acc, hp, ha | .continue .., acc, hp, ha | .tick, acc, hp, ha
  | .opCurrHeap .., acc, hp, ha | .locValue .., acc, hp, ha | .install .., acc, hp, ha
  | .codeBufferWrite .., acc, hp, ha | .dataBufferWrite .., acc, hp, ha | .ffi .., acc, hp, ha
  | .shareInst .., acc, hp, ha => by
      rw [WordUnreach.seqAssocRight] <;> first | exact t_simpSeq _ _ hp ha | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_removeUnreach {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : WordNoAlloc p = true) : WordNoAlloc (WordUnreach.removeUnreach p) = true :=
  t_seqAssocRight p _ h rfl

/-- The tail `threeToTwo ∘ removeUnreach ∘ removeMustTerminate`-shaped fragment preserves `WordNoAlloc`. -/
theorem t_tail_chain {width : Nat} [NeZero width] (b : Bool) (p : WordLangProgHOL (BitVec width))
    (h : WordNoAlloc p = true) :
    WordNoAlloc (WordRemove.removeMustTerminate (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b p))) = true :=
  t_removeMustTerminate _ (t_removeUnreach _ (t_threeToTwo b p h))

/-- `WordNoAlloc` is weaker than `NoSC` of `PanToWordNoStoreConsts` (alloc allowed). -/
theorem NoSC_imp_WordNoAlloc {α : Type} : ∀ p : WordLangProgHOL α,
    PanToWordNoStoreConsts.NoSC p = true → WordNoAlloc p = true
  | .seq a b, h | .ite _ _ _ a b, h => by
      simp only [PanToWordNoStoreConsts.NoSC, WordNoAlloc, Bool.and_eq_true] at h ⊢
      exact ⟨NoSC_imp_WordNoAlloc a h.1, NoSC_imp_WordNoAlloc b h.2⟩
  | .mustTerminate a, h | .loop _ a _, h => NoSC_imp_WordNoAlloc a h
  | .call none _ _ none, _ => rfl
  | .call none _ _ (some (_, q, _, _)), h => by
      simp only [PanToWordNoStoreConsts.NoSC, WordNoAlloc, Bool.true_and] at h ⊢; exact NoSC_imp_WordNoAlloc q h
  | .call (some (_, _, r, _, _)) _ _ none, h => by
      simp only [PanToWordNoStoreConsts.NoSC, WordNoAlloc, Bool.and_true] at h ⊢; exact NoSC_imp_WordNoAlloc r h
  | .call (some (_, _, r, _, _)) _ _ (some (_, q, _, _)), h => by
      simp only [PanToWordNoStoreConsts.NoSC, WordNoAlloc, Bool.and_eq_true] at h ⊢
      exact ⟨NoSC_imp_WordNoAlloc r h.1, NoSC_imp_WordNoAlloc q h.2⟩
  | .alloc .., h => by simp [PanToWordNoStoreConsts.NoSC] at h
  | .storeConsts .., _ | .skip, _ | .move .., _ | .inst .., _ | .assign .., _ | .get .., _ | .set .., _
  | .store .., _ | .raise .., _ | .return .., _ | .break .., _ | .continue .., _ | .tick, _
  | .opCurrHeap .., _ | .locValue .., _ | .install .., _ | .codeBufferWrite .., _
  | .dataBufferWrite .., _ | .ffi .., _ | .shareInst .., _ => rfl

/-- LoopToWord output satisfies `WordNoAlloc`. -/
theorem loopToWord_WordNoAlloc {width : Nat} [NeZero width] (ctx : Spt Nat) (p : HolLoopProg width)
    (l : Nat × Nat) : WordNoAlloc (LoopToWord.compHOL ctx p l).1 = true :=
  NoSC_imp_WordNoAlloc _ (PanToWordNoStoreConsts.compHOL_NoSC ctx p l)

/-- `WordNoAlloc` is not trivial. -/
theorem WordNoAlloc_counterexample {α : Type} :
    WordNoAlloc (WordLangProgHOL.loop (α := α) .ln (.alloc 0 (.ln, .ln)) .ln) = false := rfl


end InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordPassesPreserveNoAlloc



namespace InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordMidPassesPreserveNoAlloc

open Flapjack
open Flapjack.Compiler.Backend
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordPassesPreserveNoAlloc
open Flapjack.Compiler.Encoders.Asm

theorem t_instSelectExp {width : Nat} [NeZero width] (c : AsmConfigExact width) :
    ∀ (n : Nat) (tar temp : Nat) (e : WordLangExpHOL (BitVec width)), sizeOf e = n →
      WordNoAlloc (WordInst.instSelectExp c tar temp e) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro tar temp e hn
    rw [WordInst.instSelectExp.eq_def]
    dsimp only
    (repeat' (first | split_ifs | split)) <;> simp only [WordNoAlloc, Bool.and_eq_true, Bool.and_true, Bool.true_and, and_true, true_and] <;>
      (repeat' constructor) <;>
      (try (exact ih _ (by subst hn; simp only [WordLangExpHOL.load.sizeOf_spec, WordLangExpHOL.op.sizeOf_spec, WordLangExpHOL.shift.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega) _ _ _ rfl))

theorem t_ise {width : Nat} [NeZero width] (c : AsmConfigExact width) (tar temp : Nat)
    (e : WordLangExpHOL (BitVec width)) : WordNoAlloc (WordInst.instSelectExp c tar temp e) = true :=
  t_instSelectExp c _ tar temp e rfl

theorem t_copyPropInst {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (cs : WordCopy.CopyState) : WordNoAlloc (WordCopy.copyPropInst i cs).1 = true := by
  unfold WordCopy.copyPropInst; (repeat' split) <;> simp_all [WordNoAlloc]

theorem t_instSelect {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)), WordNoAlloc p = true → WordNoAlloc (WordInst.instSelect c temp p) = true
  | .seq a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordInst.instSelect.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_instSelect c temp a h.1, t_instSelect c temp b h.2⟩
  | .ite cm r ri a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordInst.instSelect.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_instSelect c temp a h.1, t_instSelect c temp b h.2⟩
  | .mustTerminate a, h => by rw [WordInst.instSelect.eq_def]; exact t_instSelect c temp a h
  | .loop x a y, h => by rw [WordInst.instSelect.eq_def]; exact t_instSelect c temp a h
  | .call none d args none, h => by rw [WordInst.instSelect.eq_def]; rfl
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.instSelect.eq_def]; simp only [WordNoAlloc, Bool.true_and] at h ⊢; exact t_instSelect c temp q h
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordInst.instSelect.eq_def]; simp only [WordNoAlloc, Bool.and_true] at h ⊢; exact t_instSelect c temp r h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.instSelect.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true] at h ⊢
      exact ⟨t_instSelect c temp r h.1, t_instSelect c temp q h.2⟩
  | .assign .., h | .set .., h | .store .., h | .shareInst .., h => by
      rw [WordInst.instSelect.eq_def]; dsimp only
      (repeat' (first | split_ifs | split)) <;> simp_all [WordNoAlloc, t_ise]
  | .skip, h | .move .., h | .inst .., h | .get .., h | .storeConsts .., h | .alloc .., h
  | .raise .., h | .return .., h | .break .., h | .continue .., h | .tick, h
  | .opCurrHeap .., h | .locValue .., h | .install .., h | .codeBufferWrite .., h
  | .dataBufferWrite .., h | .ffi .., h => by
      rw [WordInst.instSelect.eq_def] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_removeDead {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
      (lt : List (NumSet × NumSet)), WordNoAlloc p = true → WordNoAlloc (WordAlloc.removeDead p live nlive lt).1 = true
  | .seq a b, live, nlive, lt, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordAlloc.removeDead.eq_def]; dsimp only
      have h2 := t_removeDead b live nlive lt h.2
      have h1 := t_removeDead a (WordAlloc.removeDead b live nlive lt).2.1 (WordAlloc.removeDead b live nlive lt).2.2 lt h.1
      split <;> simp_all [WordNoAlloc]
  | .ite cm r ri a b, live, nlive, lt, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordAlloc.removeDead.eq_def]; dsimp only
      have h1 := t_removeDead a live nlive lt h.1
      have h2 := t_removeDead b live nlive lt h.2
      (repeat' split) <;> simp_all [WordNoAlloc]
  | .mustTerminate a, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; exact t_removeDead a live nlive lt h
  | .loop x a y, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; exact t_removeDead a _ _ _ h
  | .call none d args hd, live, nlive, lt, h => by rw [WordAlloc.removeDead.eq_def]; exact h
  | .call (some (r1, r2, r, r3, r4)) d args none, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; simp only [WordNoAlloc, Bool.and_true] at h ⊢; exact t_removeDead r _ _ _ h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true] at h ⊢
      exact ⟨t_removeDead r _ _ _ h.1, t_removeDead q _ _ _ h.2⟩
  | .skip, _, _, _, h | .move .., _, _, _, h | .inst .., _, _, _, h | .get .., _, _, _, h
  | .set .., _, _, _, h | .assign .., _, _, _, h | .store .., _, _, _, h | .storeConsts .., _, _, _, h
  | .alloc .., _, _, _, h | .raise .., _, _, _, h | .return .., _, _, _, h
  | .break .., _, _, _, h | .continue .., _, _, _, h | .tick, _, _, _, h
  | .opCurrHeap .., _, _, _, h | .locValue .., _, _, _, h | .install .., _, _, _, h
  | .codeBufferWrite .., _, _, _, h | .dataBufferWrite .., _, _, _, h | .ffi .., _, _, _, h
  | .shareInst .., _, _, _, h => by
      rw [WordAlloc.removeDead.eq_def] <;> (try dsimp only) <;> (repeat' (first | split_ifs | split)) <;>
        first | exact h | rfl | (intros; simp_all) | simp_all [WordNoAlloc]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_removeDeadProg {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : WordNoAlloc p = true) : WordNoAlloc (WordAlloc.removeDeadProg p) = true :=
  t_removeDead p _ _ _ h

theorem t_copyPropProg {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : WordCopy.CopyState),
      WordNoAlloc p = true → WordNoAlloc (WordCopy.copyPropProg p cs).1 = true
  | .seq a b, cs, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordCopy.copyPropProg.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_copyPropProg a cs h.1, t_copyPropProg b _ h.2⟩
  | .ite cm r ri a b, cs, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordCopy.copyPropProg.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_copyPropProg a cs h.1, t_copyPropProg b cs h.2⟩
  | .mustTerminate a, cs, h => by rw [WordCopy.copyPropProg.eq_def]; exact t_copyPropProg a cs h
  | .loop x a y, cs, h => by rw [WordCopy.copyPropProg.eq_def]; exact t_copyPropProg a _ h
  | .inst i, cs, h => by rw [WordCopy.copyPropProg.eq_def]; exact t_copyPropInst i cs
  | .call .., cs, h | .skip, cs, h | .move .., cs, h | .get .., cs, h
  | .set .., cs, h | .assign .., cs, h | .store .., cs, h | .storeConsts .., cs, h
  | .alloc .., cs, h | .raise .., cs, h | .return .., cs, h
  | .break .., cs, h | .continue .., cs, h | .tick, cs, h
  | .opCurrHeap .., cs, h | .locValue .., cs, h | .install .., cs, h
  | .codeBufferWrite .., cs, h | .dataBufferWrite .., cs, h | .ffi .., cs, h
  | .shareInst .., cs, h => by
      rw [WordCopy.copyPropProg.eq_def] <;> (try dsimp only) <;> (repeat' (first | split_ifs | split)) <;>
        first | exact h | rfl | simp_all [WordNoAlloc]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_copyProp {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : WordNoAlloc p = true) : WordNoAlloc (WordCopy.copyProp p) = true :=
  t_copyPropProg p _ h

/-- Proven segment of `fullCompileSingle` (SSA, CSE, WordSimp, wordAlloc still open):
instSelect → removeDeadProg → copyProp → threeToTwo → removeUnreach → removeMustTerminate. -/
theorem t_mid_tail_chain {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat)
    (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : WordNoAlloc p = true) :
    WordNoAlloc (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordAlloc.removeDeadProg
        (WordInst.instSelect c temp p)))))) = true :=
  t_tail_chain b _ (t_copyProp _ (t_removeDeadProg _ (t_instSelect c temp p h)))

/-- `instSelect` keeps an existing `storeConsts` (no erasure, no creation). -/
theorem instSelect_keeps_alloc {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp : Nat) : WordNoAlloc (WordInst.instSelect c temp
      (WordLangProgHOL.alloc (α := BitVec width) 0 (.ln, .ln))) = false := by
  rw [WordInst.instSelect.eq_def]; rfl


end InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordMidPassesPreserveNoAlloc



namespace InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordSsaCsePreserveNoAlloc

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordPassesPreserveNoAlloc
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordMidPassesPreserveNoAlloc

theorem t_listNextVarRenameMove {width : Nat} [NeZero width] (ssa : Spt Nat) (n : Nat)
    (ls : List Nat) : WordNoAlloc (listNextVarRenameMove (width := width) ssa n ls).1 = true := by
  unfold listNextVarRenameMove; rfl

theorem t_ssaReconcile {width : Nat} [NeZero width] {β : Type} (a b : Spt Nat) (ns : Spt β) :
    WordNoAlloc (ssaReconcile (width := width) a b ns) = true := by
  unfold ssaReconcile; dsimp only; split <;> rfl

theorem t_fakeMoveFold {width : Nat} [NeZero width] (l : List Nat) :
    WordNoAlloc ((l.map fun r => fakeMove (width := width) r).foldr .seq .skip) = true := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.foldr_cons, WordNoAlloc, Bool.and_eq_true]; exact ⟨rfl, ih⟩

theorem t_loopSetup {width : Nat} [NeZero width] (names exitNames : Spt Unit) (ssa : Spt Nat)
    (na : Nat) : WordNoAlloc (loopSetup (width := width) names exitNames ssa na).1 = true := by
  unfold loopSetup
  simp only [WordNoAlloc, Bool.and_eq_true]
  exact ⟨t_fakeMoveFold _, t_listNextVarRenameMove _ _ _⟩

theorem t_fakeMoves {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit)) :
    ∀ (l : List Nat) (sl sr : Spt Nat) (na : Nat),
      WordNoAlloc (fakeMoves (width := width) prio l sl sr na).1 = true ∧
      WordNoAlloc (fakeMoves (width := width) prio l sl sr na).2.1 = true
  | [], _, _, _ => ⟨rfl, rfl⟩
  | x :: xs, sl, sr, na => by
      have ih := t_fakeMoves (width := width) prio xs sl sr na
      rw [fakeMoves]; dsimp only
      split <;> simp_all [WordNoAlloc, fakeMove]

theorem t_fixInconsistencies {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit))
    (sl sr : Spt Nat) (na : Nat) :
    WordNoAlloc (fixInconsistencies (width := width) prio sl sr na).1 = true ∧
    WordNoAlloc (fixInconsistencies (width := width) prio sl sr na).2.1 = true := by
  unfold fixInconsistencies; dsimp only
  have := t_fakeMoves (width := width) prio
  simp_all [WordNoAlloc]

theorem t_ssaCcTransInst {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (ssa : Spt Nat) (na : Nat) : WordNoAlloc (ssaCcTransInst i ssa na).1 = true := by
  unfold ssaCcTransInst; (repeat' split) <;> simp_all [WordNoAlloc]

theorem t_ssaCcTrans {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (na : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      WordNoAlloc p = true → WordNoAlloc (ssaCcTrans p ssa na lt).1 = true
  | .seq a b, ssa, na, lt, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_ssaCcTrans a _ _ _ h.1, t_ssaCcTrans b _ _ _ h.2⟩
  | .ite cm r ri a b, ssa, na, lt, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true]
      have hf := t_fixInconsistencies (width := width)
      exact ⟨⟨t_ssaCcTrans a _ _ _ h.1, (hf _ _ _ _).1⟩, ⟨t_ssaCcTrans b _ _ _ h.2, (hf _ _ _ _).2⟩⟩
  | .mustTerminate a, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; exact t_ssaCcTrans a _ _ _ h
  | .loop names body ex, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; dsimp only
      simp only [WordNoAlloc, Bool.and_eq_true]
      refine ⟨t_loopSetup _ _ _ _, ?_⟩
      split
      · exact t_ssaCcTrans body _ _ _ h
      · simp only [WordNoAlloc, Bool.and_eq_true]; exact ⟨t_ssaCcTrans body _ _ _ h, t_ssaReconcile _ _ _⟩
  | .call none d args hd, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; dsimp only
      rcases hd with _ | ⟨h1, q, h2, h3⟩ <;> simp_all [WordNoAlloc]
  | .call (some (r1, r2, r, r3, r4)) d args none, ssa, na, lt, h => by
      simp only [WordNoAlloc, Bool.and_true] at h
      rw [ssaCcTrans.eq_def]; dsimp only
      simp only [WordNoAlloc, Bool.and_eq_true, Bool.and_true, t_listNextVarRenameMove, true_and]
      exact t_ssaCcTrans r _ _ _ h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), ssa, na, lt, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; dsimp only
      have hf := t_fixInconsistencies (width := width)
      simp only [WordNoAlloc, Bool.and_eq_true, t_listNextVarRenameMove, true_and, and_true]
      exact ⟨⟨t_ssaCcTrans r _ _ _ h.1, (hf _ _ _ _).1⟩, ⟨t_ssaCcTrans q _ _ _ h.2, (hf _ _ _ _).2⟩⟩
  | .inst i, ssa, na, lt, h => by rw [ssaCcTrans.eq_def]; exact t_ssaCcTransInst i ssa na
  | .alloc .., _, _, _, h => by simp [WordNoAlloc] at h
  | .skip, _, _, _, h | .move .., _, _, _, h | .get .., _, _, _, h
  | .set .., _, _, _, h | .assign .., _, _, _, h | .store .., _, _, _, h | .storeConsts .., _, _, _, h
  | .raise .., _, _, _, h | .return .., _, _, _, h
  | .break .., _, _, _, h | .continue .., _, _, _, h | .tick, _, _, _, h
  | .opCurrHeap .., _, _, _, h | .locValue .., _, _, _, h | .install .., _, _, _, h
  | .codeBufferWrite .., _, _, _, h | .dataBufferWrite .., _, _, _, h | .ffi .., _, _, _, h
  | .shareInst .., _, _, _, h => by
      rw [ssaCcTrans.eq_def] <;> (try dsimp only) <;> (repeat' (first | split_ifs | split)) <;>
        simp_all [WordNoAlloc, t_listNextVarRenameMove, t_ssaReconcile]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_fullSsaCcTrans {width : Nat} [NeZero width] (n : Nat)
    (p : WordLangProgHOL (BitVec width)) (h : WordNoAlloc p = true) :
    WordNoAlloc (fullSsaCcTrans n p) = true := by
  unfold fullSsaCcTrans setupSSA; dsimp only
  simp only [WordNoAlloc, Bool.true_and]; exact t_ssaCcTrans p _ _ _ h

theorem t_addToDataAux {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (key : List Nat) (o : WordLangProgHOL (BitVec width)) (h : WordNoAlloc o = true) :
    WordNoAlloc (WordCse.addToDataAux data d key o).2 = true := by
  unfold WordCse.addToDataAux; (repeat' (first | split_ifs | split)) <;> simp_all [WordNoAlloc]

theorem t_addToLoadAux {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (key : List Nat) (o : WordLangProgHOL (BitVec width)) (h : WordNoAlloc o = true) :
    WordNoAlloc (WordCse.addToLoadAux data d key o).2 = true := by
  unfold WordCse.addToLoadAux; (repeat' (first | split_ifs | split)) <;> simp_all [WordNoAlloc]

theorem t_addToDataConst {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (w : BitVec width) : WordNoAlloc (WordCse.addToDataConst data d w).2 = true := by
  unfold WordCse.addToDataConst; dsimp only; split <;> rfl

theorem t_wordCseInst {width : Nat} [NeZero width] (data : WordCse.Knowledge)
    (i : HolInst width) : WordNoAlloc (WordCse.wordCseInst data i).2 = true := by
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
      WordNoAlloc p = true → WordNoAlloc (WordCse.wordCse data p).2 = true
  | data, .seq a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordCse.wordCse.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_wordCse _ a h.1, t_wordCse _ b h.2⟩
  | data, .ite cm r ri a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordCse.wordCse.eq_def]; simp only [WordNoAlloc, Bool.and_eq_true]
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
  | data, .assign .., h | data, .store .., h | data, .storeConsts .., h
  | data, .alloc .., h | data, .raise .., h | data, .return .., h
  | data, .break .., h | data, .continue .., h | data, .tick, h
  | data, .install .., h | data, .codeBufferWrite .., h | data, .dataBufferWrite .., h
  | data, .ffi .., h | data, .shareInst .., h => by
      rw [WordCse.wordCse.eq_def] <;> first | exact h | (intros; simp_all) | skip
termination_by _ p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_wordCommonSubexpElim {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : WordNoAlloc p = true) : WordNoAlloc (WordCse.wordCommonSubexpElim p) = true := by
  unfold WordCse.wordCommonSubexpElim; exact t_wordCse _ p h

/-- Exact post-`instSelect` segment of `compileSingle` (before `wordAlloc`), then
`removeMustTerminate`: ssa → removeDead → cse → copyProp → threeToTwo → removeUnreach
→ removeDead. Plus the compiled-order mid/tail chain. -/
theorem t_ssa_cse_mid_tail_chain {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp argc : Nat) (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : WordNoAlloc p = true) :
    WordNoAlloc (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
      (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
        (fullSsaCcTrans argc (WordInst.instSelect c temp p)))))))) = true :=
  t_removeDeadProg _ (t_removeUnreach _ (t_threeToTwo b _ (t_copyProp _
    (t_wordCommonSubexpElim _ (t_removeDeadProg _ (t_fullSsaCcTrans argc _
      (t_instSelect c temp p h)))))))

/-- Corollary: no `storeConsts` instruction anywhere, hence no StackRemove
allowance source (the only non-zero allowance in `CompCorrect` is `StoreConsts`). -/
def allocAllowance {α : Type} (p : WordLangProgHOL α) : Nat := if WordNoAlloc p then 0 else 1

theorem allocAllowance_chain_zero {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp argc : Nat) (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : WordNoAlloc p = true) :
    allocAllowance (WordAlloc.removeDeadProg (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordCse.wordCommonSubexpElim
        (WordAlloc.removeDeadProg (fullSsaCcTrans argc (WordInst.instSelect c temp p)))))))) = 0 := by
  simp [allocAllowance, t_ssa_cse_mid_tail_chain c temp argc b p h]

theorem allocAllowance_tight {α : Type} :
    allocAllowance (WordLangProgHOL.alloc (α := α) 0 (.ln, .ln)) = 1 := rfl


end InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordSsaCsePreserveNoAlloc



namespace InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordSimpPreservesNoAlloc

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordPassesPreserveNoAlloc
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordMidPassesPreserveNoAlloc
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordSsaCsePreserveNoAlloc

variable {width : Nat} [NeZero width]

theorem t_smartSeq (a b : WordLangProgHOL (BitVec width)) (ha : WordNoAlloc a = true)
    (hb : WordNoAlloc b = true) : WordNoAlloc (WordSimp.smartSeqHOL a b) = true := by
  unfold WordSimp.smartSeqHOL; split <;> simp_all [WordNoAlloc]

theorem t_dropConsts (cs : Spt (BitVec width)) :
    ∀ l : List Nat, WordNoAlloc (WordSimp.dropConsts cs l) = true
  | [] => rfl
  | n :: ns => by
      rw [WordSimp.dropConsts]; split
      · exact t_dropConsts cs ns
      · exact t_smartSeq _ _ (t_dropConsts cs ns) rfl

theorem t_seqAssoc :
    ∀ (p1 q : WordLangProgHOL (BitVec width)), WordNoAlloc p1 = true → WordNoAlloc q = true →
      WordNoAlloc (WordSimp.seqAssoc p1 q) = true
  | p1, .skip, h1, _ => by rw [WordSimp.seqAssoc]; exact h1
  | p1, .seq a b, h1, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; exact t_seqAssoc _ b (t_seqAssoc p1 a h1 h.1) h.2
  | p1, .ite v n r a b, h1, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_seqAssoc _ a rfl h.1, t_seqAssoc _ b rfl h.2⟩
  | p1, .mustTerminate a, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 (t_seqAssoc _ a rfl h)
  | p1, .loop x a y, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 (t_seqAssoc _ a rfl h)
  | p1, .call none d args none, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 rfl
  | p1, .call none d args (some (y1, q, y2, y3)), h1, h => by
      simp only [WordNoAlloc, Bool.true_and] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [WordNoAlloc, Bool.true_and]; exact t_seqAssoc _ q rfl h
  | p1, .call (some (x1, x2, r, x3, x4)) d args none, h1, h => by
      simp only [WordNoAlloc, Bool.and_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [WordNoAlloc, Bool.and_true]; exact t_seqAssoc _ r rfl h
  | p1, .call (some (x1, x2, r, x3, x4)) d args (some (y1, q, y2, y3)), h1, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_seqAssoc _ r rfl h.1, t_seqAssoc _ q rfl h.2⟩
  | p1, .move .., h1, h | p1, .inst .., h1, h | p1, .assign .., h1, h | p1, .get .., h1, h
  | p1, .set .., h1, h | p1, .store .., h1, h | p1, .storeConsts .., h1, h
  | p1, .alloc .., h1, h | p1, .raise .., h1, h | p1, .return .., h1, h
  | p1, .break .., h1, h | p1, .continue .., h1, h | p1, .tick, h1, h
  | p1, .opCurrHeap .., h1, h | p1, .locValue .., h1, h | p1, .install .., h1, h
  | p1, .codeBufferWrite .., h1, h | p1, .dataBufferWrite .., h1, h | p1, .ffi .., h1, h
  | p1, .shareInst .., h1, h => by
      rw [WordSimp.seqAssoc] <;> first | exact t_smartSeq _ _ h1 h | (intros; simp_all) | skip
termination_by _ q => sizeOf q
decreasing_by all_goals (simp_wf; try omega)

theorem t_constFpLoop :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : Spt (BitVec width)),
      WordNoAlloc p = true → WordNoAlloc (WordSimp.constFpLoop p cs).1 = true
  | .seq a b, cs, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordSimp.constFpLoop]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_constFpLoop a _ h.1, t_constFpLoop b _ h.2⟩
  | .ite c l r a b, cs, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordSimp.constFpLoop]; dsimp only
      split
      · split
        · exact t_constFpLoop a _ h.1
        · exact t_constFpLoop b _ h.2
      · simp only [WordNoAlloc, Bool.and_eq_true]
        exact ⟨t_constFpLoop a _ h.1, t_constFpLoop b _ h.2⟩
  | .mustTerminate a, cs, h => by rw [WordSimp.constFpLoop]; exact t_constFpLoop a _ h
  | .loop x a y, cs, h => by rw [WordSimp.constFpLoop]; exact t_constFpLoop a _ h
  | .call none d args hd, cs, h => by
      rw [WordSimp.constFpLoop]; exact t_smartSeq _ _ (t_dropConsts _ _) h
  | .call (some (n, nm, r, l1, l2)) d args none, cs, h => by
      simp only [WordNoAlloc, Bool.and_true] at h
      rw [WordSimp.constFpLoop]; dsimp only
      apply t_smartSeq _ _ (t_dropConsts _ _)
      simp only [WordNoAlloc, Bool.and_true]; exact t_constFpLoop r _ h
  | .call (some (n, nm, r, l1, l2)) d args (some hh), cs, h => by
      rw [WordSimp.constFpLoop]; exact t_smartSeq _ _ (t_dropConsts _ _) h
  | .ffi .., cs, h | .storeConsts .., cs, h | .install .., cs, h => by
      rw [WordSimp.constFpLoop] <;> first | rfl | (apply t_smartSeq _ _ (t_dropConsts _ _); rfl)
  | .alloc .., _, h => by simp [WordNoAlloc] at h
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

theorem t_constFp (p : WordLangProgHOL (BitVec width)) (h : WordNoAlloc p = true) :
    WordNoAlloc (WordSimp.constFp p) = true := t_constFpLoop p _ h

theorem t_destIf (p : WordLangProgHOL (BitVec width)) (h : WordNoAlloc p = true)
    (c : Cmp) (l : Nat) (r : WordRegImm (BitVec width)) (b1 b2 : WordLangProgHOL (BitVec width))
    (e : WordSimp.destIf p = some (c, l, r, b1, b2)) : WordNoAlloc b1 = true ∧ WordNoAlloc b2 = true := by
  unfold WordSimp.destIf at e; split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, -, -, rfl, rfl⟩ := e
    simpa [WordNoAlloc] using h
  · simp at e

theorem t_tryIfHoist2 : ∀ (n : Nat) (p1 interm dummy p2 r : WordLangProgHOL (BitVec width)),
    WordNoAlloc p1 = true → WordNoAlloc interm = true → WordNoAlloc p2 = true →
      WordSimp.tryIfHoist2 n p1 interm dummy p2 = some r → WordNoAlloc r = true
  | 0, _, _, _, _, _, _, _, _, e => by simp [WordSimp.tryIfHoist2] at e
  | n + 1, p1, interm, dummy, p2, r, h1, hi, h2, e => by
      unfold WordSimp.tryIfHoist2 at e
      split at e
      · rename_i c l rr b1 b2
        simp only [WordNoAlloc, Bool.and_eq_true] at h1
        dsimp only at e
        split at e; · simp at e
        split at e; · simp at e
        simp only [Option.some.injEq] at e; subst e
        apply t_constFp; simp_all [WordNoAlloc]
      · rename_i p3 p4
        simp only [WordNoAlloc, Bool.and_eq_true] at h1
        split at e
        · rename_i c l rr b1 b2 hd
          have hb := t_destIf p4 h1.2 _ _ _ _ _ hd
          dsimp only at e
          split at e; · simp at e
          split at e; · simp at e
          simp only [Option.some.injEq] at e; subst e
          simp only [WordNoAlloc, Bool.and_eq_true]
          refine ⟨h1.1, t_constFp _ ?_⟩
          simp_all [WordNoAlloc]
        · split at e
          · exact t_tryIfHoist2 n p3 _ dummy p2 r h1.1 (by simp_all [WordNoAlloc]) h2 e
          · simp at e
      · simp at e

theorem t_tryIfHoist1 (p1 p2 r : WordLangProgHOL (BitVec width)) (h1 : WordNoAlloc p1 = true)
    (h2 : WordNoAlloc p2 = true) (e : WordSimp.tryIfHoist1 p1 p2 = some r) : WordNoAlloc r = true := by
  unfold WordSimp.tryIfHoist1 at e; split at e
  · simp at e
  · exact t_tryIfHoist2 _ _ _ _ _ _ h1 rfl h2 e

theorem t_simpDuplicateIf :
    ∀ (p : WordLangProgHOL (BitVec width)), WordNoAlloc p = true → WordNoAlloc (WordSimp.simpDuplicateIf p) = true
  | .seq a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      have ha := t_simpDuplicateIf a h.1
      have hb := t_simpDuplicateIf b h.2
      rw [WordSimp.simpDuplicateIf]
      split
      · simp only [WordNoAlloc, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · rename_i p3 e
        exact t_seqAssoc _ _ rfl (t_tryIfHoist1 _ _ _ ha hb e)
  | .ite c l r a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [WordSimp.simpDuplicateIf]; simp only [WordNoAlloc, Bool.and_eq_true]
      exact ⟨t_simpDuplicateIf a h.1, t_simpDuplicateIf b h.2⟩
  | .mustTerminate a, h => by rw [WordSimp.simpDuplicateIf]; exact t_simpDuplicateIf a h
  | .loop x a y, h => by rw [WordSimp.simpDuplicateIf]; exact t_simpDuplicateIf a h
  | .call none d args none, h => by rw [WordSimp.simpDuplicateIf]; rfl
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordSimp.simpDuplicateIf]; simp only [WordNoAlloc, Bool.true_and] at h ⊢; exact t_simpDuplicateIf q h
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordSimp.simpDuplicateIf]; simp only [WordNoAlloc, Bool.and_true] at h ⊢; exact t_simpDuplicateIf r h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordSimp.simpDuplicateIf]; simp only [WordNoAlloc, Bool.and_eq_true] at h ⊢
      exact ⟨t_simpDuplicateIf r h.1, t_simpDuplicateIf q h.2⟩
  | .skip, h | .move .., h | .inst .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .storeConsts .., h | .alloc .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .opCurrHeap .., h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by
      rw [WordSimp.simpDuplicateIf] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_pushOutIfAux :
    ∀ (p : WordLangProgHOL (BitVec width)), WordNoAlloc p = true → WordNoAlloc (WordSimp.pushOutIfAux p).1 = true
  | .seq a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      have ha := t_pushOutIfAux a h.1
      have hb := t_pushOutIfAux b h.2
      rw [WordSimp.pushOutIfAux]
      split
      · rename_i c1 e; rw [e] at ha; simp_all [WordNoAlloc]
      · rename_i c1 e; rw [e] at ha; split
        rename_i c2 bb e2; rw [e2] at hb; simp_all [WordNoAlloc]
  | .ite c l r a b, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      have ha := t_pushOutIfAux a h.1
      have hb := t_pushOutIfAux b h.2
      rw [WordSimp.pushOutIfAux]
      split <;> (rename_i e1 e2; rw [e1] at ha; rw [e2] at hb; simp_all [WordNoAlloc])
  | .mustTerminate a, h => by
      have ha := t_pushOutIfAux a h
      rw [WordSimp.pushOutIfAux]; split; rename_i c b e; rw [e] at ha; exact ha
  | .loop x a y, h => by rw [WordSimp.pushOutIfAux]; exact t_pushOutIfAux a h
  | .call none .., h => by rw [WordSimp.pushOutIfAux]; exact h
  | .call (some _) d args hd, h => by
      rw [WordSimp.pushOutIfAux] <;> first | exact h | (intros; simp_all) | skip
  | .skip, h | .move .., h | .inst .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .storeConsts .., h | .alloc .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .opCurrHeap .., h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by
      rw [WordSimp.pushOutIfAux] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_pushOutIf (p : WordLangProgHOL (BitVec width)) (h : WordNoAlloc p = true) :
    WordNoAlloc (WordSimp.pushOutIf p) = true := t_pushOutIfAux p h

theorem t_compileExp (p : WordLangProgHOL (BitVec width)) (h : WordNoAlloc p = true) :
    WordNoAlloc (WordSimp.compileExp p) = true := by
  unfold WordSimp.compileExp
  exact t_pushOutIf _ (t_simpDuplicateIf _ (t_constFp _ (t_seqAssoc _ _ rfl h)))

/-- LoopToWord output, then WordSimp, then every pass of `compileSingle` up to
(but excluding) `wordAlloc`, in the exact source order. -/
theorem t_loopToWord_simp_chain (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (c : AsmConfigExact width) (temp argc : Nat) (b : Bool) :
    WordNoAlloc (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
      (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
        (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp
          (WordSimp.compileExp (LoopToWord.compHOL ctx q l).1))))))))) = true :=
  t_ssa_cse_mid_tail_chain c temp argc b _ (t_compileExp _ (loopToWord_WordNoAlloc ctx q l))

theorem allowance_zero_through_simp (ctx : Spt Nat) (q : HolLoopProg width) (l : Nat × Nat)
    (c : AsmConfigExact width) (temp argc : Nat) (b : Bool) :
    allocAllowance (WordAlloc.removeDeadProg (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordCse.wordCommonSubexpElim
        (WordAlloc.removeDeadProg (WordAlloc.fullSsaCcTrans argc (WordInst.instSelect c temp
          (WordSimp.compileExp (LoopToWord.compHOL ctx q l).1))))))))) = 0 := by
  simp [allocAllowance, t_loopToWord_simp_chain ctx q l c temp argc b]


end InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordSimpPreservesNoAlloc



namespace InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordToWordFullCompileNoAlloc

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordPassesPreserveNoAlloc
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordMidPassesPreserveNoAlloc
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordSsaCsePreserveNoAlloc
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordSimpPreservesNoAlloc

variable {width : Nat} [NeZero width]

/-- Colouring renames registers; it never adds or removes a `storeConsts`. -/
theorem applyColour_WordNoAlloc_iff (f : Nat → Nat) :
    ∀ p : WordLangProgHOL (BitVec width), WordNoAlloc (Flapjack.WordAlloc.applyColour f p) = WordNoAlloc p
  | .seq a b => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [WordNoAlloc]
      rw [applyColour_WordNoAlloc_iff f a, applyColour_WordNoAlloc_iff f b]
  | .ite c r ri a b => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [WordNoAlloc]
      rw [applyColour_WordNoAlloc_iff f a, applyColour_WordNoAlloc_iff f b]
  | .mustTerminate a => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [WordNoAlloc]; exact applyColour_WordNoAlloc_iff f a
  | .loop x a y => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [WordNoAlloc]; exact applyColour_WordNoAlloc_iff f a
  | .call none d args none => by rw [Flapjack.WordAlloc.applyColour]; rfl
  | .call none d args (some (v, q, l1, l2)) => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [WordNoAlloc]; rw [applyColour_WordNoAlloc_iff f q]
  | .call (some (vs, cs, r, l1, l2)) d args none => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [WordNoAlloc]; rw [applyColour_WordNoAlloc_iff f r]
  | .call (some (vs, cs, r, l1, l2)) d args (some (v, q, m1, m2)) => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [WordNoAlloc]
      rw [applyColour_WordNoAlloc_iff f r, applyColour_WordNoAlloc_iff f q]
  | .skip | .move .. | .inst .. | .assign .. | .get .. | .set .. | .store .. | .storeConsts ..
  | .alloc .. | .raise .. | .return .. | .break .. | .continue .. | .tick
  | .opCurrHeap .. | .locValue .. | .install .. | .codeBufferWrite .. | .dataBufferWrite ..
  | .ffi .. | .shareInst .. => by
      rw [Flapjack.WordAlloc.applyColour] <;> first | rfl | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_applyColour (f : Nat → Nat) (p : WordLangProgHOL (BitVec width)) (h : WordNoAlloc p = true) :
    WordNoAlloc (Flapjack.WordAlloc.applyColour f p) = true := by
  rw [applyColour_WordNoAlloc_iff]; exact h

theorem t_oracleColourOk (k : Nat) (co : Option (Spt Nat)) (tree : RegAlloc.ClashTree)
    (p q : WordLangProgHOL (BitVec width)) (forced : List (Nat × Nat)) (h : WordNoAlloc p = true)
    (e : Flapjack.WordAlloc.oracleColourOk k co tree p forced = some q) : WordNoAlloc q = true := by
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
    (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat)) (h : WordNoAlloc p = true) :
    WordNoAlloc (Flapjack.WordAlloc.wordAlloc fc c alg k p co) = true := by
  unfold Flapjack.WordAlloc.wordAlloc; dsimp only
  split
  · split
    · exact t_applyColour _ _ h
    · exact h
  · rename_i q e; exact t_oracleColourOk _ _ _ _ _ _ h e

/-- Master: every function body accepted by `fullCompileSingle` with `WordNoAlloc` input
yields `WordNoAlloc` output (all 11 calls of the HOL pipeline). -/
theorem t_fullCompileSingle (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (nm ac : Nat) (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat))
    (h : WordNoAlloc p = true) :
    WordNoAlloc (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.2 = true := by
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
theorem loopToWord_fullCompileSingle_WordNoAlloc (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac : Nat)
    (co : Option (Spt Nat)) :
    WordNoAlloc (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = true :=
  t_fullCompileSingle b rc alg c nm ac _ co (loopToWord_WordNoAlloc ctx q l)

theorem loopToWord_fullCompileSingle_allowance_zero (ctx : Spt Nat) (q : HolLoopProg width)
    (l : Nat × Nat) (b : Bool) (rc alg : Nat) (c : AsmConfigExact width) (nm ac : Nat)
    (co : Option (Spt Nat)) :
    allocAllowance (WordToWord.fullCompileSingle b rc alg c
      ((nm, ac, (LoopToWord.compHOL ctx q l).1), co)).2.2 = 0 := by
  simp [allocAllowance, loopToWord_fullCompileSingle_WordNoAlloc ctx q l b rc alg c nm ac co]

/-- Whole-program lift over any list of `WordNoAlloc` functions. -/
theorem t_fullCompile_list (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (ps : List ((Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)))
    (h : ∀ x ∈ ps, WordNoAlloc x.1.2.2 = true) :
    ∀ y ∈ ps.map (WordToWord.fullCompileSingle b rc alg c), WordNoAlloc y.2.2 = true := by
  intro y hy
  obtain ⟨⟨⟨nm, ac, p⟩, co⟩, hx, rfl⟩ := List.mem_map.1 hy
  exact t_fullCompileSingle b rc alg c nm ac p co (h _ hx)

/-- Colouring is not a source of `storeConsts` but keeps an existing one. -/
theorem applyColour_keeps_alloc (f : Nat → Nat) :
    WordNoAlloc (Flapjack.WordAlloc.applyColour f
      (WordLangProgHOL.alloc (α := BitVec width) 0 (.ln, .ln))) = false := by
  rw [applyColour_WordNoAlloc_iff]; rfl

theorem fullCompileSingle_needs_hyp_counterexample :
    WordNoAlloc (WordLangProgHOL.mustTerminate (α := BitVec width)
      (.alloc 0 (.ln, .ln))) = false := rfl


end InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordToWordFullCompileNoAlloc



namespace InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.PanLang
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordPassesPreserveNoAlloc
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.WordToWordFullCompileNoAlloc

variable {width : Nat} [NeZero width]

/-! ## Word side: the whole `panToWordCompileProgHOL` output, through `WordToWord.compile` -/

theorem loopToWordCompFunc_WordNoAlloc (name : Nat) (params : List Nat) (body : HolLoopProg width) :
    WordNoAlloc (loopToWordCompFuncHOL name params body) = true := by
  unfold loopToWordCompFuncHOL; exact loopToWord_WordNoAlloc _ _ _

theorem loopToWordCompile_WordNoAlloc (code : List (Nat × List Nat × HolLoopProg width)) :
    ∀ x ∈ loopToWordCompileHOL code, WordNoAlloc x.2.2 = true := by
  intro x hx
  unfold loopToWordCompileHOL loopToWordCompileProgHOL at hx
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  exact loopToWordCompFunc_WordNoAlloc _ _ _

/-- Every function emitted by the whole Pancake→Word front end has `WordNoAlloc`. -/
theorem panToWord_WordNoAlloc (arch : AsmArchitecture) (prog : List (DeclHOL width)) :
    ∀ x ∈ panToWordCompileProgHOL arch prog, WordNoAlloc x.2.2 = true := by
  unfold panToWordCompileProgHOL; exact loopToWordCompile_WordNoAlloc _

theorem wordToWordCompile_WordNoAlloc (wc : WordToWord.Config) (ac : AsmConfigExact width)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, WordNoAlloc x.2.2 = true) :
    ∀ y ∈ (WordToWord.compile wc ac progs).2, WordNoAlloc y.2.2 = true := by
  unfold WordToWord.compile; dsimp only
  apply t_fullCompile_list
  intro x hx
  exact h _ (List.of_mem_zip hx).1

/-- Pancake → … → LoopToWord → WordToWord: every function has `WordNoAlloc`. -/
theorem panToWordToWord_WordNoAlloc (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) :
    ∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoAlloc y.2.2 = true :=
  wordToWordCompile_WordNoAlloc wc ac _ (panToWord_WordNoAlloc arch prog)

/-! ## Stack side -/

/-- No StackLang `storeConsts` anywhere. -/
def StackNoAlloc : HolProg width → Bool
  | .alloc .. => false
  | .seq a b => StackNoAlloc a && StackNoAlloc b
  | .ite _ _ _ a b => StackNoAlloc a && StackNoAlloc b
  | .loop b => StackNoAlloc b
  | .call ret _ h =>
      (match ret with | none => true | some (r, _, _, _) => StackNoAlloc r) &&
      (match h with | none => true | some (q, _, _) => StackNoAlloc q)
  | _ => true

theorem s_stackLoad : ∀ (l : List (Nat × Nat)) (x : HolProg width),
    StackNoAlloc (wStackLoadNative l x) = StackNoAlloc x
  | [], x => rfl
  | (r, i) :: ps, x => by
      simp only [wStackLoadNative, StackNoAlloc, Bool.true_and]; exact s_stackLoad ps x

theorem s_regWrite1 (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (hg : ∀ n, StackNoAlloc (g n) = true) : StackNoAlloc (wRegWrite1Native g r kf) = true := by
  unfold wRegWrite1Native; dsimp only; split
  · exact hg _
  · simp [StackNoAlloc, hg]

theorem s_wInst (i : HolInst width) (kf : Nat × Nat × Nat) :
    StackNoAlloc (wInstNative i kf) = true := by
  unfold wInstNative
  split <;> (try simp only [s_stackLoad]) <;>
    first | rfl | (apply s_regWrite1; intro n; rfl)

theorem s_wMoveAux : ∀ (l : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat),
    StackNoAlloc (wMoveAuxNative (width := width) l kf) = true
  | [], _ => rfl
  | [xy], kf => by
      rw [wMoveAuxNative]; unfold wMoveSingleNative; split <;> rfl
  | xy :: y :: ys, kf => by
      simp only [wMoveAuxNative, StackNoAlloc, Bool.and_eq_true]
      refine ⟨?_, s_wMoveAux (y :: ys) kf⟩
      unfold wMoveSingleNative; split <;> rfl

theorem s_wMove (m : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    StackNoAlloc (wMoveNative (width := width) m kf) = true := by
  unfold wMoveNative; exact s_wMoveAux _ _

theorem s_seqStackFree (n : Nat) (p : HolProg width) (h : StackNoAlloc p = true) :
    StackNoAlloc (seqStackFreeNative n p) = true := by
  unfold seqStackFreeNative; split
  · exact h
  · simpa [StackNoAlloc] using h

theorem s_copyRetAux (k f : Nat) : ∀ n, StackNoAlloc (copyRetAuxNative (width := width) k f n) = true
  | 0 => rfl
  | n + 1 => by
      rw [copyRetAuxNative]; simp only [listSeq, StackNoAlloc, Bool.true_and]
      exact s_copyRetAux k f n

theorem s_copyRet {β γ : Type} (perf ih : Bool) (kf : Nat × Nat × γ) (vs : List β)
    (kont : HolProg width) (h : StackNoAlloc kont = true) :
    StackNoAlloc (copyRetNative perf ih kf vs kont) = true := by
  unfold copyRetNative; dsimp only; split
  · exact h
  · simp only [StackNoAlloc, Bool.and_eq_true]
    exact ⟨s_copyRetAux _ _ _, s_seqStackFree _ _ h⟩

theorem s_stackMove (start offset i : Nat) (p : HolProg width) (h : StackNoAlloc p = true) :
    ∀ n, StackNoAlloc (stackMoveNative n start offset i p) = true := by
  intro n
  induction n generalizing start with
  | zero => exact h
  | succ n ih =>
      rw [stackMoveNative]; simp only [StackNoAlloc, Bool.and_true]; exact ih _

theorem s_stackArgs {α β : Type} (d : Sum α β) (ac : Nat) (kf : Nat × Nat × Nat) :
    StackNoAlloc (stackArgsNative (width := width) d ac kf) = true := by
  unfold stackArgsNative; exact s_stackMove _ _ _ _ rfl _

theorem s_callDest (pos : Option Nat) (args : List Nat) (kf : Nat × Nat × Nat) :
    StackNoAlloc (callDestNative (width := width) pos args kf).1 = true := by
  unfold callDestNative; split
  · rfl
  · split
    · rfl
    · dsimp only; rw [s_stackLoad]; rfl

theorem s_pushHandler {β γ : Type} (perf : Bool) (l1 l2 : Nat) (kf : Nat × β × γ) :
    StackNoAlloc (pushHandlerNative (width := width) perf l1 l2 kf) = true := by
  unfold pushHandlerNative; cases perf <;> rfl

theorem s_popHandler {β γ : Type} (perf : Bool) (kf : Nat × β × γ) (p : HolProg width)
    (h : StackNoAlloc p = true) : StackNoAlloc (popHandlerNative perf kf p) = true := by
  unfold popHandlerNative; simpa [StackNoAlloc] using h

theorem s_wLive (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : StackNoAlloc (wLiveNative live bs kf).1 = true := by
  unfold wLiveNative; split <;> rfl

theorem s_wShareInst (op : HolMemop) (v : Nat) (a : HolAddr width) (kf : Nat × Nat × Nat) :
    StackNoAlloc (wShareInstNative op v a kf) = true := by
  unfold wShareInstNative
  split <;> (try simp only [s_stackLoad]) <;> first | rfl | (apply s_regWrite1; intro n; rfl)

/-- WordToStack never creates a StackLang `storeConsts` from a `WordNoAlloc` WordLang body. -/
theorem s_compNative (conf : AsmConfigExact width) (perf : Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
      (kf : Nat × Nat × Nat), WordNoAlloc p = true → StackNoAlloc (compNative conf perf p bs kf).1 = true
  | .seq a b, bs, kf, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      rw [compNative]; simp only [StackNoAlloc, Bool.and_eq_true]
      exact ⟨s_compNative conf perf a _ _ h.1, s_compNative conf perf b _ _ h.2⟩
  | .ite c r ri a b, bs, kf, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      have ha := s_compNative conf perf a bs kf h.1
      have hb := s_compNative conf perf b (compNative conf perf a bs kf).2 kf h.2
      rw [compNative]; dsimp only
      split
      · rw [s_stackLoad]; simp only [StackNoAlloc, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · split
        · rw [s_stackLoad]; simp only [StackNoAlloc, Bool.and_eq_true]; exact ⟨ha, hb⟩
        · simp only [StackNoAlloc, Bool.true_and]; rw [s_stackLoad]
          simp only [StackNoAlloc, Bool.and_eq_true]; exact ⟨ha, hb⟩
  | .mustTerminate a, bs, kf, h => by rw [compNative]; exact s_compNative conf perf a _ _ h
  | .loop x a y, bs, kf, h => by
      rw [compNative]; exact s_compNative conf perf a _ _ h
  | .call none d args hd, bs, kf, h => by
      rw [compNative]; dsimp only
      simp only [StackNoAlloc, Bool.and_eq_true]
      exact ⟨s_callDest _ _ _, s_seqStackFree _ _ rfl⟩
  | .call (some (vs, live, rc, l1, l2)) d args none, bs, kf, h => by
      simp only [WordNoAlloc, Bool.and_true] at h
      have hr := s_compNative conf perf rc (wLiveNative live bs kf).2 kf h
      rw [compNative]; dsimp only
      simp only [StackNoAlloc, Bool.and_eq_true, Bool.and_true]
      refine ⟨s_callDest _ _ _, s_wLive _ _ _, s_stackArgs _ _ _, ?_, ?_⟩
      · split <;> rfl
      · refine ⟨?_, s_copyRet _ _ _ _ _ hr⟩
        split <;> rfl
  | .call (some (vs, live, rc, l1, l2)) d args (some (e, hc, h1, h2)), bs, kf, h => by
      simp only [WordNoAlloc, Bool.and_eq_true] at h
      have hr := s_compNative conf perf rc (wLiveNative live bs kf).2 kf h.1
      have hh := s_compNative conf perf hc
        (compNative conf perf rc (wLiveNative live bs kf).2 kf).2 kf h.2
      rw [compNative]; dsimp only
      simp only [StackNoAlloc, Bool.and_eq_true]
      refine ⟨s_callDest _ _ _, s_wLive _ _ _, s_pushHandler _ _ _ _,
        s_stackArgs _ _ _, ?_, ⟨?_, s_copyRet _ _ _ _ _ (s_popHandler _ _ _ hr)⟩, hh⟩
      · split <;> rfl
      · split <;> rfl
  | .alloc .., _, _, h => by simp [WordNoAlloc] at h
  | .move .., bs, kf, h => by rw [compNative]; exact s_wMove _ _
  | .inst i, bs, kf, h => by rw [compNative]; exact s_wInst _ _
  | .return v vs, bs, kf, h => by
      rw [compNative]; dsimp only; rw [s_stackLoad]; exact s_seqStackFree _ _ rfl
  | .opCurrHeap .., bs, kf, h => by
      rw [compNative]; dsimp only; rw [s_stackLoad]; apply s_regWrite1; intro; rfl
  | .set name e, bs, kf, h => by
      rw [compNative.eq_def]; dsimp only
      repeat' split
      all_goals first | rfl | (rw [s_stackLoad]; rfl)
  | .get d st, bs, kf, h => by
      rw [compNative]; exact s_regWrite1 (fun r => .get r (storeNameOfWord st)) d kf (fun _ => rfl)
  | .locValue d l, bs, kf, h => by
      rw [compNative]; exact s_regWrite1 (fun n => .locValue n l 0) d kf (fun _ => rfl)
  | .storeConsts .., bs, kf, h => by rw [compNative]; rfl
  | .install .., bs, kf, h | .codeBufferWrite .., bs, kf, h | .dataBufferWrite .., bs, kf, h => by
      rw [compNative] <;> (try dsimp only) <;> rw [s_stackLoad] <;> rfl
  | .shareInst op v e, bs, kf, h => by
      rw [compNative]; split
      · rfl
      · exact s_wShareInst _ _ _ _
  | .skip, _, _, _ | .raise .., _, _, _ | .tick, _, _, _ | .break .., _, _, _
  | .continue .., _, _, _ | .ffi .., _, _, _ | .assign .., _, _, _ | .store .., _, _, _ => by
      rw [compNative] <;> first | rfl | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem s_compileProgNative (conf : AsmConfigExact width) (perf : Bool)
    (p : WordLangProgHOL (BitVec width)) (ac rc : Nat) (bs : AppList (BitVec width) × Nat)
    (h : WordNoAlloc p = true) : StackNoAlloc (compileProgNative conf perf p ac rc bs).1 = true := by
  unfold compileProgNative; dsimp only
  simp only [StackNoAlloc, Bool.true_and]; exact s_compNative conf perf p _ _ h

theorem s_compileWordToStack {β : Type} (conf : AsmConfigExact width) (perf : Bool) (rc : Nat) :
    ∀ (progs : List (β × Nat × WordLangProgHOL (BitVec width))) (bs : AppList (BitVec width) × Nat),
      (∀ x ∈ progs, WordNoAlloc x.2.2 = true) →
      ∀ y ∈ (compileWordToStackNative conf perf rc progs bs).1, StackNoAlloc y.2 = true
  | [], _, _ => by intro y hy; simp [compileWordToStackNative] at hy
  | (i, ac, p) :: ps, bs, h => by
      intro y hy
      rw [compileWordToStackNative] at hy; dsimp only at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact s_compileProgNative conf perf p ac rc bs (h _ (List.mem_cons_self ..))
      · exact s_compileWordToStack conf perf rc ps _
          (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy

/-- Top-level WordToStack: every *compiled body* is `StackNoAlloc`; the only
StackLang `storeConsts` is the fixed prepended stub. -/
theorem s_compileNative_bodies (conf : AsmConfigExact width) (perf : Bool)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, WordNoAlloc x.2.2 = true) :
    ∀ y ∈ (compileNative conf perf progs).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoAlloc y.2 = true := by
  intro y hy
  unfold compileNative at hy; dsimp only at hy
  rcases List.mem_cons.1 hy with rfl | hy
  · right; unfold raiseStubNative; cases perf <;> rfl
  rcases List.mem_cons.1 hy with rfl | hy
  · left; rfl
  · right; exact s_compileWordToStack conf perf _ progs _ h y hy

/-- StackAlloc `comp` preserves `StackNoAlloc` (it only rewrites `alloc` / `storeConsts (some _)`). -/
theorem s_stackAllocComp : ∀ (n m : Nat) (p : HolProg width), StackNoAlloc p = true →
    StackNoAlloc (StackAlloc.comp n m p).1 = true
  | n, m, .seq a b, h => by
      simp only [StackNoAlloc, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [StackNoAlloc, Bool.and_eq_true]
      exact ⟨s_stackAllocComp n m a h.1, s_stackAllocComp n _ b h.2⟩
  | n, m, .ite c r ri a b, h => by
      simp only [StackNoAlloc, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [StackNoAlloc, Bool.and_eq_true]
      exact ⟨s_stackAllocComp n m a h.1, s_stackAllocComp n _ b h.2⟩
  | n, m, .loop a, h => by
      rw [StackAlloc.comp]; exact s_stackAllocComp n m a h
  | n, m, .call none d e, h => by rw [StackAlloc.comp]; rfl
  | n, m, .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [StackNoAlloc, Bool.and_true] at h
      rw [StackAlloc.comp]; simp only [StackNoAlloc, Bool.and_true]
      exact s_stackAllocComp n m p1 h
  | n, m, .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [StackNoAlloc, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [StackNoAlloc, Bool.and_eq_true]
      exact ⟨s_stackAllocComp n m p1 h.1, s_stackAllocComp n _ p2 h.2⟩
  | n, m, .storeConsts _ _ c, h => by cases c <;> rw [StackAlloc.comp.eq_def] <;> rfl
  | n, m, .alloc .., h => by simp [StackNoAlloc] at h
  | n, m, .skip, h | n, m, .inst .., h | n, m, .get .., h | n, m, .set .., h
  | n, m, .opCurrHeap .., h | n, m, .jumpLower .., h | n, m, .raise .., h | n, m, .ret .., h
  | n, m, .break .., h | n, m, .continue .., h | n, m, .ffi .., h | n, m, .tick, h
  | n, m, .locValue .., h | n, m, .install .., h | n, m, .shMemOp .., h
  | n, m, .codeBufferWrite .., h | n, m, .dataBufferWrite .., h | n, m, .rawCall .., h
  | n, m, .stackAlloc .., h | n, m, .stackFree .., h | n, m, .stackStore .., h
  | n, m, .stackStoreAny .., h | n, m, .stackLoad .., h | n, m, .stackLoadAny .., h
  | n, m, .stackGetSize .., h | n, m, .stackSetSize .., h | n, m, .bitmapLoad .., h
  | n, m, .halt .., h => by
      rw [StackAlloc.comp] <;> first | exact h | (intros; simp_all) | skip
termination_by _ _ p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem s_progComp (x : Nat × HolProg width) (h : StackNoAlloc x.2 = true) :
    StackNoAlloc (StackAlloc.progComp x).2 = true := by
  obtain ⟨n, p⟩ := x; unfold StackAlloc.progComp; exact s_stackAllocComp _ _ _ h

/-- End-to-end: Pancake → Word → WordToWord → WordToStack → StackAlloc.comp: every
non-stub body is `StackNoAlloc`. -/
theorem panToStackAlloc_WordNoAlloc (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoAlloc (StackAlloc.progComp y).2 = true := by
  intro y hy
  rcases s_compileNative_bodies ac perf _ (panToWordToWord_WordNoAlloc arch prog wc ac) y hy with h | h
  · exact Or.inl h
  · exact Or.inr (s_progComp y h)


end InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc

/-! # Stack side: StackRawCall / StackAlloc structure, and the master -/

namespace InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open PanToStackNoAlloc (StackNoAlloc)

variable {width : Nat} [NeZero width]

/-- No direct call to the GC stub label. -/
def NoGcCall : HolProg width → Bool
  | .call ret t h =>
      (match t with | .inl n => n != gcStubLocation | .inr _ => true) &&
      (match ret with | none => true | some (r, _, _, _) => NoGcCall r) &&
      (match h with | none => true | some (q, _, _) => NoGcCall q)
  | .seq a b => NoGcCall a && NoGcCall b
  | .ite _ _ _ a b => NoGcCall a && NoGcCall b
  | .loop b => NoGcCall b
  | .storeConsts _ _ (some l) => l != gcStubLocation
  | _ => true

theorem gcStubLocation_eq : gcStubLocation = 4 := by decide

/-! ## StackRawCall preserves `StackNoAlloc` -/

theorem a_compSeq (a b fb : HolProg width) (info : Spt Nat) (hfb : StackNoAlloc fb = true) :
    StackNoAlloc (StackRawCall.compSeq a b info fb) = true := by
  unfold StackRawCall.compSeq; split
  · exact hfb
  · split
    · exact hfb
    · split
      · rfl
      · split <;> rfl

theorem a_rawCallComp (info : Spt Nat) :
    ∀ p : HolProg width, StackNoAlloc p = true → StackNoAlloc (StackRawCall.comp info p) = true
  | .seq a b, h => by
      simp only [StackNoAlloc, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; apply a_compSeq
      simp only [StackNoAlloc, Bool.and_eq_true]
      exact ⟨a_rawCallComp info a h.1, a_rawCallComp info b h.2⟩
  | .ite c r ri a b, h => by
      simp only [StackNoAlloc, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [StackNoAlloc, Bool.and_eq_true]
      exact ⟨a_rawCallComp info a h.1, a_rawCallComp info b h.2⟩
  | .loop a, h => by rw [StackRawCall.comp]; exact a_rawCallComp info a h
  | .call none d e, h => by rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all)
  | .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [StackNoAlloc, Bool.and_true] at h
      rw [StackRawCall.comp]; simp only [StackNoAlloc, Bool.and_true]
      exact a_rawCallComp info p1 h
  | .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [StackNoAlloc, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [StackNoAlloc, Bool.and_eq_true]
      exact ⟨a_rawCallComp info p1 h.1, a_rawCallComp info p2 h.2⟩
  | .skip, h | .inst .., h | .get .., h | .set .., h | .opCurrHeap .., h
  | .jumpLower .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .ret .., h
  | .break .., h | .continue .., h | .ffi .., h | .tick, h | .locValue .., h
  | .install .., h | .shMemOp .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .rawCall .., h
  | .stackAlloc .., h | .stackFree .., h | .stackStore .., h | .stackStoreAny .., h | .stackLoad .., h
  | .stackLoadAny .., h | .stackGetSize .., h | .stackSetSize .., h | .bitmapLoad .., h | .halt .., h => by
      rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem a_rawCallCompTop (info : Spt Nat) (p : HolProg width) (h : StackNoAlloc p = true) :
    StackNoAlloc (StackRawCall.compTop info p) = true := by
  rw [StackRawCall.compTop.eq_def]; split
  · rename_i a b
    simp only [StackNoAlloc, Bool.and_eq_true] at h
    simp only [StackNoAlloc, Bool.and_eq_true]
    exact ⟨a_rawCallComp info a h.1, a_rawCallComp info b h.2⟩
  · exact a_rawCallComp info p h

/-! ## StackAlloc on `.alloc`-free code: never calls the GC stub -/

/-- Under `StackNoAlloc`, `StackAlloc.comp` emits no call to `gcStubLocation`, and keeps
`StackNoAlloc`. (The only `.inl gcStubLocation` it creates comes from `.alloc`; a
`storeConsts _ _ (some loc)` becomes a call to `loc`, which on our pipeline is `6 ≠ 4`.) -/
theorem g_stackAllocComp : ∀ (n m : Nat) (p : HolProg width),
    StackNoAlloc p = true → NoGcCall p = true →
    StackNoAlloc (StackAlloc.comp n m p).1 = true ∧ NoGcCall (StackAlloc.comp n m p).1 = true
  | n, m, .seq a b, h, g => by
      simp only [StackNoAlloc, NoGcCall, Bool.and_eq_true] at h g
      have h1 := g_stackAllocComp n m a h.1 g.1
      have h2 := g_stackAllocComp n (StackAlloc.comp n m a).2 b h.2 g.2
      rw [StackAlloc.comp]; simp only [StackNoAlloc, NoGcCall, Bool.and_eq_true]
      exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩
  | n, m, .ite c r ri a b, h, g => by
      simp only [StackNoAlloc, NoGcCall, Bool.and_eq_true] at h g
      have h1 := g_stackAllocComp n m a h.1 g.1
      have h2 := g_stackAllocComp n (StackAlloc.comp n m a).2 b h.2 g.2
      rw [StackAlloc.comp]; simp only [StackNoAlloc, NoGcCall, Bool.and_eq_true]
      exact ⟨⟨h1.1, h2.1⟩, h1.2, h2.2⟩
  | n, m, .loop a, h, g => by
      rw [StackAlloc.comp]; exact g_stackAllocComp n m a h g
  | n, m, .call none d e, h, g => by
      rw [StackAlloc.comp]
      cases d <;> cases e <;> simp_all [NoGcCall, StackNoAlloc]
  | n, m, .call (some (p1, lr, l1, l2)) d none, h, g => by
      simp only [StackNoAlloc, NoGcCall, Bool.and_true, Bool.and_eq_true] at h g
      have h1 := g_stackAllocComp n m p1 h g.2
      rw [StackAlloc.comp]; simp only [StackNoAlloc, NoGcCall, Bool.and_true, Bool.and_eq_true]
      exact ⟨h1.1, g.1, h1.2⟩
  | n, m, .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h, g => by
      simp only [StackNoAlloc, NoGcCall, Bool.and_eq_true] at h g
      have h1 := g_stackAllocComp n m p1 h.1 g.1.2
      have h2 := g_stackAllocComp n (StackAlloc.comp n m p1).2 p2 h.2 g.2
      rw [StackAlloc.comp]; simp only [StackNoAlloc, NoGcCall, Bool.and_eq_true]
      exact ⟨⟨h1.1, h2.1⟩, ⟨g.1.1, h1.2⟩, h2.2⟩
  | n, m, .alloc _, h, _ => by simp [StackNoAlloc] at h
  | n, m, .storeConsts a b c, h, g => by
      cases c with
      | none => rw [StackAlloc.comp.eq_def]; exact ⟨rfl, rfl⟩
      | some loc =>
          rw [StackAlloc.comp]
          simp_all [StackNoAlloc, NoGcCall]
  | n, m, .skip, h, g | n, m, .inst .., h, g | n, m, .get .., h, g | n, m, .set .., h, g
  | n, m, .opCurrHeap .., h, g | n, m, .jumpLower .., h, g | n, m, .raise .., h, g | n, m, .ret .., h, g
  | n, m, .break .., h, g | n, m, .continue .., h, g | n, m, .ffi .., h, g | n, m, .tick, h, g
  | n, m, .locValue .., h, g | n, m, .install .., h, g | n, m, .shMemOp .., h, g
  | n, m, .codeBufferWrite .., h, g | n, m, .dataBufferWrite .., h, g | n, m, .rawCall .., h, g
  | n, m, .stackAlloc .., h, g | n, m, .stackFree .., h, g | n, m, .stackStore .., h, g
  | n, m, .stackStoreAny .., h, g | n, m, .stackLoad .., h, g | n, m, .stackLoadAny .., h, g
  | n, m, .stackGetSize .., h, g | n, m, .stackSetSize .., h, g | n, m, .bitmapLoad .., h, g
  | n, m, .halt .., h, g => by
      rw [StackAlloc.comp] <;> first | exact ⟨h, g⟩ | (intros; simp_all) | skip
termination_by _ _ p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

/-! ## StackAlloc is the identity on `.alloc`/`storeConsts`-free code -/

/-- Tail calls (`ret = none`) carry no handler (StackAlloc drops such handlers, as in HOL;
WordToStack only emits `.call none dest none`). -/
def NoTailHandler : HolProg width → Bool
  | .call none _ h => h.isNone
  | .call (some (r, _, _, _)) _ h =>
      NoTailHandler r && (match h with | none => true | some (q, _, _) => NoTailHandler q)
  | .seq a b => NoTailHandler a && NoTailHandler b
  | .ite _ _ _ a b => NoTailHandler a && NoTailHandler b
  | .loop b => NoTailHandler b
  | _ => true

theorem stackAllocComp_id : ∀ (n m : Nat) (p : HolProg width),
    StackNoAlloc p = true → InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt p = true →
    NoTailHandler p = true → StackAlloc.comp n m p = (p, m)
  | n, m, .seq a b, h, s, t => by
      simp only [StackNoAlloc, InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt,
        Bool.and_eq_true] at h s
      simp only [NoTailHandler, Bool.and_eq_true] at t
      rw [StackAlloc.comp, stackAllocComp_id n m a h.1 s.1 t.1]; dsimp only
      rw [stackAllocComp_id n m b h.2 s.2 t.2]
  | n, m, .ite c r ri a b, h, s, t => by
      simp only [StackNoAlloc, InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt,
        Bool.and_eq_true] at h s
      simp only [NoTailHandler, Bool.and_eq_true] at t
      rw [StackAlloc.comp, stackAllocComp_id n m a h.1 s.1 t.1]; dsimp only
      rw [stackAllocComp_id n m b h.2 s.2 t.2]
  | n, m, .loop a, h, s, t => by
      rw [StackAlloc.comp, stackAllocComp_id n m a h s t]
  | n, m, .call none d e, h, s, t => by
      cases e with
      | none => rw [StackAlloc.comp]
      | some _ => simp [NoTailHandler] at t
  | n, m, .call (some (p1, lr, l1, l2)) d none, h, s, t => by
      simp only [StackNoAlloc, InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt,
        Bool.and_true] at h s
      simp only [NoTailHandler, Bool.and_true] at t
      rw [StackAlloc.comp, stackAllocComp_id n m p1 h s t]
  | n, m, .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h, s, t => by
      simp only [StackNoAlloc, InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt,
        Bool.and_eq_true] at h s
      simp only [NoTailHandler, Bool.and_eq_true] at t
      rw [StackAlloc.comp, stackAllocComp_id n m p1 h.1 s.1 t.1]; dsimp only
      rw [stackAllocComp_id n m p2 h.2 s.2 t.2]
  | n, m, .alloc _, h, _, _ => by simp [StackNoAlloc] at h
  | n, m, .storeConsts .., _, s, _ => by
      simp [InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt] at s
  | n, m, .skip, h, s, t | n, m, .inst .., h, s, t | n, m, .get .., h, s, t | n, m, .set .., h, s, t
  | n, m, .opCurrHeap .., h, s, t | n, m, .jumpLower .., h, s, t | n, m, .raise .., h, s, t | n, m, .ret .., h, s, t
  | n, m, .break .., h, s, t | n, m, .continue .., h, s, t | n, m, .ffi .., h, s, t | n, m, .tick, h, s, t
  | n, m, .locValue .., h, s, t | n, m, .install .., h, s, t | n, m, .shMemOp .., h, s, t
  | n, m, .codeBufferWrite .., h, s, t | n, m, .dataBufferWrite .., h, s, t | n, m, .rawCall .., h, s, t
  | n, m, .stackAlloc .., h, s, t | n, m, .stackFree .., h, s, t | n, m, .stackStore .., h, s, t
  | n, m, .stackStoreAny .., h, s, t | n, m, .stackLoad .., h, s, t | n, m, .stackLoadAny .., h, s, t
  | n, m, .stackGetSize .., h, s, t | n, m, .stackSetSize .., h, s, t | n, m, .bitmapLoad .., h, s, t
  | n, m, .halt .., h, s, t => by
      rw [StackAlloc.comp] <;> first | rfl | (intros; simp_all) | skip
termination_by _ _ p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

/-- Tight: a tail call with a handler is rewritten (handler dropped). -/
theorem stackAllocComp_drops_tail_handler (n m : Nat) (d : Sum Nat Nat) (q : HolProg width) (k1 k2 : Nat) :
    StackAlloc.comp n m (.call none d (some (q, k1, k2))) = (.call none d none, m) := by
  rw [StackAlloc.comp]

/-! ## Unconditional pipeline facts -/

/-- **No `.alloc` anywhere**, for any Pancake program, in every section produced by
`panToWordCompileProgHOL → WordToWord.compile → compileNative → StackRawCall.compile`,
stubs of `compileNative` included (raise stub and the `storeConsts` stub `6`). -/
theorem panToStackRawCall_noAlloc_unconditional (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true := by
  intro y hy
  simp only [StackRawCall.compile] at hy
  rcases List.mem_map.1 hy with ⟨x, hx, rfl⟩
  apply a_rawCallCompTop
  rcases PanToStackNoAlloc.s_compileNative_bodies ac perf _
      (PanToStackNoAlloc.panToWordToWord_WordNoAlloc arch prog wc ac) x hx with h | h
  · -- the stub `6` = `storeConstsStubNative k` has no `.alloc`
    have hmem := hx
    unfold compileNative at hmem; dsimp only at hmem
    rcases List.mem_cons.1 hmem with rfl | hmem
    · unfold raiseStubNative; cases perf <;> rfl
    rcases List.mem_cons.1 hmem with rfl | hmem
    · rfl
    · exact PanToStackNoAlloc.s_compileWordToStack ac perf _ _ _
        (PanToStackNoAlloc.panToWordToWord_WordNoAlloc arch prog wc ac) x hmem
  · exact h

/-- **StackAlloc structural on the real pipeline.** For every Pancake program and every
section `y` of `StackRawCall.compile …` whose source has no direct GC call, the StackAlloc
image `progComp y` has no `.alloc` and no direct call to the GC stub `4`. -/
theorem panToStackAlloc_noAlloc_noGcCall (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      NoGcCall y.2 = true →
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true := by
  intro y hy hg
  obtain ⟨n, p⟩ := y
  unfold StackAlloc.progComp
  exact g_stackAllocComp _ _ _ (panToStackRawCall_noAlloc_unconditional arch prog wc ac perf _ hy) hg

/-! ## Master: PanToWord → WordToWord → WordToStack → StackRawCall → StackAlloc → StackRemove -/

/-- **Master.** For every Pancake program:
1. no section of the StackRawCall output contains `.alloc` (stubs included);
2. StackAlloc creates no GC call: a section without a direct GC call keeps none and stays
   `.alloc`-free;
3. every section `≠ 6` after StackAlloc is `Clean` (no `storeConsts`, no direct call to `6`);
4. every user body `≠ 6` is simulated by `StackRemove.comp` with zero extra clock (at most one
   tick on a final `halt`), from a state whose code is the live table (section `6` removed),
   assuming only a `storeConsts`-free run-time oracle. -/
theorem panToStackRemove_noAlloc_noGc_zeroExtraClock {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) :
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2, StackNoAlloc y.2 = true) ∧
    (∀ y ∈ StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      NoGcCall y.2 = true →
      StackNoAlloc (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    (∀ e ∈ InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
        arch prog wc ac perf dc, e.1 ≠ storeConstsStubLocation →
      InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true ∧
      InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts.Clean e.2 = true) ∧
    (∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = sptFromAList
          (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.liveSections
            (InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections
              arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1,
          InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt e.2 = true) →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget,
          InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock.ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget)) :=
  ⟨panToStackRawCall_noAlloc_unconditional arch prog wc ac perf,
   panToStackAlloc_noAlloc_noGcCall arch prog wc ac perf,
   fun e he hne =>
     let h := InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.stackAllocSections_noSt_and_noStubCall
       arch prog wc ac perf dc e he hne
     ⟨h.1, h.2.2⟩,
   InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.panToStackRemove_body_zeroExtraClock_liveTable
     arch prog wc ac perf dc info⟩

/-! ## Tightness -/

theorem alloc_not_noAlloc (k : Nat) : StackNoAlloc (.alloc k : HolProg width) = false := rfl

/-- On a real `.alloc`, StackAlloc does emit a GC call: the hypothesis is necessary. -/
theorem stackAlloc_alloc_calls_gc (n m k : Nat) :
    NoGcCall (StackAlloc.comp n m (.alloc k : HolProg width)).1 = false := by
  rw [StackAlloc.comp]; simp [NoGcCall]

theorem noGcCall_rejects_gc :
    NoGcCall (.call none (.inl gcStubLocation) none : HolProg width) = false := by
  simp [NoGcCall]

end InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural
