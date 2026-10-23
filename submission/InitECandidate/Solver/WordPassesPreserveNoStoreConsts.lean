import InitECandidate.Solver.PanToWordNoStoreConsts
import Flapjack.Compiler.Backend.WordToWord.Compile

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.WordPassesPreserveNoStoreConsts

open Flapjack
open Flapjack.Compiler.Backend

/-- No `storeConsts` anywhere (StackRemove's only offset source). -/
def NoSt {α : Type} : WordLangProgHOL α → Bool
  | .storeConsts .. => false
  | .mustTerminate b => NoSt b
  | .seq a b => NoSt a && NoSt b
  | .ite _ _ _ a b => NoSt a && NoSt b
  | .loop _ b _ => NoSt b
  | .call ret _ _ h =>
      (match ret with | none => true | some (_, _, r, _, _) => NoSt r) &&
      (match h with | none => true | some (_, p, _, _) => NoSt p)
  | _ => true

theorem t_removeMustTerminate {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)), NoSt p = true → NoSt (WordRemove.removeMustTerminate p) = true
  | .seq a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordRemove.removeMustTerminate]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_removeMustTerminate a h.1, t_removeMustTerminate b h.2⟩
  | .ite c r ri a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordRemove.removeMustTerminate]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_removeMustTerminate a h.1, t_removeMustTerminate b h.2⟩
  | .mustTerminate a, h => by
      rw [WordRemove.removeMustTerminate]; exact t_removeMustTerminate a h
  | .loop x a y, h => by
      rw [WordRemove.removeMustTerminate]; exact t_removeMustTerminate a h
  | .call none d args none, h => by rw [WordRemove.removeMustTerminate.eq_def]; rfl
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [NoSt, Bool.true_and] at h ⊢; exact t_removeMustTerminate q h
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [NoSt, Bool.and_true] at h ⊢; exact t_removeMustTerminate r h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [NoSt, Bool.and_eq_true] at h ⊢
      exact ⟨t_removeMustTerminate r h.1, t_removeMustTerminate q h.2⟩
  | .skip, h | .move .., h | .inst .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .opCurrHeap .., h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by simp_all [WordRemove.removeMustTerminate, NoSt]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_threeToTwoReg {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)), NoSt p = true → NoSt (WordInst.threeToTwoReg p) = true
  | .seq a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordInst.threeToTwoReg]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_threeToTwoReg a h.1, t_threeToTwoReg b h.2⟩
  | .ite c r ri a b, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [WordInst.threeToTwoReg]; simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_threeToTwoReg a h.1, t_threeToTwoReg b h.2⟩
  | .mustTerminate a, h => by
      rw [WordInst.threeToTwoReg]; exact t_threeToTwoReg a h
  | .loop x a y, h => by
      rw [WordInst.threeToTwoReg]; exact t_threeToTwoReg a h
  | .call none d args none, h => by rw [WordInst.threeToTwoReg.eq_def]; rfl
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [NoSt, Bool.true_and] at h ⊢; exact t_threeToTwoReg q h
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [NoSt, Bool.and_true] at h ⊢; exact t_threeToTwoReg r h
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [NoSt, Bool.and_eq_true] at h ⊢
      exact ⟨t_threeToTwoReg r h.1, t_threeToTwoReg q h.2⟩
  | .opCurrHeap .., h => by rw [WordInst.threeToTwoReg]; rfl
  | .inst i, h => by
      rw [WordInst.threeToTwoReg.eq_def]; split <;> simp_all [NoSt]
  | .skip, h | .move .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by rw [WordInst.threeToTwoReg]; all_goals first | exact h | (intros; contradiction) | simp_all
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_threeToTwo {width : Nat} [NeZero width] (b : Bool) (p : WordLangProgHOL (BitVec width))
    (h : NoSt p = true) : NoSt (WordInst.threeToTwoRegProg b p) = true := by
  unfold WordInst.threeToTwoRegProg; split
  · exact t_threeToTwoReg p h
  · exact h

theorem t_destSeqMove {width : Nat} [NeZero width] (q : WordLangProgHOL (BitVec width))
    (hq : NoSt q = true) (n : Nat) (l : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (h : WordUnreach.destSeqMove q = some (n, l, rest)) : NoSt rest = true := by
  unfold WordUnreach.destSeqMove at h
  split at h <;> simp_all [NoSt]
  all_goals (obtain ⟨-, -, rfl⟩ := h; simp_all [NoSt])

theorem t_simpSeq {width : Nat} [NeZero width] (p q : WordLangProgHOL (BitVec width))
    (hp : NoSt p = true) (hq : NoSt q = true) : NoSt (WordUnreach.simpSeq p q) = true := by
  unfold WordUnreach.simpSeq
  split
  · exact hp
  · split <;> (try exact hp) <;> (try exact hq) <;> (try simp_all [NoSt])
    all_goals (split <;> (try simp_all [NoSt]) <;> (try split) <;> (try simp_all [NoSt]))
    all_goals (rename_i heq _; exact t_destSeqMove _ hq _ _ _ heq)

theorem t_seqAssocRight {width : Nat} [NeZero width] :
    ∀ (p acc : WordLangProgHOL (BitVec width)), NoSt p = true → NoSt acc = true →
      NoSt (WordUnreach.seqAssocRight p acc) = true
  | .skip, acc, _, ha => by rw [WordUnreach.seqAssocRight]; exact ha
  | .seq a b, acc, hp, ha => by
      simp only [NoSt, Bool.and_eq_true] at hp
      rw [WordUnreach.seqAssocRight]
      exact t_seqAssocRight a _ hp.1 (t_seqAssocRight b acc hp.2 ha)
  | .ite v n r a b, acc, hp, ha => by
      simp only [NoSt, Bool.and_eq_true] at hp
      rw [WordUnreach.seqAssocRight]
      apply t_simpSeq _ _ _ ha
      simp only [NoSt, Bool.and_eq_true]
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
      simp only [NoSt, Bool.and_true] at hp
      apply t_simpSeq _ _ _ ha
      simp only [NoSt, Bool.and_true]; exact t_seqAssocRight q1 _ hp rfl
  | .call (some (x1, x2, q1, x3, x4)) d args (some (y1, q2, y2, y3)), acc, hp, ha => by
      rw [WordUnreach.seqAssocRight]
      simp only [NoSt, Bool.and_eq_true] at hp
      apply t_simpSeq _ _ _ ha
      simp only [NoSt, Bool.and_eq_true]
      exact ⟨t_seqAssocRight q1 _ hp.1 rfl, t_seqAssocRight q2 _ hp.2 rfl⟩
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
    (h : NoSt p = true) : NoSt (WordUnreach.removeUnreach p) = true :=
  t_seqAssocRight p _ h rfl

/-- The tail `threeToTwo ∘ removeUnreach ∘ removeMustTerminate`-shaped fragment preserves `NoSt`. -/
theorem t_tail_chain {width : Nat} [NeZero width] (b : Bool) (p : WordLangProgHOL (BitVec width))
    (h : NoSt p = true) :
    NoSt (WordRemove.removeMustTerminate (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b p))) = true :=
  t_removeMustTerminate _ (t_removeUnreach _ (t_threeToTwo b p h))

/-- `NoSt` is weaker than `NoSC` of `PanToWordNoStoreConsts` (alloc allowed). -/
theorem NoSC_imp_NoSt {α : Type} : ∀ p : WordLangProgHOL α,
    PanToWordNoStoreConsts.NoSC p = true → NoSt p = true
  | .seq a b, h | .ite _ _ _ a b, h => by
      simp only [PanToWordNoStoreConsts.NoSC, NoSt, Bool.and_eq_true] at h ⊢
      exact ⟨NoSC_imp_NoSt a h.1, NoSC_imp_NoSt b h.2⟩
  | .mustTerminate a, h | .loop _ a _, h => NoSC_imp_NoSt a h
  | .call none _ _ none, _ => rfl
  | .call none _ _ (some (_, q, _, _)), h => by
      simp only [PanToWordNoStoreConsts.NoSC, NoSt, Bool.true_and] at h ⊢; exact NoSC_imp_NoSt q h
  | .call (some (_, _, r, _, _)) _ _ none, h => by
      simp only [PanToWordNoStoreConsts.NoSC, NoSt, Bool.and_true] at h ⊢; exact NoSC_imp_NoSt r h
  | .call (some (_, _, r, _, _)) _ _ (some (_, q, _, _)), h => by
      simp only [PanToWordNoStoreConsts.NoSC, NoSt, Bool.and_eq_true] at h ⊢
      exact ⟨NoSC_imp_NoSt r h.1, NoSC_imp_NoSt q h.2⟩
  | .storeConsts .., h => by simp [PanToWordNoStoreConsts.NoSC] at h
  | .alloc .., _ | .skip, _ | .move .., _ | .inst .., _ | .assign .., _ | .get .., _ | .set .., _
  | .store .., _ | .raise .., _ | .return .., _ | .break .., _ | .continue .., _ | .tick, _
  | .opCurrHeap .., _ | .locValue .., _ | .install .., _ | .codeBufferWrite .., _
  | .dataBufferWrite .., _ | .ffi .., _ | .shareInst .., _ => rfl

/-- LoopToWord output satisfies `NoSt`. -/
theorem loopToWord_NoSt {width : Nat} [NeZero width] (ctx : Spt Nat) (p : HolLoopProg width)
    (l : Nat × Nat) : NoSt (LoopToWord.compHOL ctx p l).1 = true :=
  NoSC_imp_NoSt _ (PanToWordNoStoreConsts.compHOL_NoSC ctx p l)

/-- `NoSt` is not trivial. -/
theorem NoSt_counterexample {α : Type} :
    NoSt (WordLangProgHOL.loop (α := α) .ln (.storeConsts 0 2 4 6 []) .ln) = false := rfl


end InitECandidate.Solver.WordPassesPreserveNoStoreConsts
