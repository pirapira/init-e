import InitECandidate.Solver.StackToLabAndLabToTargetNoStubCall
import Flapjack.Pancake.CrepToLoop.Proofs.LocValueFree
import Flapjack.Pancake.PanToTarget

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# No `locValue` / return label into section `storeConstsStubLocation`

Completes `StackToLabAndLabToTargetNoStubCall`: besides direct jumps/calls, no LabLang
`locValue` line of a user section loads an address inside section `storeConstsStubLocation = 6`.

Sources of `locValue` lines, all tracked:
* Loop/Word `locValue`: none are produced from Pancake (Flapjack `LocValueFree`), and every
  WordToWord pass keeps the label of an existing one;
* return / handler labels of calls: LoopToWord uses `(name, k)` with the function name `≥ 64`;
  WordToWord and WordToStack copy them (`perfCallPrefix`, `pushHandler`, `flattenHOL` call arm);
* StackAlloc GC call: return label `(n, m)` with `n` the (non-stub) section name;
* `ffi` / `install`: label of the current section (non-stub).
-/

namespace InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordAlloc
open Flapjack.Compiler.Encoders.Asm

/-! ## WordLang predicate -/

def labOk : Option Nat → Bool
  | some l => l != storeConstsStubLocation
  | none => true

@[simp] def retLab {α : Type} :
    Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL α × Nat × Nat) → Option Nat
  | none => none
  | some (_, _, _, l1, _) => some l1

@[simp] def hLab {α : Type} : Option (Nat × WordLangProgHOL α × Nat × Nat) → Option Nat
  | none => none
  | some (_, _, l1, _) => some l1

/-- Call header: target and return/handler label sections avoid the stub. -/
def callHdr (d : Option Nat) (r h : Option Nat) : Bool :=
  d != some storeConstsStubLocation && labOk r && labOk h

/-- `WordNoStubCall` strengthened with label sections (`locValue`, return, handler). -/
def NSL {α : Type} : WordLangProgHOL α → Bool
  | .mustTerminate b => NSL b
  | .seq a b => NSL a && NSL b
  | .ite _ _ _ a b => NSL a && NSL b
  | .loop _ b _ => NSL b
  | .call ret d _ h =>
      callHdr d (retLab ret) (hLab h) &&
      (match ret with | none => true | some (_, _, r, _, _) => NSL r) &&
      (match h with | none => true | some (_, p, _, _) => NSL p)
  | .locValue _ l => l != storeConstsStubLocation
  | _ => true

section
variable {width : Nat} [NeZero width]

/-! ## from WordPassesPreserveNSCoreConsts -/



theorem t_removeMustTerminate {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)), NSL p = true → NSL (WordRemove.removeMustTerminate p) = true
  | .seq a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordRemove.removeMustTerminate]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_removeMustTerminate a h.1, t_removeMustTerminate b h.2⟩
  | .ite c r ri a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordRemove.removeMustTerminate]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_removeMustTerminate a h.1, t_removeMustTerminate b h.2⟩
  | .mustTerminate a, h => by
      rw [WordRemove.removeMustTerminate]; exact t_removeMustTerminate a h
  | .loop x a y, h => by
      rw [WordRemove.removeMustTerminate]; exact t_removeMustTerminate a h
  | .call none d args none, h => by rw [WordRemove.removeMustTerminate.eq_def]; first | exact h | rfl | simpa [NSL, retLab, hLab, retLab, hLab] using h
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_removeMustTerminate q h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_removeMustTerminate r h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordRemove.removeMustTerminate.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, t_removeMustTerminate r h.1.2⟩, t_removeMustTerminate q h.2⟩
  | .skip, h | .move .., h | .inst .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .opCurrHeap .., h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by simp_all [WordRemove.removeMustTerminate, NSL]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_threeToTwoReg {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)), NSL p = true → NSL (WordInst.threeToTwoReg p) = true
  | .seq a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordInst.threeToTwoReg]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_threeToTwoReg a h.1, t_threeToTwoReg b h.2⟩
  | .ite c r ri a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordInst.threeToTwoReg]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_threeToTwoReg a h.1, t_threeToTwoReg b h.2⟩
  | .mustTerminate a, h => by
      rw [WordInst.threeToTwoReg]; exact t_threeToTwoReg a h
  | .loop x a y, h => by
      rw [WordInst.threeToTwoReg]; exact t_threeToTwoReg a h
  | .call none d args none, h => by rw [WordInst.threeToTwoReg.eq_def]; first | exact h | rfl | simpa [NSL, retLab, hLab, retLab, hLab] using h
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_threeToTwoReg q h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_threeToTwoReg r h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.threeToTwoReg.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, t_threeToTwoReg r h.1.2⟩, t_threeToTwoReg q h.2⟩
  | .opCurrHeap .., h => by rw [WordInst.threeToTwoReg]; rfl
  | .inst i, h => by
      rw [WordInst.threeToTwoReg.eq_def]; split <;> simp_all [NSL, retLab, hLab, retLab, hLab]
  | .skip, h | .move .., h | .assign .., h | .get .., h | .set .., h
  | .store .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .return .., h
  | .break .., h | .continue .., h | .tick, h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .ffi .., h
  | .shareInst .., h => by rw [WordInst.threeToTwoReg]; all_goals first | exact h | (intros; contradiction) | simp_all
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_threeToTwo {width : Nat} [NeZero width] (b : Bool) (p : WordLangProgHOL (BitVec width))
    (h : NSL p = true) : NSL (WordInst.threeToTwoRegProg b p) = true := by
  unfold WordInst.threeToTwoRegProg; split
  · exact t_threeToTwoReg p h
  · exact h

theorem t_destSeqMove {width : Nat} [NeZero width] (q : WordLangProgHOL (BitVec width))
    (hq : NSL q = true) (n : Nat) (l : List (Nat × Nat)) (rest : WordLangProgHOL (BitVec width))
    (h : WordUnreach.destSeqMove q = some (n, l, rest)) : NSL rest = true := by
  unfold WordUnreach.destSeqMove at h
  split at h <;> simp_all [NSL, retLab, hLab, retLab, hLab]
  all_goals (obtain ⟨-, -, rfl⟩ := h; simp_all [NSL, retLab, hLab, retLab, hLab])

theorem t_simpSeq {width : Nat} [NeZero width] (p q : WordLangProgHOL (BitVec width))
    (hp : NSL p = true) (hq : NSL q = true) : NSL (WordUnreach.simpSeq p q) = true := by
  unfold WordUnreach.simpSeq
  split
  · exact hp
  · split <;> (try exact hp) <;> (try exact hq) <;> (try simp_all [NSL, retLab, hLab, retLab, hLab])
    all_goals (split <;> (try simp_all [NSL, retLab, hLab, retLab, hLab]) <;> (try split) <;> (try simp_all [NSL, retLab, hLab, retLab, hLab]))
    all_goals (rename_i heq _; exact t_destSeqMove _ hq _ _ _ heq)

theorem t_seqAssocRight {width : Nat} [NeZero width] :
    ∀ (p acc : WordLangProgHOL (BitVec width)), NSL p = true → NSL acc = true →
      NSL (WordUnreach.seqAssocRight p acc) = true
  | .skip, acc, _, ha => by rw [WordUnreach.seqAssocRight]; exact ha
  | .seq a b, acc, hp, ha => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at hp
      rw [WordUnreach.seqAssocRight]
      exact t_seqAssocRight a _ hp.1 (t_seqAssocRight b acc hp.2 ha)
  | .ite v n r a b, acc, hp, ha => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at hp
      rw [WordUnreach.seqAssocRight]
      apply t_simpSeq _ _ _ ha
      simp only [NSL, retLab, hLab, Bool.and_eq_true]
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
      simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at hp
      apply t_simpSeq _ _ _ ha
      simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true]; exact ⟨hp.1, t_seqAssocRight q1 _ hp.2 rfl⟩
  | .call (some (x1, x2, q1, x3, x4)) d args (some (y1, q2, y2, y3)), acc, hp, ha => by
      rw [WordUnreach.seqAssocRight]
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at hp
      apply t_simpSeq _ _ _ ha
      simp only [NSL, retLab, hLab, Bool.and_eq_true]
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
    (h : NSL p = true) : NSL (WordUnreach.removeUnreach p) = true :=
  t_seqAssocRight p _ h rfl

/-- The tail `threeToTwo ∘ removeUnreach ∘ removeMustTerminate`-shaped fragment preserves `NSL`. -/
theorem t_tail_chain {width : Nat} [NeZero width] (b : Bool) (p : WordLangProgHOL (BitVec width))
    (h : NSL p = true) :
    NSL (WordRemove.removeMustTerminate (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b p))) = true :=
  t_removeMustTerminate _ (t_removeUnreach _ (t_threeToTwo b p h))

/-! ## from WordMidPassesPreserveNSCoreConsts -/


theorem t_instSelectExp {width : Nat} [NeZero width] (c : AsmConfigExact width) :
    ∀ (n : Nat) (tar temp : Nat) (e : WordLangExpHOL (BitVec width)), sizeOf e = n →
      NSL (WordInst.instSelectExp c tar temp e) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro tar temp e hn
    rw [WordInst.instSelectExp.eq_def]
    dsimp only
    (repeat' (first | split_ifs | split)) <;> simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.and_true, Bool.true_and, and_true, true_and] <;>
      (repeat' constructor) <;>
      (try (exact ih _ (by subst hn; simp only [WordLangExpHOL.load.sizeOf_spec, WordLangExpHOL.op.sizeOf_spec, WordLangExpHOL.shift.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega) _ _ _ rfl))

theorem t_ise {width : Nat} [NeZero width] (c : AsmConfigExact width) (tar temp : Nat)
    (e : WordLangExpHOL (BitVec width)) : NSL (WordInst.instSelectExp c tar temp e) = true :=
  t_instSelectExp c _ tar temp e rfl

theorem t_copyPropInst {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (cs : WordCopy.CopyState) : NSL (WordCopy.copyPropInst i cs).1 = true := by
  unfold WordCopy.copyPropInst; (repeat' split) <;> simp_all [NSL, retLab, hLab, retLab, hLab]

theorem t_instSelect {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat) :
    ∀ (p : WordLangProgHOL (BitVec width)), NSL p = true → NSL (WordInst.instSelect c temp p) = true
  | .seq a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordInst.instSelect.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_instSelect c temp a h.1, t_instSelect c temp b h.2⟩
  | .ite cm r ri a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordInst.instSelect.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_instSelect c temp a h.1, t_instSelect c temp b h.2⟩
  | .mustTerminate a, h => by rw [WordInst.instSelect.eq_def]; exact t_instSelect c temp a h
  | .loop x a y, h => by rw [WordInst.instSelect.eq_def]; exact t_instSelect c temp a h
  | .call none d args none, h => by rw [WordInst.instSelect.eq_def]; first | exact h | rfl | simpa [NSL, retLab, hLab, retLab, hLab] using h
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.instSelect.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_instSelect c temp q h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordInst.instSelect.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_instSelect c temp r h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordInst.instSelect.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, t_instSelect c temp r h.1.2⟩, t_instSelect c temp q h.2⟩
  | .assign .., h | .set .., h | .store .., h | .shareInst .., h => by
      rw [WordInst.instSelect.eq_def]; dsimp only
      (repeat' (first | split_ifs | split)) <;> simp_all [NSL, retLab, hLab, t_ise]
  | .skip, h | .move .., h | .inst .., h | .get .., h | .alloc .., h | .storeConsts .., h
  | .raise .., h | .return .., h | .break .., h | .continue .., h | .tick, h
  | .opCurrHeap .., h | .locValue .., h | .install .., h | .codeBufferWrite .., h
  | .dataBufferWrite .., h | .ffi .., h => by
      rw [WordInst.instSelect.eq_def] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_removeDead {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
      (lt : List (NumSet × NumSet)), NSL p = true → NSL (WordAlloc.removeDead p live nlive lt).1 = true
  | .seq a b, live, nlive, lt, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordAlloc.removeDead.eq_def]; dsimp only
      have h2 := t_removeDead b live nlive lt h.2
      have h1 := t_removeDead a (WordAlloc.removeDead b live nlive lt).2.1 (WordAlloc.removeDead b live nlive lt).2.2 lt h.1
      split <;> simp_all [NSL, retLab, hLab, retLab, hLab]
  | .ite cm r ri a b, live, nlive, lt, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordAlloc.removeDead.eq_def]; dsimp only
      have h1 := t_removeDead a live nlive lt h.1
      have h2 := t_removeDead b live nlive lt h.2
      (repeat' split) <;> simp_all [NSL, retLab, hLab, retLab, hLab]
  | .mustTerminate a, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; exact t_removeDead a live nlive lt h
  | .loop x a y, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; exact t_removeDead a _ _ _ h
  | .call none d args hd, live, nlive, lt, h => by rw [WordAlloc.removeDead.eq_def]; exact h
  | .call (some (r1, r2, r, r3, r4)) d args none, live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_removeDead r _ _ _ h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), live, nlive, lt, h => by
      rw [WordAlloc.removeDead.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, t_removeDead r _ _ _ h.1.2⟩, t_removeDead q _ _ _ h.2⟩
  | .skip, _, _, _, h | .move .., _, _, _, h | .inst .., _, _, _, h | .get .., _, _, _, h
  | .set .., _, _, _, h | .assign .., _, _, _, h | .store .., _, _, _, h | .alloc .., _, _, _, h
  | .storeConsts .., _, _, _, h | .raise .., _, _, _, h | .return .., _, _, _, h
  | .break .., _, _, _, h | .continue .., _, _, _, h | .tick, _, _, _, h
  | .opCurrHeap .., _, _, _, h | .locValue .., _, _, _, h | .install .., _, _, _, h
  | .codeBufferWrite .., _, _, _, h | .dataBufferWrite .., _, _, _, h | .ffi .., _, _, _, h
  | .shareInst .., _, _, _, h => by
      rw [WordAlloc.removeDead.eq_def] <;> (try dsimp only) <;> (repeat' (first | split_ifs | split)) <;>
        first | exact h | rfl | (intros; simp_all) | simp_all [NSL, retLab, hLab, retLab, hLab]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_removeDeadProg {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : NSL p = true) : NSL (WordAlloc.removeDeadProg p) = true :=
  t_removeDead p _ _ _ h

theorem t_copyPropProg {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (cs : WordCopy.CopyState),
      NSL p = true → NSL (WordCopy.copyPropProg p cs).1 = true
  | .seq a b, cs, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordCopy.copyPropProg.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_copyPropProg a cs h.1, t_copyPropProg b _ h.2⟩
  | .ite cm r ri a b, cs, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordCopy.copyPropProg.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
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
        first | exact h | rfl | simp_all [NSL, retLab, hLab, retLab, hLab]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_copyProp {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width))
    (h : NSL p = true) : NSL (WordCopy.copyProp p) = true :=
  t_copyPropProg p _ h

/-- Proven segment of `fullCompileSingle` (SSA, CSE, WordSimp, wordAlloc still open):
instSelect → removeDeadProg → copyProp → threeToTwo → removeUnreach → removeMustTerminate. -/
theorem t_mid_tail_chain {width : Nat} [NeZero width] (c : AsmConfigExact width) (temp : Nat)
    (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : NSL p = true) :
    NSL (WordRemove.removeMustTerminate (WordUnreach.removeUnreach
      (WordInst.threeToTwoRegProg b (WordCopy.copyProp (WordAlloc.removeDeadProg
        (WordInst.instSelect c temp p)))))) = true :=
  t_tail_chain b _ (t_copyProp _ (t_removeDeadProg _ (t_instSelect c temp p h)))


/-! ## from WordSsaCsePreserveNSCoreConsts -/


theorem t_listNextVarRenameMove {width : Nat} [NeZero width] (ssa : Spt Nat) (n : Nat)
    (ls : List Nat) : NSL (listNextVarRenameMove (width := width) ssa n ls).1 = true := by
  unfold listNextVarRenameMove; rfl

theorem t_ssaReconcile {width : Nat} [NeZero width] {β : Type} (a b : Spt Nat) (ns : Spt β) :
    NSL (ssaReconcile (width := width) a b ns) = true := by
  unfold ssaReconcile; dsimp only; split <;> rfl

theorem t_fakeMoveFold {width : Nat} [NeZero width] (l : List Nat) :
    NSL ((l.map fun r => fakeMove (width := width) r).foldr .seq .skip) = true := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, List.foldr_cons, NSL, Bool.and_eq_true]; exact ⟨rfl, ih⟩

theorem t_loopSetup {width : Nat} [NeZero width] (names exitNames : Spt Unit) (ssa : Spt Nat)
    (na : Nat) : NSL (loopSetup (width := width) names exitNames ssa na).1 = true := by
  unfold loopSetup
  simp only [NSL, retLab, hLab, Bool.and_eq_true]
  exact ⟨t_fakeMoveFold _, t_listNextVarRenameMove _ _ _⟩

theorem t_fakeMoves {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit)) :
    ∀ (l : List Nat) (sl sr : Spt Nat) (na : Nat),
      NSL (fakeMoves (width := width) prio l sl sr na).1 = true ∧
      NSL (fakeMoves (width := width) prio l sl sr na).2.1 = true
  | [], _, _, _ => ⟨rfl, rfl⟩
  | x :: xs, sl, sr, na => by
      have ih := t_fakeMoves (width := width) prio xs sl sr na
      rw [fakeMoves]; dsimp only
      split <;> simp_all [NSL, retLab, hLab, fakeMove]

theorem t_fixInconsistencies {width : Nat} [NeZero width] (prio : Option (Unit ⊕ Unit))
    (sl sr : Spt Nat) (na : Nat) :
    NSL (fixInconsistencies (width := width) prio sl sr na).1 = true ∧
    NSL (fixInconsistencies (width := width) prio sl sr na).2.1 = true := by
  unfold fixInconsistencies; dsimp only
  have := t_fakeMoves (width := width) prio
  simp_all [NSL, retLab, hLab, retLab, hLab]

theorem t_ssaCcTransInst {width : Nat} [NeZero width] (i : WordLangInst (BitVec width))
    (ssa : Spt Nat) (na : Nat) : NSL (ssaCcTransInst i ssa na).1 = true := by
  unfold ssaCcTransInst; (repeat' split) <;> simp_all [NSL, retLab, hLab, retLab, hLab]

theorem t_ssaCcTrans {width : Nat} [NeZero width] :
    ∀ (p : WordLangProgHOL (BitVec width)) (ssa : Spt Nat) (na : Nat)
      (lt : List (Spt Nat × Spt Unit × Spt Unit)),
      NSL p = true → NSL (ssaCcTrans p ssa na lt).1 = true
  | .seq a b, ssa, na, lt, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_ssaCcTrans a _ _ _ h.1, t_ssaCcTrans b _ _ _ h.2⟩
  | .ite cm r ri a b, ssa, na, lt, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      have hf := t_fixInconsistencies (width := width)
      exact ⟨⟨t_ssaCcTrans a _ _ _ h.1, (hf _ _ _ _).1⟩, ⟨t_ssaCcTrans b _ _ _ h.2, (hf _ _ _ _).2⟩⟩
  | .mustTerminate a, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; exact t_ssaCcTrans a _ _ _ h
  | .loop names body ex, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; dsimp only
      simp only [NSL, retLab, hLab, Bool.and_eq_true]
      refine ⟨t_loopSetup _ _ _ _, ?_⟩
      split
      · exact t_ssaCcTrans body _ _ _ h
      · simp only [NSL, retLab, hLab, Bool.and_eq_true]; exact ⟨t_ssaCcTrans body _ _ _ h, t_ssaReconcile _ _ _⟩
  | .call none d args hd, ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; dsimp only
      rcases hd with _ | ⟨h1, q, h2, h3⟩ <;> simp_all [NSL, retLab, hLab, retLab, hLab]
  | .call (some (r1, r2, r, r3, r4)) d args none, ssa, na, lt, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h
      rw [ssaCcTrans.eq_def]; dsimp only
      simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.and_true, t_listNextVarRenameMove, true_and]
      exact ⟨h.1, t_ssaCcTrans r _ _ _ h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), ssa, na, lt, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [ssaCcTrans.eq_def]; dsimp only
      have hf := t_fixInconsistencies (width := width)
      simp only [NSL, retLab, hLab, Bool.and_eq_true, t_listNextVarRenameMove, true_and, and_true]
      exact ⟨⟨h.1.1, t_ssaCcTrans r _ _ _ h.1.2, (hf _ _ _ _).1⟩, ⟨t_ssaCcTrans q _ _ _ h.2, (hf _ _ _ _).2⟩⟩
  | .inst i, ssa, na, lt, h => by rw [ssaCcTrans.eq_def]; exact t_ssaCcTransInst i ssa na
  | .storeConsts .., ssa, na, lt, h => by
      rw [ssaCcTrans.eq_def]; dsimp only; simp [NSL, retLab, hLab, retLab, hLab]
  | .skip, _, _, _, h | .move .., _, _, _, h | .get .., _, _, _, h
  | .set .., _, _, _, h | .assign .., _, _, _, h | .store .., _, _, _, h | .alloc .., _, _, _, h
  | .raise .., _, _, _, h | .return .., _, _, _, h
  | .break .., _, _, _, h | .continue .., _, _, _, h | .tick, _, _, _, h
  | .opCurrHeap .., _, _, _, h | .locValue .., _, _, _, h | .install .., _, _, _, h
  | .codeBufferWrite .., _, _, _, h | .dataBufferWrite .., _, _, _, h | .ffi .., _, _, _, h
  | .shareInst .., _, _, _, h => by
      rw [ssaCcTrans.eq_def] <;> (try dsimp only) <;> (repeat' (first | split_ifs | split)) <;>
        simp_all [NSL, retLab, hLab, t_listNextVarRenameMove, t_ssaReconcile]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_fullSsaCcTrans {width : Nat} [NeZero width] (n : Nat)
    (p : WordLangProgHOL (BitVec width)) (h : NSL p = true) :
    NSL (fullSsaCcTrans n p) = true := by
  unfold fullSsaCcTrans setupSSA; dsimp only
  simp only [NSL, retLab, hLab, Bool.true_and]; exact t_ssaCcTrans p _ _ _ h

theorem t_addToDataAux {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (key : List Nat) (o : WordLangProgHOL (BitVec width)) (h : NSL o = true) :
    NSL (WordCse.addToDataAux data d key o).2 = true := by
  unfold WordCse.addToDataAux; (repeat' (first | split_ifs | split)) <;> simp_all [NSL, retLab, hLab, retLab, hLab]

theorem t_addToLoadAux {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (key : List Nat) (o : WordLangProgHOL (BitVec width)) (h : NSL o = true) :
    NSL (WordCse.addToLoadAux data d key o).2 = true := by
  unfold WordCse.addToLoadAux; (repeat' (first | split_ifs | split)) <;> simp_all [NSL, retLab, hLab, retLab, hLab]

theorem t_addToDataConst {width : Nat} [NeZero width] (data : WordCse.Knowledge) (d : Nat)
    (w : BitVec width) : NSL (WordCse.addToDataConst data d w).2 = true := by
  unfold WordCse.addToDataConst; dsimp only; split <;> rfl

theorem t_wordCseInst {width : Nat} [NeZero width] (data : WordCse.Knowledge)
    (i : HolInst width) : NSL (WordCse.wordCseInst data i).2 = true := by
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
      NSL p = true → NSL (WordCse.wordCse data p).2 = true
  | data, .seq a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordCse.wordCse.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_wordCse _ a h.1, t_wordCse _ b h.2⟩
  | data, .ite cm r ri a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordCse.wordCse.eq_def]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
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
      rw [WordCse.wordCse.eq_def]; exact t_addToDataAux _ _ _ _ h
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
    (h : NSL p = true) : NSL (WordCse.wordCommonSubexpElim p) = true := by
  unfold WordCse.wordCommonSubexpElim; exact t_wordCse _ p h

/-- Exact post-`instSelect` segment of `compileSingle` (before `wordAlloc`), then
`removeMustTerminate`: ssa → removeDead → cse → copyProp → threeToTwo → removeUnreach
→ removeDead. Plus the compiled-order mid/tail chain. -/
theorem t_ssa_cse_mid_tail_chain {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (temp argc : Nat) (b : Bool) (p : WordLangProgHOL (BitVec width)) (h : NSL p = true) :
    NSL (WordAlloc.removeDeadProg (WordUnreach.removeUnreach (WordInst.threeToTwoRegProg b
      (WordCopy.copyProp (WordCse.wordCommonSubexpElim (WordAlloc.removeDeadProg
        (fullSsaCcTrans argc (WordInst.instSelect c temp p)))))))) = true :=
  t_removeDeadProg _ (t_removeUnreach _ (t_threeToTwo b _ (t_copyProp _
    (t_wordCommonSubexpElim _ (t_removeDeadProg _ (t_fullSsaCcTrans argc _
      (t_instSelect c temp p h)))))))

def storeConstsAllowance {α : Type} (p : WordLangProgHOL α) : Nat := if NSL p then 0 else 1

/-! ## from WordSimpPreservesNSCoreConsts -/



theorem t_smartSeq (a b : WordLangProgHOL (BitVec width)) (ha : NSL a = true)
    (hb : NSL b = true) : NSL (WordSimp.smartSeqHOL a b) = true := by
  unfold WordSimp.smartSeqHOL; split <;> simp_all [NSL, retLab, hLab, retLab, hLab]

theorem t_dropConsts (cs : Spt (BitVec width)) :
    ∀ l : List Nat, NSL (WordSimp.dropConsts cs l) = true
  | [] => rfl
  | n :: ns => by
      rw [WordSimp.dropConsts]; split
      · exact t_dropConsts cs ns
      · exact t_smartSeq _ _ (t_dropConsts cs ns) rfl

theorem t_seqAssoc :
    ∀ (p1 q : WordLangProgHOL (BitVec width)), NSL p1 = true → NSL q = true →
      NSL (WordSimp.seqAssoc p1 q) = true
  | p1, .skip, h1, _ => by rw [WordSimp.seqAssoc]; exact h1
  | p1, .seq a b, h1, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; exact t_seqAssoc _ b (t_seqAssoc p1 a h1 h.1) h.2
  | p1, .ite v n r a b, h1, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_seqAssoc _ a rfl h.1, t_seqAssoc _ b rfl h.2⟩
  | p1, .mustTerminate a, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 (t_seqAssoc _ a rfl h)
  | p1, .loop x a y, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 (t_seqAssoc _ a rfl h)
  | p1, .call none d args none, h1, h => by
      rw [WordSimp.seqAssoc]; exact t_smartSeq _ _ h1 h
  | p1, .call none d args (some (y1, q, y2, y3)), h1, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true]; exact ⟨h.1, t_seqAssoc _ q rfl h.2⟩
  | p1, .call (some (x1, x2, r, x3, x4)) d args none, h1, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true]; exact ⟨h.1, t_seqAssoc _ r rfl h.2⟩
  | p1, .call (some (x1, x2, r, x3, x4)) d args (some (y1, q, y2, y3)), h1, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordSimp.seqAssoc]; apply t_smartSeq _ _ h1
      simp only [NSL, retLab, hLab, Bool.and_eq_true]
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
      NSL p = true → NSL (WordSimp.constFpLoop p cs).1 = true
  | .seq a b, cs, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordSimp.constFpLoop]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_constFpLoop a _ h.1, t_constFpLoop b _ h.2⟩
  | .ite c l r a b, cs, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordSimp.constFpLoop]; dsimp only
      split
      · split
        · exact t_constFpLoop a _ h.1
        · exact t_constFpLoop b _ h.2
      · simp only [NSL, retLab, hLab, Bool.and_eq_true]
        exact ⟨t_constFpLoop a _ h.1, t_constFpLoop b _ h.2⟩
  | .mustTerminate a, cs, h => by rw [WordSimp.constFpLoop]; exact t_constFpLoop a _ h
  | .loop x a y, cs, h => by rw [WordSimp.constFpLoop]; exact t_constFpLoop a _ h
  | .call none d args hd, cs, h => by
      rw [WordSimp.constFpLoop]; exact t_smartSeq _ _ (t_dropConsts _ _) h
  | .call (some (n, nm, r, l1, l2)) d args none, cs, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h
      rw [WordSimp.constFpLoop]; dsimp only
      apply t_smartSeq _ _ (t_dropConsts _ _)
      simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true]; exact ⟨h.1, t_constFpLoop r _ h.2⟩
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

theorem t_constFp (p : WordLangProgHOL (BitVec width)) (h : NSL p = true) :
    NSL (WordSimp.constFp p) = true := t_constFpLoop p _ h

theorem t_destIf (p : WordLangProgHOL (BitVec width)) (h : NSL p = true)
    (c : Cmp) (l : Nat) (r : WordRegImm (BitVec width)) (b1 b2 : WordLangProgHOL (BitVec width))
    (e : WordSimp.destIf p = some (c, l, r, b1, b2)) : NSL b1 = true ∧ NSL b2 = true := by
  unfold WordSimp.destIf at e; split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨-, -, -, rfl, rfl⟩ := e
    simpa [NSL, retLab, hLab, retLab, hLab] using h
  · simp at e

theorem t_tryIfHoist2 : ∀ (n : Nat) (p1 interm dummy p2 r : WordLangProgHOL (BitVec width)),
    NSL p1 = true → NSL interm = true → NSL p2 = true →
      WordSimp.tryIfHoist2 n p1 interm dummy p2 = some r → NSL r = true
  | 0, _, _, _, _, _, _, _, _, e => by simp [WordSimp.tryIfHoist2] at e
  | n + 1, p1, interm, dummy, p2, r, h1, hi, h2, e => by
      unfold WordSimp.tryIfHoist2 at e
      split at e
      · rename_i c l rr b1 b2
        simp only [NSL, retLab, hLab, Bool.and_eq_true] at h1
        dsimp only at e
        split at e; · simp at e
        split at e; · simp at e
        simp only [Option.some.injEq] at e; subst e
        apply t_constFp; simp_all [NSL, retLab, hLab, retLab, hLab]
      · rename_i p3 p4
        simp only [NSL, retLab, hLab, Bool.and_eq_true] at h1
        split at e
        · rename_i c l rr b1 b2 hd
          have hb := t_destIf p4 h1.2 _ _ _ _ _ hd
          dsimp only at e
          split at e; · simp at e
          split at e; · simp at e
          simp only [Option.some.injEq] at e; subst e
          simp only [NSL, retLab, hLab, Bool.and_eq_true]
          refine ⟨h1.1, t_constFp _ ?_⟩
          simp_all [NSL, retLab, hLab, retLab, hLab]
        · split at e
          · exact t_tryIfHoist2 n p3 _ dummy p2 r h1.1 (by simp_all [NSL, retLab, hLab, retLab, hLab]) h2 e
          · simp at e
      · simp at e

theorem t_tryIfHoist1 (p1 p2 r : WordLangProgHOL (BitVec width)) (h1 : NSL p1 = true)
    (h2 : NSL p2 = true) (e : WordSimp.tryIfHoist1 p1 p2 = some r) : NSL r = true := by
  unfold WordSimp.tryIfHoist1 at e; split at e
  · simp at e
  · exact t_tryIfHoist2 _ _ _ _ _ _ h1 rfl h2 e

theorem t_simpDuplicateIf :
    ∀ (p : WordLangProgHOL (BitVec width)), NSL p = true → NSL (WordSimp.simpDuplicateIf p) = true
  | .seq a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      have ha := t_simpDuplicateIf a h.1
      have hb := t_simpDuplicateIf b h.2
      rw [WordSimp.simpDuplicateIf]
      split
      · simp only [NSL, retLab, hLab, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · rename_i p3 e
        exact t_seqAssoc _ _ rfl (t_tryIfHoist1 _ _ _ ha hb e)
  | .ite c l r a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      rw [WordSimp.simpDuplicateIf]; simp only [NSL, retLab, hLab, Bool.and_eq_true]
      exact ⟨t_simpDuplicateIf a h.1, t_simpDuplicateIf b h.2⟩
  | .mustTerminate a, h => by rw [WordSimp.simpDuplicateIf]; exact t_simpDuplicateIf a h
  | .loop x a y, h => by rw [WordSimp.simpDuplicateIf]; exact t_simpDuplicateIf a h
  | .call none d args none, h => by rw [WordSimp.simpDuplicateIf]; first | exact h | rfl | simpa [NSL, retLab, hLab, retLab, hLab] using h
  | .call none d args (some (h1, q, h2, h3)), h => by
      rw [WordSimp.simpDuplicateIf]; simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_simpDuplicateIf q h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args none, h => by
      rw [WordSimp.simpDuplicateIf]; simp only [NSL, retLab, hLab, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢; exact ⟨h.1, t_simpDuplicateIf r h.2⟩
  | .call (some (r1, r2, r, r3, r4)) d args (some (h1, q, h2, h3)), h => by
      rw [WordSimp.simpDuplicateIf]; simp only [NSL, retLab, hLab, Bool.and_eq_true] at h ⊢
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
    ∀ (p : WordLangProgHOL (BitVec width)), NSL p = true → NSL (WordSimp.pushOutIfAux p).1 = true
  | .seq a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      have ha := t_pushOutIfAux a h.1
      have hb := t_pushOutIfAux b h.2
      rw [WordSimp.pushOutIfAux]
      split
      · rename_i c1 e; rw [e] at ha; simp_all [NSL, retLab, hLab, retLab, hLab]
      · rename_i c1 e; rw [e] at ha; split
        rename_i c2 bb e2; rw [e2] at hb; simp_all [NSL, retLab, hLab, retLab, hLab]
  | .ite c l r a b, h => by
      simp only [NSL, retLab, hLab, Bool.and_eq_true] at h
      have ha := t_pushOutIfAux a h.1
      have hb := t_pushOutIfAux b h.2
      rw [WordSimp.pushOutIfAux]
      split <;> (rename_i e1 e2; rw [e1] at ha; rw [e2] at hb; simp_all [NSL, retLab, hLab, retLab, hLab])
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

theorem t_pushOutIf (p : WordLangProgHOL (BitVec width)) (h : NSL p = true) :
    NSL (WordSimp.pushOutIf p) = true := t_pushOutIfAux p h

theorem t_compileExp (p : WordLangProgHOL (BitVec width)) (h : NSL p = true) :
    NSL (WordSimp.compileExp p) = true := by
  unfold WordSimp.compileExp
  exact t_pushOutIf _ (t_simpDuplicateIf _ (t_constFp _ (t_seqAssoc _ _ rfl h)))


/-! ## from WordToWordFullCompileNSCoreConsts -/



/-- Colouring renames registers; it never adds or removes a `storeConsts`. -/
theorem applyColour_NSC_iff (f : Nat → Nat) :
    ∀ p : WordLangProgHOL (BitVec width), NSL (Flapjack.WordAlloc.applyColour f p) = NSL p
  | .seq a b => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSL, retLab, hLab, retLab, hLab]
      rw [applyColour_NSC_iff f a, applyColour_NSC_iff f b]
  | .ite c r ri a b => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSL, retLab, hLab, retLab, hLab]
      rw [applyColour_NSC_iff f a, applyColour_NSC_iff f b]
  | .mustTerminate a => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSL, retLab, hLab, retLab, hLab]; exact applyColour_NSC_iff f a
  | .loop x a y => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSL, retLab, hLab, retLab, hLab]; exact applyColour_NSC_iff f a
  | .call none d args none => by rw [Flapjack.WordAlloc.applyColour]; first | exact h | rfl | simpa [NSL, retLab, hLab, retLab, hLab] using h
  | .call none d args (some (v, q, l1, l2)) => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSL, retLab, hLab, retLab, hLab]; rw [applyColour_NSC_iff f q]
  | .call (some (vs, cs, r, l1, l2)) d args none => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSL, retLab, hLab, retLab, hLab]; rw [applyColour_NSC_iff f r]
  | .call (some (vs, cs, r, l1, l2)) d args (some (v, q, m1, m2)) => by
      rw [Flapjack.WordAlloc.applyColour]; simp only [NSL, retLab, hLab, retLab, hLab]
      rw [applyColour_NSC_iff f r, applyColour_NSC_iff f q]
  | .skip | .move .. | .inst .. | .assign .. | .get .. | .set .. | .store .. | .alloc ..
  | .storeConsts .. | .raise .. | .return .. | .break .. | .continue .. | .tick
  | .opCurrHeap .. | .locValue .. | .install .. | .codeBufferWrite .. | .dataBufferWrite ..
  | .ffi .. | .shareInst .. => by
      rw [Flapjack.WordAlloc.applyColour] <;> first | rfl | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem t_applyColour (f : Nat → Nat) (p : WordLangProgHOL (BitVec width)) (h : NSL p = true) :
    NSL (Flapjack.WordAlloc.applyColour f p) = true := by
  rw [applyColour_NSC_iff]; exact h

theorem t_oracleColourOk (k : Nat) (co : Option (Spt Nat)) (tree : RegAlloc.ClashTree)
    (p q : WordLangProgHOL (BitVec width)) (forced : List (Nat × Nat)) (h : NSL p = true)
    (e : Flapjack.WordAlloc.oracleColourOk k co tree p forced = some q) : NSL q = true := by
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
    (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat)) (h : NSL p = true) :
    NSL (Flapjack.WordAlloc.wordAlloc fc c alg k p co) = true := by
  unfold Flapjack.WordAlloc.wordAlloc; dsimp only
  split
  · split
    · exact t_applyColour _ _ h
    · exact h
  · rename_i q e; exact t_oracleColourOk _ _ _ _ _ _ h e

/-- Master: every function body accepted by `fullCompileSingle` with `NSL` input
yields `NSL` output (all 11 calls of the HOL pipeline). -/
theorem t_fullCompileSingle (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (nm ac : Nat) (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat))
    (h : NSL p = true) :
    NSL (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.2 = true := by
  unfold WordToWord.fullCompileSingle WordToWord.compileSingle; dsimp only
  apply t_removeMustTerminate
  apply t_wordAlloc
  exact t_ssa_cse_mid_tail_chain c _ ac b _ (t_compileExp _ h)

theorem fullCompileSingle_preserves_meta (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (nm ac : Nat) (p : WordLangProgHOL (BitVec width)) (co : Option (Spt Nat)) :
    (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).1 = nm ∧
    (WordToWord.fullCompileSingle b rc alg c ((nm, ac, p), co)).2.1 = ac := by
  unfold WordToWord.fullCompileSingle WordToWord.compileSingle; exact ⟨rfl, rfl⟩


/-- Whole-program lift over any list of `NSL` functions. -/
theorem t_fullCompile_list (b : Bool) (rc alg : Nat) (c : AsmConfigExact width)
    (ps : List ((Nat × Nat × WordLangProgHOL (BitVec width)) × Option (Spt Nat)))
    (h : ∀ x ∈ ps, NSL x.1.2.2 = true) :
    ∀ y ∈ ps.map (WordToWord.fullCompileSingle b rc alg c), NSL y.2.2 = true := by
  intro y hy
  obtain ⟨⟨⟨nm, ac, p⟩, co⟩, hx, rfl⟩ := List.mem_map.1 hy
  exact t_fullCompileSingle b rc alg c nm ac p co (h _ hx)


end

/-! ## Pancake → LoopToWord: `NSL`, no hypothesis -/

section front
open InitECandidate.Solver.PanToWordNoStubCall

theorem labOk_of_ne {n : Nat} (h : n ≠ storeConstsStubLocation) : labOk (some n) = true := by
  simp [labOk, h]

/-- LoopToWord only bumps the second component of the label counter. -/
theorem compHOL_fst {width : Nat} [NeZero width] (ctx : Spt Nat) :
    ∀ (p : HolLoopProg width) (l : Nat × Nat), (LoopToWord.compHOL ctx p l).2.1 = l.1
  | .seq a b, l => by
      have ha := compHOL_fst ctx a l
      rcases ha' : LoopToWord.compHOL ctx a l with ⟨w1, l1⟩
      have hb := compHOL_fst ctx b l1
      rcases hb' : LoopToWord.compHOL ctx b l1 with ⟨w2, l2⟩
      rw [ha'] at ha; rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp only [ha', hb']; simp_all
  | .ite o c r a b lv, l => by
      have ha := compHOL_fst ctx a l
      rcases ha' : LoopToWord.compHOL ctx a l with ⟨w1, l1⟩
      have hb := compHOL_fst ctx b l1
      rcases hb' : LoopToWord.compHOL ctx b l1 with ⟨w2, l2⟩
      rw [ha'] at ha; rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp only [ha', hb']; simp_all
  | .loop li b lo, l => by
      have hb := compHOL_fst ctx b l
      rcases hb' : LoopToWord.compHOL ctx b l with ⟨w, l1⟩
      rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp only [hb']; simp_all
  | .mark b, l => by
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); exact compHOL_fst ctx b l
  | .call none t args hd, l => by
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only)
  | .call (some (vs, live)) t args none, l => by
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only)
  | .call (some (vs, live)) t args (some (n, p1, p2, lo)), l => by
      have h1 := compHOL_fst ctx p1 (l.1, l.2 + 1)
      rcases h1' : LoopToWord.compHOL ctx p1 (l.1, l.2 + 1) with ⟨w1, l1⟩
      have h2 := compHOL_fst ctx p2 l1
      rcases h2' : LoopToWord.compHOL ctx p2 l1 with ⟨w2, l2⟩
      rw [h1'] at h1; rw [h2'] at h2
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp only [h1', h2']; simp_all
  | .skip, _ | .assign .., _ | .store .., _ | .setGlobal .., _ | .load32 .., _
  | .loadByte .., _ | .store32 .., _ | .storeByte .., _ | .break .., _ | .continue .., _
  | .raise .., _ | .return .., _ | .tick, _ | .fail, _ | .locValue .., _ | .ffi .., _
  | .shMem .., _ => by rw [LoopToWord.compHOL]
  | .primitive ds .addCarry as, _ => by
      rw [LoopToWord.compHOL.eq_def]; dsimp only; split <;> rfl
  | .arith (.longMul ..), _ | .arith (.longDiv ..), _ | .arith (.div ..), _ => by
      rw [LoopToWord.compHOL]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem compHOL_nsl {width : Nat} [NeZero width] (ctx : Spt Nat) :
    ∀ (p : HolLoopProg width) (l : Nat × Nat), l.1 ≠ storeConstsStubLocation →
      loopTgtOk p → holLoopProgLocValueFree p → NSL (LoopToWord.compHOL ctx p l).1 = true
  | .seq a b, l, hl, h, hf => by
      simp only [loopTgtOk] at h; simp only [holLoopProgLocValueFree] at hf
      have ha := compHOL_nsl ctx a l hl h.1 hf.1
      have hfa := compHOL_fst ctx a l
      rcases ha' : LoopToWord.compHOL ctx a l with ⟨w1, l1⟩
      rw [ha'] at ha hfa
      have hb := compHOL_nsl ctx b l1 (by simp only at hfa; rw [hfa]; exact hl) h.2 hf.2
      rcases hb' : LoopToWord.compHOL ctx b l1 with ⟨w2, l2⟩
      rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp only [ha', hb', NSL, Bool.and_eq_true]
      exact ⟨ha, hb⟩
  | .ite o c r a b lv, l, hl, h, hf => by
      simp only [loopTgtOk] at h; simp only [holLoopProgLocValueFree] at hf
      have ha := compHOL_nsl ctx a l hl h.1 hf.1
      have hfa := compHOL_fst ctx a l
      rcases ha' : LoopToWord.compHOL ctx a l with ⟨w1, l1⟩
      rw [ha'] at ha hfa
      have hb := compHOL_nsl ctx b l1 (by simp only at hfa; rw [hfa]; exact hl) h.2 hf.2
      rcases hb' : LoopToWord.compHOL ctx b l1 with ⟨w2, l2⟩
      rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [ha', hb', NSL, ha, hb]
  | .loop li b lo, l, hl, h, hf => by
      simp only [loopTgtOk] at h; simp only [holLoopProgLocValueFree] at hf
      have hb := compHOL_nsl ctx b l hl h hf
      rcases hb' : LoopToWord.compHOL ctx b l with ⟨w, l1⟩
      rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [hb', NSL, hb]
  | .mark b, l, hl, h, hf => by
      simp only [loopTgtOk] at h; simp only [holLoopProgLocValueFree] at hf
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); exact compHOL_nsl ctx b l hl h hf
  | .call none t args hd, l, hl, h, hf => by
      have ht : TgtGood t := by
        cases hd with
        | none => simpa [loopTgtOk] using h
        | some e => rcases e with ⟨_, _, _, _⟩; simp only [loopTgtOk] at h; exact h.1
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only)
      simp [NSL, callHdr, labOk, tgt_ne ht]
  | .call (some (vs, live)) t args none, l, hl, h, hf => by
      have ht : TgtGood t := by simpa [loopTgtOk] using h
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only)
      simp [NSL, callHdr, labOk, tgt_ne ht, hl]
  | .call (some (vs, live)) t args (some (n, p1, p2, lo)), l, hl, h, hf => by
      simp only [loopTgtOk] at h; simp only [holLoopProgLocValueFree] at hf
      obtain ⟨ht, h1, h2⟩ := h
      have hw1 := compHOL_nsl ctx p1 (l.1, l.2 + 1) hl h1 hf.1
      have hf1 := compHOL_fst ctx p1 (l.1, l.2 + 1)
      rcases hw1' : LoopToWord.compHOL ctx p1 (l.1, l.2 + 1) with ⟨w1, l1⟩
      rw [hw1'] at hw1 hf1
      have hl1 : l1.1 ≠ storeConstsStubLocation := by simp only at hf1; rw [hf1]; exact hl
      have hw2 := compHOL_nsl ctx p2 l1 hl1 h2 hf.2
      rcases hw2' : LoopToWord.compHOL ctx p2 l1 with ⟨w2, l2⟩
      rw [hw2'] at hw2
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only)
      have hf2 := compHOL_fst ctx p2 l1
      rw [hw2'] at hf2; simp only at hf2
      simp [hw1', hw2', NSL, callHdr, labOk, tgt_ne ht, hw1, hw2, hl, hl1, hf2]
  | .locValue .., _, _, _, hf => by simp [holLoopProgLocValueFree] at hf
  | .skip, _, _, _, _ | .assign .., _, _, _, _ | .store .., _, _, _, _ | .setGlobal .., _, _, _, _
  | .load32 .., _, _, _, _ | .loadByte .., _, _, _, _ | .store32 .., _, _, _, _
  | .storeByte .., _, _, _, _ | .break .., _, _, _, _ | .continue .., _, _, _, _
  | .raise .., _, _, _, _ | .return .., _, _, _, _ | .tick, _, _, _, _ | .fail, _, _, _, _
  | .ffi .., _, _, _, _ | .shMem .., _, _, _, _ => by rw [LoopToWord.compHOL]; rfl
  | .primitive ds .addCarry as, _, _, _, _ => by
      rw [LoopToWord.compHOL.eq_def]; dsimp only; split <;> rfl
  | .arith (.longMul ..), _, _, _, _ | .arith (.longDiv ..), _, _, _, _
  | .arith (.div ..), _, _, _, _ => by rw [LoopToWord.compHOL]; rfl
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

/-- Every WordLang function produced from any Pancake program satisfies `NSL`. -/
theorem panToWord_NSL {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width)) :
    ∀ y ∈ panToWordCompileProgHOL arch prog, NSL y.2.2 = true := by
  intro y hy
  unfold panToWordCompileProgHOL loopToWordCompileHOL loopToWordCompileProgHOL at hy
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
  obtain ⟨i, hi, -⟩ := compileProgHOLExact_names _ _ e he
  unfold loopToWordCompFuncHOL
  apply compHOL_nsl
  · show e.1 ≠ storeConstsStubLocation
    rw [hi]; simp [storeConstsStubLocation, wordNumStubs, stackNumStubs]; omega
  · exact compileProgHOLExact_bodiesTgtOk _ _ e he
  · exact compileProgHOLExact_rowLocValueFree _ _ e he

theorem wordToWordCompile_NSL {width : Nat} [NeZero width] (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, NSL x.2.2 = true) :
    ∀ y ∈ (WordToWord.compile wc ac progs).2, NSL y.2.2 = true := by
  unfold WordToWord.compile; dsimp only
  apply t_fullCompile_list
  intro x hx
  exact h _ (List.of_mem_zip hx).1

theorem panToWordToWord_NSL {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) :
    ∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2, NSL y.2.2 = true :=
  wordToWordCompile_NSL wc ac _ (panToWord_NSL arch prog)

end front


/-! # Stack / LabLang part -/

section stack
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Solver.PanToStackNoStoreConsts

variable {width : Nat} [NeZero width]

def tgtOk6 : Sum Nat Nat → Bool
  | .inl n => n != storeConstsStubLocation
  | .inr _ => true

@[simp] def sRet : Option (HolProg width × Nat × Nat × Nat) → Option Nat
  | none => none
  | some (_, _, l, _) => some l

@[simp] def sHd : Option (HolProg width × Nat × Nat) → Option Nat
  | none => none
  | some (_, l, _) => some l

/-- Stack call header: target, return section and handler section avoid the stub. -/
def sH (t : Sum Nat Nat) (r h : Option Nat) : Bool := tgtOk6 t && labOk r && labOk h

/-! ## Stack-level invariants -/

/-- No direct call (any shape) to the `storeConsts` stub label. -/
def J : HolProg width → Bool
  | .call ret t h =>
      sH t (sRet ret) (sHd h) &&
      (match ret with | none => true | some (r, _, _, _) => J r) &&
      (match h with | none => true | some (q, _, _) => J q)
  | .seq a b => J a && J b
  | .ite _ _ _ a b => J a && J b
  | .loop b => J b
  | .rawCall t => t != storeConstsStubLocation
  | .jumpLower _ _ t => t != storeConstsStubLocation
  | .locValue _ l _ => l != storeConstsStubLocation
  | _ => true


/-- Both invariants at once (no `storeConsts`, no call to the stub label). -/
def JC : HolProg width → Bool
  | .storeConsts .. => false
  | .call ret t h =>
      sH t (sRet ret) (sHd h) &&
      (match ret with | none => true | some (r, _, _, _) => JC r) &&
      (match h with | none => true | some (q, _, _) => JC q)
  | .seq a b => JC a && JC b
  | .ite _ _ _ a b => JC a && JC b
  | .loop b => JC b
  | .rawCall t => t != storeConstsStubLocation
  | .jumpLower _ _ t => t != storeConstsStubLocation
  | .locValue _ l _ => l != storeConstsStubLocation
  | _ => true

theorem clean_eq : ∀ p : HolProg width, JC p = (StackNoSt p && J p)
  | .seq a b => by
      simp only [JC, sH, sRet, sHd, labOk, StackNoSt, J, clean_eq a, clean_eq b]
      cases StackNoSt a <;> cases StackNoSt b <;> cases J a <;> cases J b <;> rfl
  | .ite _ _ _ a b => by
      simp only [JC, sH, sRet, sHd, labOk, StackNoSt, J, clean_eq a, clean_eq b]
      cases StackNoSt a <;> cases StackNoSt b <;> cases J a <;> cases J b <;> rfl
  | .loop a => by simp only [JC, sH, sRet, sHd, labOk, StackNoSt, J, clean_eq a]
  | .call none t none => by cases t <;> rfl
  | .call none t (some (q, _, _)) => by
      simp only [JC, sH, sRet, sHd, labOk, StackNoSt, J, clean_eq q]
      cases t <;> simp only [sH, tgtOk6, sRet, sHd, labOk] <;> cases StackNoSt q <;> cases J q <;> simp
  | .call (some (r, _, _, _)) t none => by
      simp only [JC, sH, sRet, sHd, labOk, StackNoSt, J, clean_eq r]
      cases t <;> simp only [sH, tgtOk6, sRet, sHd, labOk] <;> cases StackNoSt r <;> cases J r <;> simp
  | .call (some (r, _, _, _)) t (some (q, _, _)) => by
      simp only [JC, sH, sRet, sHd, labOk, StackNoSt, J, clean_eq r, clean_eq q]
      cases t <;> simp only [sH, tgtOk6, sRet, sHd, labOk] <;> cases StackNoSt r <;> cases J r <;>
        cases StackNoSt q <;> cases J q <;> simp
  | .skip | .inst .. | .get .. | .set .. | .opCurrHeap ..
  | .jumpLower .. | .alloc .. | .storeConsts .. | .raise .. | .ret ..
  | .break .. | .continue .. | .ffi .. | .tick | .locValue ..
  | .install .. | .shMemOp .. | .codeBufferWrite .. | .dataBufferWrite .. | .rawCall ..
  | .stackAlloc .. | .stackFree .. | .stackStore .. | .stackStoreAny .. | .stackLoad ..
  | .stackLoadAny .. | .stackGetSize .. | .stackSetSize .. | .bitmapLoad .. | .halt .. => by simp [JC, sH, sRet, sHd, labOk, StackNoSt, J]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem clean_of {p : HolProg width} (h1 : StackNoSt p = true) (h2 : J p = true) :
    JC p = true := by rw [clean_eq, h1, h2]; rfl

theorem of_clean {p : HolProg width} (h : JC p = true) :
    StackNoSt p = true ∧ J p = true := by
  rw [clean_eq, Bool.and_eq_true] at h; exact h

/-! ### small StackRemove helpers -/

theorem c_listSeq : ∀ (l : List (HolProg width)), (∀ x ∈ l, JC x = true) →
    JC (listSeqHOL l) = true
  | [], _ => rfl
  | [x], h => by rw [listSeqHOL]; exact h x (List.mem_singleton_self x)
  | x :: y :: ys, h => by
      rw [listSeqHOL]
      have hx := h x (List.mem_cons_self ..)
      have hr := c_listSeq (y :: ys) (fun z hz => h z (List.mem_cons_of_mem _ hz))
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨hx, hr⟩

theorem c_upshift (r : Nat) : ∀ n, JC (StackRemove.upshift (width := width) r n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.upshift]; split
    · rfl
    · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.true_and] at this ⊢
      exact this

theorem c_downshift (r : Nat) : ∀ n, JC (StackRemove.downshift (width := width) r n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.downshift]; split
    · rfl
    · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.true_and] at this ⊢
      exact this

theorem c_stackFree (ptr : Nat) : ∀ n, JC (StackRemove.stackFree (width := width) ptr n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.stackFree]; split
    · rfl
    · split
      · rfl
      · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
        simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨rfl, this⟩

theorem c_singleStackAlloc (j : Bool) (ptr n : Nat) :
    JC (StackRemove.singleStackAlloc (width := width) j ptr n) = true := by
  unfold StackRemove.singleStackAlloc; split <;> rfl

theorem c_stackAlloc (j : Bool) (ptr : Nat) :
    ∀ n, JC (StackRemove.stackAlloc (width := width) j ptr n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.stackAlloc]; split
    · rfl
    · split
      · exact c_singleStackAlloc _ _ _
      · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
        have h0 := c_singleStackAlloc (width := width) j ptr StackRemove.maxStackAlloc
        simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨h0, this⟩

theorem c_split {a b : HolProg width} (ha : JC a = true) (hb : JC b = true) :
    JC (.seq a b) = true := by
  simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨ha, hb⟩

/-- StackRemove `comp` keeps both invariants; its `.storeConsts` (copy-loop) branch
is never taken on a `StackNoSt` body (that arm is discharged by contradiction). -/
theorem c_stackRemoveComp (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) :
    ∀ p : HolProg width, JC p = true → JC (StackRemove.comp j bd ptr p) = true
  | .seq a b, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
      rw [StackRemove.comp]; exact c_split (c_stackRemoveComp j bd ptr a h.1) (c_stackRemoveComp j bd ptr b h.2)
  | .ite c r ri a b, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
      rw [StackRemove.comp]; simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨c_stackRemoveComp j bd ptr a h.1, c_stackRemoveComp j bd ptr b h.2⟩
  | .loop a, h => by rw [StackRemove.comp]; exact c_stackRemoveComp j bd ptr a h
  | .call none t none, h => by
      rw [StackRemove.comp]
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_true] at h ⊢; exact h
  | .call none t (some (q, y1, y2)), h => by
      rw [StackRemove.comp]
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true] at h ⊢; exact ⟨h.1, c_stackRemoveComp j bd ptr q h.2⟩
  | .call (some (r, x1, x2, x3)) t none, h => by
      rw [StackRemove.comp]
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true] at h ⊢; exact ⟨h.1, c_stackRemoveComp j bd ptr r h.2⟩
  | .call (some (r, x1, x2, x3)) t (some (q, y1, y2)), h => by
      rw [StackRemove.comp]
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, c_stackRemoveComp j bd ptr r h.1.2⟩, c_stackRemoveComp j bd ptr q h.2⟩
  | .storeConsts .., h => by simp [JC, sH, sRet, sHd, labOk, StackNoSt] at h
  | .get .., h | .set .., h => by
      rw [StackRemove.comp]; split <;> rfl
  | .stackFree n, h => by rw [StackRemove.comp]; exact c_stackFree _ _
  | .stackAlloc n, h => by rw [StackRemove.comp]; exact c_stackAlloc _ _ _
  | .stackStore r n, h => by
      rw [StackRemove.comp]; split
      · rfl
      · unfold StackRemove.stackStore
        exact c_split (c_upshift _ _) (c_split rfl (c_downshift _ _))
  | .stackLoad r n, h => by
      rw [StackRemove.comp]; split
      · rfl
      · unfold StackRemove.stackLoad
        exact c_split rfl (c_split (c_upshift _ _) rfl)
  | .bitmapLoad .., h => by
      rw [StackRemove.comp]; exact c_listSeq _ (by simp [JC, sH, sRet, sHd, labOk, addInst, StackRemove.leftShiftInst])
  | .skip, h | .inst .., h | .opCurrHeap .., h | .jumpLower .., h | .alloc .., h
  | .raise .., h | .ret .., h | .break .., h | .continue .., h | .ffi .., h
  | .tick, h | .locValue .., h | .install .., h | .shMemOp .., h | .codeBufferWrite .., h
  | .dataBufferWrite .., h | .rawCall .., h | .stackStoreAny .., h | .stackLoadAny .., h | .stackGetSize .., h
  | .stackSetSize .., h | .halt .., h => by
      rw [StackRemove.comp] <;> first | rfl | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

/-! ### StackNames -/

theorem c_stackNames (f : Spt Nat) :
    ∀ p : HolProg width, JC p = true → JC (StackNames.progCompHOL f p) = true
  | .seq a b, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
      rw [StackNames.progCompHOL]; exact c_split (c_stackNames f a h.1) (c_stackNames f b h.2)
  | .ite c r ri a b, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
      rw [StackNames.progCompHOL]; simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨c_stackNames f a h.1, c_stackNames f b h.2⟩
  | .loop a, h => by rw [StackNames.progCompHOL]; exact c_stackNames f a h
  | .call none t none, h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk6 (StackNames.destFindNameHOL f t) = tgtOk6 t := by cases t <;> rfl
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_true, ht] at h ⊢; exact h
  | .call none t (some (q, y1, y2)), h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk6 (StackNames.destFindNameHOL f t) = tgtOk6 t := by cases t <;> rfl
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true, ht] at h ⊢; exact ⟨h.1, c_stackNames f q h.2⟩
  | .call (some (r, x1, x2, x3)) t none, h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk6 (StackNames.destFindNameHOL f t) = tgtOk6 t := by cases t <;> rfl
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true, ht] at h ⊢; exact ⟨h.1, c_stackNames f r h.2⟩
  | .call (some (r, x1, x2, x3)) t (some (q, y1, y2)), h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk6 (StackNames.destFindNameHOL f t) = tgtOk6 t := by cases t <;> rfl
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, ht] at h ⊢
      exact ⟨⟨h.1.1, c_stackNames f r h.1.2⟩, c_stackNames f q h.2⟩
  | .shMemOp op r a, h => by
      cases a; rw [StackNames.progCompHOL]; rfl
  | .skip, h | .inst .., h | .get .., h | .set .., h | .opCurrHeap .., h
  | .jumpLower .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .ret .., h
  | .break .., h | .continue .., h | .ffi .., h | .tick, h | .locValue .., h
  | .install .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .rawCall .., h | .stackAlloc .., h
  | .stackFree .., h | .stackStore .., h | .stackStoreAny .., h | .stackLoad .., h | .stackLoadAny .., h
  | .stackGetSize .., h | .stackSetSize .., h | .bitmapLoad .., h | .halt .., h => by
      rw [StackNames.progCompHOL] <;> first | rfl | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

/-- StackNames renaming leaves `StackNoSt` *exactly* unchanged on `storeConsts`
(fixed point), so the invariant is not trivially created by renaming. -/
theorem stackNames_keeps_storeConsts (f : Spt Nat) :
    StackNoSt (StackNames.progCompHOL f (.storeConsts 0 1 none : HolProg width)) = false := by
  rw [StackNames.progCompHOL.eq_def]; rfl

/-! ### StackAlloc, StackRawCall -/

theorem c_stackAllocComp : ∀ (n m : Nat) (p : HolProg width), n ≠ storeConstsStubLocation → JC p = true →
    JC (StackAlloc.comp n m p).1 = true
  | n, m, .seq a b, hn, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨c_stackAllocComp n m a hn h.1, c_stackAllocComp n _ b hn h.2⟩
  | n, m, .ite c r ri a b, hn, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨c_stackAllocComp n m a hn h.1, c_stackAllocComp n _ b hn h.2⟩
  | n, m, .loop a, hn, h => by rw [StackAlloc.comp]; exact c_stackAllocComp n m a hn h
  | n, m, .call none d e, hn, h => by
      rw [StackAlloc.comp]; rcases e with _ | ⟨q, y1, y2⟩ <;>
        simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢ <;>
        first | exact h | exact h.1 | exact h.1.1
  | n, m, .call (some (p1, lr, l1, l2)) d none, hn, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true] at h
      rw [StackAlloc.comp]; simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true]
      exact ⟨h.1, c_stackAllocComp n m p1 hn h.2⟩
  | n, m, .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), hn, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]
      exact ⟨⟨h.1.1, c_stackAllocComp n m p1 hn h.1.2⟩, c_stackAllocComp n _ p2 hn h.2⟩
  | n, m, .alloc _, hn, h => by
      simp only [storeConstsStubLocation, wordNumStubs, stackNumStubs] at hn
      rw [StackAlloc.comp]; simp [JC, sH, sRet, sHd, labOk, sH, sRet, sHd, labOk, tgtOk6, gcStubLocation, hn,
        storeConstsStubLocation, wordNumStubs, stackNumStubs]
  | n, m, .storeConsts .., hn, h => by simp [JC, sH, sRet, sHd, labOk, StackNoSt] at h
  | n, m, .skip, hn, h | n, m, .inst .., hn, h | n, m, .get .., hn, h | n, m, .set .., hn, h | n, m, .opCurrHeap .., hn, h
  | n, m, .jumpLower .., hn, h | n, m, .raise .., hn, h | n, m, .ret .., hn, h | n, m, .break .., hn, h | n, m, .continue .., hn, h
  | n, m, .ffi .., hn, h | n, m, .tick, hn, h | n, m, .locValue .., hn, h | n, m, .install .., hn, h | n, m, .shMemOp .., hn, h
  | n, m, .codeBufferWrite .., hn, h | n, m, .dataBufferWrite .., hn, h | n, m, .rawCall .., hn, h | n, m, .stackAlloc .., hn, h | n, m, .stackFree .., hn, h
  | n, m, .stackStore .., hn, h | n, m, .stackStoreAny .., hn, h | n, m, .stackLoad .., hn, h | n, m, .stackLoadAny .., hn, h | n, m, .stackGetSize .., hn, h
  | n, m, .stackSetSize .., hn, h | n, m, .bitmapLoad .., hn, h | n, m, .halt .., hn, h => by
      rw [StackAlloc.comp] <;> first | exact h | (intros; simp_all) | skip
termination_by _ _ p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem c_compSeq (a b fb : HolProg width) (info : Spt Nat) (hb : JC b = true)
    (hfb : JC fb = true) : JC (StackRawCall.compSeq a b info fb) = true := by
  unfold StackRawCall.compSeq
  rcases hd : StackRawCall.destCase a b with _ | ⟨k, dest⟩
  · exact hfb
  · have hdst : (dest != storeConstsStubLocation) = true := by
      revert hd; unfold StackRawCall.destCase; split
      · intro e; simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨-, rfl⟩ := e
        simpa [JC, sH, sRet, sHd, labOk, sH, tgtOk6, sRet, sHd, labOk] using hb
      · intro e; exact absurd e (by simp)
    dsimp only
    split
    · exact hfb
    · split
      · simpa [JC] using hdst
      · split <;> simpa [JC] using hdst

theorem c_rawCallComp (info : Spt Nat) :
    ∀ p : HolProg width, JC p = true → JC (StackRawCall.comp info p) = true
  | .seq a b, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; exact c_compSeq _ _ _ _ h.2 (c_split (c_rawCallComp info a h.1) (c_rawCallComp info b h.2))
  | .ite c r ri a b, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨c_rawCallComp info a h.1, c_rawCallComp info b h.2⟩
  | .loop a, h => by rw [StackRawCall.comp]; exact c_rawCallComp info a h
  | .call none d e, h => by rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all)
  | .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true] at h
      rw [StackRawCall.comp]; simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true]
      exact ⟨h.1, c_rawCallComp info p1 h.2⟩
  | .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true]
      exact ⟨⟨h.1.1, c_rawCallComp info p1 h.1.2⟩, c_rawCallComp info p2 h.2⟩
  | .skip, h | .inst .., h | .get .., h | .set .., h | .opCurrHeap .., h
  | .jumpLower .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .ret .., h
  | .break .., h | .continue .., h | .ffi .., h | .tick, h | .locValue .., h
  | .install .., h | .shMemOp .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .rawCall .., h
  | .stackAlloc .., h | .stackFree .., h | .stackStore .., h | .stackStoreAny .., h | .stackLoad .., h
  | .stackLoadAny .., h | .stackGetSize .., h | .stackSetSize .., h | .bitmapLoad .., h | .halt .., h => by
      rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem c_rawCallCompTop (info : Spt Nat) (p : HolProg width) (h : JC p = true) :
    JC (StackRawCall.compTop info p) = true := by
  rw [StackRawCall.compTop.eq_def]; split
  · rename_i a b
    simp only [JC, sH, sRet, sHd, labOk, Bool.and_eq_true] at h
    exact c_split (c_rawCallComp info a h.1) (c_rawCallComp info b h.2)
  · exact c_rawCallComp info p h

/-! ## WordToStack: no stub call, under a WordLang call-target hypothesis -/


theorem n_stackLoad : ∀ (l : List (Nat × Nat)) (x : HolProg width),
    J (wStackLoadNative l x) = J x
  | [], x => rfl
  | (r, i) :: ps, x => by
      simp only [wStackLoadNative, J, Bool.true_and]; exact n_stackLoad ps x

theorem n_regWrite1 (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (hg : ∀ n, J (g n) = true) : J (wRegWrite1Native g r kf) = true := by
  unfold wRegWrite1Native; dsimp only; split
  · exact hg _
  · simp [J, sH, sRet, sHd, labOk, hg]

theorem n_wInst (i : HolInst width) (kf : Nat × Nat × Nat) :
    J (wInstNative i kf) = true := by
  unfold wInstNative
  split <;> (try simp only [n_stackLoad]) <;>
    first | rfl | (apply n_regWrite1; intro n; rfl)

theorem n_wMoveAux : ∀ (l : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat),
    J (wMoveAuxNative (width := width) l kf) = true
  | [], _ => rfl
  | [xy], kf => by
      rw [wMoveAuxNative]; unfold wMoveSingleNative; split <;> rfl
  | xy :: y :: ys, kf => by
      simp only [wMoveAuxNative, J, Bool.and_eq_true]
      refine ⟨?_, n_wMoveAux (y :: ys) kf⟩
      unfold wMoveSingleNative; split <;> rfl

theorem n_seqStackFree (n : Nat) (p : HolProg width) (h : J p = true) :
    J (seqStackFreeNative n p) = true := by
  unfold seqStackFreeNative; split
  · exact h
  · simpa [J] using h

theorem n_copyRetAux (k f : Nat) : ∀ n, J (copyRetAuxNative (width := width) k f n) = true
  | 0 => rfl
  | n + 1 => by
      rw [copyRetAuxNative]; simp only [listSeq, J, Bool.true_and]
      exact n_copyRetAux k f n

theorem n_copyRet {β γ : Type} (perf ih : Bool) (kf : Nat × Nat × γ) (vs : List β)
    (kont : HolProg width) (h : J kont = true) :
    J (copyRetNative perf ih kf vs kont) = true := by
  unfold copyRetNative; dsimp only; split
  · exact h
  · simp only [J, sH, sRet, sHd, labOk, Bool.and_eq_true]
    exact ⟨n_copyRetAux _ _ _, n_seqStackFree _ _ h⟩

theorem n_stackMove (offset i : Nat) (p : HolProg width) (h : J p = true) :
    ∀ n start, J (stackMoveNative n start offset i p) = true := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih => intro s; rw [stackMoveNative]; simp only [J, sH, sRet, sHd, labOk, Bool.and_true]; exact ih _

theorem n_stackArgs {α β : Type} (d : Sum α β) (ac : Nat) (kf : Nat × Nat × Nat) :
    J (stackArgsNative (width := width) d ac kf) = true := by
  unfold stackArgsNative; exact n_stackMove _ _ _ rfl _ _

theorem n_callDest (pos : Option Nat) (args : List Nat) (kf : Nat × Nat × Nat)
    (hp : pos ≠ some storeConstsStubLocation) :
    J (callDestNative (width := width) pos args kf).1 = true ∧
    (match (callDestNative (width := width) pos args kf).2 with
      | .inl n => n != storeConstsStubLocation | .inr _ => true) = true := by
  unfold callDestNative; split
  · rename_i p; refine ⟨rfl, ?_⟩; simp only [bne_iff_ne, ne_eq]; intro e; exact hp (by rw [e])
  · split
    · exact ⟨rfl, by simp [raiseStubLocation, storeConstsStubLocation, wordNumStubs, stackNumStubs]⟩
    · dsimp only; rw [n_stackLoad]; exact ⟨rfl, rfl⟩

theorem n_wMove (m : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    J (wMoveNative (width := width) m kf) = true := by
  unfold wMoveNative; exact n_wMoveAux _ _

theorem n_pushHandler {β γ : Type} (perf : Bool) (l1 l2 : Nat) (kf : Nat × β × γ)
    (hl : (l1 != storeConstsStubLocation) = true) :
    J (pushHandlerNative (width := width) perf l1 l2 kf) = true := by
  unfold pushHandlerNative; cases perf <;> simp [J, listSeq, hl]

theorem n_stackHandlerArgs {α β : Type} (perf : Bool) (d : Sum α β) (ac : Nat) (kf : Nat × Nat × Nat) :
    J (stackHandlerArgsNative (width := width) perf d ac kf) = true := by
  unfold stackHandlerArgsNative; exact n_stackArgs _ _ _

theorem n_perfPrefix (l1 l2 k : Nat) (hl : (l1 != storeConstsStubLocation) = true) :
    J (perfCallPrefixNative (width := width) l1 l2 k) = true := by
  unfold perfCallPrefixNative; simp [J, listSeq, hl]

theorem n_popHandler {β γ : Type} (perf : Bool) (kf : Nat × β × γ) (p : HolProg width)
    (h : J p = true) : J (popHandlerNative perf kf p) = true := by
  unfold popHandlerNative; simpa [J] using h

theorem n_wLive (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : J (wLiveNative live bs kf).1 = true := by
  unfold wLiveNative; split <;> rfl

theorem n_wShareInst (op : HolMemop) (v : Nat) (a : HolAddr width) (kf : Nat × Nat × Nat) :
    J (wShareInstNative op v a kf) = true := by
  unfold wShareInstNative
  split <;> (try simp only [n_stackLoad]) <;> first | rfl | (apply n_regWrite1; intro n; rfl)

theorem n_compNative (conf : AsmConfigExact width) (perf : Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
      (kf : Nat × Nat × Nat), NSL p = true → J (compNative conf perf p bs kf).1 = true
  | .seq a b, bs, kf, h => by
      simp only [NSL, Bool.and_eq_true] at h
      rw [compNative]; simp only [J, sH, sRet, sHd, labOk, Bool.and_eq_true]
      exact ⟨n_compNative conf perf a _ _ h.1, n_compNative conf perf b _ _ h.2⟩
  | .ite c r ri a b, bs, kf, h => by
      simp only [NSL, Bool.and_eq_true] at h
      have ha := n_compNative conf perf a bs kf h.1
      have hb := n_compNative conf perf b (compNative conf perf a bs kf).2 kf h.2
      rw [compNative]; dsimp only
      split
      · rw [n_stackLoad]; simp only [J, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · split
        · rw [n_stackLoad]; simp only [J, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨ha, hb⟩
        · simp only [J, sH, sRet, sHd, labOk, Bool.true_and]; rw [n_stackLoad]
          simp only [J, sH, sRet, sHd, labOk, Bool.and_eq_true]; exact ⟨ha, hb⟩
  | .mustTerminate a, bs, kf, h => by rw [compNative]; exact n_compNative conf perf a _ _ h
  | .loop x a y, bs, kf, h => by
      rw [compNative]; exact n_compNative conf perf a _ _ h
  | .call none d args hd, bs, kf, h => by
      have hdn : d ≠ some storeConstsStubLocation := by
        intro e; subst e; unfold NSL at h; simp only [bne_self_eq_false, Bool.false_and] at h; exact Bool.false_ne_true h
      obtain ⟨hq0, hdst⟩ := n_callDest (width := width) d args kf hdn
      rw [compNative]
      rcases hc : callDestNative (width := width) d args kf with ⟨q0, dst⟩
      rw [hc] at hq0 hdst; dsimp only at hq0 hdst ⊢
      change tgtOk6 dst = true at hdst
      simp only [J, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true]
      refine ⟨hq0, n_seqStackFree _ _ ?_⟩
      simp only [J, sH, sRet, sHd, labOk, Bool.and_true]; exact hdst
  | .call (some (vs, live, rc, l1, l2)) d args none, bs, kf, h => by
      have hdn : d ≠ some storeConstsStubLocation := by
        intro e; subst e; unfold NSL at h; simp only [bne_self_eq_false, Bool.false_and] at h; exact Bool.false_ne_true h
      have hL := h
      simp only [NSL, Bool.and_eq_true, Bool.and_true] at h
      have hr := n_compNative conf perf rc (wLiveNative live bs kf).2 kf h.2
      obtain ⟨hq0, hdst⟩ := n_callDest (width := width) d args kf hdn
      rw [compNative]
      rcases hc : callDestNative (width := width) d args kf with ⟨q0, dst⟩
      rw [hc] at hq0 hdst; dsimp only at hq0 hdst ⊢
      change tgtOk6 dst = true at hdst
      simp only [J, sH, sRet, sHd, labOk, Bool.and_eq_true, Bool.and_true]
      have hl1 : (l1 != storeConstsStubLocation) = true := by simp_all [NSL, callHdr, labOk]
      refine ⟨hq0, n_wLive _ _ _, n_stackArgs _ _ _, ?_, ⟨hdst, hl1⟩, ?_, n_copyRet _ _ _ _ _ hr⟩
      · split
        · exact n_perfPrefix _ _ _ hl1
        · rfl
      · split <;> rfl
  | .call (some (vs, live, rc, l1, l2)) d args (some (e, hc', h1, h2)), bs, kf, h => by
      have hdn : d ≠ some storeConstsStubLocation := by
        intro e; subst e; unfold NSL at h; simp only [bne_self_eq_false, Bool.false_and] at h; exact Bool.false_ne_true h
      have hL := h
      simp only [NSL, Bool.and_eq_true] at h
      have hr := n_compNative conf perf rc (wLiveNative live bs kf).2 kf h.1.2
      have hh := n_compNative conf perf hc'
        (compNative conf perf rc (wLiveNative live bs kf).2 kf).2 kf h.2
      obtain ⟨hq0, hdst⟩ := n_callDest (width := width) d args kf hdn
      rw [compNative]
      rcases hc : callDestNative (width := width) d args kf with ⟨q0, dst⟩
      rw [hc] at hq0 hdst; dsimp only at hq0 hdst ⊢
      change tgtOk6 dst = true at hdst
      have hcH : callHdr d (some l1) (some h1) = true := h.1.1
      simp only [callHdr, labOk, Bool.and_eq_true] at hcH
      have hl1 : (l1 != storeConstsStubLocation) = true := hcH.1.2
      have hh1 : (h1 != storeConstsStubLocation) = true := hcH.2
      have hpre : J (if perf then perfCallPrefixNative l1 l2 kf.1 else (.skip : HolProg width)) = true := by
        split
        · exact n_perfPrefix _ _ _ hl1
        · rfl
      have hsuf : J (if perf then perfCallSuffixNative else (.skip : HolProg width)) = true := by
        split <;> rfl
      have hcr := n_copyRet perf true kf vs _ (n_popHandler perf kf _ hr)
      have hph := n_pushHandler (width := width) perf h1 h2 kf hh1
      have hsa := n_stackHandlerArgs (width := width) perf dst (args.length + 1) kf
      simp only [J, sH, sRet, sHd, labOk, tgtOk6, Bool.and_eq_true] at hcr hsuf ⊢
      have hwl := n_wLive (width := width) live bs kf
      simp only [hq0, hwl, hph, hsa, hpre, hsuf, hcr, hh, hl1, hh1, hdst, and_self, true_and, and_true]
      try (cases dst <;> simp_all [tgtOk6])
  | .storeConsts .., bs, kf, h => by
      rw [compNative]; dsimp only; rfl
  | .move .., bs, kf, h => by rw [compNative]; exact n_wMove _ _
  | .inst i, bs, kf, h => by rw [compNative]; exact n_wInst _ _
  | .return v vs, bs, kf, h => by
      rw [compNative]; dsimp only; rw [n_stackLoad]; exact n_seqStackFree _ _ rfl
  | .opCurrHeap .., bs, kf, h => by
      rw [compNative]; dsimp only; rw [n_stackLoad]; apply n_regWrite1; intro; rfl
  | .set name e, bs, kf, h => by
      rw [compNative.eq_def]; dsimp only
      repeat' split
      all_goals first | rfl | (rw [n_stackLoad]; rfl)
  | .get d st, bs, kf, h => by
      rw [compNative]; exact n_regWrite1 (fun r => .get r (storeNameOfWord st)) d kf (fun _ => rfl)
  | .locValue d l, bs, kf, h => by
      simp only [NSL] at h
      rw [compNative]; exact n_regWrite1 (fun n => .locValue n l 0) d kf (fun _ => by simp [J, h])
  | .alloc _ live, bs, kf, h => by
      rw [compNative]; simp only [J, sH, sRet, sHd, labOk, Bool.and_true]; exact n_wLive _ _ _
  | .install .., bs, kf, h | .codeBufferWrite .., bs, kf, h | .dataBufferWrite .., bs, kf, h => by
      rw [compNative] <;> (try dsimp only) <;> rw [n_stackLoad] <;> rfl
  | .shareInst op v e, bs, kf, h => by
      rw [compNative]; split
      · rfl
      · exact n_wShareInst _ _ _ _
  | .raise .., _, _, _ => by rw [compNative]; simp [J, sH, sRet, sHd, labOk, tgtOk6, raiseStubLocation, storeConstsStubLocation, wordNumStubs, stackNumStubs]
  | .skip, _, _, _ | .tick, _, _, _ | .break .., _, _, _
  | .continue .., _, _, _ | .ffi .., _, _, _ | .assign .., _, _, _ | .store .., _, _, _ => by
      rw [compNative] <;> first | rfl | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)


theorem n_compileWordToStack {β : Type} (conf : AsmConfigExact width) (perf : Bool) (rc : Nat) :
    ∀ (progs : List (β × Nat × WordLangProgHOL (BitVec width))) (bs : AppList (BitVec width) × Nat),
      (∀ x ∈ progs, WordPassesPreserveNoStoreConsts.NoSt x.2.2 = true ∧ NSL x.2.2 = true) →
      ∀ y ∈ (compileWordToStackNative conf perf rc progs bs).1, JC y.2 = true
  | [], _, _ => by intro y hy; simp [compileWordToStackNative] at hy
  | (i, ac, p) :: ps, bs, h => by
      intro y hy
      rw [compileWordToStackNative] at hy; dsimp only at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · have hp := h _ (List.mem_cons_self ..)
        apply clean_of
        · exact s_compileProgNative conf perf p ac rc bs hp.1
        · unfold compileProgNative; dsimp only
          simp only [J, sH, sRet, sHd, labOk, Bool.true_and]; exact n_compNative conf perf p _ _ hp.2
      · exact n_compileWordToStack conf perf rc ps _
          (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy

/-- Top-level WordToStack: every entry is either the `storeConsts` stub itself or `JC`. -/
theorem c_compileNative (conf : AsmConfigExact width) (perf : Bool)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, WordPassesPreserveNoStoreConsts.NoSt x.2.2 = true ∧ NSL x.2.2 = true) :
    ∀ y ∈ (compileNative conf perf progs).2.2.2,
      y.1 = storeConstsStubLocation ∨ JC y.2 = true := by
  intro y hy
  unfold compileNative at hy; dsimp only at hy
  rcases List.mem_cons.1 hy with rfl | hy
  · right; unfold raiseStubNative; cases perf <;> rfl
  rcases List.mem_cons.1 hy with rfl | hy
  · left; rfl
  · right; exact n_compileWordToStack conf perf _ progs _ h y hy

/-- One body through the whole StackToLab stack-side chain (raw call → StackAlloc →
StackRemove → StackNames) stays `JC`. -/
theorem c_body_chain (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat)
    (f : Spt Nat) (n : Nat) (p : HolProg width) (hn : n ≠ storeConstsStubLocation) (h : JC p = true) :
    JC (StackNames.progCompHOL f (StackRemove.comp j bd ptr
      (StackAlloc.progComp (n, StackRawCall.compTop info p)).2)) = true := by
  apply c_stackNames; apply c_stackRemoveComp
  unfold StackAlloc.progComp; exact c_stackAllocComp _ _ _ hn (c_rawCallCompTop info p h)


/-! ## LabLang line invariant -/

/-- A label target that is not inside the `storeConsts` stub section. -/
def tOk : LabLang.Lab → Bool
  | .lab s _ => s != storeConstsStubLocation

/-- Control-transfer instructions (`jump`, `jumpCmp`, `call`) never target section 6. -/
def aOk : AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString → Bool
  | .jump t => tOk t
  | .jumpCmp _ _ _ t => tOk t
  | .call t => tOk t
  | .locValue _ t => tOk t
  | _ => true

def JumpOk : LabSem.LabLineHOL width → Bool
  | .labAsm a _ _ _ => aOk a
  | _ => true

def AOk (l : AppList (LabSem.LabLineHOL width)) : Prop := ∀ x ∈ appendAux l [], JumpOk x = true

theorem aok_append (a b : AppList (LabSem.LabLineHOL width)) :
    AOk (.append a b) ↔ AOk a ∧ AOk b := by
  unfold AOk; rw [appendAux, Flapjack.appendAux_thm]; simp only [List.mem_append]
  constructor
  · intro h; exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩
  · rintro ⟨h1, h2⟩ x (hx | hx)
    · exact h1 x hx
    · exact h2 x hx

theorem aok_list (v : List (LabSem.LabLineHOL width)) :
    AOk (.list v) ↔ ∀ x ∈ v, JumpOk x = true := by
  unfold AOk; simp [appendAux]

theorem jo_compileJump (t : Sum Nat Nat) (h : tgtOk6 t = true) :
    JumpOk (StackToLab.compileJumpHOL (width := width) t) = true := by
  cases t <;> simp_all [StackToLab.compileJumpHOL, JumpOk, aOk, tOk, tgtOk6]

@[simp] theorem jo_label (a b c : Nat) : JumpOk (.label a b c : LabSem.LabLineHOL width) = true := rfl
@[simp] theorem jo_asm (a : AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (b : List (BitVec 8)) (c : Nat) :
    JumpOk (.asm a b c : LabSem.LabLineHOL width) = true := rfl
theorem jo_loc {s : Nat} (hs : s ≠ storeConstsStubLocation) (r k : Nat) (w : BitVec width)
    (b : List (BitVec 8)) (c : Nat) :
    JumpOk (.labAsm (.locValue r (.lab s k)) w b c : LabSem.LabLineHOL width) = true := by
  simp [JumpOk, aOk, tOk, hs]
@[simp] theorem jo_ffi (f : Basis.Pure.MlString.MlString) (w : BitVec width) (b : List (BitVec 8)) (c : Nat) :
    JumpOk (.labAsm (.callFFI f) w b c : LabSem.LabLineHOL width) = true := rfl
@[simp] theorem jo_install (w : BitVec width) (b : List (BitVec 8)) (c : Nat) :
    JumpOk (.labAsm .install w b c : LabSem.LabLineHOL width) = true := rfl
@[simp] theorem jo_halt (w : BitVec width) (b : List (BitVec 8)) (c : Nat) :
    JumpOk (.labAsm .halt w b c : LabSem.LabLineHOL width) = true := rfl
theorem jo_jump {s : Nat} (hs : s ≠ storeConstsStubLocation) (k : Nat) (w : BitVec width)
    (b : List (BitVec 8)) (c : Nat) :
    JumpOk (.labAsm (.jump (.lab s k)) w b c : LabSem.LabLineHOL width) = true := by
  simp [JumpOk, aOk, tOk, hs]
theorem jo_jcmp {s : Nat} (hs : s ≠ storeConstsStubLocation) (k : Nat) (o : HolCmp) (r : Nat)
    (ri : HolRegImm width) (w : BitVec width) (b : List (BitVec 8)) (c : Nat) :
    JumpOk (.labAsm (.jumpCmp o r ri (.lab s k)) w b c : LabSem.LabLineHOL width) = true := by
  simp [JumpOk, aOk, tOk, hs]

theorem jc_call_tgt {ret : Option (HolProg width × Nat × Nat × Nat)} {t : Sum Nat Nat}
    {hd : Option (HolProg width × Nat × Nat)} (h : JC (.call ret t hd) = true) : tgtOk6 t = true := by
  rcases ret with _ | ⟨r, a, b, c⟩ <;> rcases hd with _ | ⟨q, a', b'⟩ <;>
    simp only [JC, Bool.and_eq_true, Bool.and_true] at h <;> first | exact (by simp_all [sH]) | exact h.1.1

theorem jc_call_ret {r : HolProg width} {a b c : Nat} {t : Sum Nat Nat}
    {hd : Option (HolProg width × Nat × Nat)} (h : JC (.call (some (r, a, b, c)) t hd) = true) :
    JC r = true := by
  rcases hd with _ | ⟨q, a', b'⟩ <;>
    simp only [JC, Bool.and_eq_true, Bool.and_true] at h <;> first | exact h.2 | exact h.1.2

theorem jc_call_hd {ret : Option (HolProg width × Nat × Nat × Nat)} {t : Sum Nat Nat}
    {q : HolProg width} {a b : Nat} (h : JC (.call ret t (some (q, a, b))) = true) : JC q = true := by
  rcases ret with _ | ⟨r, a1, b1, c1⟩ <;>
    simp only [JC, Bool.and_eq_true, Bool.true_and] at h <;> first | exact h.2 | exact h

/-- `flattenHOL` of a `JC` body inside a non-stub section emits no jump/call into section 6. -/
theorem f_ok : ∀ (p : HolProg width) (tail : Bool) (sid next : Nat) (conts breaks : List Nat),
    sid ≠ storeConstsStubLocation → JC p = true →
    AOk (StackToLab.flattenHOL tail p sid next conts breaks).1
  | .seq a b, tail, sid, next, conts, breaks, hs, h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackToLab.flattenHOL]
      rcases ea : StackToLab.flattenHOL false a sid next conts breaks with ⟨xs, nr1, n1⟩
      rcases eb : StackToLab.flattenHOL false b sid n1 conts breaks with ⟨ys, nr2, n2⟩
      have hxs : AOk xs := by have := f_ok a false sid next conts breaks hs h.1; rw [ea] at this; exact this
      have hys : AOk ys := by have := f_ok b false sid n1 conts breaks hs h.2; rw [eb] at this; exact this
      simp only [ea, eb]
      split <;> simp_all [aok_append, aok_list, JC, jo_jump, jo_jcmp, jo_loc, jo_compileJump, sH, sRet, sHd, labOk, tgtOk6]
  | .ite c r ri a b, tail, sid, next, conts, breaks, hs, h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackToLab.flattenHOL]
      rcases ea : StackToLab.flattenHOL false a sid next conts breaks with ⟨xs, nr1, n1⟩
      rcases eb : StackToLab.flattenHOL false b sid n1 conts breaks with ⟨ys, nr2, n2⟩
      have hxs : AOk xs := by have := f_ok a false sid next conts breaks hs h.1; rw [ea] at this; exact this
      have hys : AOk ys := by have := f_ok b false sid n1 conts breaks hs h.2; rw [eb] at this; exact this
      simp only [ea, eb]
      split_ifs <;> simp_all [aok_append, aok_list, JC, jo_jump, jo_jcmp, jo_loc, jo_compileJump, sH, sRet, sHd, labOk, tgtOk6]
  | .loop a, tail, sid, next, conts, breaks, hs, h => by
      simp only [JC] at h
      rw [StackToLab.flattenHOL]
      rcases ea : StackToLab.flattenHOL false a sid (next + 2) (next :: conts) ((next + 1) :: breaks)
        with ⟨xs, nr1, n1⟩
      have hxs : AOk xs := by
        have := f_ok a false sid (next + 2) (next :: conts) ((next + 1) :: breaks) hs h
        rw [ea] at this; exact this
      simp only [ea]
      simp_all [aok_append, aok_list, JC, jo_jump, jo_jcmp, jo_loc, jo_compileJump, sH, sRet, sHd, labOk, tgtOk6]
  | .call none t hd, tail, sid, next, conts, breaks, hs, h => by
      have ht := jc_call_tgt h
      rw [StackToLab.flattenHOL]; simp [aok_list, jo_compileJump t ht]
  | .call (some (r, lr, rs, rl)) t none, tail, sid, next, conts, breaks, hs, h => by
      have ht := jc_call_tgt h
      have hr := jc_call_ret h
      rw [StackToLab.flattenHOL]
      rcases ea : StackToLab.flattenHOL false r sid next conts breaks with ⟨xs, nr1, n1⟩
      have hxs : AOk xs := by have := f_ok r false sid next conts breaks hs hr; rw [ea] at this; exact this
      simp only [ea]
      simp_all [aok_append, aok_list, JC, jo_jump, jo_jcmp, jo_loc, jo_compileJump, sH, sRet, sHd, labOk, tgtOk6]
  | .call (some (r, lr, rs, rl)) t (some (q, hs1, hl1)), tail, sid, next, conts, breaks, hs, h => by
      have ht := jc_call_tgt h
      have hr := jc_call_ret h
      have hq := jc_call_hd h
      rw [StackToLab.flattenHOL]
      rcases ea : StackToLab.flattenHOL false r sid next conts breaks with ⟨xs, nr1, n1⟩
      rcases eb : StackToLab.flattenHOL false q sid n1 conts breaks with ⟨ys, nr2, n2⟩
      have hxs : AOk xs := by have := f_ok r false sid next conts breaks hs hr; rw [ea] at this; exact this
      have hys : AOk ys := by have := f_ok q false sid n1 conts breaks hs hq; rw [eb] at this; exact this
      simp only [ea, eb]
      simp_all [aok_append, aok_list, JC, jo_jump, jo_jcmp, jo_loc, jo_compileJump, sH, sRet, sHd, labOk, tgtOk6]
  | .rawCall t, tail, sid, next, conts, breaks, hs, h => by
      simp only [JC] at h
      rw [StackToLab.flattenHOL]; simp_all [aok_append, aok_list, JC, jo_jump, jo_jcmp, jo_loc, jo_compileJump, sH, sRet, sHd, labOk, tgtOk6]
  | .jumpLower l r t, tail, sid, next, conts, breaks, hs, h => by
      simp only [JC] at h
      rw [StackToLab.flattenHOL]; simp_all [aok_append, aok_list, JC, jo_jump, jo_jcmp, jo_loc, jo_compileJump, sH, sRet, sHd, labOk, tgtOk6]
  | .break i, tail, sid, next, conts, breaks, hs, h
  | .continue i, tail, sid, next, conts, breaks, hs, h => by
      rw [StackToLab.flattenHOL]; simp_all [aok_append, aok_list, JC, jo_jump, jo_jcmp, jo_loc, jo_compileJump, sH, sRet, sHd, labOk, tgtOk6]
  | .skip, _, _, _, _, _, hs, h | .inst .., _, _, _, _, _, hs, h | .get .., _, _, _, _, _, hs, h
  | .set .., _, _, _, _, _, hs, h | .opCurrHeap .., _, _, _, _, _, hs, h
  | .alloc .., _, _, _, _, _, hs, h | .storeConsts .., _, _, _, _, _, hs, h
  | .raise .., _, _, _, _, _, hs, h | .ret .., _, _, _, _, _, hs, h | .ffi .., _, _, _, _, _, hs, h
  | .tick, _, _, _, _, _, hs, h | .locValue .., _, _, _, _, _, hs, h | .install .., _, _, _, _, _, hs, h
  | .shMemOp .., _, _, _, _, _, hs, h | .codeBufferWrite .., _, _, _, _, _, hs, h
  | .dataBufferWrite .., _, _, _, _, _, hs, h | .stackAlloc .., _, _, _, _, _, hs, h
  | .stackFree .., _, _, _, _, _, hs, h | .stackStore .., _, _, _, _, _, hs, h
  | .stackStoreAny .., _, _, _, _, _, hs, h | .stackLoad .., _, _, _, _, _, hs, h
  | .stackLoadAny .., _, _, _, _, _, hs, h | .stackGetSize .., _, _, _, _, _, hs, h
  | .stackSetSize .., _, _, _, _, _, hs, h | .bitmapLoad .., _, _, _, _, _, hs, h
  | .halt .., _, _, _, _, _, hs, h => by
      rw [StackToLab.flattenHOL] <;> simp_all [aok_append, aok_list, JC, jo_jump, jo_jcmp, jo_loc, jo_compileJump, sH, sRet, sHd, labOk, tgtOk6]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

def LOk (xs : List (LabSem.LabLineHOL width)) : Prop := ∀ x ∈ xs, JumpOk x = true

theorem sec_ok (n : Nat) (p : HolProg width) (hs : n ≠ storeConstsStubLocation) (h : JC p = true) :
    LOk (StackToLab.progToSectionHOL (n, p)).lines := by
  unfold StackToLab.progToSectionHOL; dsimp only
  rcases e : StackToLab.flattenHOL true p n (StackAlloc.nextLab p 2) [] [] with ⟨ls, nr, nx⟩
  have hl : AOk ls := by have := f_ok p true n (StackAlloc.nextLab p 2) [] [] hs h; rw [e] at this; exact this
  simp only [e]
  have : AOk (.append ls (.list [.label n (if StackToLab.isSeqHOL p then nx else 1) 0])) := by
    rw [aok_append]; exact ⟨hl, by simp [aok_list, JumpOk]⟩
  intro x hx; unfold appListAppend at hx; exact this x hx

/-! ## StackToLab sections -/

open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock in
theorem stackToLab_lines (sc : StackToLab.Config) (dc : DataToWord.Config)
    (mh sp : Nat) (off : BitVec width × BitVec width) (L : List (Nat × HolProg width))
    (hL : ∀ x ∈ L, x.1 = storeConstsStubLocation ∨ JC x.2 = true) :
    ∀ s ∈ StackToLab.compile sc dc mh sp off L,
      IsStubLabel s.sectionId = true ∨ LOk s.lines := by
  intro s hs
  unfold StackToLab.compile at hs
  obtain ⟨y4, hy4, rfl⟩ := List.mem_map.1 hs
  obtain ⟨y3, hy3, rfl⟩ := stackNames_compileHOL_mem _ _ y4 hy4
  have hid : (StackToLab.progToSectionHOL (y3.1, StackNames.progCompHOL sc.regNames y3.2)).sectionId
      = y3.1 := rfl
  rcases stackRemove_compileHOL_mem _ _ _ _ _ _ _ y3 hy3 with h0 | ⟨y2, hy2, rfl⟩
  · left; rw [hid]; rcases h0 with h | h | h <;> simp [IsStubLabel, h]
  rcases stackAlloc_compile_mem _ _ y2 hy2 with hg | ⟨y1, hy1, rfl⟩
  · left; rw [hid]; simp [IsStubLabel, hg]
  obtain ⟨x, hx, hfst, info, hsnd⟩ := rawCall_compile_mem _ y1 hy1
  by_cases h6 : x.1 = storeConstsStubLocation
  · left; rw [hid]; simp only [stackAlloc_progComp_fst, hfst, h6]; simp [IsStubLabel]
  rcases hL x hx with hst | hok
  · exact absurd hst h6
  right
  apply sec_ok _ _ (by simp only [stackAlloc_progComp_fst, hfst]; exact h6)
  apply c_stackNames; apply c_stackRemoveComp
  obtain ⟨n1, p1⟩ := y1
  have hn1 : n1 ≠ storeConstsStubLocation := by
    have : n1 = x.1 := hfst
    rw [this]; exact h6
  dsimp only at hsnd; subst hsnd
  unfold StackAlloc.progComp
  exact c_stackAllocComp _ _ _ hn1 (c_rawCallCompTop info x.2 hok)

/-- Pancake → … → StackToLab: every section is a stub section or has no jump/call line
into section `storeConstsStubLocation`. No hypothesis on the program. -/
theorem panToLab_lines (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    ∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
      PanToLabSectionAndStackRemoveClock.IsStubLabel s.sectionId = true ∨ LOk s.lines :=
  stackToLab_lines sc dc mh sp off _
    (c_compileNative ac perf _ (fun x hx =>
      ⟨panToWordToWord_NoSt arch prog wc ac x hx,
       panToWordToWord_NSL arch prog wc ac x hx⟩))

/-! ## LabToTarget passes keep the line invariant -/

abbrev Sec (width : Nat) [NeZero width] := LabToTargetSectionCleanPreservation.Sec width

def SQ (s : Sec width) : Prop :=
  PanToLabSectionAndStackRemoveClock.IsStubLabel s.sectionId = true ∨ LOk s.lines

def AllQ (L : List (Sec width)) : Prop := ∀ s ∈ L, SQ s

theorem q_filterSkip : ∀ L : List (Sec width), AllQ L → AllQ (filterSkip L)
  | [], _ => by rw [filterSkip]; exact fun _ h => absurd h (List.not_mem_nil)
  | ⟨n, xs⟩ :: rest, h => by
      rw [filterSkip]; intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · rcases h _ (List.mem_cons_self ..) with st | ok
        · exact Or.inl st
        · exact Or.inr (fun x hx => ok x (List.mem_filter.1 hx).1)
      · exact q_filterSkip rest (fun s hs => h s (List.mem_cons_of_mem _ hs)) s hs

theorem jo_encLine (enc : HolAsm width → List (BitVec 8)) (k : Nat) (x : LabSem.LabLineHOL width) :
    JumpOk (encLine enc k x) = JumpOk x := by
  cases x <;> rfl

theorem q_encSecList (enc : HolAsm width → List (BitVec 8)) (L : List (Sec width)) (h : AllQ L) :
    AllQ (encSecList enc L) := by
  intro s hs; unfold encSecList at hs
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.1 hs
  rcases h s0 hs0 with st | ok
  · exact Or.inl st
  · right; intro x hx; unfold encSec at hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rw [jo_encLine]; exact ok y hy

theorem lok_cons {x : LabSem.LabLineHOL width} {xs : List (LabSem.LabLineHOL width)}
    (hx : JumpOk x = true) (h : LOk xs) : LOk (x :: xs) := by
  intro y hy; rcases List.mem_cons.1 hy with rfl | hy
  · exact hx
  · exact h y hy

theorem lok_tail {x : LabSem.LabLineHOL width} {xs : List (LabSem.LabLineHOL width)}
    (h : LOk (x :: xs)) : LOk xs := fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem lok_encLinesAgain (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) :
    ∀ (lines acc : List (LabSem.LabLineHOL width)) (pos : Nat) (ok : Bool),
      LOk lines → LOk acc → LOk (encLinesAgain labs ffis pos enc lines acc ok).1
  | [], acc, pos, ok, _, ha => by
      rw [encLinesAgain]; intro x hx; exact ha x (List.mem_reverse.1 hx)
  | .label a b c :: xs, acc, pos, ok, hl, ha => by
      rw [encLinesAgain]
      exact lok_encLinesAgain labs ffis enc xs _ _ _ (lok_tail hl) (lok_cons rfl ha)
  | .asm a b c :: xs, acc, pos, ok, hl, ha => by
      rw [encLinesAgain]
      exact lok_encLinesAgain labs ffis enc xs _ _ _ (lok_tail hl) (lok_cons rfl ha)
  | .labAsm a w bs l :: xs, acc, pos, ok, hl, ha => by
      have h0 : aOk a = true := hl _ (List.mem_cons_self ..)
      rw [encLinesAgain]; dsimp only
      split
      · exact lok_encLinesAgain labs ffis enc xs _ _ _ (lok_tail hl) (lok_cons h0 ha)
      · exact lok_encLinesAgain labs ffis enc xs _ _ _ (lok_tail hl) (lok_cons h0 ha)

theorem q_encSecsAgain (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (enc : HolAsm width → List (BitVec 8)) :
    ∀ (L : List (Sec width)) (pos : Nat), AllQ L → AllQ (encSecsAgain pos labs ffis enc L).1
  | [], _, _ => by rw [encSecsAgain]; exact fun _ h => absurd h (List.not_mem_nil)
  | ⟨s, lines⟩ :: rest, pos, h => by
      rcases e1 : encLinesAgain labs ffis pos enc lines [] true with ⟨l1, p1, o1⟩
      rcases e2 : encSecsAgain p1 labs ffis enc rest with ⟨r1, o2⟩
      have hr : AllQ r1 := by
        have := q_encSecsAgain labs ffis enc rest p1 (fun s hs => h s (List.mem_cons_of_mem _ hs))
        rw [e2] at this; exact this
      rw [encSecsAgain]; simp only [e1, e2]
      intro s' hs'
      rcases List.mem_cons.1 hs' with rfl | hs'
      · rcases h _ (List.mem_cons_self ..) with st | ok
        · exact Or.inl st
        · right
          have := lok_encLinesAgain labs ffis enc lines [] pos true ok (fun _ h => absurd h List.not_mem_nil)
          rw [e1] at this; exact this
      · exact hr s' hs'

theorem lok_linesUpdLabLen :
    ∀ (pos : Nat) (lines acc : List (LabSem.LabLineHOL width)),
      LOk lines → LOk acc → LOk (linesUpdLabLen pos lines acc).1
  | pos, [], acc, _, ha => by
      rw [linesUpdLabLen]; intro x hx; exact ha x (List.mem_reverse.1 hx)
  | pos, .label a b c :: xs, acc, hl, ha => by
      rw [linesUpdLabLen]; exact lok_linesUpdLabLen _ xs _ (lok_tail hl) (lok_cons rfl ha)
  | pos, .asm a b c :: xs, acc, hl, ha => by
      rw [linesUpdLabLen]; exact lok_linesUpdLabLen _ xs _ (lok_tail hl) (lok_cons rfl ha)
  | pos, .labAsm a w bs l :: xs, acc, hl, ha => by
      have h0 : aOk a = true := hl _ (List.mem_cons_self ..)
      rw [linesUpdLabLen]; exact lok_linesUpdLabLen _ xs _ (lok_tail hl) (lok_cons h0 ha)

theorem q_updLabLen : ∀ (L : List (Sec width)) (pos : Nat), AllQ L → AllQ (updLabLen pos L)
  | [], _, _ => by rw [updLabLen]; exact fun _ h => absurd h (List.not_mem_nil)
  | ⟨s, lines⟩ :: rest, pos, h => by
      rcases e1 : linesUpdLabLen pos lines [] with ⟨l1, p1⟩
      have hr := q_updLabLen rest p1 (fun s hs => h s (List.mem_cons_of_mem _ hs))
      rw [updLabLen]; simp only [e1]
      intro s' hs'
      rcases List.mem_cons.1 hs' with rfl | hs'
      · rcases h _ (List.mem_cons_self ..) with st | ok
        · exact Or.inl st
        · right
          have := lok_linesUpdLabLen pos lines [] ok (fun _ h => absurd h List.not_mem_nil)
          rw [e1] at this; exact this
      · exact hr s' hs'

theorem lok_addNop (nop : List (BitVec 8)) :
    ∀ xs : List (LabSem.LabLineHOL width), LOk xs → LOk (addNop nop xs)
  | [], _ => by rw [addNop]; exact fun _ h => absurd h List.not_mem_nil
  | .label a b c :: xs, h => by
      rw [addNop]; exact lok_cons rfl (lok_addNop nop xs (lok_tail h))
  | .asm a b c :: xs, h => by rw [addNop]; exact lok_cons rfl (lok_tail h)
  | .labAsm a w bs l :: xs, h => by
      have h0 : aOk a = true := h _ (List.mem_cons_self ..)
      rw [addNop]; exact lok_cons h0 (lok_tail h)

theorem lok_padSection (nop : List (BitVec 8)) :
    ∀ (lines aux : List (LabSem.LabLineHOL width)), LOk lines → LOk aux → LOk (padSection nop lines aux)
  | [], aux, _, ha => by rw [padSection]; intro x hx; exact ha x (List.mem_reverse.1 hx)
  | .label a b c :: xs, aux, hl, ha => by
      rw [padSection]
      refine lok_padSection nop xs _ (lok_tail hl) (lok_cons rfl ?_)
      split
      · exact ha
      · exact lok_addNop nop aux ha
  | .asm a b c :: xs, aux, hl, ha => by
      rw [padSection]; exact lok_padSection nop xs _ (lok_tail hl) (lok_cons rfl ha)
  | .labAsm a w bs l :: xs, aux, hl, ha => by
      have h0 : aOk a = true := hl _ (List.mem_cons_self ..)
      rw [padSection]
      exact lok_padSection nop xs _ (lok_tail hl) (lok_cons h0 ha)

theorem q_padCode (nop : List (BitVec 8)) : ∀ L : List (Sec width), AllQ L → AllQ (padCode nop L)
  | [], _ => by rw [padCode]; exact fun _ h => absurd h (List.not_mem_nil)
  | ⟨n, xs⟩ :: rest, h => by
      rw [padCode]; intro s hs
      rcases List.mem_cons.1 hs with rfl | hs
      · rcases h _ (List.mem_cons_self ..) with st | ok
        · exact Or.inl st
        · exact Or.inr (lok_padSection nop xs [] ok (fun _ h => absurd h List.not_mem_nil))
      · exact q_padCode nop rest (fun s hs => h s (List.mem_cons_of_mem _ hs)) s hs

theorem q_removeLabelsLoop (config : AsmConfigExact width) (pos : Nat)
    (initLabs : Spt (Spt Nat)) (ffis : List HolFfiName) :
    ∀ (clock : Nat) (L L' : List (Sec width)) (labs : Spt (Spt Nat)), AllQ L →
      removeLabelsLoop clock config pos initLabs ffis L = some (L', labs) → AllQ L'
  | clock, L, L', labs, hq, h => by
      rw [removeLabelsLoop] at h
      dsimp only at h
      split at h
      · split at h
        · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h).symm
          apply q_padCode; apply q_encSecsAgain; apply q_updLabLen; apply q_encSecsAgain; exact hq
        · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · exact q_removeLabelsLoop config pos initLabs ffis (clock - 1) _ L' labs
            (q_encSecsAgain _ _ _ _ _ hq) h
termination_by clock => clock
decreasing_by omega

theorem q_removeLabels (ic : Nat) (config : AsmConfigExact width) (pos : Nat)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (L L' : List (Sec width))
    (labs' : Spt (Spt Nat)) (hq : AllQ L) (h : removeLabels ic config pos labs ffis L = some (L', labs')) :
    AllQ L' := by
  unfold removeLabels at h
  exact q_removeLabelsLoop config pos labs ffis ic _ L' labs' (q_encSecList _ _ hq) h

/-! ## End to end -/

/-- Pancake → … → StackToLab → LabToTarget (`filterSkip`, `encSecList`, `encSecsAgain`,
`updLabLen`, `padCode` inside `removeLabels`): every encoded section is a stub section or contains
no `jump` / `jumpCmp` / `call` line into section `storeConstsStubLocation`. No program hypothesis. -/
theorem panToTarget_noStubJumpOrLocValue (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) :
    ∀ s' ∈ L', PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = true ∨
      ∀ x ∈ s'.lines, JumpOk x = true :=
  q_removeLabels ic ac pos labs ffis _ L' labs'
    (q_filterSkip _ (panToLab_lines arch prog wc ac perf sc dc mh sp off)) h

/-- Same statement for user sections (not stub labels). -/
theorem panToTarget_user_sections_noStubJumpOrLocValue (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (s' : Sec width) (hs : s' ∈ L')
    (hu : PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false) :
    ∀ x ∈ s'.lines, JumpOk x = true := by
  rcases panToTarget_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs
    with st | ok
  · rw [hu] at st; exact absurd st (by decide)
  · exact ok


/-! ## Witnesses (non-vacuity / tightness) -/

theorem jumpOk_rejects_stub_jump :
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false := by
  simp [JumpOk, aOk, tOk]

theorem jumpOk_rejects_stub_locValue :
    JumpOk (.labAsm (.locValue 3 (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false := by
  simp [JumpOk, aOk, tOk]

theorem jumpOk_accepts_user_locValue :
    JumpOk (.labAsm (.locValue 3 (.lab 64 1)) (0 : BitVec width) [] 0) = true := by
  simp [JumpOk, aOk, tOk, storeConstsStubLocation, wordNumStubs, stackNumStubs]

theorem jc_rejects_locValue_stub :
    JC (.locValue 0 storeConstsStubLocation 0 : HolProg width) = false := by simp [JC]

theorem jc_rejects_return_into_stub :
    JC (.call (some (.skip, 0, storeConstsStubLocation, 0)) (.inl 64) none : HolProg width) = false := by
  simp [JC, sH, tgtOk6, labOk, storeConstsStubLocation, wordNumStubs, stackNumStubs]

theorem flatten_locValue_stub_tight (sid next : Nat) (cs bs : List Nat) :
    ¬ AOk (StackToLab.flattenHOL false (.locValue 0 storeConstsStubLocation 0 : HolProg width)
      sid next cs bs).1 := by
  rw [StackToLab.flattenHOL]; simp [aok_list, JumpOk, aOk, tOk]

/-! ## Instance on the full `PanToTarget.compileProgHOL` pipeline -/

/-- The section list that `Pancake.PanToTarget.compileProgHOL` hands to `removeLabels`
(through `Backend.fromWord → fromStack → fromLab → LabToTarget.compile → compileLab`):
whenever label removal succeeds, every non-stub section has no `jump` / `jumpCmp` / `call` /
`locValue` line into section `storeConstsStubLocation`. Holds for every Pancake program and
every backend configuration. -/
theorem compileProgHOL_sections_avoid_stub (asmConf : AsmConfigExact width)
    (config : Flapjack.Compiler.Backend.Backend.Config) (program : List (Pancake.PanLang.DeclHOL width))
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic asmConf pos labs ffis (filterSkip
        (StackToLab.compile config.stackConf config.dataConf
          (2 * DataToWord.maxHeapLimit width config.dataConf - 1)
          (asmConf.regCount - (asmConf.avoidRegs.length + 3)) asmConf.addrOffset
          (compileNative asmConf config.stackConf.perfCalls
            (WordToWord.compile config.wordToWordConf asmConf
              (panToWordCompileProgHOL asmConf.isa
                (Pancake.PanToTarget.mainFirstHOL program))).2).2.2.2)) = some (L', labs')) :
    ∀ s' ∈ L', PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = true ∨
      ∀ x ∈ s'.lines, JumpOk x = true :=
  panToTarget_noStubJumpOrLocValue asmConf.isa _ config.wordToWordConf asmConf
    config.stackConf.perfCalls config.stackConf config.dataConf _ _ asmConf.addrOffset
    ic pos labs ffis L' labs' h

/-- `compileProgHOL` really is `fromWord` applied to exactly that WordToWord output. -/
theorem compileProgHOL_unfold (asmConf : AsmConfigExact width)
    (config : Flapjack.Compiler.Backend.Backend.Config) (program : List (Pancake.PanLang.DeclHOL width)) :
    ∃ cfg names, Pancake.PanToTarget.compileProgHOL asmConf config program =
      Flapjack.Compiler.Backend.Backend.fromWord asmConf cfg names
        (WordToWord.compile config.wordToWordConf asmConf
          (panToWordCompileProgHOL asmConf.isa (Pancake.PanToTarget.mainFirstHOL program))).2 ∧
      cfg.stackConf = config.stackConf ∧ cfg.dataConf = config.dataConf := by
  unfold Pancake.PanToTarget.compileProgHOL
  exact ⟨_, _, rfl, rfl, rfl⟩


end stack

theorem nsl_rejects_locValue_stub {α : Type} :
    NSL (WordLangProgHOL.locValue (α := α) 0 storeConstsStubLocation) = false := by simp [NSL]

theorem nsl_rejects_return_into_stub {α : Type} :
    NSL (WordLangProgHOL.call (α := α) (some ([], (.ln, .ln), .skip, storeConstsStubLocation, 0))
      (some 64) [] none) = false := by
  simp [NSL, callHdr, labOk, storeConstsStubLocation, wordNumStubs, stackNumStubs]

theorem nsl_accepts_user {α : Type} :
    NSL (WordLangProgHOL.call (α := α) (some ([], (.ln, .ln), .locValue 1 64, 64, 0))
      (some 64) [] none) = true := by
  simp [NSL, callHdr, labOk, storeConstsStubLocation, wordNumStubs, stackNumStubs]


end InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6
