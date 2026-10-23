import InitECandidate.Solver.WordToWordNoStubCall
import InitECandidate.Solver.LabToTargetSectionCleanPreservation

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# StackToLab → LabToTarget: section `storeConstsStubLocation` is unreachable

Starting from the unconditional `WordToWordNoStubCall.panToStackNames_NoSt_and_NoStubCall_unconditional`
(every non-stub body is `StackNoSt` and has no call to the stub label, with **no** Pancake hypothesis),
this module strengthens the stack-level invariant to also bound `rawCall` and `jumpLower` targets,
pushes it through `flattenHOL`/`progToSectionHOL` to a LabLang *line* invariant ("no produced line
names section `storeConstsStubLocation`"), and shows that invariant survives every LabToTarget pass
(`filterSkip`, `encSec`/`encLine`, `encSecsAgain`, `updLabLen`, `padCode`).
-/

namespace InitECandidate.Solver.StackToLabAndLabToTargetNoStubCall

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.PanToStackNoStoreConsts
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts
open InitECandidate.Solver.WordToWordNoStubCall

variable {width : Nat} [NeZero width]

/-! ## Stack-level invariants -/

/-- No direct call (any shape) to the `storeConsts` stub label. -/
def J : HolProg width → Bool
  | .call ret t h =>
      (match t with | .inl n => n != storeConstsStubLocation | .inr _ => true) &&
      (match ret with | none => true | some (r, _, _, _) => J r) &&
      (match h with | none => true | some (q, _, _) => J q)
  | .seq a b => J a && J b
  | .ite _ _ _ a b => J a && J b
  | .loop b => J b
  | .rawCall t => t != storeConstsStubLocation
  | .jumpLower _ _ t => t != storeConstsStubLocation
  | _ => true

def tgtOk : Sum Nat Nat → Bool
  | .inl n => n != storeConstsStubLocation
  | .inr _ => true

/-- Both invariants at once (no `storeConsts`, no call to the stub label). -/
def JC : HolProg width → Bool
  | .storeConsts .. => false
  | .call ret t h =>
      tgtOk t &&
      (match ret with | none => true | some (r, _, _, _) => JC r) &&
      (match h with | none => true | some (q, _, _) => JC q)
  | .seq a b => JC a && JC b
  | .ite _ _ _ a b => JC a && JC b
  | .loop b => JC b
  | .rawCall t => t != storeConstsStubLocation
  | .jumpLower _ _ t => t != storeConstsStubLocation
  | _ => true

theorem clean_eq : ∀ p : HolProg width, JC p = (StackNoSt p && J p)
  | .seq a b => by
      simp only [JC, StackNoSt, J, clean_eq a, clean_eq b]
      cases StackNoSt a <;> cases StackNoSt b <;> cases J a <;> cases J b <;> rfl
  | .ite _ _ _ a b => by
      simp only [JC, StackNoSt, J, clean_eq a, clean_eq b]
      cases StackNoSt a <;> cases StackNoSt b <;> cases J a <;> cases J b <;> rfl
  | .loop a => by simp only [JC, StackNoSt, J, clean_eq a]
  | .call none t none => by cases t <;> rfl
  | .call none t (some (q, _, _)) => by
      simp only [JC, StackNoSt, J, clean_eq q]
      cases t <;> simp only [tgtOk] <;> cases StackNoSt q <;> cases J q <;> simp
  | .call (some (r, _, _, _)) t none => by
      simp only [JC, StackNoSt, J, clean_eq r]
      cases t <;> simp only [tgtOk] <;> cases StackNoSt r <;> cases J r <;> simp
  | .call (some (r, _, _, _)) t (some (q, _, _)) => by
      simp only [JC, StackNoSt, J, clean_eq r, clean_eq q]
      cases t <;> simp only [tgtOk] <;> cases StackNoSt r <;> cases J r <;>
        cases StackNoSt q <;> cases J q <;> simp
  | .skip | .inst .. | .get .. | .set .. | .opCurrHeap ..
  | .jumpLower .. | .alloc .. | .storeConsts .. | .raise .. | .ret ..
  | .break .. | .continue .. | .ffi .. | .tick | .locValue ..
  | .install .. | .shMemOp .. | .codeBufferWrite .. | .dataBufferWrite .. | .rawCall ..
  | .stackAlloc .. | .stackFree .. | .stackStore .. | .stackStoreAny .. | .stackLoad ..
  | .stackLoadAny .. | .stackGetSize .. | .stackSetSize .. | .bitmapLoad .. | .halt .. => by simp [JC, StackNoSt, J]
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
      simp only [JC, Bool.and_eq_true]; exact ⟨hx, hr⟩

theorem c_upshift (r : Nat) : ∀ n, JC (StackRemove.upshift (width := width) r n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.upshift]; split
    · rfl
    · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp only [JC, Bool.and_eq_true, Bool.true_and] at this ⊢
      exact this

theorem c_downshift (r : Nat) : ∀ n, JC (StackRemove.downshift (width := width) r n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.downshift]; split
    · rfl
    · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp only [JC, Bool.and_eq_true, Bool.true_and] at this ⊢
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
        simp only [JC, Bool.and_eq_true]; exact ⟨rfl, this⟩

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
        simp only [JC, Bool.and_eq_true]; exact ⟨h0, this⟩

theorem c_split {a b : HolProg width} (ha : JC a = true) (hb : JC b = true) :
    JC (.seq a b) = true := by
  simp only [JC, Bool.and_eq_true]; exact ⟨ha, hb⟩

/-- StackRemove `comp` keeps both invariants; its `.storeConsts` (copy-loop) branch
is never taken on a `StackNoSt` body (that arm is discharged by contradiction). -/
theorem c_stackRemoveComp (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) :
    ∀ p : HolProg width, JC p = true → JC (StackRemove.comp j bd ptr p) = true
  | .seq a b, h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackRemove.comp]; exact c_split (c_stackRemoveComp j bd ptr a h.1) (c_stackRemoveComp j bd ptr b h.2)
  | .ite c r ri a b, h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackRemove.comp]; simp only [JC, Bool.and_eq_true]; exact ⟨c_stackRemoveComp j bd ptr a h.1, c_stackRemoveComp j bd ptr b h.2⟩
  | .loop a, h => by rw [StackRemove.comp]; exact c_stackRemoveComp j bd ptr a h
  | .call none t none, h => by
      rw [StackRemove.comp]
      simp only [JC, Bool.and_true] at h ⊢; exact h
  | .call none t (some (q, y1, y2)), h => by
      rw [StackRemove.comp]
      simp only [JC, Bool.and_eq_true, Bool.and_true] at h ⊢; exact ⟨h.1, c_stackRemoveComp j bd ptr q h.2⟩
  | .call (some (r, x1, x2, x3)) t none, h => by
      rw [StackRemove.comp]
      simp only [JC, Bool.and_eq_true, Bool.and_true] at h ⊢; exact ⟨h.1, c_stackRemoveComp j bd ptr r h.2⟩
  | .call (some (r, x1, x2, x3)) t (some (q, y1, y2)), h => by
      rw [StackRemove.comp]
      simp only [JC, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, c_stackRemoveComp j bd ptr r h.1.2⟩, c_stackRemoveComp j bd ptr q h.2⟩
  | .storeConsts .., h => by simp [JC, StackNoSt] at h
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
      rw [StackRemove.comp]; exact c_listSeq _ (by simp [JC, addInst, StackRemove.leftShiftInst])
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
      simp only [JC, Bool.and_eq_true] at h
      rw [StackNames.progCompHOL]; exact c_split (c_stackNames f a h.1) (c_stackNames f b h.2)
  | .ite c r ri a b, h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackNames.progCompHOL]; simp only [JC, Bool.and_eq_true]; exact ⟨c_stackNames f a h.1, c_stackNames f b h.2⟩
  | .loop a, h => by rw [StackNames.progCompHOL]; exact c_stackNames f a h
  | .call none t none, h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk (StackNames.destFindNameHOL f t) = tgtOk t := by cases t <;> rfl
      simp only [JC, Bool.and_true, ht] at h ⊢; exact h
  | .call none t (some (q, y1, y2)), h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk (StackNames.destFindNameHOL f t) = tgtOk t := by cases t <;> rfl
      simp only [JC, Bool.and_eq_true, Bool.and_true, ht] at h ⊢; exact ⟨h.1, c_stackNames f q h.2⟩
  | .call (some (r, x1, x2, x3)) t none, h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk (StackNames.destFindNameHOL f t) = tgtOk t := by cases t <;> rfl
      simp only [JC, Bool.and_eq_true, Bool.and_true, ht] at h ⊢; exact ⟨h.1, c_stackNames f r h.2⟩
  | .call (some (r, x1, x2, x3)) t (some (q, y1, y2)), h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk (StackNames.destFindNameHOL f t) = tgtOk t := by cases t <;> rfl
      simp only [JC, Bool.and_eq_true, ht] at h ⊢
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

theorem c_stackAllocComp : ∀ (n m : Nat) (p : HolProg width), JC p = true →
    JC (StackAlloc.comp n m p).1 = true
  | n, m, .seq a b, h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [JC, Bool.and_eq_true]; exact ⟨c_stackAllocComp n m a h.1, c_stackAllocComp n _ b h.2⟩
  | n, m, .ite c r ri a b, h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [JC, Bool.and_eq_true]; exact ⟨c_stackAllocComp n m a h.1, c_stackAllocComp n _ b h.2⟩
  | n, m, .loop a, h => by rw [StackAlloc.comp]; exact c_stackAllocComp n m a h
  | n, m, .call none d e, h => by
      rw [StackAlloc.comp]; rcases e with _ | ⟨q, y1, y2⟩ <;>
        simp only [JC, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢ <;>
        first | exact h | exact h.1
  | n, m, .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [JC, Bool.and_eq_true, Bool.and_true] at h
      rw [StackAlloc.comp]; simp only [JC, Bool.and_eq_true, Bool.and_true]
      exact ⟨h.1, c_stackAllocComp n m p1 h.2⟩
  | n, m, .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [JC, Bool.and_eq_true]
      exact ⟨⟨h.1.1, c_stackAllocComp n m p1 h.1.2⟩, c_stackAllocComp n _ p2 h.2⟩
  | n, m, .alloc _, h => by
      rw [StackAlloc.comp]; simp [JC, tgtOk, gcStubLocation,
        storeConstsStubLocation, wordNumStubs, stackNumStubs]
  | n, m, .storeConsts .., h => by simp [JC, StackNoSt] at h
  | n, m, .skip, h | n, m, .inst .., h | n, m, .get .., h | n, m, .set .., h | n, m, .opCurrHeap .., h
  | n, m, .jumpLower .., h | n, m, .raise .., h | n, m, .ret .., h | n, m, .break .., h | n, m, .continue .., h
  | n, m, .ffi .., h | n, m, .tick, h | n, m, .locValue .., h | n, m, .install .., h | n, m, .shMemOp .., h
  | n, m, .codeBufferWrite .., h | n, m, .dataBufferWrite .., h | n, m, .rawCall .., h | n, m, .stackAlloc .., h | n, m, .stackFree .., h
  | n, m, .stackStore .., h | n, m, .stackStoreAny .., h | n, m, .stackLoad .., h | n, m, .stackLoadAny .., h | n, m, .stackGetSize .., h
  | n, m, .stackSetSize .., h | n, m, .bitmapLoad .., h | n, m, .halt .., h => by
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
        simpa [JC, tgtOk] using hb
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
      simp only [JC, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; exact c_compSeq _ _ _ _ h.2 (c_split (c_rawCallComp info a h.1) (c_rawCallComp info b h.2))
  | .ite c r ri a b, h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [JC, Bool.and_eq_true]; exact ⟨c_rawCallComp info a h.1, c_rawCallComp info b h.2⟩
  | .loop a, h => by rw [StackRawCall.comp]; exact c_rawCallComp info a h
  | .call none d e, h => by rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all)
  | .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [JC, Bool.and_eq_true, Bool.and_true] at h
      rw [StackRawCall.comp]; simp only [JC, Bool.and_eq_true, Bool.and_true]
      exact ⟨h.1, c_rawCallComp info p1 h.2⟩
  | .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [JC, Bool.and_eq_true]
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
    simp only [JC, Bool.and_eq_true] at h
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
  · simp [J, hg]

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
  · simp only [J, Bool.and_eq_true]
    exact ⟨n_copyRetAux _ _ _, n_seqStackFree _ _ h⟩

theorem n_stackMove (offset i : Nat) (p : HolProg width) (h : J p = true) :
    ∀ n start, J (stackMoveNative n start offset i p) = true := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih => intro s; rw [stackMoveNative]; simp only [J, Bool.and_true]; exact ih _

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

theorem n_pushHandler {β γ : Type} (perf : Bool) (l1 l2 : Nat) (kf : Nat × β × γ) :
    J (pushHandlerNative (width := width) perf l1 l2 kf) = true := by
  unfold pushHandlerNative; cases perf <;> rfl

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
      (kf : Nat × Nat × Nat), StackRemoveAndNamesNoStoreConsts.WordNoStubCall p = true → J (compNative conf perf p bs kf).1 = true
  | .seq a b, bs, kf, h => by
      simp only [StackRemoveAndNamesNoStoreConsts.WordNoStubCall, Bool.and_eq_true] at h
      rw [compNative]; simp only [J, Bool.and_eq_true]
      exact ⟨n_compNative conf perf a _ _ h.1, n_compNative conf perf b _ _ h.2⟩
  | .ite c r ri a b, bs, kf, h => by
      simp only [StackRemoveAndNamesNoStoreConsts.WordNoStubCall, Bool.and_eq_true] at h
      have ha := n_compNative conf perf a bs kf h.1
      have hb := n_compNative conf perf b (compNative conf perf a bs kf).2 kf h.2
      rw [compNative]; dsimp only
      split
      · rw [n_stackLoad]; simp only [J, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · split
        · rw [n_stackLoad]; simp only [J, Bool.and_eq_true]; exact ⟨ha, hb⟩
        · simp only [J, Bool.true_and]; rw [n_stackLoad]
          simp only [J, Bool.and_eq_true]; exact ⟨ha, hb⟩
  | .mustTerminate a, bs, kf, h => by rw [compNative]; exact n_compNative conf perf a _ _ h
  | .loop x a y, bs, kf, h => by
      rw [compNative]; exact n_compNative conf perf a _ _ h
  | .call none d args hd, bs, kf, h => by
      have hdn : d ≠ some storeConstsStubLocation := by
        intro e; subst e; unfold StackRemoveAndNamesNoStoreConsts.WordNoStubCall at h; simp only [bne_self_eq_false, Bool.false_and] at h; exact Bool.false_ne_true h
      obtain ⟨hq0, hdst⟩ := n_callDest (width := width) d args kf hdn
      rw [compNative]
      rcases hc : callDestNative (width := width) d args kf with ⟨q0, dst⟩
      rw [hc] at hq0 hdst; dsimp only at hq0 hdst ⊢
      simp only [J, Bool.and_eq_true, Bool.and_true]
      refine ⟨hq0, n_seqStackFree _ _ ?_⟩
      simp only [J, Bool.and_true]; exact hdst
  | .call (some (vs, live, rc, l1, l2)) d args none, bs, kf, h => by
      have hdn : d ≠ some storeConstsStubLocation := by
        intro e; subst e; unfold StackRemoveAndNamesNoStoreConsts.WordNoStubCall at h; simp only [bne_self_eq_false, Bool.false_and] at h; exact Bool.false_ne_true h
      simp only [StackRemoveAndNamesNoStoreConsts.WordNoStubCall, Bool.and_eq_true, Bool.and_true] at h
      have hr := n_compNative conf perf rc (wLiveNative live bs kf).2 kf h.2
      obtain ⟨hq0, hdst⟩ := n_callDest (width := width) d args kf hdn
      rw [compNative]
      rcases hc : callDestNative (width := width) d args kf with ⟨q0, dst⟩
      rw [hc] at hq0 hdst; dsimp only at hq0 hdst ⊢
      simp only [J, Bool.and_eq_true, Bool.and_true]
      refine ⟨hq0, n_wLive _ _ _, n_stackArgs _ _ _, ?_, hdst, ?_, n_copyRet _ _ _ _ _ hr⟩
      · split <;> rfl
      · split <;> rfl
  | .call (some (vs, live, rc, l1, l2)) d args (some (e, hc', h1, h2)), bs, kf, h => by
      have hdn : d ≠ some storeConstsStubLocation := by
        intro e; subst e; unfold StackRemoveAndNamesNoStoreConsts.WordNoStubCall at h; simp only [bne_self_eq_false, Bool.false_and] at h; exact Bool.false_ne_true h
      simp only [StackRemoveAndNamesNoStoreConsts.WordNoStubCall, Bool.and_eq_true] at h
      have hr := n_compNative conf perf rc (wLiveNative live bs kf).2 kf h.1.2
      have hh := n_compNative conf perf hc'
        (compNative conf perf rc (wLiveNative live bs kf).2 kf).2 kf h.2
      obtain ⟨hq0, hdst⟩ := n_callDest (width := width) d args kf hdn
      rw [compNative]
      rcases hc : callDestNative (width := width) d args kf with ⟨q0, dst⟩
      rw [hc] at hq0 hdst; dsimp only at hq0 hdst ⊢
      simp only [J, Bool.and_eq_true]
      refine ⟨hq0, n_wLive _ _ _, n_pushHandler _ _ _ _, n_stackArgs _ _ _, ?_,
        ⟨hdst, ?_, n_copyRet _ _ _ _ _ (n_popHandler _ _ _ hr)⟩, hh⟩
      · split <;> rfl
      · split <;> rfl
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
      rw [compNative]; exact n_regWrite1 (fun n => .locValue n l 0) d kf (fun _ => rfl)
  | .alloc _ live, bs, kf, h => by
      rw [compNative]; simp only [J, Bool.and_true]; exact n_wLive _ _ _
  | .install .., bs, kf, h | .codeBufferWrite .., bs, kf, h | .dataBufferWrite .., bs, kf, h => by
      rw [compNative] <;> (try dsimp only) <;> rw [n_stackLoad] <;> rfl
  | .shareInst op v e, bs, kf, h => by
      rw [compNative]; split
      · rfl
      · exact n_wShareInst _ _ _ _
  | .raise .., _, _, _ => by rw [compNative]; simp [J, raiseStubLocation, storeConstsStubLocation, wordNumStubs, stackNumStubs]
  | .skip, _, _, _ | .tick, _, _, _ | .break .., _, _, _
  | .continue .., _, _, _ | .ffi .., _, _, _ | .assign .., _, _, _ | .store .., _, _, _ => by
      rw [compNative] <;> first | rfl | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)


theorem n_compileWordToStack {β : Type} (conf : AsmConfigExact width) (perf : Bool) (rc : Nat) :
    ∀ (progs : List (β × Nat × WordLangProgHOL (BitVec width))) (bs : AppList (BitVec width) × Nat),
      (∀ x ∈ progs, NoSt x.2.2 = true ∧ StackRemoveAndNamesNoStoreConsts.WordNoStubCall x.2.2 = true) →
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
          simp only [J, Bool.true_and]; exact n_compNative conf perf p _ _ hp.2
      · exact n_compileWordToStack conf perf rc ps _
          (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy

/-- Top-level WordToStack: every entry is either the `storeConsts` stub itself or `JC`. -/
theorem c_compileNative (conf : AsmConfigExact width) (perf : Bool)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, NoSt x.2.2 = true ∧ StackRemoveAndNamesNoStoreConsts.WordNoStubCall x.2.2 = true) :
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
    (f : Spt Nat) (n : Nat) (p : HolProg width) (h : JC p = true) :
    JC (StackNames.progCompHOL f (StackRemove.comp j bd ptr
      (StackAlloc.progComp (n, StackRawCall.compTop info p)).2)) = true := by
  apply c_stackNames; apply c_stackRemoveComp
  unfold StackAlloc.progComp; exact c_stackAllocComp _ _ _ (c_rawCallCompTop info p h)


/-! ## LabLang line invariant -/

/-- A label target that is not inside the `storeConsts` stub section. -/
def tOk : LabLang.Lab → Bool
  | .lab s _ => s != storeConstsStubLocation

/-- Control-transfer instructions (`jump`, `jumpCmp`, `call`) never target section 6. -/
def aOk : AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString → Bool
  | .jump t => tOk t
  | .jumpCmp _ _ _ t => tOk t
  | .call t => tOk t
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

theorem jo_compileJump (t : Sum Nat Nat) (h : tgtOk t = true) :
    JumpOk (StackToLab.compileJumpHOL (width := width) t) = true := by
  cases t <;> simp_all [StackToLab.compileJumpHOL, JumpOk, aOk, tOk, tgtOk]

@[simp] theorem jo_label (a b c : Nat) : JumpOk (.label a b c : LabSem.LabLineHOL width) = true := rfl
@[simp] theorem jo_asm (a : AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) (b : List (BitVec 8)) (c : Nat) :
    JumpOk (.asm a b c : LabSem.LabLineHOL width) = true := rfl
@[simp] theorem jo_loc (r : Nat) (t : LabLang.Lab) (w : BitVec width) (b : List (BitVec 8)) (c : Nat) :
    JumpOk (.labAsm (.locValue r t) w b c : LabSem.LabLineHOL width) = true := rfl
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
    {hd : Option (HolProg width × Nat × Nat)} (h : JC (.call ret t hd) = true) : tgtOk t = true := by
  rcases ret with _ | ⟨r, a, b, c⟩ <;> rcases hd with _ | ⟨q, a', b'⟩ <;>
    simp only [JC, Bool.and_eq_true, Bool.and_true] at h <;> first | exact h | exact h.1 | exact h.1.1

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
      split <;> simp_all [aok_append, aok_list, jo_jump, jo_jcmp, jo_compileJump]
  | .ite c r ri a b, tail, sid, next, conts, breaks, hs, h => by
      simp only [JC, Bool.and_eq_true] at h
      rw [StackToLab.flattenHOL]
      rcases ea : StackToLab.flattenHOL false a sid next conts breaks with ⟨xs, nr1, n1⟩
      rcases eb : StackToLab.flattenHOL false b sid n1 conts breaks with ⟨ys, nr2, n2⟩
      have hxs : AOk xs := by have := f_ok a false sid next conts breaks hs h.1; rw [ea] at this; exact this
      have hys : AOk ys := by have := f_ok b false sid n1 conts breaks hs h.2; rw [eb] at this; exact this
      simp only [ea, eb]
      split_ifs <;> simp_all [aok_append, aok_list, jo_jump, jo_jcmp, jo_compileJump]
  | .loop a, tail, sid, next, conts, breaks, hs, h => by
      simp only [JC] at h
      rw [StackToLab.flattenHOL]
      rcases ea : StackToLab.flattenHOL false a sid (next + 2) (next :: conts) ((next + 1) :: breaks)
        with ⟨xs, nr1, n1⟩
      have hxs : AOk xs := by
        have := f_ok a false sid (next + 2) (next :: conts) ((next + 1) :: breaks) hs h
        rw [ea] at this; exact this
      simp only [ea]
      simp_all [aok_append, aok_list, jo_jump, jo_jcmp, jo_compileJump]
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
      simp_all [aok_append, aok_list, jo_jump, jo_jcmp, jo_compileJump]
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
      simp_all [aok_append, aok_list, jo_jump, jo_jcmp, jo_compileJump]
  | .rawCall t, tail, sid, next, conts, breaks, hs, h => by
      simp only [JC] at h
      rw [StackToLab.flattenHOL]; simp_all [aok_append, aok_list, jo_jump, jo_jcmp, jo_compileJump]
  | .jumpLower l r t, tail, sid, next, conts, breaks, hs, h => by
      simp only [JC] at h
      rw [StackToLab.flattenHOL]; simp_all [aok_append, aok_list, jo_jump, jo_jcmp, jo_compileJump]
  | .break i, tail, sid, next, conts, breaks, hs, h
  | .continue i, tail, sid, next, conts, breaks, hs, h => by
      rw [StackToLab.flattenHOL]; simp_all [aok_append, aok_list, jo_jump, jo_jcmp, jo_compileJump]
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
      rw [StackToLab.flattenHOL] <;> simp_all [aok_append, aok_list, jo_jump, jo_jcmp, jo_compileJump]
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
  dsimp only at hsnd; subst hsnd
  unfold StackAlloc.progComp
  exact c_stackAllocComp _ _ _ (c_rawCallCompTop info x.2 hok)

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
       WordToWordNoStubCall.panToWordToWord_NoStubCall arch prog wc ac x hx⟩))

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
theorem panToTarget_noStubJump (arch : AsmArchitecture)
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
theorem panToTarget_user_sections_noStubJump (arch : AsmArchitecture)
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
  rcases panToTarget_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs
    with st | ok
  · rw [hu] at st; exact absurd st (by decide)
  · exact ok

/-! ## Witnesses (non-vacuity / tightness) -/

theorem jumpOk_rejects_stub :
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false := by
  simp [JumpOk, aOk, tOk]

theorem jumpOk_accepts_user :
    JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true := by
  simp [JumpOk, aOk, tOk, storeConstsStubLocation, wordNumStubs, stackNumStubs]

theorem jc_rejects_rawCall_stub : JC (.rawCall storeConstsStubLocation : HolProg width) = false := by
  simp [JC]

theorem flatten_rawCall_stub_tight (sid next : Nat) (cs bs : List Nat) :
    ¬ AOk (StackToLab.flattenHOL false (.rawCall storeConstsStubLocation : HolProg width) sid next cs bs).1 := by
  rw [StackToLab.flattenHOL]; simp [aok_list, JumpOk, aOk, tOk]


end InitECandidate.Solver.StackToLabAndLabToTargetNoStubCall
