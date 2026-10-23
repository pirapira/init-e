import InitECandidate.Solver.PanToStackNoStoreConsts
import Flapjack.Compiler.Backend.StackToLab.Compile

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.PanToStackNoStoreConsts

variable {width : Nat} [NeZero width]

/-! ## Stack-level invariants -/

/-- No direct call (any shape) to the `storeConsts` stub label. -/
def NoStubCall : HolProg width → Bool
  | .call ret t h =>
      (match t with | .inl n => n != storeConstsStubLocation | .inr _ => true) &&
      (match ret with | none => true | some (r, _, _, _) => NoStubCall r) &&
      (match h with | none => true | some (q, _, _) => NoStubCall q)
  | .seq a b => NoStubCall a && NoStubCall b
  | .ite _ _ _ a b => NoStubCall a && NoStubCall b
  | .loop b => NoStubCall b
  | _ => true

def tgtOk : Sum Nat Nat → Bool
  | .inl n => n != storeConstsStubLocation
  | .inr _ => true

/-- Both invariants at once (no `storeConsts`, no call to the stub label). -/
def Clean : HolProg width → Bool
  | .storeConsts .. => false
  | .call ret t h =>
      tgtOk t &&
      (match ret with | none => true | some (r, _, _, _) => Clean r) &&
      (match h with | none => true | some (q, _, _) => Clean q)
  | .seq a b => Clean a && Clean b
  | .ite _ _ _ a b => Clean a && Clean b
  | .loop b => Clean b
  | _ => true

theorem clean_eq : ∀ p : HolProg width, Clean p = (StackNoSt p && NoStubCall p)
  | .seq a b => by
      simp only [Clean, StackNoSt, NoStubCall, clean_eq a, clean_eq b]
      cases StackNoSt a <;> cases StackNoSt b <;> cases NoStubCall a <;> cases NoStubCall b <;> rfl
  | .ite _ _ _ a b => by
      simp only [Clean, StackNoSt, NoStubCall, clean_eq a, clean_eq b]
      cases StackNoSt a <;> cases StackNoSt b <;> cases NoStubCall a <;> cases NoStubCall b <;> rfl
  | .loop a => by simp only [Clean, StackNoSt, NoStubCall, clean_eq a]
  | .call none t none => by cases t <;> rfl
  | .call none t (some (q, _, _)) => by
      simp only [Clean, StackNoSt, NoStubCall, clean_eq q]
      cases t <;> simp only [tgtOk] <;> cases StackNoSt q <;> cases NoStubCall q <;> simp
  | .call (some (r, _, _, _)) t none => by
      simp only [Clean, StackNoSt, NoStubCall, clean_eq r]
      cases t <;> simp only [tgtOk] <;> cases StackNoSt r <;> cases NoStubCall r <;> simp
  | .call (some (r, _, _, _)) t (some (q, _, _)) => by
      simp only [Clean, StackNoSt, NoStubCall, clean_eq r, clean_eq q]
      cases t <;> simp only [tgtOk] <;> cases StackNoSt r <;> cases NoStubCall r <;>
        cases StackNoSt q <;> cases NoStubCall q <;> simp
  | .skip | .inst .. | .get .. | .set .. | .opCurrHeap ..
  | .jumpLower .. | .alloc .. | .storeConsts .. | .raise .. | .ret ..
  | .break .. | .continue .. | .ffi .. | .tick | .locValue ..
  | .install .. | .shMemOp .. | .codeBufferWrite .. | .dataBufferWrite .. | .rawCall ..
  | .stackAlloc .. | .stackFree .. | .stackStore .. | .stackStoreAny .. | .stackLoad ..
  | .stackLoadAny .. | .stackGetSize .. | .stackSetSize .. | .bitmapLoad .. | .halt .. => by simp [Clean, StackNoSt, NoStubCall]
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem clean_of {p : HolProg width} (h1 : StackNoSt p = true) (h2 : NoStubCall p = true) :
    Clean p = true := by rw [clean_eq, h1, h2]; rfl

theorem of_clean {p : HolProg width} (h : Clean p = true) :
    StackNoSt p = true ∧ NoStubCall p = true := by
  rw [clean_eq, Bool.and_eq_true] at h; exact h

/-! ### small StackRemove helpers -/

theorem c_listSeq : ∀ (l : List (HolProg width)), (∀ x ∈ l, Clean x = true) →
    Clean (listSeqHOL l) = true
  | [], _ => rfl
  | [x], h => by rw [listSeqHOL]; exact h x (List.mem_singleton_self x)
  | x :: y :: ys, h => by
      rw [listSeqHOL]
      have hx := h x (List.mem_cons_self ..)
      have hr := c_listSeq (y :: ys) (fun z hz => h z (List.mem_cons_of_mem _ hz))
      simp only [Clean, Bool.and_eq_true]; exact ⟨hx, hr⟩

theorem c_upshift (r : Nat) : ∀ n, Clean (StackRemove.upshift (width := width) r n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.upshift]; split
    · rfl
    · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp only [Clean, Bool.and_eq_true, Bool.true_and] at this ⊢
      exact this

theorem c_downshift (r : Nat) : ∀ n, Clean (StackRemove.downshift (width := width) r n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.downshift]; split
    · rfl
    · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp only [Clean, Bool.and_eq_true, Bool.true_and] at this ⊢
      exact this

theorem c_stackFree (ptr : Nat) : ∀ n, Clean (StackRemove.stackFree (width := width) ptr n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.stackFree]; split
    · rfl
    · split
      · rfl
      · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
        simp only [Clean, Bool.and_eq_true]; exact ⟨rfl, this⟩

theorem c_singleStackAlloc (j : Bool) (ptr n : Nat) :
    Clean (StackRemove.singleStackAlloc (width := width) j ptr n) = true := by
  unfold StackRemove.singleStackAlloc; split <;> rfl

theorem c_stackAlloc (j : Bool) (ptr : Nat) :
    ∀ n, Clean (StackRemove.stackAlloc (width := width) j ptr n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.stackAlloc]; split
    · rfl
    · split
      · exact c_singleStackAlloc _ _ _
      · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
        have h0 := c_singleStackAlloc (width := width) j ptr StackRemove.maxStackAlloc
        simp only [Clean, Bool.and_eq_true]; exact ⟨h0, this⟩

theorem c_split {a b : HolProg width} (ha : Clean a = true) (hb : Clean b = true) :
    Clean (.seq a b) = true := by
  simp only [Clean, Bool.and_eq_true]; exact ⟨ha, hb⟩

/-- StackRemove `comp` keeps both invariants; its `.storeConsts` (copy-loop) branch
is never taken on a `StackNoSt` body (that arm is discharged by contradiction). -/
theorem c_stackRemoveComp (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) :
    ∀ p : HolProg width, Clean p = true → Clean (StackRemove.comp j bd ptr p) = true
  | .seq a b, h => by
      simp only [Clean, Bool.and_eq_true] at h
      rw [StackRemove.comp]; exact c_split (c_stackRemoveComp j bd ptr a h.1) (c_stackRemoveComp j bd ptr b h.2)
  | .ite c r ri a b, h => by
      simp only [Clean, Bool.and_eq_true] at h
      rw [StackRemove.comp]; simp only [Clean, Bool.and_eq_true]; exact ⟨c_stackRemoveComp j bd ptr a h.1, c_stackRemoveComp j bd ptr b h.2⟩
  | .loop a, h => by rw [StackRemove.comp]; exact c_stackRemoveComp j bd ptr a h
  | .call none t none, h => by
      rw [StackRemove.comp]
      simp only [Clean, Bool.and_true] at h ⊢; exact h
  | .call none t (some (q, y1, y2)), h => by
      rw [StackRemove.comp]
      simp only [Clean, Bool.and_eq_true, Bool.and_true] at h ⊢; exact ⟨h.1, c_stackRemoveComp j bd ptr q h.2⟩
  | .call (some (r, x1, x2, x3)) t none, h => by
      rw [StackRemove.comp]
      simp only [Clean, Bool.and_eq_true, Bool.and_true] at h ⊢; exact ⟨h.1, c_stackRemoveComp j bd ptr r h.2⟩
  | .call (some (r, x1, x2, x3)) t (some (q, y1, y2)), h => by
      rw [StackRemove.comp]
      simp only [Clean, Bool.and_eq_true] at h ⊢
      exact ⟨⟨h.1.1, c_stackRemoveComp j bd ptr r h.1.2⟩, c_stackRemoveComp j bd ptr q h.2⟩
  | .storeConsts .., h => by simp [Clean, StackNoSt] at h
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
      rw [StackRemove.comp]; exact c_listSeq _ (by simp [Clean, addInst, StackRemove.leftShiftInst])
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
    ∀ p : HolProg width, Clean p = true → Clean (StackNames.progCompHOL f p) = true
  | .seq a b, h => by
      simp only [Clean, Bool.and_eq_true] at h
      rw [StackNames.progCompHOL]; exact c_split (c_stackNames f a h.1) (c_stackNames f b h.2)
  | .ite c r ri a b, h => by
      simp only [Clean, Bool.and_eq_true] at h
      rw [StackNames.progCompHOL]; simp only [Clean, Bool.and_eq_true]; exact ⟨c_stackNames f a h.1, c_stackNames f b h.2⟩
  | .loop a, h => by rw [StackNames.progCompHOL]; exact c_stackNames f a h
  | .call none t none, h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk (StackNames.destFindNameHOL f t) = tgtOk t := by cases t <;> rfl
      simp only [Clean, Bool.and_true, ht] at h ⊢; exact h
  | .call none t (some (q, y1, y2)), h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk (StackNames.destFindNameHOL f t) = tgtOk t := by cases t <;> rfl
      simp only [Clean, Bool.and_eq_true, Bool.and_true, ht] at h ⊢; exact ⟨h.1, c_stackNames f q h.2⟩
  | .call (some (r, x1, x2, x3)) t none, h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk (StackNames.destFindNameHOL f t) = tgtOk t := by cases t <;> rfl
      simp only [Clean, Bool.and_eq_true, Bool.and_true, ht] at h ⊢; exact ⟨h.1, c_stackNames f r h.2⟩
  | .call (some (r, x1, x2, x3)) t (some (q, y1, y2)), h => by
      rw [StackNames.progCompHOL]
      have ht : tgtOk (StackNames.destFindNameHOL f t) = tgtOk t := by cases t <;> rfl
      simp only [Clean, Bool.and_eq_true, ht] at h ⊢
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

theorem c_stackAllocComp : ∀ (n m : Nat) (p : HolProg width), Clean p = true →
    Clean (StackAlloc.comp n m p).1 = true
  | n, m, .seq a b, h => by
      simp only [Clean, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [Clean, Bool.and_eq_true]; exact ⟨c_stackAllocComp n m a h.1, c_stackAllocComp n _ b h.2⟩
  | n, m, .ite c r ri a b, h => by
      simp only [Clean, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [Clean, Bool.and_eq_true]; exact ⟨c_stackAllocComp n m a h.1, c_stackAllocComp n _ b h.2⟩
  | n, m, .loop a, h => by rw [StackAlloc.comp]; exact c_stackAllocComp n m a h
  | n, m, .call none d e, h => by
      rw [StackAlloc.comp]; rcases e with _ | ⟨q, y1, y2⟩ <;>
        simp only [Clean, Bool.and_eq_true, Bool.true_and, Bool.and_true] at h ⊢ <;>
        first | exact h | exact h.1
  | n, m, .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [Clean, Bool.and_eq_true, Bool.and_true] at h
      rw [StackAlloc.comp]; simp only [Clean, Bool.and_eq_true, Bool.and_true]
      exact ⟨h.1, c_stackAllocComp n m p1 h.2⟩
  | n, m, .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [Clean, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [Clean, Bool.and_eq_true]
      exact ⟨⟨h.1.1, c_stackAllocComp n m p1 h.1.2⟩, c_stackAllocComp n _ p2 h.2⟩
  | n, m, .alloc _, h => by
      rw [StackAlloc.comp]; simp [Clean, tgtOk, gcStubLocation,
        storeConstsStubLocation, wordNumStubs, stackNumStubs]
  | n, m, .storeConsts .., h => by simp [Clean, StackNoSt] at h
  | n, m, .skip, h | n, m, .inst .., h | n, m, .get .., h | n, m, .set .., h | n, m, .opCurrHeap .., h
  | n, m, .jumpLower .., h | n, m, .raise .., h | n, m, .ret .., h | n, m, .break .., h | n, m, .continue .., h
  | n, m, .ffi .., h | n, m, .tick, h | n, m, .locValue .., h | n, m, .install .., h | n, m, .shMemOp .., h
  | n, m, .codeBufferWrite .., h | n, m, .dataBufferWrite .., h | n, m, .rawCall .., h | n, m, .stackAlloc .., h | n, m, .stackFree .., h
  | n, m, .stackStore .., h | n, m, .stackStoreAny .., h | n, m, .stackLoad .., h | n, m, .stackLoadAny .., h | n, m, .stackGetSize .., h
  | n, m, .stackSetSize .., h | n, m, .bitmapLoad .., h | n, m, .halt .., h => by
      rw [StackAlloc.comp] <;> first | exact h | (intros; simp_all) | skip
termination_by _ _ p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem c_compSeq (a b fb : HolProg width) (info : Spt Nat) (hfb : Clean fb = true) :
    Clean (StackRawCall.compSeq a b info fb) = true := by
  unfold StackRawCall.compSeq; split
  · exact hfb
  · split
    · exact hfb
    · split
      · rfl
      · split <;> rfl

theorem c_rawCallComp (info : Spt Nat) :
    ∀ p : HolProg width, Clean p = true → Clean (StackRawCall.comp info p) = true
  | .seq a b, h => by
      simp only [Clean, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; exact c_compSeq _ _ _ _ (c_split (c_rawCallComp info a h.1) (c_rawCallComp info b h.2))
  | .ite c r ri a b, h => by
      simp only [Clean, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [Clean, Bool.and_eq_true]; exact ⟨c_rawCallComp info a h.1, c_rawCallComp info b h.2⟩
  | .loop a, h => by rw [StackRawCall.comp]; exact c_rawCallComp info a h
  | .call none d e, h => by rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all)
  | .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [Clean, Bool.and_eq_true, Bool.and_true] at h
      rw [StackRawCall.comp]; simp only [Clean, Bool.and_eq_true, Bool.and_true]
      exact ⟨h.1, c_rawCallComp info p1 h.2⟩
  | .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [Clean, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [Clean, Bool.and_eq_true]
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

theorem c_rawCallCompTop (info : Spt Nat) (p : HolProg width) (h : Clean p = true) :
    Clean (StackRawCall.compTop info p) = true := by
  rw [StackRawCall.compTop.eq_def]; split
  · rename_i a b
    simp only [Clean, Bool.and_eq_true] at h
    exact c_split (c_rawCallComp info a h.1) (c_rawCallComp info b h.2)
  · exact c_rawCallComp info p h

/-! ## WordToStack: no stub call, under a WordLang call-target hypothesis -/

/-- No WordLang call targets the `storeConsts` stub label. -/
def WordNoStubCall {α : Type} : WordLangProgHOL α → Bool
  | .mustTerminate b => WordNoStubCall b
  | .seq a b => WordNoStubCall a && WordNoStubCall b
  | .ite _ _ _ a b => WordNoStubCall a && WordNoStubCall b
  | .loop _ b _ => WordNoStubCall b
  | .call ret d _ h =>
      (d != some storeConstsStubLocation) &&
      (match ret with | none => true | some (_, _, r, _, _) => WordNoStubCall r) &&
      (match h with | none => true | some (_, p, _, _) => WordNoStubCall p)
  | _ => true

theorem n_stackLoad : ∀ (l : List (Nat × Nat)) (x : HolProg width),
    NoStubCall (wStackLoadNative l x) = NoStubCall x
  | [], x => rfl
  | (r, i) :: ps, x => by
      simp only [wStackLoadNative, NoStubCall, Bool.true_and]; exact n_stackLoad ps x

theorem n_regWrite1 (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (hg : ∀ n, NoStubCall (g n) = true) : NoStubCall (wRegWrite1Native g r kf) = true := by
  unfold wRegWrite1Native; dsimp only; split
  · exact hg _
  · simp [NoStubCall, hg]

theorem n_wInst (i : HolInst width) (kf : Nat × Nat × Nat) :
    NoStubCall (wInstNative i kf) = true := by
  unfold wInstNative
  split <;> (try simp only [n_stackLoad]) <;>
    first | rfl | (apply n_regWrite1; intro n; rfl)

theorem n_wMoveAux : ∀ (l : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat),
    NoStubCall (wMoveAuxNative (width := width) l kf) = true
  | [], _ => rfl
  | [xy], kf => by
      rw [wMoveAuxNative]; unfold wMoveSingleNative; split <;> rfl
  | xy :: y :: ys, kf => by
      simp only [wMoveAuxNative, NoStubCall, Bool.and_eq_true]
      refine ⟨?_, n_wMoveAux (y :: ys) kf⟩
      unfold wMoveSingleNative; split <;> rfl

theorem n_seqStackFree (n : Nat) (p : HolProg width) (h : NoStubCall p = true) :
    NoStubCall (seqStackFreeNative n p) = true := by
  unfold seqStackFreeNative; split
  · exact h
  · simpa [NoStubCall] using h

theorem n_copyRetAux (k f : Nat) : ∀ n, NoStubCall (copyRetAuxNative (width := width) k f n) = true
  | 0 => rfl
  | n + 1 => by
      rw [copyRetAuxNative]; simp only [listSeq, NoStubCall, Bool.true_and]
      exact n_copyRetAux k f n

theorem n_copyRet {β γ : Type} (perf ih : Bool) (kf : Nat × Nat × γ) (vs : List β)
    (kont : HolProg width) (h : NoStubCall kont = true) :
    NoStubCall (copyRetNative perf ih kf vs kont) = true := by
  unfold copyRetNative; dsimp only; split
  · exact h
  · simp only [NoStubCall, Bool.and_eq_true]
    exact ⟨n_copyRetAux _ _ _, n_seqStackFree _ _ h⟩

theorem n_stackMove (offset i : Nat) (p : HolProg width) (h : NoStubCall p = true) :
    ∀ n start, NoStubCall (stackMoveNative n start offset i p) = true := by
  intro n
  induction n with
  | zero => intro _; exact h
  | succ n ih => intro s; rw [stackMoveNative]; simp only [NoStubCall, Bool.and_true]; exact ih _

theorem n_stackArgs {α β : Type} (d : Sum α β) (ac : Nat) (kf : Nat × Nat × Nat) :
    NoStubCall (stackArgsNative (width := width) d ac kf) = true := by
  unfold stackArgsNative; exact n_stackMove _ _ _ rfl _ _

theorem n_callDest (pos : Option Nat) (args : List Nat) (kf : Nat × Nat × Nat)
    (hp : pos ≠ some storeConstsStubLocation) :
    NoStubCall (callDestNative (width := width) pos args kf).1 = true ∧
    (match (callDestNative (width := width) pos args kf).2 with
      | .inl n => n != storeConstsStubLocation | .inr _ => true) = true := by
  unfold callDestNative; split
  · rename_i p; refine ⟨rfl, ?_⟩; simp only [bne_iff_ne, ne_eq]; intro e; exact hp (by rw [e])
  · split
    · exact ⟨rfl, by simp [raiseStubLocation, storeConstsStubLocation, wordNumStubs, stackNumStubs]⟩
    · dsimp only; rw [n_stackLoad]; exact ⟨rfl, rfl⟩

theorem n_wMove (m : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    NoStubCall (wMoveNative (width := width) m kf) = true := by
  unfold wMoveNative; exact n_wMoveAux _ _

theorem n_pushHandler {β γ : Type} (perf : Bool) (l1 l2 : Nat) (kf : Nat × β × γ) :
    NoStubCall (pushHandlerNative (width := width) perf l1 l2 kf) = true := by
  unfold pushHandlerNative; cases perf <;> rfl

theorem n_popHandler {β γ : Type} (perf : Bool) (kf : Nat × β × γ) (p : HolProg width)
    (h : NoStubCall p = true) : NoStubCall (popHandlerNative perf kf p) = true := by
  unfold popHandlerNative; simpa [NoStubCall] using h

theorem n_wLive (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : NoStubCall (wLiveNative live bs kf).1 = true := by
  unfold wLiveNative; split <;> rfl

theorem n_wShareInst (op : HolMemop) (v : Nat) (a : HolAddr width) (kf : Nat × Nat × Nat) :
    NoStubCall (wShareInstNative op v a kf) = true := by
  unfold wShareInstNative
  split <;> (try simp only [n_stackLoad]) <;> first | rfl | (apply n_regWrite1; intro n; rfl)

theorem n_compNative (conf : AsmConfigExact width) (perf : Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
      (kf : Nat × Nat × Nat), WordNoStubCall p = true → NoStubCall (compNative conf perf p bs kf).1 = true
  | .seq a b, bs, kf, h => by
      simp only [WordNoStubCall, Bool.and_eq_true] at h
      rw [compNative]; simp only [NoStubCall, Bool.and_eq_true]
      exact ⟨n_compNative conf perf a _ _ h.1, n_compNative conf perf b _ _ h.2⟩
  | .ite c r ri a b, bs, kf, h => by
      simp only [WordNoStubCall, Bool.and_eq_true] at h
      have ha := n_compNative conf perf a bs kf h.1
      have hb := n_compNative conf perf b (compNative conf perf a bs kf).2 kf h.2
      rw [compNative]; dsimp only
      split
      · rw [n_stackLoad]; simp only [NoStubCall, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · split
        · rw [n_stackLoad]; simp only [NoStubCall, Bool.and_eq_true]; exact ⟨ha, hb⟩
        · simp only [NoStubCall, Bool.true_and]; rw [n_stackLoad]
          simp only [NoStubCall, Bool.and_eq_true]; exact ⟨ha, hb⟩
  | .mustTerminate a, bs, kf, h => by rw [compNative]; exact n_compNative conf perf a _ _ h
  | .loop x a y, bs, kf, h => by
      rw [compNative]; exact n_compNative conf perf a _ _ h
  | .call none d args hd, bs, kf, h => by
      have hdn : d ≠ some storeConstsStubLocation := by
        intro e; subst e; unfold WordNoStubCall at h; simp only [bne_self_eq_false, Bool.false_and] at h; exact Bool.false_ne_true h
      obtain ⟨hq0, hdst⟩ := n_callDest (width := width) d args kf hdn
      rw [compNative]
      rcases hc : callDestNative (width := width) d args kf with ⟨q0, dst⟩
      rw [hc] at hq0 hdst; dsimp only at hq0 hdst ⊢
      simp only [NoStubCall, Bool.and_eq_true, Bool.and_true]
      refine ⟨hq0, n_seqStackFree _ _ ?_⟩
      simp only [NoStubCall, Bool.and_true]; exact hdst
  | .call (some (vs, live, rc, l1, l2)) d args none, bs, kf, h => by
      have hdn : d ≠ some storeConstsStubLocation := by
        intro e; subst e; unfold WordNoStubCall at h; simp only [bne_self_eq_false, Bool.false_and] at h; exact Bool.false_ne_true h
      simp only [WordNoStubCall, Bool.and_eq_true, Bool.and_true] at h
      have hr := n_compNative conf perf rc (wLiveNative live bs kf).2 kf h.2
      obtain ⟨hq0, hdst⟩ := n_callDest (width := width) d args kf hdn
      rw [compNative]
      rcases hc : callDestNative (width := width) d args kf with ⟨q0, dst⟩
      rw [hc] at hq0 hdst; dsimp only at hq0 hdst ⊢
      simp only [NoStubCall, Bool.and_eq_true, Bool.and_true]
      refine ⟨hq0, n_wLive _ _ _, n_stackArgs _ _ _, ?_, hdst, ?_, n_copyRet _ _ _ _ _ hr⟩
      · split <;> rfl
      · split <;> rfl
  | .call (some (vs, live, rc, l1, l2)) d args (some (e, hc', h1, h2)), bs, kf, h => by
      have hdn : d ≠ some storeConstsStubLocation := by
        intro e; subst e; unfold WordNoStubCall at h; simp only [bne_self_eq_false, Bool.false_and] at h; exact Bool.false_ne_true h
      simp only [WordNoStubCall, Bool.and_eq_true] at h
      have hr := n_compNative conf perf rc (wLiveNative live bs kf).2 kf h.1.2
      have hh := n_compNative conf perf hc'
        (compNative conf perf rc (wLiveNative live bs kf).2 kf).2 kf h.2
      obtain ⟨hq0, hdst⟩ := n_callDest (width := width) d args kf hdn
      rw [compNative]
      rcases hc : callDestNative (width := width) d args kf with ⟨q0, dst⟩
      rw [hc] at hq0 hdst; dsimp only at hq0 hdst ⊢
      simp only [NoStubCall, Bool.and_eq_true]
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
      rw [compNative]; simp only [NoStubCall, Bool.and_true]; exact n_wLive _ _ _
  | .install .., bs, kf, h | .codeBufferWrite .., bs, kf, h | .dataBufferWrite .., bs, kf, h => by
      rw [compNative] <;> (try dsimp only) <;> rw [n_stackLoad] <;> rfl
  | .shareInst op v e, bs, kf, h => by
      rw [compNative]; split
      · rfl
      · exact n_wShareInst _ _ _ _
  | .raise .., _, _, _ => by rw [compNative]; simp [NoStubCall, raiseStubLocation, storeConstsStubLocation, wordNumStubs, stackNumStubs]
  | .skip, _, _, _ | .tick, _, _, _ | .break .., _, _, _
  | .continue .., _, _, _ | .ffi .., _, _, _ | .assign .., _, _, _ | .store .., _, _, _ => by
      rw [compNative] <;> first | rfl | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)


theorem n_compileWordToStack {β : Type} (conf : AsmConfigExact width) (perf : Bool) (rc : Nat) :
    ∀ (progs : List (β × Nat × WordLangProgHOL (BitVec width))) (bs : AppList (BitVec width) × Nat),
      (∀ x ∈ progs, NoSt x.2.2 = true ∧ WordNoStubCall x.2.2 = true) →
      ∀ y ∈ (compileWordToStackNative conf perf rc progs bs).1, Clean y.2 = true
  | [], _, _ => by intro y hy; simp [compileWordToStackNative] at hy
  | (i, ac, p) :: ps, bs, h => by
      intro y hy
      rw [compileWordToStackNative] at hy; dsimp only at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · have hp := h _ (List.mem_cons_self ..)
        apply clean_of
        · exact s_compileProgNative conf perf p ac rc bs hp.1
        · unfold compileProgNative; dsimp only
          simp only [NoStubCall, Bool.true_and]; exact n_compNative conf perf p _ _ hp.2
      · exact n_compileWordToStack conf perf rc ps _
          (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy

/-- Top-level WordToStack: every entry is either the `storeConsts` stub itself or `Clean`. -/
theorem c_compileNative (conf : AsmConfigExact width) (perf : Bool)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, NoSt x.2.2 = true ∧ WordNoStubCall x.2.2 = true) :
    ∀ y ∈ (compileNative conf perf progs).2.2.2,
      y.1 = storeConstsStubLocation ∨ Clean y.2 = true := by
  intro y hy
  unfold compileNative at hy; dsimp only at hy
  rcases List.mem_cons.1 hy with rfl | hy
  · right; unfold raiseStubNative; cases perf <;> rfl
  rcases List.mem_cons.1 hy with rfl | hy
  · left; rfl
  · right; exact n_compileWordToStack conf perf _ progs _ h y hy

/-- One body through the whole StackToLab stack-side chain (raw call → StackAlloc →
StackRemove → StackNames) stays `Clean`. -/
theorem c_body_chain (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat)
    (f : Spt Nat) (n : Nat) (p : HolProg width) (h : Clean p = true) :
    Clean (StackNames.progCompHOL f (StackRemove.comp j bd ptr
      (StackAlloc.progComp (n, StackRawCall.compTop info p)).2)) = true := by
  apply c_stackNames; apply c_stackRemoveComp
  unfold StackAlloc.progComp; exact c_stackAllocComp _ _ _ (c_rawCallCompTop info p h)

/-- Master: Pancake → … → WordToStack, then the stack-side passes of `StackToLab.compile`
(raw call, StackAlloc, StackRemove, StackNames), body by body. Hypothesis: no WordLang
call names the stub label directly (frontend function names start at 64). -/
theorem panToStackNames_bodies_NoSt_and_NoStubCall (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (hcall : ∀ x ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      WordNoStubCall x.2.2 = true)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true ∧
       NoStubCall (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true) := by
  intro y hy
  rcases c_compileNative ac perf _
      (fun x hx => ⟨panToWordToWord_NoSt arch prog wc ac x hx, hcall x hx⟩) y hy with e | hc
  · exact Or.inl e
  · right
    exact of_clean (c_body_chain info j bd ptr f y.1 y.2 hc)

/-- Tightness: StackAlloc turns a stub-tagged `storeConsts` into a call to that stub. -/
theorem stackAlloc_storeConsts_calls_stub (n m : Nat) :
    NoStubCall (StackAlloc.comp n m
      (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width)).1 = false := by
  rw [StackAlloc.comp]; rfl


end InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts
