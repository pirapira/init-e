import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Pancake.CrepToLoop.ContextExact
import Flapjack.Pancake.LoopLive
import Flapjack.Pancake.LoopLive.Fixedpoint
import Flapjack.Pancake.PanToWord
import InitECandidate.Solver.PanToStackNoStoreConsts
import InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
import InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false



namespace InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.StackGc

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
      (match t with | .inl n => n != Flapjack.Compiler.Backend.StackLang.gcStubLocation | .inr _ => true) &&
      (match ret with | none => true | some (r, _, _, _) => NoStubCall r) &&
      (match h with | none => true | some (q, _, _) => NoStubCall q)
  | .seq a b => NoStubCall a && NoStubCall b
  | .ite _ _ _ a b => NoStubCall a && NoStubCall b
  | .loop b => NoStubCall b
  | _ => true

def tgtOk : Sum Nat Nat → Bool
  | .inl n => n != Flapjack.Compiler.Backend.StackLang.gcStubLocation
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
      (d != some Flapjack.Compiler.Backend.StackLang.gcStubLocation) &&
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
    (hp : pos ≠ some Flapjack.Compiler.Backend.StackLang.gcStubLocation) :
    NoStubCall (callDestNative (width := width) pos args kf).1 = true ∧
    (match (callDestNative (width := width) pos args kf).2 with
      | .inl n => n != Flapjack.Compiler.Backend.StackLang.gcStubLocation | .inr _ => true) = true := by
  unfold callDestNative; split
  · rename_i p; refine ⟨rfl, ?_⟩; simp only [bne_iff_ne, ne_eq]; intro e; exact hp (by rw [e])
  · split
    · exact ⟨rfl, by simp [raiseStubLocation, Flapjack.Compiler.Backend.StackLang.gcStubLocation, wordNumStubs, stackNumStubs]⟩
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
      have hdn : d ≠ some Flapjack.Compiler.Backend.StackLang.gcStubLocation := by
        intro e; subst e; unfold WordNoStubCall at h; simp only [bne_self_eq_false, Bool.false_and] at h; exact Bool.false_ne_true h
      obtain ⟨hq0, hdst⟩ := n_callDest (width := width) d args kf hdn
      rw [compNative]
      rcases hc : callDestNative (width := width) d args kf with ⟨q0, dst⟩
      rw [hc] at hq0 hdst; dsimp only at hq0 hdst ⊢
      simp only [NoStubCall, Bool.and_eq_true, Bool.and_true]
      refine ⟨hq0, n_seqStackFree _ _ ?_⟩
      simp only [NoStubCall, Bool.and_true]; exact hdst
  | .call (some (vs, live, rc, l1, l2)) d args none, bs, kf, h => by
      have hdn : d ≠ some Flapjack.Compiler.Backend.StackLang.gcStubLocation := by
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
      have hdn : d ≠ some Flapjack.Compiler.Backend.StackLang.gcStubLocation := by
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
  | .raise .., _, _, _ => by rw [compNative]; simp [NoStubCall, raiseStubLocation, Flapjack.Compiler.Backend.StackLang.gcStubLocation, wordNumStubs, stackNumStubs]
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


end InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.StackGc



/-!
# Discharging `hcall`: no WordLang call ever targets the `storeConsts` stub

CrepToLoop numbers user functions `64 + i` (`firstLoopName = 64`) and sends an unknown
callee to label `0`; every Loop call it emits carries `some label`. The Loop optimiser
(`loopCallCompHOL`, `shrinkHOL`, `markAllHOL`) and LoopToWord keep call targets. Hence every
call target produced from any Pancake program is `0` or `≥ 64`, never
`Flapjack.Compiler.Backend.StackLang.gcStubLocation = 6`. Proof skeleton follows Flapjack's
`Pancake/CrepToLoop/Proofs/LocValueFree.lean` with the predicate changed to call targets.
-/

namespace InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.PanToWordGc

open Flapjack
open Flapjack.Compiler.Backend
open InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.StackGc

/-- Admissible call target: present, and `0` or a user label `≥ 64`. -/
def TgtGood : Option Nat → Prop
  | some n => n = 0 ∨ 64 ≤ n
  | none => False

/-- Every function label stored in the CrepToLoop context is `≥ 64`. -/
def FuncsGood (context : CrepToLoopContextExact) : Prop :=
  ∀ k l a, context.funcs.lookup k = some (l, a) → 64 ≤ l

theorem findLab_good (context : CrepToLoopContextExact) (name : Basis.Pure.MlString.MlString)
    (hf : FuncsGood context) :
    findLabExact context name = 0 ∨ 64 ≤ findLabExact context name := by
  unfold findLabExact
  cases h : context.funcs.lookup name with
  | none => left; rfl
  | some v => obtain ⟨l, a⟩ := v; right; exact hf name l a h

theorem fupdateList_good {α : Type} [BEq α] (P : Nat × Nat → Prop) :
    ∀ (entries : List (α × (Nat × Nat))) (f : FiniteMap α (Nat × Nat)),
      (∀ k v, f k = some v → P v) → (∀ e ∈ entries, P e.2) →
      ∀ k v, FUPDATE_LIST f entries k = some v → P v
  | [], f, hf, _, k, v, h => hf k v h
  | e :: es, f, hf, he, k, v, h => by
      rw [FUPDATE_LIST_cons] at h
      refine fupdateList_good P es _ ?_ (fun x hx => he x (List.mem_cons_of_mem _ hx)) k v h
      intro k' v' h'
      unfold FUPDATE at h'
      split at h'
      · cases h'; exact he e List.mem_cons_self
      · exact hf k' v' h'

/-- CrepToLoop's function table maps every name to a label `64 + i`. -/
theorem makeFuncs_good {β γ : Type}
    (prog : List (Basis.Pure.MlString.MlString × List β × γ)) :
    ∀ k l a, (crepToLoopMakeFuncsExactExecutable prog).lookup k = some (l, a) → 64 ≤ l := by
  intro k l a h
  have := fupdateList_good (fun v => 64 ≤ v.1) _ (HolFiniteMapExact.empty.lookup)
    (by intro k v h; simp [HolFiniteMapExact.empty] at h) ?_ k (l, a) h
  · exact this
  · intro e he
    rw [List.mem_reverse] at he
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 he
    simp [firstLoopName]

/-- Every Loop call has a target `some n` with `n = 0 ∨ 64 ≤ n` (never a stub label),
including inside call handlers. -/
def loopTgtOk {width : Nat} [NeZero width] :
    HolLoopProg width → Prop
  | .seq first second => loopTgtOk first ∧ loopTgtOk second
  | .ite _ _ _ thenBranch elseBranch _ =>
      loopTgtOk thenBranch ∧ loopTgtOk elseBranch
  | .loop _ body _ => loopTgtOk body
  | .mark body => loopTgtOk body
  | .call _ t _ none => TgtGood t
  | .call _ t _ (some (_, handler, normal, _)) =>
      TgtGood t ∧ loopTgtOk handler ∧ loopTgtOk normal
  | _ => True
termination_by program => sizeOf program
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [HolLoopProg.call.sizeOf_spec]; omega)

/-- Every element of a list satisfies the nested LocValue-free predicate. -/
def loopListTgtOk {width : Nat} [NeZero width]
    (programs : List (HolLoopProg width)) : Prop :=
  ∀ program, program ∈ programs → loopTgtOk program

private theorem loopListTgtOk_append {width : Nat} [NeZero width]
    (first second : List (HolLoopProg width))
    (hfirst : loopListTgtOk first)
    (hsecond : loopListTgtOk second) :
    loopListTgtOk (first ++ second) := by
  intro program hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hfirst program hmem
  · exact hsecond program hmem

private theorem loopListTgtOk_append3 {width : Nat} [NeZero width]
    (first second : List (HolLoopProg width)) (last : HolLoopProg width)
    (hfirst : loopListTgtOk first)
    (hsecond : loopListTgtOk second)
    (hlast : loopListTgtOk [last]) :
    loopListTgtOk (first ++ second ++ [last]) := by
  intro program hmem
  rcases List.mem_append.mp hmem with hprefix | hlastMem
  · rcases List.mem_append.mp hprefix with hfirstMem | hsecondMem
    · exact hfirst program hfirstMem
    · exact hsecond program hsecondMem
  · exact hlast program (by simpa using hlastMem)

private theorem loopNestedSeqHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (programs : List (HolLoopProg width))
    (hfree : loopListTgtOk programs) :
    loopTgtOk (loopNestedSeqHOL programs) := by
  induction programs with
  | nil => simp [loopNestedSeqHOL, loopTgtOk]
  | cons first rest ih =>
      have hfirst := hfree first (by simp)
      have hrest : loopListTgtOk rest := by
        intro program hmem
        exact hfree program (by simp [hmem])
      simpa [loopNestedSeqHOL, loopTgtOk] using And.intro hfirst (ih hrest)

private theorem loopListTgtOk_zipWith {width : Nat} [NeZero width]
    {α β : Type} (f : α → β → HolLoopProg width)
    (hfree : ∀ x y, loopTgtOk (f x y)) :
    ∀ (xs : List α) (ys : List β), loopListTgtOk (xs.zipWith f ys)
  | [], _ => by simp [loopListTgtOk]
  | _ :: _, [] => by simp [loopListTgtOk]
  | x :: xs, y :: ys => by
      simp only [List.zipWith_cons_cons, loopListTgtOk, List.mem_cons]
      intro program hmem
      rcases hmem with rfl | hmem
      · exact hfree x y
      · exact loopListTgtOk_zipWith f hfree xs ys program hmem

private theorem compileCrepopHOLExact_codeTgtOk {width : Nat} [NeZero width]
    (operator : CrepOp) (target : Compiler.Encoders.Asm.AsmArchitecture)
    (left right tmp : Nat)
    (live : NumSet) :
    loopListTgtOk
      (compileCrepopHOLExact (width := width) operator target left right tmp live).1 := by
  cases operator with
  | mul =>
      by_cases htarget : target = .armv7 <;>
        simp [compileCrepopHOLExact, htarget,
          loopListTgtOk, loopTgtOk]

mutual
private theorem compileExpHOLExact_codeTgtOk {width : Nat} [NeZero width]
    (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∀ expression : CrepExpHOL width,
      loopListTgtOk (compileExpHOLExact context tmp live expression).1
  | .baseAddr => by simp [compileExpHOLExact, loopListTgtOk]
  | .topAddr => by simp [compileExpHOLExact, loopListTgtOk]
  | .const _ => by simp [compileExpHOLExact, loopListTgtOk]
  | .var _ => by simp [compileExpHOLExact, loopListTgtOk]
  | .load address => by
      have ih := compileExpHOLExact_codeTgtOk context tmp live address
      rcases hA : compileExpHOLExact context tmp live address with ⟨code, value, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact ih
  | .load32 address => by
      have ih := compileExpHOLExact_codeTgtOk context tmp live address
      rcases hA : compileExpHOLExact context tmp live address with ⟨code, value, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact loopListTgtOk_append code _ ih (by
        simp [loopListTgtOk, loopTgtOk])
  | .loadByte address => by
      have ih := compileExpHOLExact_codeTgtOk context tmp live address
      rcases hA : compileExpHOLExact context tmp live address with ⟨code, value, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact loopListTgtOk_append code _ ih (by
        simp [loopListTgtOk, loopTgtOk])
  | .loadGlob _ => by simp [compileExpHOLExact, loopListTgtOk]
  | .op operator expressions => by
      have ih := compileExpsHOLExact_codeTgtOk context tmp live expressions
      rcases hA : compileExpsHOLExact context tmp live expressions with
        ⟨code, values, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      simp only [compileExpHOLExact, hA]
      exact ih
  | .crepOp operator expressions => by
      have ih := compileExpsHOLExact_codeTgtOk context tmp live expressions
      rcases hA : compileExpsHOLExact context tmp live expressions with
        ⟨code, values, next, outLive⟩
      rw [hA] at ih
      simp only at ih
      rcases hC : compileCrepopHOLExact (width := width) operator context.target next (next + 1)
          (next + values.length)
          (sptListInsert ((List.range values.length).map (fun offset => next + offset)) outLive)
          with ⟨operationCode, destination⟩
      simp only [compileExpHOLExact, hA, hC]
      have hAssigned : loopListTgtOk
          ((List.range values.length).zipWith
            (fun offset value => HolLoopProg.assign (next + offset) value) values) :=
        loopListTgtOk_zipWith _
          (fun _ _ => by simp [loopTgtOk]) _ _
      have hPrefix := loopListTgtOk_append code _ ih hAssigned
      have hOperation : loopListTgtOk operationCode := by
        have h := compileCrepopHOLExact_codeTgtOk (width := width) operator context.target next
          (next + 1) (next + values.length)
          (sptListInsert ((List.range values.length).map (fun offset => next + offset)) outLive)
        rw [hC] at h
        exact h
      exact loopListTgtOk_append _ operationCode hPrefix hOperation
  | .cmp operator left right => by
      have ihLeft := compileExpHOLExact_codeTgtOk context tmp live left
      rcases hA : compileExpHOLExact context tmp live left with
        ⟨leftCode, leftValue, leftNext, leftLive⟩
      rw [hA] at ihLeft
      simp only at ihLeft
      have ihRight := compileExpHOLExact_codeTgtOk context leftNext leftLive right
      rcases hB : compileExpHOLExact context leftNext leftLive right with
        ⟨rightCode, rightValue, rightNext, rightLive⟩
      rw [hB] at ihRight
      simp only at ihRight
      simp only [compileExpHOLExact, hA, hB, progIfHOLExact]
      have htail : loopListTgtOk
          [.assign (rightNext + 1) leftValue,
           .assign (rightNext + 2) rightValue,
           .ite operator (rightNext + 1) (.reg (rightNext + 2))
             (.assign (rightNext + 1) (.const 1))
             (.assign (rightNext + 1) (.const 0))
             (sptListInsert [rightNext + 1, rightNext + 2] rightLive)] := by
        simp [loopListTgtOk, loopTgtOk]
      exact loopListTgtOk_append (leftCode ++ rightCode) _
        (loopListTgtOk_append leftCode rightCode ihLeft ihRight) htail
  | .shift operator left right => by
      have ihLeft := compileExpHOLExact_codeTgtOk context tmp live left
      rcases hA : compileExpHOLExact context tmp live left with
        ⟨leftCode, leftValue, leftNext, leftLive⟩
      rw [hA] at ihLeft
      simp only at ihLeft
      have ihRight := compileExpHOLExact_codeTgtOk context leftNext leftLive right
      rcases hB : compileExpHOLExact context leftNext leftLive right with
        ⟨rightCode, rightValue, rightNext, rightLive⟩
      rw [hB] at ihRight
      simp only at ihRight
      simp only [compileExpHOLExact, hA, hB]
      exact loopListTgtOk_append leftCode rightCode ihLeft ihRight
  termination_by expression => sizeOf expression

private theorem compileExpsHOLExact_codeTgtOk {width : Nat} [NeZero width]
    (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∀ expressions : List (CrepExpHOL width),
      loopListTgtOk (compileExpsHOLExact context tmp live expressions).1
  | [] => by simp [compileExpsHOLExact, loopListTgtOk]
  | expression :: expressions => by
      have ihExpression :=
        compileExpHOLExact_codeTgtOk context tmp live expression
      rcases hA : compileExpHOLExact context tmp live expression with
        ⟨code, value, next, outLive⟩
      rw [hA] at ihExpression
      simp only at ihExpression
      have ihTail := compileExpsHOLExact_codeTgtOk context next outLive expressions
      rcases hB : compileExpsHOLExact context next outLive expressions with
        ⟨tailCode, tailValues, finalTemp, finalLive⟩
      rw [hB] at ihTail
      simp only at ihTail
      simp only [compileExpsHOLExact, hA, hB]
      exact loopListTgtOk_append code tailCode ihExpression ihTail
  termination_by expressions => sizeOf expressions
end

private theorem compileHOLExact_tgtOk {width : Nat} [NeZero width] :
    ∀ (context : CrepToLoopContextExact) (live : NumSet)
      (program : CrepProgHOL width), FuncsGood context →
      loopTgtOk (compileHOLExact context live program)
  | context, live, .skip, hf => by simp [compileHOLExact, loopTgtOk]
  | context, live, .break _, hf => by simp [compileHOLExact, loopTgtOk]
  | context, live, .continue _, hf => by simp [compileHOLExact, loopTgtOk]
  | context, live, .tick, hf => by simp [compileHOLExact, loopTgtOk]
  | context, live, .raise exception, hf => by
      simp [compileHOLExact, loopTgtOk]
  | context, live, .shMem operator name address, hf => by
      cases hname : context.vars.lookup name with
      | none => simp [compileHOLExact, hname, loopTgtOk]
      | some mappedName =>
          rcases hA : compileExpHOLExact context (context.vmax + 1) live address with
            ⟨code, compiledAddress, next, outLive⟩
          have hcode := compileExpHOLExact_codeTgtOk context
            (context.vmax + 1) live address
          rw [hA] at hcode
          simp only at hcode
          simp only [compileHOLExact, hname, hA]
          apply loopNestedSeqHOL_preserves_tgtOk
          exact loopListTgtOk_append code _ hcode (by
            simp [loopListTgtOk, loopTgtOk])
  | context, live, .store destination source, hf => by
      rcases hD : compileExpHOLExact context (context.vmax + 1) live destination with
        ⟨destinationCode, address, nextTemporary, nextLive⟩
      rcases hS : compileExpHOLExact context nextTemporary nextLive source with
        ⟨sourceCode, value, finalTemporary, finalLive⟩
      have hDfree := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live destination
      have hSfree := compileExpHOLExact_codeTgtOk context
        nextTemporary nextLive source
      rw [hD] at hDfree
      rw [hS] at hSfree
      simp only at hDfree hSfree
      simp only [compileHOLExact, hD, hS]
      apply loopNestedSeqHOL_preserves_tgtOk
      have htail : loopListTgtOk
          [.assign finalTemporary value, .store address finalTemporary] := by
        simp [loopListTgtOk, loopTgtOk]
      apply loopListTgtOk_append
        (destinationCode ++ sourceCode) _
        (loopListTgtOk_append destinationCode sourceCode hDfree hSfree)
      exact htail
  | context, live, .store32 destination source, hf => by
      rcases hD : compileExpHOLExact context (context.vmax + 1) live destination with
        ⟨destinationCode, address, nextTemporary, nextLive⟩
      rcases hS : compileExpHOLExact context nextTemporary nextLive source with
        ⟨sourceCode, value, finalTemporary, finalLive⟩
      have hDfree := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live destination
      have hSfree := compileExpHOLExact_codeTgtOk context
        nextTemporary nextLive source
      rw [hD] at hDfree
      rw [hS] at hSfree
      simp only at hDfree hSfree
      simp only [compileHOLExact, hD, hS]
      apply loopNestedSeqHOL_preserves_tgtOk
      have htail : loopListTgtOk
          [.assign finalTemporary address, .assign (finalTemporary + 1) value,
           .store32 finalTemporary (finalTemporary + 1)] := by
        simp [loopListTgtOk, loopTgtOk]
      apply loopListTgtOk_append
        (destinationCode ++ sourceCode) _
        (loopListTgtOk_append destinationCode sourceCode hDfree hSfree)
      exact htail
  | context, live, .storeByte destination source, hf => by
      rcases hD : compileExpHOLExact context (context.vmax + 1) live destination with
        ⟨destinationCode, address, nextTemporary, nextLive⟩
      rcases hS : compileExpHOLExact context nextTemporary nextLive source with
        ⟨sourceCode, value, finalTemporary, finalLive⟩
      have hDfree := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live destination
      have hSfree := compileExpHOLExact_codeTgtOk context
        nextTemporary nextLive source
      rw [hD] at hDfree
      rw [hS] at hSfree
      simp only at hDfree hSfree
      simp only [compileHOLExact, hD, hS]
      apply loopNestedSeqHOL_preserves_tgtOk
      have htail : loopListTgtOk
          [.assign finalTemporary address, .assign (finalTemporary + 1) value,
           .storeByte finalTemporary (finalTemporary + 1)] := by
        simp [loopListTgtOk, loopTgtOk]
      apply loopListTgtOk_append
        (destinationCode ++ sourceCode) _
        (loopListTgtOk_append destinationCode sourceCode hDfree hSfree)
      exact htail
  | context, live, .storeGlob address value, hf => by
      rcases hA : compileExpHOLExact context (context.vmax + 1) live value with
        ⟨code, compiledValue, next, outLive⟩
      have hcode := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live value
      rw [hA] at hcode
      simp only at hcode
      simp only [compileHOLExact, hA]
      apply loopNestedSeqHOL_preserves_tgtOk
      exact loopListTgtOk_append code _ hcode (by
        simp [loopListTgtOk, loopTgtOk])
  | context, live, .seq first second, hf => by
      simp only [compileHOLExact, loopTgtOk]
      exact ⟨compileHOLExact_tgtOk context live first hf,
        compileHOLExact_tgtOk context live second hf⟩
  | context, live, .ite condition thenBranch elseBranch, hf => by
      rcases hC : compileExpHOLExact context (context.vmax + 1) live condition with
        ⟨conditionCode, compiledCondition, temporary, outLive⟩
      have hcode := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live condition
      rw [hC] at hcode
      simp only at hcode
      have hthen := compileHOLExact_tgtOk context live thenBranch hf
      have helse := compileHOLExact_tgtOk context live elseBranch hf
      simp only [compileHOLExact, hC]
      apply loopNestedSeqHOL_preserves_tgtOk
      have htail : loopListTgtOk
          [.assign temporary compiledCondition,
           .ite .notEqual temporary (.imm (0 : BitVec width))
             (compileHOLExact context live thenBranch)
             (compileHOLExact context live elseBranch) live] := by
        simp [loopListTgtOk, loopTgtOk, hthen, helse]
      exact loopListTgtOk_append conditionCode _ hcode htail
  | context, live, .while condition body, hf => by
      rcases hC : compileExpHOLExact context (context.vmax + 1) live condition with
        ⟨conditionCode, compiledCondition, temporary, outLive⟩
      have hcode := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live condition
      rw [hC] at hcode
      simp only at hcode
      have hbody := compileHOLExact_tgtOk context live body hf
      simp only [compileHOLExact, hC, loopTgtOk]
      apply loopNestedSeqHOL_preserves_tgtOk
      have htail : loopListTgtOk
          [.assign temporary compiledCondition,
           .ite .notEqual temporary (.imm (0 : BitVec width))
             (.seq (compileHOLExact context live body) (.continue 0)) (.break 0) live] := by
        simp [loopListTgtOk, loopTgtOk, hbody]
      exact loopListTgtOk_append conditionCode _ hcode htail
  | context, live, .assign name value, hf => by
      cases hname : context.vars.lookup name with
      | none => simp [compileHOLExact, hname, loopTgtOk]
      | some mappedName =>
          rcases hA : compileExpHOLExact context (context.vmax + 1) live value with
            ⟨code, compiledValue, next, outLive⟩
          have hcode := compileExpHOLExact_codeTgtOk context
            (context.vmax + 1) live value
          rw [hA] at hcode
          simp only at hcode
          simp only [compileHOLExact, hname, hA]
          apply loopNestedSeqHOL_preserves_tgtOk
          exact loopListTgtOk_append code _ hcode (by
            simp [loopListTgtOk, loopTgtOk])
  | context, live, .primitive destinations operator arguments, hf => by
      cases hDest : destinations.mapM context.vars.lookup <;>
        cases hArgs : arguments.mapM context.vars.lookup <;>
          simp [compileHOLExact, hDest, hArgs, loopTgtOk]
  | context, live, .dec name value body, hf => by
      rcases hA : compileExpHOLExact context (context.vmax + 1) live value with
        ⟨code, compiledValue, temporary, outLive⟩
      have hcode := compileExpHOLExact_codeTgtOk context
        (context.vmax + 1) live value
      rw [hA] at hcode
      simp only at hcode
      let bodyContext :=
        { context with vars := context.vars.updateEq (name, temporary), vmax := temporary }
      let bodyLive := sptInsert temporary () live
      have hbody := compileHOLExact_tgtOk bodyContext bodyLive body hf
      simp only [compileHOLExact, hA, loopTgtOk]
      exact ⟨loopNestedSeqHOL_preserves_tgtOk code hcode, True.intro, hbody⟩
  | context, live, .call none name arguments, hf => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live arguments with
        ⟨code, values, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeTgtOk context
        (context.vmax + 1) live arguments
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := loopListTgtOk_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [loopTgtOk])
        (genTemps nextTemporary values.length) values
      have hCall : loopListTgtOk
          [HolLoopProg.call (width := width) none (some (findLabExact context name))
            (genTemps nextTemporary values.length) none] := by
        simp [loopListTgtOk, loopTgtOk, TgtGood, findLab_good context name hf]
      simp only [compileHOLExact, hA]
      apply loopNestedSeqHOL_preserves_tgtOk
      exact loopListTgtOk_append3 code
        (List.zipWith HolLoopProg.assign (genTemps nextTemporary values.length) values)
        (HolLoopProg.call none (some (findLabExact context name))
          (genTemps nextTemporary values.length) none)
        hcode hAssignments hCall
  | context, live, .call (some (returns, none)) name arguments, hf => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live arguments with
        ⟨code, values, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeTgtOk context
        (context.vmax + 1) live arguments
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := loopListTgtOk_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [loopTgtOk])
        (genTemps nextTemporary values.length) values
      have hCall : loopListTgtOk
          [HolLoopProg.call (width := width)
            (some ((match returns.mapM context.vars.lookup with
              | none => [context.vmax + 2]
              | some names => names), live))
            (some (findLabExact context name)) (genTemps nextTemporary values.length)
            (some (context.vmax + 1, .raise (context.vmax + 1), .skip, live))] := by
        simp [loopListTgtOk, loopTgtOk, TgtGood, findLab_good context name hf]
      rw [compileHOLExact]
      simp only [hA]
      apply loopNestedSeqHOL_preserves_tgtOk
      exact loopListTgtOk_append3 code
        (List.zipWith HolLoopProg.assign (genTemps nextTemporary values.length) values)
        (HolLoopProg.call
          (some ((match returns.mapM context.vars.lookup with
            | none => [context.vmax + 2]
            | some names => names), live))
          (some (findLabExact context name)) (genTemps nextTemporary values.length)
          (some (context.vmax + 1, .raise (context.vmax + 1), .skip, live)))
        hcode hAssignments hCall
  | context, live, .call (some (returns, some (exception, handler))) name arguments, hf => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live arguments with
        ⟨code, values, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeTgtOk context
        (context.vmax + 1) live arguments
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := loopListTgtOk_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [loopTgtOk])
        (genTemps nextTemporary values.length) values
      have hhandler := compileHOLExact_tgtOk context live handler hf
      have hCall : loopListTgtOk
          [HolLoopProg.call (width := width)
            (some ((match returns.mapM context.vars.lookup with
              | none => [context.vmax + 2]
              | some names => names), live))
            (some (findLabExact context name)) (genTemps nextTemporary values.length)
            (some (context.vmax + 1,
              .ite .notEqual (context.vmax + 1) (.imm exception) (.raise (context.vmax + 1))
                (.seq .tick (compileHOLExact context live handler)) live,
              .skip, live))] := by
        simp [loopListTgtOk, loopTgtOk, TgtGood, findLab_good context name hf, hhandler]
      rw [compileHOLExact]
      simp only [hA]
      apply loopNestedSeqHOL_preserves_tgtOk
      exact loopListTgtOk_append3 code
        (List.zipWith HolLoopProg.assign (genTemps nextTemporary values.length) values)
        (HolLoopProg.call
          (some ((match returns.mapM context.vars.lookup with
            | none => [context.vmax + 2]
            | some names => names), live))
          (some (findLabExact context name)) (genTemps nextTemporary values.length)
          (some (context.vmax + 1,
            .ite .notEqual (context.vmax + 1) (.imm exception)
              (.raise (context.vmax + 1)) (.seq .tick (compileHOLExact context live handler)) live,
            .skip, live)))
        hcode hAssignments hCall
  | context, live, .extCall function configuration configurationLength array arrayLength, hf => by
      rw [compileHOLExact]
      split <;> simp [loopTgtOk]
  | context, live, .return values, hf => by
      rcases hA : compileExpsHOLExact context (context.vmax + 1) live values with
        ⟨code, compiledValues, nextTemporary, outLive⟩
      have hcode := compileExpsHOLExact_codeTgtOk context
        (context.vmax + 1) live values
      rw [hA] at hcode
      simp only at hcode
      have hAssignments := loopListTgtOk_zipWith
        HolLoopProg.assign
        (fun _ _ => by simp [loopTgtOk])
        (genTemps nextTemporary compiledValues.length) compiledValues
      have hReturn : loopListTgtOk
          [HolLoopProg.return (width := width)
            (genTemps nextTemporary compiledValues.length)] := by
        simp [loopListTgtOk, loopTgtOk]
      unfold compileHOLExact
      simp only [hA]
      apply loopNestedSeqHOL_preserves_tgtOk
      exact loopListTgtOk_append3 code
        (List.zipWith HolLoopProg.assign
          (genTemps nextTemporary compiledValues.length) compiledValues)
        (HolLoopProg.return (width := width)
          (genTemps nextTemporary compiledValues.length))
        hcode hAssignments hReturn
termination_by _ _ program => sizeOf program
decreasing_by
  all_goals simp_wf
  all_goals first
    | decreasing_trivial
    | (simp_all only [CrepProgHOL.dec.sizeOf_spec, CrepProgHOL.seq.sizeOf_spec,
        CrepProgHOL.ite.sizeOf_spec, CrepProgHOL.while.sizeOf_spec,
        CrepProgHOL.call.sizeOf_spec]; omega)

/-- The exact loop-call optimizer does not introduce `locValue` into a
program that was recursively free of it.  The live-set parameter is
generalized so the `Seq` case can use the second induction hypothesis at the
live set returned by compiling the first child. -/
theorem loopCallCompHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (program : HolLoopProg width) (live : Spt Nat)
    (hfree : loopTgtOk program) :
    loopTgtOk (loopCallCompHOL live program).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    ∀ live, loopTgtOk p →
      loopTgtOk (loopCallCompHOL live p).1
  let mPair : HolLoopProg width × NumSet → Prop := fun _ => True
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop := fun _ => True
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop := fun _ => True
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop :=
    fun _ => True
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_2 =>
      intro name value live
      intro hfree
      cases value with
      | var m => simp [loopCallCompHOL.eq_5, loopTgtOk]
      | const value => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | lookup address => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | load address => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | op operator args => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | shift operator left right => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | baseAddr => simp [loopCallCompHOL.eq_6, loopTgtOk]
      | topAddr => simp [loopCallCompHOL.eq_6, loopTgtOk]
    case refine_4 =>
      intro operation live
      intro hfree
      cases operation with
      | longMul => simp [loopCallCompHOL.eq_19, loopTgtOk]
      | longDiv => simp [loopCallCompHOL.eq_20, loopTgtOk]
      | div => simp [loopCallCompHOL.eq_21, loopTgtOk]
    case refine_23 =>
      intro returns target arguments handler ih live hfree
      cases target with
      | none => cases handler with
        | none => simp [loopTgtOk, TgtGood] at hfree
        | some e => rcases e with ⟨_, _, _, _⟩; simp [loopTgtOk, TgtGood] at hfree
      | some t => cases handler with
        | none => simpa [loopCallCompHOL.eq_2, loopTgtOk] using hfree
        | some e =>
            rcases e with ⟨_, _, _, _⟩
            simpa [loopCallCompHOL.eq_2, loopTgtOk] using hfree
    all_goals simp_all [mProg, mPair, mTriple, mQuad, mHandler,
      loopTgtOk, loopCallCompHOL.eq_1, loopCallCompHOL.eq_2,
      loopCallCompHOL.eq_3, loopCallCompHOL.eq_4, loopCallCompHOL.eq_5,
      loopCallCompHOL.eq_6, loopCallCompHOL.eq_7, loopCallCompHOL.eq_8,
      loopCallCompHOL.eq_9, loopCallCompHOL.eq_10, loopCallCompHOL.eq_11,
      loopCallCompHOL.eq_12, loopCallCompHOL.eq_13, loopCallCompHOL.eq_14,
      loopCallCompHOL.eq_15, loopCallCompHOL.eq_16, loopCallCompHOL.eq_17,
      loopCallCompHOL.eq_18, loopCallCompHOL.eq_19, loopCallCompHOL.eq_20,
      loopCallCompHOL.eq_21, loopCallCompHOL.eq_22]
  exact hgeneral live hfree

/-- `shrinkHOL` cannot introduce the runtime-only `locValue` constructor.
This is Flapjack-specific infrastructure: it supplies the optimizer half of
the parser-routed compile-path invariant and is not an additional HOL result.
The loop branch uses the reviewed `fixedpoint_thm` equation to reduce a
successful fixedpoint result to one structural `shrinkHOL` call on its body. -/
theorem shrinkHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (program : HolLoopProg width) (live : NumSet)
    (hfree : loopTgtOk program) :
    loopTgtOk (shrinkHOL [] program live).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    ∀ lt live, loopTgtOk p →
      loopTgtOk (shrinkHOL lt p live).1
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_2 =>
      intro name value lt live hfree
      simp only [shrinkHOL.eq_15]
      cases hlookup : sptLookup name live <;>
        simp [loopTgtOk]
    case refine_12 =>
      intro operator condition right thenBranch elseBranch branchLive
        ihThen ihElse lt live hfree
      simp only [loopTgtOk] at hfree
      rcases hfree with ⟨hthen, helse⟩
      cases right with
      | reg r =>
          simp only [shrinkHOL.eq_3]
          rcases hsThen : shrinkHOL lt thenBranch (sptInter live branchLive) with
            ⟨then', liveThen⟩
          rcases hsElse : shrinkHOL lt elseBranch (sptInter live branchLive) with
            ⟨else', liveElse⟩
          have hthenFree := ihThen lt (sptInter live branchLive) hthen
          have helseFree := ihElse lt (sptInter live branchLive) helse
          rw [hsThen] at hthenFree
          rw [hsElse] at helseFree
          simp only [loopTgtOk]
          exact ⟨hthenFree, helseFree⟩
      | imm value =>
          simp only [shrinkHOL.eq_4]
          rcases hsThen : shrinkHOL lt thenBranch (sptInter live branchLive) with
            ⟨then', liveThen⟩
          rcases hsElse : shrinkHOL lt elseBranch (sptInter live branchLive) with
            ⟨else', liveElse⟩
          have hthenFree := ihThen lt (sptInter live branchLive) hthen
          have helseFree := ihElse lt (sptInter live branchLive) helse
          rw [hsThen] at hthenFree
          rw [hsElse] at helseFree
          simp only [loopTgtOk]
          exact ⟨hthenFree, helseFree⟩
    case refine_13 =>
      intro liveIn body liveOut ihBody lt live hfree
      simp only [shrinkHOL.eq_2]
      have hfreeBody : loopTgtOk body := by
        simpa [loopTgtOk] using hfree
      cases hfp : fixedpointHOL lt liveIn .ln
          (sptUnion liveIn (sptInter liveOut live)) body with
      | none =>
          have hbody := ihBody ((liveIn, sptInter liveOut live) :: lt)
            (sptUnion liveIn (sptInter liveOut live)) hfreeBody
          simp only [loopTgtOk]
          exact hbody
      | some result =>
          rcases result with ⟨body', liveBody⟩
          have hfixed := fixedpoint_thm lt liveIn .ln
            (sptUnion liveIn (sptInter liveOut live)) body liveBody body' hfp
          have hfreeBody' : loopTgtOk body' := by
            have h := ihBody
              ((sptInter liveIn liveBody, sptUnion liveIn (sptInter liveOut live)) :: lt)
              (sptUnion liveIn (sptInter liveOut live)) hfreeBody
            rw [hfixed] at h
            exact h
          simp only [loopTgtOk]
          exact hfreeBody'
    case refine_22 =>
      intro d s lt live _
      cases h : sptLookup d live <;> simp_all [shrinkHOL, loopTgtOk]
    case refine_23 =>
      intro returns target arguments handler hHandler lt live hfree
      have ht : TgtGood target := by
        cases handler with
        | none => simpa [loopTgtOk] using hfree
        | some e => rcases e with ⟨_, _, _, _⟩; simp only [loopTgtOk] at hfree; exact hfree.1
      cases returns with
      | none => simp only [shrinkHOL.eq_19, loopTgtOk]; exact ht
      | some returnData =>
          rcases returnData with ⟨returnNames, returnLive⟩
          cases handler with
          | none => simp only [shrinkHOL.eq_20, loopTgtOk]; exact ht
          | some entry =>
              rcases entry with ⟨exception, handler, normal, liveOut⟩
              rw [shrinkHOL.eq_21]
              rcases hHandler with ⟨ihHandler, ihNormal⟩
              simp only [loopTgtOk] at hfree
              rcases hfree with ⟨-, hHandlerFree, hNormalFree⟩
              rcases hsNormal : shrinkHOL lt normal live with ⟨normal', liveNormal⟩
              rcases hsHandler : shrinkHOL lt handler live with ⟨handler', liveHandler⟩
              have hNormal' := ihNormal lt live hNormalFree
              have hHandler' := ihHandler lt live hHandlerFree
              rw [hsNormal] at hNormal'
              rw [hsHandler] at hHandler'
              simp only [loopTgtOk]
              exact ⟨ht, hHandler', hNormal'⟩
    all_goals
      simp_all [mProg, mPair, mTriple, mQuad, mHandler,
        loopTgtOk, shrinkHOL, shrinkHOL.eq_1, shrinkHOL.eq_2,
        shrinkHOL.eq_3, shrinkHOL.eq_4, shrinkHOL.eq_5, shrinkHOL.eq_6,
        shrinkHOL.eq_7, shrinkHOL.eq_8, shrinkHOL.eq_9, shrinkHOL.eq_10,
        shrinkHOL.eq_11, shrinkHOL.eq_12, shrinkHOL.eq_13, shrinkHOL.eq_14,
        shrinkHOL.eq_15, shrinkHOL.eq_16, shrinkHOL.eq_17, shrinkHOL.eq_18,
        shrinkHOL.eq_19, shrinkHOL.eq_20, shrinkHOL.eq_21, shrinkHOL.eq_22,
        shrinkHOL.eq_23, shrinkHOL.eq_24, shrinkHOL.eq_25, shrinkHOL.eq_26,
        shrinkHOL.eq_27]
  exact hgeneral [] live hfree

/-- `markAllHOL` preserves the Flapjack-only recursive absence of `locValue`,
including in both programs stored by a call handler. This is infrastructure
for the parser-routed compile-path invariant, not an additional HOL result. -/
theorem markAllHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (program : HolLoopProg width)
    (hfree : loopTgtOk program) :
    loopTgtOk (markAllHOL program).1 := by
  let mProg : HolLoopProg width → Prop := fun p =>
    loopTgtOk p →
      loopTgtOk (markAllHOL p).1
  let mPair : HolLoopProg width × NumSet → Prop := fun p => mProg p.1
  let mTriple : HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mProg p.1 ∧ mProg p.2.1
  let mQuad : Nat × HolLoopProg width × HolLoopProg width × NumSet → Prop :=
    fun p => mTriple p.2
  let mHandler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet) → Prop
    | none => True
    | some entry => mQuad entry
  have hgeneral : mProg program := by
    refine HolLoopProg.rec
        (motive_1 := mProg) (motive_2 := mHandler) (motive_3 := mQuad)
        (motive_4 := mTriple) (motive_5 := mPair)
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ program
    case refine_11 =>
      intro first second ihFirst ihSecond hfree
      simp only [loopTgtOk] at hfree
      rcases hfree with ⟨hFirst, hSecond⟩
      have hFirst' := ihFirst hFirst
      have hSecond' := ihSecond hSecond
      simp only [markAllHOL]
      cases hmarkFirst : markAllHOL first with
      | mk first' firstMarked =>
              cases hmarkSecond : markAllHOL second with
              | mk second' secondMarked =>
              rw [hmarkFirst] at hFirst'
              rw [hmarkSecond] at hSecond'
              cases firstMarked <;> cases secondMarked <;>
                simp [loopTgtOk, hFirst', hSecond']
    case refine_12 =>
      intro operator condition right thenBranch elseBranch branchLive ihThen ihElse hfree
      simp only [loopTgtOk] at hfree
      rcases hfree with ⟨hthen, helse⟩
      have hthen' := ihThen hthen
      have helse' := ihElse helse
      simp only [markAllHOL]
      cases hmarkThen : markAllHOL thenBranch with
      | mk then' thenMarked =>
          cases hmarkElse : markAllHOL elseBranch with
          | mk else' elseMarked =>
              rw [hmarkThen] at hthen'
              rw [hmarkElse] at helse'
              cases thenMarked <;> cases elseMarked <;>
                simp [loopTgtOk, hthen', helse']
    case refine_23 =>
      intro returns target arguments handler hHandler hfree
      cases handler with
      | none => simpa [markAllHOL, loopTgtOk] using hfree
      | some entry =>
          rcases entry with ⟨exception, handler, normal, liveOut⟩
          rcases hHandler with ⟨ihHandler, ihNormal⟩
          simp only [loopTgtOk] at hfree
          rcases hfree with ⟨ht, hHandlerFree, hNormalFree⟩
          have hHandler' := ihHandler hHandlerFree
          have hNormal' := ihNormal hNormalFree
          simp only [markAllHOL]
          cases hmarkHandler : markAllHOL handler with
          | mk handler' handlerMarked =>
              cases hmarkNormal : markAllHOL normal with
              | mk normal' normalMarked =>
                  rw [hmarkHandler] at hHandler'
                  rw [hmarkNormal] at hNormal'
                  cases handlerMarked <;> cases normalMarked <;>
                    simp [loopTgtOk, ht, hHandler', hNormal']
    all_goals
      intros
      simp_all [mProg, mPair, mTriple, mQuad, mHandler,
        loopTgtOk, markAllHOL]
  exact hgeneral hfree

private theorem compHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (program : HolLoopProg width) (hfree : loopTgtOk program) :
    loopTgtOk (compHOL program) := by
  exact markAllHOL_preserves_tgtOk _
    (shrinkHOL_preserves_tgtOk program .ln hfree)

private theorem optimiseHOL_preserves_tgtOk {width : Nat} [NeZero width]
    (program : HolLoopProg width) (hfree : loopTgtOk program) :
    loopTgtOk (optimiseHOL program) := by
  apply compHOL_preserves_tgtOk
  exact loopCallCompHOL_preserves_tgtOk program .ln hfree


/-! ## Whole CrepToLoop output -/

theorem zipWith_fst_mem {α β γ : Type} (g : α → β → γ) :
    ∀ (l1 : List α) (l2 : List β) (x : α × γ),
      x ∈ List.zipWith (fun n e => (n, g n e)) l1 l2 → x.1 ∈ l1
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: as, b :: bs, x, h => by
      rw [List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (zipWith_fst_mem g as bs x h)

/-- (1) CrepToLoop numbers every user function `64 + i`. -/
theorem compileProgHOLExact_names {width : Nat} [NeZero width]
    (target : Compiler.Encoders.Asm.AsmArchitecture)
    (program : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width)) :
    ∀ x ∈ compileProgHOLExact target program, ∃ i, x.1 = 64 + i ∧ i < program.length := by
  intro x hx
  unfold compileProgHOLExact at hx
  have := zipWith_fst_mem (fun (_ : Nat) (entry : Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width) => (List.range entry.2.1.length,
      optimiseHOL (compFuncHOLExact target (crepToLoopMakeFuncsExactExecutable program)
        entry.2.1 (crepSimpProgHOL entry.2.2)))) _ _ x hx
  obtain ⟨i, hi, he⟩ := List.mem_map.1 this
  exact ⟨i, by rw [← he, firstLoopName]; omega, List.mem_range.1 hi⟩


/-- Every body emitted by CrepToLoop (after the Loop optimiser) only calls admissible targets. -/
theorem compileProgHOLExact_bodiesTgtOk {width : Nat} [NeZero width]
    (target : Compiler.Encoders.Asm.AsmArchitecture)
    (program : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width)) :
    ∀ x ∈ compileProgHOLExact target program, loopTgtOk x.2.2 := by
  intro x hx
  unfold compileProgHOLExact at hx
  have key : ∀ (l1 : List Nat) (l2 : List (Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width))
      (y : Nat × List Nat × HolLoopProg width),
      y ∈ List.zipWith (fun (n : Nat) (entry : Basis.Pure.MlString.MlString × List Nat × CrepProgHOL width) => (n, List.range entry.2.1.length,
        optimiseHOL (compFuncHOLExact target (crepToLoopMakeFuncsExactExecutable program)
          entry.2.1 (crepSimpProgHOL entry.2.2)))) l1 l2 → loopTgtOk y.2.2 := by
    intro l1
    induction l1 with
    | nil => intro l2 y h; simp at h
    | cons a as ih =>
        intro l2 y h
        cases l2 with
        | nil => simp at h
        | cons b bs =>
            rw [List.zipWith_cons_cons, List.mem_cons] at h
            rcases h with rfl | h
            · apply optimiseHOL_preserves_tgtOk
              unfold compFuncHOLExact
              exact compileHOLExact_tgtOk _ _ _ (makeFuncs_good program)
            · exact ih bs y h
  exact key _ _ x hx

/-! ## LoopToWord keeps call targets -/

theorem tgt_ne {t : Option Nat} (h : TgtGood t) : (t != some Flapjack.Compiler.Backend.StackLang.gcStubLocation) = true := by
  cases t with
  | none => exact absurd h id
  | some n =>
      simp only [TgtGood] at h
      have : n ≠ 4 := by omega
      simp [Flapjack.Compiler.Backend.StackLang.gcStubLocation, wordNumStubs, stackNumStubs, this]

theorem compHOL_noStub {width : Nat} [NeZero width] (ctx : Spt Nat) :
    ∀ (p : HolLoopProg width) (l : Nat × Nat), loopTgtOk p →
      WordNoStubCall (LoopToWord.compHOL ctx p l).1 = true
  | .seq a b, l, h => by
      simp only [loopTgtOk] at h
      have ha := compHOL_noStub ctx a l h.1
      rcases ha' : LoopToWord.compHOL ctx a l with ⟨w1, l1⟩
      have hb := compHOL_noStub ctx b l1 h.2
      rcases hb' : LoopToWord.compHOL ctx b l1 with ⟨w2, l2⟩
      rw [ha'] at ha; rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp only [ha', hb', WordNoStubCall, Bool.and_eq_true]
      exact ⟨ha, hb⟩
  | .ite o c r a b lv, l, h => by
      simp only [loopTgtOk] at h
      have ha := compHOL_noStub ctx a l h.1
      rcases ha' : LoopToWord.compHOL ctx a l with ⟨w1, l1⟩
      have hb := compHOL_noStub ctx b l1 h.2
      rcases hb' : LoopToWord.compHOL ctx b l1 with ⟨w2, l2⟩
      rw [ha'] at ha; rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [ha', hb', WordNoStubCall, ha, hb]
  | .loop li b lo, l, h => by
      simp only [loopTgtOk] at h
      have hb := compHOL_noStub ctx b l h
      rcases hb' : LoopToWord.compHOL ctx b l with ⟨w, l1⟩
      rw [hb'] at hb
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [hb', WordNoStubCall, hb]
  | .mark b, l, h => by
      simp only [loopTgtOk] at h
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); exact compHOL_noStub ctx b l h
  | .call none t args hd, l, h => by
      have ht : TgtGood t := by
        cases hd with
        | none => simpa [loopTgtOk] using h
        | some e => rcases e with ⟨_, _, _, _⟩; simp only [loopTgtOk] at h; exact h.1
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [WordNoStubCall, tgt_ne ht]
  | .call (some (vs, live)) t args none, l, h => by
      have ht : TgtGood t := by simpa [loopTgtOk] using h
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [WordNoStubCall, tgt_ne ht]
  | .call (some (vs, live)) t args (some (n, p1, p2, lo)), l, h => by
      simp only [loopTgtOk] at h
      obtain ⟨ht, h1, h2⟩ := h
      have hw1 := compHOL_noStub ctx p1 (l.1, l.2 + 1) h1
      rcases hw1' : LoopToWord.compHOL ctx p1 (l.1, l.2 + 1) with ⟨w1, l1⟩
      have hw2 := compHOL_noStub ctx p2 l1 h2
      rcases hw2' : LoopToWord.compHOL ctx p2 l1 with ⟨w2, l2⟩
      rw [hw1'] at hw1; rw [hw2'] at hw2
      rw [LoopToWord.compHOL.eq_def]; (try dsimp only); simp [hw1', hw2', WordNoStubCall, tgt_ne ht, hw1, hw2]
  | .skip, _, _ => by rw [LoopToWord.compHOL]; rfl
  | .assign .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .store .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .setGlobal .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .load32 .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .loadByte .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .store32 .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .storeByte .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .break .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .continue .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .raise .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .return .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .tick, _, _ => by rw [LoopToWord.compHOL]; rfl
  | .fail, _, _ => by rw [LoopToWord.compHOL]; rfl
  | .locValue .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .ffi .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .shMem .., _, _ => by rw [LoopToWord.compHOL]; rfl
  | .primitive ds .addCarry as, _, _ => by
      rw [LoopToWord.compHOL.eq_def]; dsimp only; split <;> rfl
  | .arith (.longMul ..), _, _ => by rw [LoopToWord.compHOL]; rfl
  | .arith (.longDiv ..), _, _ => by rw [LoopToWord.compHOL]; rfl
  | .arith (.div ..), _, _ => by rw [LoopToWord.compHOL]; rfl
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

/-! ## Pancake → … → LoopToWord: `WordNoStubCall`, no hypothesis -/

theorem loopToWordCompile_noStub {width : Nat} [NeZero width]
    (code : List (Nat × List Nat × HolLoopProg width)) (h : ∀ x ∈ code, loopTgtOk x.2.2) :
    ∀ y ∈ loopToWordCompileHOL code, WordNoStubCall y.2.2 = true := by
  intro y hy
  unfold loopToWordCompileHOL loopToWordCompileProgHOL at hy
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
  unfold loopToWordCompFuncHOL
  exact compHOL_noStub _ _ _ (h e he)

/-- Main result: every WordLang function produced from **any** Pancake program by
PanSimp → PanStructs → PanGlobals → PanToCrep → CrepToLoop → LoopToWord has no call
targeting `Flapjack.Compiler.Backend.StackLang.gcStubLocation`. -/
theorem panToWord_NoStubCall {width : Nat} [NeZero width]
    (arch : Compiler.Encoders.Asm.AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width)) :
    ∀ y ∈ panToWordCompileProgHOL arch prog, WordNoStubCall y.2.2 = true := by
  unfold panToWordCompileProgHOL
  exact loopToWordCompile_noStub _ (compileProgHOLExact_bodiesTgtOk _ _)

/-- And every function name is a user label `≥ 64`. -/
theorem panToWord_names {width : Nat} [NeZero width]
    (arch : Compiler.Encoders.Asm.AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width)) :
    ∀ y ∈ panToWordCompileProgHOL arch prog, 64 ≤ y.1 := by
  intro y hy
  unfold panToWordCompileProgHOL loopToWordCompileHOL loopToWordCompileProgHOL at hy
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hy
  obtain ⟨i, hi, -⟩ := compileProgHOLExact_names _ _ e he
  show 64 ≤ e.1; omega

/-! ## Witnesses -/

theorem tgtGood_rejects_stub : ¬ TgtGood (some Flapjack.Compiler.Backend.StackLang.gcStubLocation) := by
  simp [TgtGood, Flapjack.Compiler.Backend.StackLang.gcStubLocation, wordNumStubs, stackNumStubs]

theorem tgtGood_accepts : TgtGood (some 0) ∧ TgtGood (some 64) ∧ ¬ TgtGood none := by
  simp [TgtGood]

theorem findLab_empty (t : Compiler.Encoders.Asm.AsmArchitecture)
    (name : Basis.Pure.MlString.MlString) :
    findLabExact (mkCtxtExact t HolFiniteMapExact.empty HolFiniteMapExact.empty 0) name = 0 := rfl

theorem wordNoStubCall_tight {α : Type} :
    WordNoStubCall (WordLangProgHOL.call (α := α) none (some Flapjack.Compiler.Backend.StackLang.gcStubLocation) [] none)
      = false ∧
    WordNoStubCall (WordLangProgHOL.call (α := α) none (some 64) [] none) = true := by
  refine ⟨?_, ?_⟩ <;> simp [WordNoStubCall, Flapjack.Compiler.Backend.StackLang.gcStubLocation, wordNumStubs, stackNumStubs]


end InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.PanToWordGc



/-!
# The 10 WordToWord passes keep `WordNoStubCall`

Same pass decomposition as modules 298–302 (`NoSt` chain), with the predicate replaced by
"no call targets `Flapjack.Compiler.Backend.StackLang.gcStubLocation`". Closes `hcall` of
`StackGc.panToStackNames_bodies_NoSt_and_NoGcCall`.
-/

namespace InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.WordToWordGc

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
      (d != some Flapjack.Compiler.Backend.StackLang.gcStubLocation) &&
      (match ret with | none => true | some (_, _, r, _, _) => NSC r) &&
      (match h with | none => true | some (_, p, _, _) => NSC p)
  | _ => true

theorem NSC_eq {α : Type} : ∀ p : WordLangProgHOL α,
    NSC p = StackGc.WordNoStubCall p
  | .mustTerminate b => by simp only [NSC, StackGc.WordNoStubCall, NSC_eq b]
  | .seq a b => by simp only [NSC, StackGc.WordNoStubCall, NSC_eq a, NSC_eq b]
  | .ite _ _ _ a b => by simp only [NSC, StackGc.WordNoStubCall, NSC_eq a, NSC_eq b]
  | .loop _ b _ => by simp only [NSC, StackGc.WordNoStubCall, NSC_eq b]
  | .call none _ _ none => rfl
  | .call none _ _ (some (_, p, _, _)) => by
      simp only [NSC, StackGc.WordNoStubCall, NSC_eq p]
  | .call (some (_, _, r, _, _)) _ _ none => by
      simp only [NSC, StackGc.WordNoStubCall, NSC_eq r]
  | .call (some (_, _, r, _, _)) _ _ (some (_, p, _, _)) => by
      simp only [NSC, StackGc.WordNoStubCall, NSC_eq r, NSC_eq p]
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
theorem panToWordToWord_NoGcCall {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) :
    ∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      StackGc.WordNoStubCall y.2.2 = true := by
  intro y hy
  rw [← NSC_eq]
  exact wordToWordCompile_NSC wc ac _
    (fun x hx => by rw [NSC_eq]; exact PanToWordGc.panToWord_NoStubCall arch prog x hx) y hy

/-! ## Witnesses -/

theorem NSC_rejects_stub_call {α : Type} :
    NSC (WordLangProgHOL.seq (α := α) .skip
      (.call none (some Flapjack.Compiler.Backend.StackLang.gcStubLocation) [] none)) = false := by
  simp [NSC, Flapjack.Compiler.Backend.StackLang.gcStubLocation, wordNumStubs, stackNumStubs]

theorem NSC_accepts_user_call {α : Type} :
    NSC (WordLangProgHOL.call (α := α) none (some 64) [] none) = true := by
  simp [NSC, Flapjack.Compiler.Backend.StackLang.gcStubLocation, wordNumStubs, stackNumStubs]

theorem NSC_allows_storeConsts {α : Type} :
    NSC (WordLangProgHOL.storeConsts (α := α) 0 1 2 3 []) = true := rfl


end InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall.WordToWordGc

namespace InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.PanLang
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural (NoTailHandler NoGcCall)

variable {width : Nat} [NeZero width]

/-! ## WordToStack and StackRawCall never put a handler on a tail call -/

theorem h_stackLoad : ∀ (l : List (Nat × Nat)) (x : HolProg width),
    NoTailHandler (wStackLoadNative l x) = NoTailHandler x
  | [], x => rfl
  | (r, i) :: ps, x => by
      simp only [wStackLoadNative, NoTailHandler, Bool.true_and]; exact h_stackLoad ps x

theorem h_regWrite1 (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (hg : ∀ n, NoTailHandler (g n) = true) : NoTailHandler (wRegWrite1Native g r kf) = true := by
  unfold wRegWrite1Native; dsimp only; split
  · exact hg _
  · simp [NoTailHandler, hg]

theorem h_wInst (i : HolInst width) (kf : Nat × Nat × Nat) :
    NoTailHandler (wInstNative i kf) = true := by
  unfold wInstNative
  split <;> (try simp only [h_stackLoad]) <;>
    first | rfl | (apply h_regWrite1; intro n; rfl)

theorem h_wMoveAux : ∀ (l : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat),
    NoTailHandler (wMoveAuxNative (width := width) l kf) = true
  | [], _ => rfl
  | [xy], kf => by
      rw [wMoveAuxNative]; unfold wMoveSingleNative; split <;> rfl
  | xy :: y :: ys, kf => by
      simp only [wMoveAuxNative, NoTailHandler, Bool.and_eq_true]
      refine ⟨?_, h_wMoveAux (y :: ys) kf⟩
      unfold wMoveSingleNative; split <;> rfl

theorem h_wMove (m : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    NoTailHandler (wMoveNative (width := width) m kf) = true := by
  unfold wMoveNative; exact h_wMoveAux _ _

theorem h_seqStackFree (n : Nat) (p : HolProg width) (h : NoTailHandler p = true) :
    NoTailHandler (seqStackFreeNative n p) = true := by
  unfold seqStackFreeNative; split
  · exact h
  · simpa [NoTailHandler] using h

theorem h_copyRetAux (k f : Nat) : ∀ n, NoTailHandler (copyRetAuxNative (width := width) k f n) = true
  | 0 => rfl
  | n + 1 => by
      rw [copyRetAuxNative]; simp only [listSeq, NoTailHandler, Bool.true_and]
      exact h_copyRetAux k f n

theorem h_copyRet {β γ : Type} (perf ih : Bool) (kf : Nat × Nat × γ) (vs : List β)
    (kont : HolProg width) (h : NoTailHandler kont = true) :
    NoTailHandler (copyRetNative perf ih kf vs kont) = true := by
  unfold copyRetNative; dsimp only; split
  · exact h
  · simp only [NoTailHandler, Bool.and_eq_true]
    exact ⟨h_copyRetAux _ _ _, h_seqStackFree _ _ h⟩

theorem h_stackMove (start offset i : Nat) (p : HolProg width) (h : NoTailHandler p = true) :
    ∀ n, NoTailHandler (stackMoveNative n start offset i p) = true := by
  intro n
  induction n generalizing start with
  | zero => exact h
  | succ n ih =>
      rw [stackMoveNative]; simp only [NoTailHandler, Bool.and_true]; exact ih _

theorem h_stackArgs {α β : Type} (d : Sum α β) (ac : Nat) (kf : Nat × Nat × Nat) :
    NoTailHandler (stackArgsNative (width := width) d ac kf) = true := by
  unfold stackArgsNative; exact h_stackMove _ _ _ _ rfl _

theorem h_callDest (pos : Option Nat) (args : List Nat) (kf : Nat × Nat × Nat) :
    NoTailHandler (callDestNative (width := width) pos args kf).1 = true := by
  unfold callDestNative; split
  · rfl
  · split
    · rfl
    · dsimp only; rw [h_stackLoad]; rfl

theorem h_pushHandler {β γ : Type} (perf : Bool) (l1 l2 : Nat) (kf : Nat × β × γ) :
    NoTailHandler (pushHandlerNative (width := width) perf l1 l2 kf) = true := by
  unfold pushHandlerNative; cases perf <;> rfl

theorem h_popHandler {β γ : Type} (perf : Bool) (kf : Nat × β × γ) (p : HolProg width)
    (h : NoTailHandler p = true) : NoTailHandler (popHandlerNative perf kf p) = true := by
  unfold popHandlerNative; simpa [NoTailHandler] using h

theorem h_wLive (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : NoTailHandler (wLiveNative live bs kf).1 = true := by
  unfold wLiveNative; split <;> rfl

theorem h_wShareInst (op : HolMemop) (v : Nat) (a : HolAddr width) (kf : Nat × Nat × Nat) :
    NoTailHandler (wShareInstNative op v a kf) = true := by
  unfold wShareInstNative
  split <;> (try simp only [h_stackLoad]) <;> first | rfl | (apply h_regWrite1; intro n; rfl)

/-- WordToStack never creates a StackLang `storeConsts` from a `NoSt` WordLang body. -/
theorem h_compNative (conf : AsmConfigExact width) (perf : Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
      (kf : Nat × Nat × Nat), NoSt p = true → NoTailHandler (compNative conf perf p bs kf).1 = true
  | .seq a b, bs, kf, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [compNative]; simp only [NoTailHandler, Bool.and_eq_true]
      exact ⟨h_compNative conf perf a _ _ h.1, h_compNative conf perf b _ _ h.2⟩
  | .ite c r ri a b, bs, kf, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      have ha := h_compNative conf perf a bs kf h.1
      have hb := h_compNative conf perf b (compNative conf perf a bs kf).2 kf h.2
      rw [compNative]; dsimp only
      split
      · rw [h_stackLoad]; simp only [NoTailHandler, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · split
        · rw [h_stackLoad]; simp only [NoTailHandler, Bool.and_eq_true]; exact ⟨ha, hb⟩
        · simp only [NoTailHandler, Bool.true_and]; rw [h_stackLoad]
          simp only [NoTailHandler, Bool.and_eq_true]; exact ⟨ha, hb⟩
  | .mustTerminate a, bs, kf, h => by rw [compNative]; exact h_compNative conf perf a _ _ h
  | .loop x a y, bs, kf, h => by
      rw [compNative]; exact h_compNative conf perf a _ _ h
  | .call none d args hd, bs, kf, h => by
      rw [compNative]; dsimp only
      simp only [NoTailHandler, Bool.and_eq_true]
      exact ⟨h_callDest _ _ _, h_seqStackFree _ _ rfl⟩
  | .call (some (vs, live, rc, l1, l2)) d args none, bs, kf, h => by
      simp only [NoSt, Bool.and_true] at h
      have hr := h_compNative conf perf rc (wLiveNative live bs kf).2 kf h
      rw [compNative]; dsimp only
      simp only [NoTailHandler, Bool.and_eq_true, Bool.and_true]
      refine ⟨h_callDest _ _ _, h_wLive _ _ _, h_stackArgs _ _ _, ?_, ?_⟩
      · split <;> rfl
      · refine ⟨?_, h_copyRet _ _ _ _ _ hr⟩
        split <;> rfl
  | .call (some (vs, live, rc, l1, l2)) d args (some (e, hc, h1, h2)), bs, kf, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      have hr := h_compNative conf perf rc (wLiveNative live bs kf).2 kf h.1
      have hh := h_compNative conf perf hc
        (compNative conf perf rc (wLiveNative live bs kf).2 kf).2 kf h.2
      rw [compNative]; dsimp only
      simp only [NoTailHandler, Bool.and_eq_true]
      refine ⟨h_callDest _ _ _, h_wLive _ _ _, h_pushHandler _ _ _ _,
        h_stackArgs _ _ _, ?_, ⟨?_, h_copyRet _ _ _ _ _ (h_popHandler _ _ _ hr)⟩, hh⟩
      · split <;> rfl
      · split <;> rfl
  | .storeConsts .., _, _, h => by simp [NoSt] at h
  | .move .., bs, kf, h => by rw [compNative]; exact h_wMove _ _
  | .inst i, bs, kf, h => by rw [compNative]; exact h_wInst _ _
  | .return v vs, bs, kf, h => by
      rw [compNative]; dsimp only; rw [h_stackLoad]; exact h_seqStackFree _ _ rfl
  | .opCurrHeap .., bs, kf, h => by
      rw [compNative]; dsimp only; rw [h_stackLoad]; apply h_regWrite1; intro; rfl
  | .set name e, bs, kf, h => by
      rw [compNative.eq_def]; dsimp only
      repeat' split
      all_goals first | rfl | (rw [h_stackLoad]; rfl)
  | .get d st, bs, kf, h => by
      rw [compNative]; exact h_regWrite1 (fun r => .get r (storeNameOfWord st)) d kf (fun _ => rfl)
  | .locValue d l, bs, kf, h => by
      rw [compNative]; exact h_regWrite1 (fun n => .locValue n l 0) d kf (fun _ => rfl)
  | .alloc _ live, bs, kf, h => by
      rw [compNative]; simp only [NoTailHandler, Bool.and_true]; exact h_wLive _ _ _
  | .install .., bs, kf, h | .codeBufferWrite .., bs, kf, h | .dataBufferWrite .., bs, kf, h => by
      rw [compNative] <;> (try dsimp only) <;> rw [h_stackLoad] <;> rfl
  | .shareInst op v e, bs, kf, h => by
      rw [compNative]; split
      · rfl
      · exact h_wShareInst _ _ _ _
  | .skip, _, _, _ | .raise .., _, _, _ | .tick, _, _, _ | .break .., _, _, _
  | .continue .., _, _, _ | .ffi .., _, _, _ | .assign .., _, _, _ | .store .., _, _, _ => by
      rw [compNative] <;> first | rfl | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem h_compileProgNative (conf : AsmConfigExact width) (perf : Bool)
    (p : WordLangProgHOL (BitVec width)) (ac rc : Nat) (bs : AppList (BitVec width) × Nat)
    (h : NoSt p = true) : NoTailHandler (compileProgNative conf perf p ac rc bs).1 = true := by
  unfold compileProgNative; dsimp only
  simp only [NoTailHandler, Bool.true_and]; exact h_compNative conf perf p _ _ h

theorem h_compileWordToStack {β : Type} (conf : AsmConfigExact width) (perf : Bool) (rc : Nat) :
    ∀ (progs : List (β × Nat × WordLangProgHOL (BitVec width))) (bs : AppList (BitVec width) × Nat),
      (∀ x ∈ progs, NoSt x.2.2 = true) →
      ∀ y ∈ (compileWordToStackNative conf perf rc progs bs).1, NoTailHandler y.2 = true
  | [], _, _ => by intro y hy; simp [compileWordToStackNative] at hy
  | (i, ac, p) :: ps, bs, h => by
      intro y hy
      rw [compileWordToStackNative] at hy; dsimp only at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h_compileProgNative conf perf p ac rc bs (h _ (List.mem_cons_self ..))
      · exact h_compileWordToStack conf perf rc ps _
          (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy

/-- Top-level WordToStack: every *compiled body* is `NoTailHandler`; the only
StackLang `storeConsts` is the fixed prepended stub. -/
theorem h_compileNative_bodies (conf : AsmConfigExact width) (perf : Bool)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, NoSt x.2.2 = true) :
    ∀ y ∈ (compileNative conf perf progs).2.2.2,
      y.1 = storeConstsStubLocation ∨ NoTailHandler y.2 = true := by
  intro y hy
  unfold compileNative at hy; dsimp only at hy
  rcases List.mem_cons.1 hy with rfl | hy
  · right; unfold raiseStubNative; cases perf <;> rfl
  rcases List.mem_cons.1 hy with rfl | hy
  · left; rfl
  · right; exact h_compileWordToStack conf perf _ progs _ h y hy

theorem th_compSeq (a b fb : HolProg width) (info : Spt Nat) (hfb : NoTailHandler fb = true) :
    NoTailHandler (StackRawCall.compSeq a b info fb) = true := by
  unfold StackRawCall.compSeq; split
  · exact hfb
  · split
    · exact hfb
    · split
      · rfl
      · split <;> rfl

theorem th_rawCallComp (info : Spt Nat) :
    ∀ p : HolProg width, NoTailHandler p = true → NoTailHandler (StackRawCall.comp info p) = true
  | .seq a b, h => by
      simp only [NoTailHandler, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; apply th_compSeq
      simp only [NoTailHandler, Bool.and_eq_true]
      exact ⟨th_rawCallComp info a h.1, th_rawCallComp info b h.2⟩
  | .ite c r ri a b, h => by
      simp only [NoTailHandler, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [NoTailHandler, Bool.and_eq_true]
      exact ⟨th_rawCallComp info a h.1, th_rawCallComp info b h.2⟩
  | .loop a, h => by rw [StackRawCall.comp]; exact th_rawCallComp info a h
  | .call none d e, h => by rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all)
  | .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [NoTailHandler, Bool.and_true] at h
      rw [StackRawCall.comp]; simp only [NoTailHandler, Bool.and_true]
      exact th_rawCallComp info p1 h
  | .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [NoTailHandler, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [NoTailHandler, Bool.and_eq_true]
      exact ⟨th_rawCallComp info p1 h.1, th_rawCallComp info p2 h.2⟩
  | .skip, h | .inst .., h | .get .., h | .set .., h | .opCurrHeap .., h
  | .jumpLower .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .ret .., h
  | .break .., h | .continue .., h | .ffi .., h | .tick, h | .locValue .., h
  | .install .., h | .shMemOp .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .rawCall .., h
  | .stackAlloc .., h | .stackFree .., h | .stackStore .., h | .stackStoreAny .., h | .stackLoad .., h
  | .stackLoadAny .., h | .stackGetSize .., h | .stackSetSize .., h | .bitmapLoad .., h | .halt .., h => by
      rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem th_rawCallCompTop (info : Spt Nat) (p : HolProg width) (h : NoTailHandler p = true) :
    NoTailHandler (StackRawCall.compTop info p) = true := by
  rw [StackRawCall.compTop.eq_def]; split
  · rename_i a b
    simp only [NoTailHandler, Bool.and_eq_true] at h
    simp only [NoTailHandler, Bool.and_eq_true]
    exact ⟨th_rawCallComp info a h.1, th_rawCallComp info b h.2⟩
  · exact th_rawCallComp info p h


/-! ## NoGcCall from the transported chain -/

/-- On `storeConsts`-free code, StackGc's `NoStubCall` (label `4`) is exactly `NoGcCall`. -/
theorem noGcCall_of : ∀ p : HolProg width,
    StackGc.NoStubCall p = true → InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt p = true →
    NoGcCall p = true
  | .seq a b, h, s => by
      simp only [StackGc.NoStubCall, InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt,
        Bool.and_eq_true] at h s
      simp only [NoGcCall, Bool.and_eq_true]; exact ⟨noGcCall_of a h.1 s.1, noGcCall_of b h.2 s.2⟩
  | .ite _ _ _ a b, h, s => by
      simp only [StackGc.NoStubCall, InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt,
        Bool.and_eq_true] at h s
      simp only [NoGcCall, Bool.and_eq_true]; exact ⟨noGcCall_of a h.1 s.1, noGcCall_of b h.2 s.2⟩
  | .loop a, h, s => by
      simp only [StackGc.NoStubCall, InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt] at h s
      simp only [NoGcCall]; exact noGcCall_of a h s
  | .call ret t hd, h, s => by
      cases ret with
      | none => cases hd with
        | none =>
          cases t <;> simp_all [StackGc.NoStubCall, NoGcCall]
        | some x =>
          obtain ⟨q, _, _⟩ := x
          simp only [StackGc.NoStubCall, InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt,
            Bool.and_eq_true, Bool.true_and] at h s
          simp only [NoGcCall, Bool.and_eq_true, Bool.true_and]
          cases t <;> simp_all [noGcCall_of q]
      | some x =>
        obtain ⟨r, _, _, _⟩ := x
        cases hd with
        | none =>
          simp only [StackGc.NoStubCall, InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt,
            Bool.and_eq_true, Bool.and_true] at h s
          simp only [NoGcCall, Bool.and_eq_true, Bool.and_true]
          cases t <;> simp_all [noGcCall_of r]
        | some y =>
          obtain ⟨q, _, _⟩ := y
          simp only [StackGc.NoStubCall, InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt,
            Bool.and_eq_true] at h s
          simp only [NoGcCall, Bool.and_eq_true]
          cases t <;> simp_all [noGcCall_of r, noGcCall_of q]
  | .storeConsts .., _, s => by
      simp [InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt] at s
  | .skip, _, _ | .inst .., _, _ | .get .., _, _ | .set .., _, _ | .opCurrHeap .., _, _
  | .jumpLower .., _, _ | .alloc .., _, _ | .raise .., _, _ | .ret .., _, _ | .break .., _, _
  | .continue .., _, _ | .ffi .., _, _ | .tick, _, _ | .locValue .., _, _ | .install .., _, _
  | .shMemOp .., _, _ | .codeBufferWrite .., _, _ | .dataBufferWrite .., _, _ | .rawCall .., _, _
  | .stackAlloc .., _, _ | .stackFree .., _, _ | .stackStore .., _, _ | .stackStoreAny .., _, _
  | .stackLoad .., _, _ | .stackLoadAny .., _, _ | .stackGetSize .., _, _ | .stackSetSize .., _, _
  | .bitmapLoad .., _, _ | .halt .., _, _ => rfl

/-- The section list fed to StackAlloc by `StackToLab.compile`. -/
noncomputable def rawCallSections (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) : List (Nat × HolProg width) :=
  StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
    (panToWordCompileProgHOL arch prog)).2).2.2.2

theorem mem_rawCallSections {arch : AsmArchitecture} {prog : List (DeclHOL width)}
    {wc : WordToWord.Config} {ac : AsmConfigExact width} {perf : Bool} {y : Nat × HolProg width}
    (hy : y ∈ rawCallSections arch prog wc ac perf) :
    ∃ x ∈ (compileNative ac perf (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y = (x.1, StackRawCall.compTop (StackRawCall.collectInfo
        (compileNative ac perf (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2).2.2.2 .ln) x.2) := by
  simp only [rawCallSections, StackRawCall.compile] at hy
  rcases List.mem_map.1 hy with ⟨x, hx, rfl⟩
  exact ⟨x, hx, rfl⟩

/-- **(1) `NoGcCall`, no hypothesis.** Every StackRawCall section of every Pancake program,
the raise stub `5` and the `storeConsts` stub `6` included, has no direct call to the GC stub `4`. -/
theorem panToStackRawCall_noGcCall_unconditional (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, NoGcCall y.2 = true := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_rawCallSections hy
  rcases StackGc.c_compileNative ac perf _
      (fun z hz => ⟨InitECandidate.Solver.PanToStackNoStoreConsts.panToWordToWord_NoSt arch prog wc ac z hz,
        WordToWordGc.panToWordToWord_NoGcCall arch prog wc ac z hz⟩) x hx with h6 | hc
  · -- stub 6: locate it and compute
    have hmem := hx
    unfold compileNative at hmem; dsimp only at hmem
    rcases List.mem_cons.1 hmem with rfl | hmem
    · simp [storeConstsStubLocation, raiseStubLocation, wordNumStubs, stackNumStubs] at h6
    rcases List.mem_cons.1 hmem with rfl | hmem
    · dsimp only
      simp [storeConstsStubNative, StackRawCall.compTop, StackRawCall.comp, NoGcCall]
    · rcases StackGc.c_compileNative ac perf _
        (fun z hz => ⟨InitECandidate.Solver.PanToStackNoStoreConsts.panToWordToWord_NoSt arch prog wc ac z hz,
          WordToWordGc.panToWordToWord_NoGcCall arch prog wc ac z hz⟩) x hx with _ | hc
      · have := StackGc.n_compileWordToStack ac perf _ _ _
          (fun z hz => ⟨InitECandidate.Solver.PanToStackNoStoreConsts.panToWordToWord_NoSt arch prog wc ac z hz,
            WordToWordGc.panToWordToWord_NoGcCall arch prog wc ac z hz⟩) x hmem
        have hcr := StackGc.c_rawCallCompTop (StackRawCall.collectInfo
          (compileNative ac perf (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2).2.2.2 .ln) _ this
        exact noGcCall_of _ (StackGc.of_clean hcr).2 (StackGc.of_clean hcr).1
      · have hcr := StackGc.c_rawCallCompTop (StackRawCall.collectInfo
          (compileNative ac perf (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2).2.2.2 .ln) _ hc
        exact noGcCall_of _ (StackGc.of_clean hcr).2 (StackGc.of_clean hcr).1
  · have hcr := StackGc.c_rawCallCompTop (StackRawCall.collectInfo
      (compileNative ac perf (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2).2.2.2 .ln) _ hc
    exact noGcCall_of _ (StackGc.of_clean hcr).2 (StackGc.of_clean hcr).1

/-- **(1') StackAlloc output: no `.alloc`, no GC call, unconditionally** (on every section
produced from Pancake; StackAlloc's own GC stub at label `4` is the only GC code). -/
theorem panToStackAlloc_noAlloc_noGcCall_unconditional (arch : AsmArchitecture)
    (prog : List (DeclHOL width)) (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true := by
  intro y hy
  exact InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.panToStackAlloc_noAlloc_noGcCall
    arch prog wc ac perf y hy (panToStackRawCall_noGcCall_unconditional arch prog wc ac perf y hy)

/-! ## (2) StackAlloc is the exact identity on every section `≠ 6` -/

theorem panToStackRawCall_noTailHandler (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, NoTailHandler y.2 = true := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_rawCallSections hy
  apply th_rawCallCompTop
  rcases h_compileNative_bodies ac perf _
      (InitECandidate.Solver.PanToStackNoStoreConsts.panToWordToWord_NoSt arch prog wc ac) x hx with h6 | h
  · have hmem := hx
    unfold compileNative at hmem; dsimp only at hmem
    rcases List.mem_cons.1 hmem with rfl | hmem
    · unfold raiseStubNative; cases perf <;> rfl
    rcases List.mem_cons.1 hmem with rfl | hmem
    · rfl
    · exact h_compileWordToStack ac perf _ _ _
        (InitECandidate.Solver.PanToStackNoStoreConsts.panToWordToWord_NoSt arch prog wc ac) x hmem
  · exact h

theorem panToStackRawCall_noSt_ne_six (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      InitECandidate.Solver.PanToStackNoStoreConsts.StackNoSt y.2 = true := by
  intro y hy hne
  obtain ⟨x, hx, rfl⟩ := mem_rawCallSections hy
  rcases InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts.c_compileNative ac perf _
      (fun z hz => ⟨InitECandidate.Solver.PanToStackNoStoreConsts.panToWordToWord_NoSt arch prog wc ac z hz,
        InitECandidate.Solver.WordToWordNoStubCall.panToWordToWord_NoStubCall arch prog wc ac z hz⟩) x hx with h | h
  · exact absurd h hne
  · exact (InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts.of_clean
      (InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts.c_rawCallCompTop _ _ h)).1

/-- **(2) Exact identity.** For every Pancake program and every StackRawCall section `y`
with `y.1 ≠ 6`, `StackAlloc.progComp y = y`: StackAlloc rewrites nothing. -/
theorem panToStackAlloc_progComp_eq_id_of_ne_six (arch : AsmArchitecture)
    (prog : List (DeclHOL width)) (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y := by
  intro y hy hne
  obtain ⟨n, p⟩ := y
  show (n, (StackAlloc.comp n (StackAlloc.nextLabHOL p 2) p).1) = (n, p)
  rw [InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.stackAllocComp_id _ _ p
    (InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.panToStackRawCall_noAlloc_unconditional
      arch prog wc ac perf _ hy)
    (panToStackRawCall_noSt_ne_six arch prog wc ac perf _ hy hne)
    (panToStackRawCall_noTailHandler arch prog wc ac perf _ hy)]

/-- Tight: StackAlloc really rewrites section `6` (its `storeConsts … none` stays, but on a
tagged `storeConsts (some 6)` it emits a stub call) — the `≠ 6` exception is a real exception
of the *invariant*, and a tail handler is really dropped. -/
theorem stackAlloc_not_id_on_tagged_storeConsts (n m : Nat) :
    StackAlloc.comp n m (.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width) ≠
      ((.storeConsts 0 1 (some storeConstsStubLocation) : HolProg width), m) := by
  rw [StackAlloc.comp]; simp

/-! ## (3) Master -/

/-- **Master.** For every Pancake program:
* every StackRawCall section has no `.alloc` and no direct GC call (no hypothesis);
* after StackAlloc, still no `.alloc` and no GC call;
* StackAlloc is the exact identity on every section `≠ 6`;
* StackRemove adds zero extra clock (≤ 1 on a final `halt`) on every user body, from the live
  code table (section `6` removed), assuming only a `storeConsts`-free run-time oracle. -/
theorem pancake_stackAllocIdentity_noGc_zeroExtraClock {C F : Type}
    (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) :
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc y.2 = true ∧
      NoGcCall y.2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf,
      InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.PanToStackNoAlloc.StackNoAlloc
        (StackAlloc.progComp y).2 = true ∧ NoGcCall (StackAlloc.progComp y).2 = true) ∧
    (∀ y ∈ rawCallSections arch prog wc ac perf, y.1 ≠ storeConstsStubLocation →
      StackAlloc.progComp y = y) ∧
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
  ⟨fun y hy => ⟨InitECandidate.Solver.PanToStackRawCallNoAllocAndStackAllocStructural.panToStackRawCall_noAlloc_unconditional
      arch prog wc ac perf y hy, panToStackRawCall_noGcCall_unconditional arch prog wc ac perf y hy⟩,
   panToStackAlloc_noAlloc_noGcCall_unconditional arch prog wc ac perf,
   panToStackAlloc_progComp_eq_id_of_ne_six arch prog wc ac perf,
   InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt.panToStackRemove_body_zeroExtraClock_liveTable
     arch prog wc ac perf dc info⟩

end InitECandidate.Solver.PanToStackAllocIdentityAndUnconditionalNoGcCall
