import InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts
import Flapjack.Compiler.Backend.StackToLab.Native

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.PanToStackNoStoreConsts

variable {width : Nat} [NeZero width]

/-! ## `StackNoSt` alone through RawCall / StackAlloc / StackRemove / StackNames -/

theorem u_listSeq : ∀ (l : List (HolProg width)), (∀ x ∈ l, StackNoSt x = true) →
    StackNoSt (listSeqHOL l) = true
  | [], _ => rfl
  | [x], h => by rw [listSeqHOL]; exact h x (List.mem_singleton_self x)
  | x :: y :: ys, h => by
      rw [listSeqHOL]
      have hx := h x (List.mem_cons_self ..)
      have hr := u_listSeq (y :: ys) (fun z hz => h z (List.mem_cons_of_mem _ hz))
      simp only [StackNoSt, Bool.and_eq_true]; exact ⟨hx, hr⟩

theorem u_upshift (r : Nat) : ∀ n, StackNoSt (StackRemove.upshift (width := width) r n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.upshift]; split
    · rfl
    · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp only [StackNoSt, Bool.and_eq_true, Bool.true_and] at this ⊢
      exact this

theorem u_downshift (r : Nat) : ∀ n, StackNoSt (StackRemove.downshift (width := width) r n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.downshift]; split
    · rfl
    · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
      simp only [StackNoSt, Bool.and_eq_true, Bool.true_and] at this ⊢
      exact this

theorem u_stackFree (ptr : Nat) : ∀ n, StackNoSt (StackRemove.stackFree (width := width) ptr n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.stackFree]; split
    · rfl
    · split
      · rfl
      · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
        simp only [StackNoSt, Bool.and_eq_true]; exact ⟨rfl, this⟩

theorem u_singleStackAlloc (j : Bool) (ptr n : Nat) :
    StackNoSt (StackRemove.singleStackAlloc (width := width) j ptr n) = true := by
  unfold StackRemove.singleStackAlloc; split <;> rfl

theorem u_stackAlloc (j : Bool) (ptr : Nat) :
    ∀ n, StackNoSt (StackRemove.stackAlloc (width := width) j ptr n) = true := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [StackRemove.stackAlloc]; split
    · rfl
    · split
      · exact u_singleStackAlloc _ _ _
      · have := ih (n - StackRemove.maxStackAlloc) (by simp only [StackRemove.maxStackAlloc] at *; omega)
        have h0 := u_singleStackAlloc (width := width) j ptr StackRemove.maxStackAlloc
        simp only [StackNoSt, Bool.and_eq_true]; exact ⟨h0, this⟩

theorem u_split {a b : HolProg width} (ha : StackNoSt a = true) (hb : StackNoSt b = true) :
    StackNoSt (.seq a b) = true := by
  simp only [StackNoSt, Bool.and_eq_true]; exact ⟨ha, hb⟩

/-- StackRemove `comp` keeps both invariants; its `.storeConsts` (copy-loop) branch
is never taken on a `StackNoSt` body (that arm is discharged by contradiction). -/
theorem u_stackRemoveComp (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) :
    ∀ p : HolProg width, StackNoSt p = true → StackNoSt (StackRemove.comp j bd ptr p) = true
  | .seq a b, h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      rw [StackRemove.comp]; exact u_split (u_stackRemoveComp j bd ptr a h.1) (u_stackRemoveComp j bd ptr b h.2)
  | .ite c r ri a b, h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      rw [StackRemove.comp]; simp only [StackNoSt, Bool.and_eq_true]; exact ⟨u_stackRemoveComp j bd ptr a h.1, u_stackRemoveComp j bd ptr b h.2⟩
  | .loop a, h => by rw [StackRemove.comp]; exact u_stackRemoveComp j bd ptr a h
  | .call none t none, h => by
      rw [StackRemove.comp]
      rfl
  | .call none t (some (q, y1, y2)), h => by
      rw [StackRemove.comp]
      simp only [StackNoSt, Bool.and_eq_true, Bool.true_and] at h ⊢; exact u_stackRemoveComp j bd ptr q h
  | .call (some (r, x1, x2, x3)) t none, h => by
      rw [StackRemove.comp]
      simp only [StackNoSt, Bool.and_eq_true, Bool.and_true] at h ⊢; exact u_stackRemoveComp j bd ptr r h
  | .call (some (r, x1, x2, x3)) t (some (q, y1, y2)), h => by
      rw [StackRemove.comp]
      simp only [StackNoSt, Bool.and_eq_true] at h ⊢
      exact ⟨u_stackRemoveComp j bd ptr r h.1, u_stackRemoveComp j bd ptr q h.2⟩
  | .storeConsts .., h => by simp [StackNoSt, StackNoSt] at h
  | .get .., h | .set .., h => by
      rw [StackRemove.comp]; split <;> rfl
  | .stackFree n, h => by rw [StackRemove.comp]; exact u_stackFree _ _
  | .stackAlloc n, h => by rw [StackRemove.comp]; exact u_stackAlloc _ _ _
  | .stackStore r n, h => by
      rw [StackRemove.comp]; split
      · rfl
      · unfold StackRemove.stackStore
        exact u_split (u_upshift _ _) (u_split rfl (u_downshift _ _))
  | .stackLoad r n, h => by
      rw [StackRemove.comp]; split
      · rfl
      · unfold StackRemove.stackLoad
        exact u_split rfl (u_split (u_upshift _ _) rfl)
  | .bitmapLoad .., h => by
      rw [StackRemove.comp]; exact u_listSeq _ (by simp [StackNoSt, addInst, StackRemove.leftShiftInst])
  | .skip, h | .inst .., h | .opCurrHeap .., h | .jumpLower .., h | .alloc .., h
  | .raise .., h | .ret .., h | .break .., h | .continue .., h | .ffi .., h
  | .tick, h | .locValue .., h | .install .., h | .shMemOp .., h | .codeBufferWrite .., h
  | .dataBufferWrite .., h | .rawCall .., h | .stackStoreAny .., h | .stackLoadAny .., h | .stackGetSize .., h
  | .stackSetSize .., h | .halt .., h => by
      rw [StackRemove.comp] <;> first | rfl | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

/-! ### StackNames -/

theorem u_stackNames (f : Spt Nat) :
    ∀ p : HolProg width, StackNoSt p = true → StackNoSt (StackNames.progCompHOL f p) = true
  | .seq a b, h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      rw [StackNames.progCompHOL]; exact u_split (u_stackNames f a h.1) (u_stackNames f b h.2)
  | .ite c r ri a b, h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      rw [StackNames.progCompHOL]; simp only [StackNoSt, Bool.and_eq_true]; exact ⟨u_stackNames f a h.1, u_stackNames f b h.2⟩
  | .loop a, h => by rw [StackNames.progCompHOL]; exact u_stackNames f a h
  | .call none t none, h => by
      rw [StackNames.progCompHOL]
      rfl
  | .call none t (some (q, y1, y2)), h => by
      rw [StackNames.progCompHOL]
      simp only [StackNoSt, Bool.and_eq_true, Bool.true_and] at h ⊢; exact u_stackNames f q h
  | .call (some (r, x1, x2, x3)) t none, h => by
      rw [StackNames.progCompHOL]
      simp only [StackNoSt, Bool.and_eq_true, Bool.and_true] at h ⊢; exact u_stackNames f r h
  | .call (some (r, x1, x2, x3)) t (some (q, y1, y2)), h => by
      rw [StackNames.progCompHOL]
      simp only [StackNoSt, Bool.and_eq_true] at h ⊢
      exact ⟨u_stackNames f r h.1, u_stackNames f q h.2⟩
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
theorem u_compSeq (a b fb : HolProg width) (info : Spt Nat) (hfb : StackNoSt fb = true) :
    StackNoSt (StackRawCall.compSeq a b info fb) = true := by
  unfold StackRawCall.compSeq; split
  · exact hfb
  · split
    · exact hfb
    · split
      · rfl
      · split <;> rfl

theorem u_rawCallComp (info : Spt Nat) :
    ∀ p : HolProg width, StackNoSt p = true → StackNoSt (StackRawCall.comp info p) = true
  | .seq a b, h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; exact u_compSeq _ _ _ _ (u_split (u_rawCallComp info a h.1) (u_rawCallComp info b h.2))
  | .ite c r ri a b, h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [StackNoSt, Bool.and_eq_true]; exact ⟨u_rawCallComp info a h.1, u_rawCallComp info b h.2⟩
  | .loop a, h => by rw [StackRawCall.comp]; exact u_rawCallComp info a h
  | .call none d e, h => by rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all)
  | .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [StackNoSt, Bool.and_eq_true, Bool.and_true] at h
      rw [StackRawCall.comp]; simp only [StackNoSt, Bool.and_eq_true, Bool.and_true]
      exact u_rawCallComp info p1 h
  | .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      rw [StackRawCall.comp]; simp only [StackNoSt, Bool.and_eq_true]
      exact ⟨u_rawCallComp info p1 h.1, u_rawCallComp info p2 h.2⟩
  | .skip, h | .inst .., h | .get .., h | .set .., h | .opCurrHeap .., h
  | .jumpLower .., h | .alloc .., h | .storeConsts .., h | .raise .., h | .ret .., h
  | .break .., h | .continue .., h | .ffi .., h | .tick, h | .locValue .., h
  | .install .., h | .shMemOp .., h | .codeBufferWrite .., h | .dataBufferWrite .., h | .rawCall .., h
  | .stackAlloc .., h | .stackFree .., h | .stackStore .., h | .stackStoreAny .., h | .stackLoad .., h
  | .stackLoadAny .., h | .stackGetSize .., h | .stackSetSize .., h | .bitmapLoad .., h | .halt .., h => by
      rw [StackRawCall.comp] <;> first | exact h | (intros; simp_all) | skip
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem u_rawCallCompTop (info : Spt Nat) (p : HolProg width) (h : StackNoSt p = true) :
    StackNoSt (StackRawCall.compTop info p) = true := by
  rw [StackRawCall.compTop.eq_def]; split
  · rename_i a b
    simp only [StackNoSt, Bool.and_eq_true] at h
    exact u_split (u_rawCallComp info a h.1) (u_rawCallComp info b h.2)
  · exact u_rawCallComp info p h


theorem u_body_chain (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat)
    (f : Spt Nat) (n : Nat) (p : HolProg width) (h : StackNoSt p = true) :
    StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
      (StackAlloc.progComp (n, StackRawCall.compTop info p)).2)) = true := by
  apply u_stackNames; apply u_stackRemoveComp
  exact s_progComp (n, _) (u_rawCallCompTop info p h)

/-- Unconditional: for every Pancake program, every non-stub body is `StackNoSt` after
WordToStack, raw-call, StackAlloc, StackRemove and StackNames. No call-target premise. -/
theorem panToStackNames_bodies_StackNoSt_unconditional (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      StackNoSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = true := by
  intro y hy
  rcases s_compileNative_bodies ac perf _ (panToWordToWord_NoSt arch prog wc ac) y hy with e | h
  · exact Or.inl e
  · exact Or.inr (u_body_chain info j bd ptr f y.1 y.2 h)

/-- StackRemove expands a real `storeConsts` into the copy loop (non-empty code): the
dead branch is not trivially empty. -/
theorem stackRemove_storeConsts_not_skip (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) :
    StackRemove.comp j bd ptr (.storeConsts 3 4 none : HolProg width) ≠ .skip := by
  rw [StackRemove.comp]; simp [listSeqHOL]

/-! ## StackToLab native `flattenHOL` -/

/-- Native `flattenHOL` has no `storeConsts` clause: it falls into the wildcard and
emits no line at all (neither `Const` nor the terminating label instruction). -/
theorem flatten_storeConsts_empty (tail : Bool) (s b : Nat) (stub : Option Nat)
    (sid next : Nat) (cs bs : List Nat) :
    StackToLab.flattenHOL tail (.storeConsts s b stub : HolProg width) sid next cs bs =
      (.list [], false, next) := by
  rw [StackToLab.flattenHOL] <;> intros <;> simp_all

/-- Some `storeConsts` node is reached by `flattenHOL`'s recursion. -/
def FlattenVisitsSt : HolProg width → Bool
  | .storeConsts .. => true
  | .seq a b => FlattenVisitsSt a || FlattenVisitsSt b
  | .ite _ _ _ a b => FlattenVisitsSt a || FlattenVisitsSt b
  | .loop b => FlattenVisitsSt b
  | .call none _ _ => false
  | .call (some (r, _, _, _)) _ h =>
      FlattenVisitsSt r || (match h with | none => false | some (q, _, _) => FlattenVisitsSt q)
  | _ => false

theorem not_visits_of_StackNoSt : ∀ p : HolProg width, StackNoSt p = true → FlattenVisitsSt p = false
  | .storeConsts .., h => by simp [StackNoSt] at h
  | .seq a b, h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      simp [FlattenVisitsSt, not_visits_of_StackNoSt a h.1, not_visits_of_StackNoSt b h.2]
  | .ite _ _ _ a b, h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      simp [FlattenVisitsSt, not_visits_of_StackNoSt a h.1, not_visits_of_StackNoSt b h.2]
  | .loop a, h => by simp only [StackNoSt] at h; simp [FlattenVisitsSt, not_visits_of_StackNoSt a h]
  | .call none _ _, _ => rfl
  | .call (some (r, _, _, _)) _ none, h => by
      simp only [StackNoSt, Bool.and_true] at h
      simp [FlattenVisitsSt, not_visits_of_StackNoSt r h]
  | .call (some (r, _, _, _)) _ (some (q, _, _)), h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      simp [FlattenVisitsSt, not_visits_of_StackNoSt r h.1, not_visits_of_StackNoSt q h.2]
  | .skip, _ | .inst .., _ | .get .., _ | .set .., _ | .opCurrHeap .., _ | .jumpLower .., _
  | .alloc .., _ | .raise .., _ | .ret .., _ | .break .., _ | .continue .., _ | .ffi .., _
  | .tick, _ | .locValue .., _ | .install .., _ | .shMemOp .., _ | .codeBufferWrite .., _ | .dataBufferWrite .., _
  | .rawCall .., _ | .stackAlloc .., _ | .stackFree .., _ | .stackStore .., _ | .stackStoreAny .., _ | .stackLoad .., _
  | .stackLoadAny .., _ | .stackGetSize .., _ | .stackSetSize .., _ | .bitmapLoad .., _ | .halt .., _ => rfl
termination_by p => sizeOf p
decreasing_by all_goals (simp_wf; try omega)

theorem visits_storeConsts_tight :
    FlattenVisitsSt (.seq .skip (.storeConsts 0 1 none) : HolProg width) = true := rfl

/-- `progToSectionHOL` keeps the function name as section id. -/
theorem progToSection_sectionId (n : Nat) (p : HolProg width) :
    (StackToLab.progToSectionHOL (n, p)).sectionId = n := rfl

/-- Final characterisation: each non-stub Pancake body reaches `progToSectionHOL` with
`StackNoSt`; `flattenHOL` never visits a `storeConsts` node; section id = function name. -/
theorem panToLabSection_unconditional (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr : Nat) (f : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      (FlattenVisitsSt (StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2)) = false ∧
       (StackToLab.progToSectionHOL (y.1, StackNames.progCompHOL f (StackRemove.comp j bd ptr
          (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2))).sectionId = y.1) := by
  intro y hy
  rcases panToStackNames_bodies_StackNoSt_unconditional arch prog wc ac perf info j bd ptr f y hy
    with e | h
  · exact Or.inl e
  · exact Or.inr ⟨not_visits_of_StackNoSt _ h, rfl⟩


end InitECandidate.Solver.PanToStackToLabUnconditionalNoStoreConsts
