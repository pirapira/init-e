import InitECandidate.Solver.WordToWordFullCompileNoStoreConsts
import Flapjack.Pancake.PanToWord
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.StackAlloc.Compile

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

namespace InitECandidate.Solver.PanToStackNoStoreConsts

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.PanLang
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.WordToWordFullCompileNoStoreConsts

variable {width : Nat} [NeZero width]

/-! ## Word side: the whole `panToWordCompileProgHOL` output, through `WordToWord.compile` -/

theorem loopToWordCompFunc_NoSt (name : Nat) (params : List Nat) (body : HolLoopProg width) :
    NoSt (loopToWordCompFuncHOL name params body) = true := by
  unfold loopToWordCompFuncHOL; exact loopToWord_NoSt _ _ _

theorem loopToWordCompile_NoSt (code : List (Nat × List Nat × HolLoopProg width)) :
    ∀ x ∈ loopToWordCompileHOL code, NoSt x.2.2 = true := by
  intro x hx
  unfold loopToWordCompileHOL loopToWordCompileProgHOL at hx
  obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
  exact loopToWordCompFunc_NoSt _ _ _

/-- Every function emitted by the whole Pancake→Word front end has `NoSt`. -/
theorem panToWord_NoSt (arch : AsmArchitecture) (prog : List (DeclHOL width)) :
    ∀ x ∈ panToWordCompileProgHOL arch prog, NoSt x.2.2 = true := by
  unfold panToWordCompileProgHOL; exact loopToWordCompile_NoSt _

theorem wordToWordCompile_NoSt (wc : WordToWord.Config) (ac : AsmConfigExact width)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, NoSt x.2.2 = true) :
    ∀ y ∈ (WordToWord.compile wc ac progs).2, NoSt y.2.2 = true := by
  unfold WordToWord.compile; dsimp only
  apply t_fullCompile_list
  intro x hx
  exact h _ (List.of_mem_zip hx).1

/-- Pancake → … → LoopToWord → WordToWord: every function has `NoSt`. -/
theorem panToWordToWord_NoSt (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) :
    ∀ y ∈ (WordToWord.compile wc ac (panToWordCompileProgHOL arch prog)).2,
      NoSt y.2.2 = true :=
  wordToWordCompile_NoSt wc ac _ (panToWord_NoSt arch prog)

/-! ## Stack side -/

/-- No StackLang `storeConsts` anywhere. -/
def StackNoSt : HolProg width → Bool
  | .storeConsts .. => false
  | .seq a b => StackNoSt a && StackNoSt b
  | .ite _ _ _ a b => StackNoSt a && StackNoSt b
  | .loop b => StackNoSt b
  | .call ret _ h =>
      (match ret with | none => true | some (r, _, _, _) => StackNoSt r) &&
      (match h with | none => true | some (q, _, _) => StackNoSt q)
  | _ => true

theorem s_stackLoad : ∀ (l : List (Nat × Nat)) (x : HolProg width),
    StackNoSt (wStackLoadNative l x) = StackNoSt x
  | [], x => rfl
  | (r, i) :: ps, x => by
      simp only [wStackLoadNative, StackNoSt, Bool.true_and]; exact s_stackLoad ps x

theorem s_regWrite1 (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (hg : ∀ n, StackNoSt (g n) = true) : StackNoSt (wRegWrite1Native g r kf) = true := by
  unfold wRegWrite1Native; dsimp only; split
  · exact hg _
  · simp [StackNoSt, hg]

theorem s_wInst (i : HolInst width) (kf : Nat × Nat × Nat) :
    StackNoSt (wInstNative i kf) = true := by
  unfold wInstNative
  split <;> (try simp only [s_stackLoad]) <;>
    first | rfl | (apply s_regWrite1; intro n; rfl)

theorem s_wMoveAux : ∀ (l : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat),
    StackNoSt (wMoveAuxNative (width := width) l kf) = true
  | [], _ => rfl
  | [xy], kf => by
      rw [wMoveAuxNative]; unfold wMoveSingleNative; split <;> rfl
  | xy :: y :: ys, kf => by
      simp only [wMoveAuxNative, StackNoSt, Bool.and_eq_true]
      refine ⟨?_, s_wMoveAux (y :: ys) kf⟩
      unfold wMoveSingleNative; split <;> rfl

theorem s_wMove (m : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    StackNoSt (wMoveNative (width := width) m kf) = true := by
  unfold wMoveNative; exact s_wMoveAux _ _

theorem s_seqStackFree (n : Nat) (p : HolProg width) (h : StackNoSt p = true) :
    StackNoSt (seqStackFreeNative n p) = true := by
  unfold seqStackFreeNative; split
  · exact h
  · simpa [StackNoSt] using h

theorem s_copyRetAux (k f : Nat) : ∀ n, StackNoSt (copyRetAuxNative (width := width) k f n) = true
  | 0 => rfl
  | n + 1 => by
      rw [copyRetAuxNative]; simp only [listSeq, StackNoSt, Bool.true_and]
      exact s_copyRetAux k f n

theorem s_copyRet {β γ : Type} (perf ih : Bool) (kf : Nat × Nat × γ) (vs : List β)
    (kont : HolProg width) (h : StackNoSt kont = true) :
    StackNoSt (copyRetNative perf ih kf vs kont) = true := by
  unfold copyRetNative; dsimp only; split
  · exact h
  · simp only [StackNoSt, Bool.and_eq_true]
    exact ⟨s_copyRetAux _ _ _, s_seqStackFree _ _ h⟩

theorem s_stackMove (start offset i : Nat) (p : HolProg width) (h : StackNoSt p = true) :
    ∀ n, StackNoSt (stackMoveNative n start offset i p) = true := by
  intro n
  induction n generalizing start with
  | zero => exact h
  | succ n ih =>
      rw [stackMoveNative]; simp only [StackNoSt, Bool.and_true]; exact ih _

theorem s_stackArgs {α β : Type} (d : Sum α β) (ac : Nat) (kf : Nat × Nat × Nat) :
    StackNoSt (stackArgsNative (width := width) d ac kf) = true := by
  unfold stackArgsNative; exact s_stackMove _ _ _ _ rfl _

theorem s_callDest (pos : Option Nat) (args : List Nat) (kf : Nat × Nat × Nat) :
    StackNoSt (callDestNative (width := width) pos args kf).1 = true := by
  unfold callDestNative; split
  · rfl
  · split
    · rfl
    · dsimp only; rw [s_stackLoad]; rfl

theorem s_pushHandler {β γ : Type} (perf : Bool) (l1 l2 : Nat) (kf : Nat × β × γ) :
    StackNoSt (pushHandlerNative (width := width) perf l1 l2 kf) = true := by
  unfold pushHandlerNative; cases perf <;> rfl

theorem s_popHandler {β γ : Type} (perf : Bool) (kf : Nat × β × γ) (p : HolProg width)
    (h : StackNoSt p = true) : StackNoSt (popHandlerNative perf kf p) = true := by
  unfold popHandlerNative; simpa [StackNoSt] using h

theorem s_wLive (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : StackNoSt (wLiveNative live bs kf).1 = true := by
  unfold wLiveNative; split <;> rfl

theorem s_wShareInst (op : HolMemop) (v : Nat) (a : HolAddr width) (kf : Nat × Nat × Nat) :
    StackNoSt (wShareInstNative op v a kf) = true := by
  unfold wShareInstNative
  split <;> (try simp only [s_stackLoad]) <;> first | rfl | (apply s_regWrite1; intro n; rfl)

/-- WordToStack never creates a StackLang `storeConsts` from a `NoSt` WordLang body. -/
theorem s_compNative (conf : AsmConfigExact width) (perf : Bool) :
    ∀ (p : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
      (kf : Nat × Nat × Nat), NoSt p = true → StackNoSt (compNative conf perf p bs kf).1 = true
  | .seq a b, bs, kf, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      rw [compNative]; simp only [StackNoSt, Bool.and_eq_true]
      exact ⟨s_compNative conf perf a _ _ h.1, s_compNative conf perf b _ _ h.2⟩
  | .ite c r ri a b, bs, kf, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      have ha := s_compNative conf perf a bs kf h.1
      have hb := s_compNative conf perf b (compNative conf perf a bs kf).2 kf h.2
      rw [compNative]; dsimp only
      split
      · rw [s_stackLoad]; simp only [StackNoSt, Bool.and_eq_true]; exact ⟨ha, hb⟩
      · split
        · rw [s_stackLoad]; simp only [StackNoSt, Bool.and_eq_true]; exact ⟨ha, hb⟩
        · simp only [StackNoSt, Bool.true_and]; rw [s_stackLoad]
          simp only [StackNoSt, Bool.and_eq_true]; exact ⟨ha, hb⟩
  | .mustTerminate a, bs, kf, h => by rw [compNative]; exact s_compNative conf perf a _ _ h
  | .loop x a y, bs, kf, h => by
      rw [compNative]; exact s_compNative conf perf a _ _ h
  | .call none d args hd, bs, kf, h => by
      rw [compNative]; dsimp only
      simp only [StackNoSt, Bool.and_eq_true]
      exact ⟨s_callDest _ _ _, s_seqStackFree _ _ rfl⟩
  | .call (some (vs, live, rc, l1, l2)) d args none, bs, kf, h => by
      simp only [NoSt, Bool.and_true] at h
      have hr := s_compNative conf perf rc (wLiveNative live bs kf).2 kf h
      rw [compNative]; dsimp only
      simp only [StackNoSt, Bool.and_eq_true, Bool.and_true]
      refine ⟨s_callDest _ _ _, s_wLive _ _ _, s_stackArgs _ _ _, ?_, ?_⟩
      · split <;> rfl
      · refine ⟨?_, s_copyRet _ _ _ _ _ hr⟩
        split <;> rfl
  | .call (some (vs, live, rc, l1, l2)) d args (some (e, hc, h1, h2)), bs, kf, h => by
      simp only [NoSt, Bool.and_eq_true] at h
      have hr := s_compNative conf perf rc (wLiveNative live bs kf).2 kf h.1
      have hh := s_compNative conf perf hc
        (compNative conf perf rc (wLiveNative live bs kf).2 kf).2 kf h.2
      rw [compNative]; dsimp only
      simp only [StackNoSt, Bool.and_eq_true]
      refine ⟨s_callDest _ _ _, s_wLive _ _ _, s_pushHandler _ _ _ _,
        s_stackArgs _ _ _, ?_, ⟨?_, s_copyRet _ _ _ _ _ (s_popHandler _ _ _ hr)⟩, hh⟩
      · split <;> rfl
      · split <;> rfl
  | .storeConsts .., _, _, h => by simp [NoSt] at h
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
  | .alloc _ live, bs, kf, h => by
      rw [compNative]; simp only [StackNoSt, Bool.and_true]; exact s_wLive _ _ _
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
    (h : NoSt p = true) : StackNoSt (compileProgNative conf perf p ac rc bs).1 = true := by
  unfold compileProgNative; dsimp only
  simp only [StackNoSt, Bool.true_and]; exact s_compNative conf perf p _ _ h

theorem s_compileWordToStack {β : Type} (conf : AsmConfigExact width) (perf : Bool) (rc : Nat) :
    ∀ (progs : List (β × Nat × WordLangProgHOL (BitVec width))) (bs : AppList (BitVec width) × Nat),
      (∀ x ∈ progs, NoSt x.2.2 = true) →
      ∀ y ∈ (compileWordToStackNative conf perf rc progs bs).1, StackNoSt y.2 = true
  | [], _, _ => by intro y hy; simp [compileWordToStackNative] at hy
  | (i, ac, p) :: ps, bs, h => by
      intro y hy
      rw [compileWordToStackNative] at hy; dsimp only at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact s_compileProgNative conf perf p ac rc bs (h _ (List.mem_cons_self ..))
      · exact s_compileWordToStack conf perf rc ps _
          (fun x hx => h x (List.mem_cons_of_mem _ hx)) y hy

/-- Top-level WordToStack: every *compiled body* is `StackNoSt`; the only
StackLang `storeConsts` is the fixed prepended stub. -/
theorem s_compileNative_bodies (conf : AsmConfigExact width) (perf : Bool)
    (progs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : ∀ x ∈ progs, NoSt x.2.2 = true) :
    ∀ y ∈ (compileNative conf perf progs).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoSt y.2 = true := by
  intro y hy
  unfold compileNative at hy; dsimp only at hy
  rcases List.mem_cons.1 hy with rfl | hy
  · right; unfold raiseStubNative; cases perf <;> rfl
  rcases List.mem_cons.1 hy with rfl | hy
  · left; rfl
  · right; exact s_compileWordToStack conf perf _ progs _ h y hy

/-- The prepended stub does contain a `storeConsts` (tightness of the exception). -/
theorem storeConstsStub_not_StackNoSt (k : Nat) :
    StackNoSt (storeConstsStubNative (width := width) k) = false := rfl

/-- StackAlloc `comp` preserves `StackNoSt` (it only rewrites `alloc` / `storeConsts (some _)`). -/
theorem s_stackAllocComp : ∀ (n m : Nat) (p : HolProg width), StackNoSt p = true →
    StackNoSt (StackAlloc.comp n m p).1 = true
  | n, m, .seq a b, h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [StackNoSt, Bool.and_eq_true]
      exact ⟨s_stackAllocComp n m a h.1, s_stackAllocComp n _ b h.2⟩
  | n, m, .ite c r ri a b, h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [StackNoSt, Bool.and_eq_true]
      exact ⟨s_stackAllocComp n m a h.1, s_stackAllocComp n _ b h.2⟩
  | n, m, .loop a, h => by
      rw [StackAlloc.comp]; exact s_stackAllocComp n m a h
  | n, m, .call none d e, h => by rw [StackAlloc.comp]; rfl
  | n, m, .call (some (p1, lr, l1, l2)) d none, h => by
      simp only [StackNoSt, Bool.and_true] at h
      rw [StackAlloc.comp]; simp only [StackNoSt, Bool.and_true]
      exact s_stackAllocComp n m p1 h
  | n, m, .call (some (p1, lr, l1, l2)) d (some (p2, k1, k2)), h => by
      simp only [StackNoSt, Bool.and_eq_true] at h
      rw [StackAlloc.comp]; simp only [StackNoSt, Bool.and_eq_true]
      exact ⟨s_stackAllocComp n m p1 h.1, s_stackAllocComp n _ p2 h.2⟩
  | n, m, .alloc _, h => by rw [StackAlloc.comp]; rfl
  | n, m, .storeConsts .., h => by simp [StackNoSt] at h
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

theorem s_progComp (x : Nat × HolProg width) (h : StackNoSt x.2 = true) :
    StackNoSt (StackAlloc.progComp x).2 = true := by
  obtain ⟨n, p⟩ := x; unfold StackAlloc.progComp; exact s_stackAllocComp _ _ _ h

/-- End-to-end: Pancake → Word → WordToWord → WordToStack → StackAlloc.comp: every
non-stub body is `StackNoSt`. -/
theorem panToStackAlloc_NoSt (arch : AsmArchitecture) (prog : List (DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨ StackNoSt (StackAlloc.progComp y).2 = true := by
  intro y hy
  rcases s_compileNative_bodies ac perf _ (panToWordToWord_NoSt arch prog wc ac) y hy with h | h
  · exact Or.inl h
  · exact Or.inr (s_progComp y h)


end InitECandidate.Solver.PanToStackNoStoreConsts
