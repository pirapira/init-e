import InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false

/-!
# Dead stub 6: `CodeNoSt` from the real StackAlloc code table

The StackRemove source code table is the list `StackAlloc.compile dc (StackRawCall.compile …)`.
1. Every section with label `≠ 6` is `Clean` (no `storeConsts`, no direct call/jump to `6`),
   including the GC stub, for every Pancake program.
2. A state whose `code` is that table with section `6` removed satisfies `CodeNoSt` with no
   further hypothesis on the code; only the dynamic `compileOracle` (code installed at run time
   by `install`) keeps an explicit hypothesis, discharged outright when the oracle installs nothing.

Limit: `Clean` only excludes direct targets `.inl 6`. It does not exclude an indirect call
`findCode (.inr r)` with a register holding `.loc 6 _`, so "evaluation never reads entry 6"
is not provable from `Clean` alone; it needs a semantic invariant on runtime values.
-/

namespace InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.PanToStackNoStoreConsts (StackNoSt panToWordToWord_NoSt)
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts
open InitECandidate.Solver.StackRemoveNoStoreConstsZeroExtraClock
open InitECandidate.Solver.StackRemoveInitMemoryAndCompileProgZeroExtraBodyClock

variable {width : Nat} [NeZero width]

/-- The real StackRemove source code table for a Pancake program. -/
noncomputable def stackAllocSections (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config) :
    List (Nat × HolProg width) :=
  StackAlloc.compile dc (StackRawCall.compile (compileNative ac perf (WordToWord.compile wc ac
    (panToWordCompileProgHOL arch prog)).2).2.2.2)

/-- The same table with the dead section `6` removed. -/
def liveSections (l : List (Nat × HolProg width)) : List (Nat × HolProg width) :=
  l.filter (fun e => e.1 != storeConstsStubLocation)

/-! ## 1. Every section other than `6` is `Clean` -/

theorem stackAllocSections_clean (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config) :
    ∀ e ∈ stackAllocSections arch prog wc ac perf dc,
      e.1 = storeConstsStubLocation ∨ Clean e.2 = true := by
  intro e he
  simp only [stackAllocSections, StackAlloc.compile, List.mem_append] at he
  rcases he with hg | hb
  · exact Or.inr (clean_gcStub dc e hg)
  · rcases List.mem_map.1 hb with ⟨b, hb', rfl⟩
    simp only [StackRawCall.compile] at hb'
    rcases List.mem_map.1 hb' with ⟨y, hy, rfl⟩
    rcases c_compileNative ac perf _
        (fun x hx => ⟨panToWordToWord_NoSt arch prog wc ac x hx,
          InitECandidate.Solver.WordToWordNoStubCall.panToWordToWord_NoStubCall arch prog wc ac x hx⟩)
        y hy with h6 | hc
    · exact Or.inl h6
    · right
      unfold StackAlloc.progComp
      exact c_stackAllocComp _ _ _ (c_rawCallCompTop _ _ hc)

/-- Every section with label `≠ 6`: no `storeConsts` **and** no direct call/jump to `6`. -/
theorem stackAllocSections_noSt_and_noStubCall (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config) :
    ∀ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 ≠ storeConstsStubLocation →
      StackNoSt e.2 = true ∧ NoStubCall e.2 = true ∧ Clean e.2 = true := by
  intro e he hne
  rcases stackAllocSections_clean arch prog wc ac perf dc e he with h | h
  · exact absurd h hne
  · exact ⟨(of_clean h).1, (of_clean h).2, h⟩

/-! ## 2. Unconditional `CodeNoSt` on the live table -/

theorem mem_of_alistLookup {α : Type} (k : Nat) (v : α) :
    ∀ l : List (Nat × α), sptAListLookup k l = some v → (k, v) ∈ l
  | [], h => by simp [sptAListLookup] at h
  | (o, w) :: rest, h => by
      simp only [sptAListLookup] at h
      split at h
      · rename_i e; subst e; cases h; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_of_alistLookup k v rest h)

/-- Every program stored in the live code table is `storeConsts`-free. -/
theorem liveTable_lookup_noSt (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config) :
    ∀ k p, sptLookup k (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = some p →
      StackNoSt p = true ∧ Clean p = true := by
  intro k p h
  rw [sptLookup_sptFromAList] at h
  have hm := mem_of_alistLookup k p _ h
  simp only [liveSections, List.mem_filter, bne_iff_ne, ne_eq] at hm
  have := stackAllocSections_noSt_and_noStubCall arch prog wc ac perf dc _ hm.1 hm.2
  exact ⟨this.1, this.2.2⟩

/-- **`CodeNoSt` with no code hypothesis.** Any state whose code table is the live table of a
Pancake program satisfies `CodeNoSt`, given only that the run-time oracle installs
`storeConsts`-free code. -/
theorem codeNoSt_liveTable {C F : Type} (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (s : StackSemStateFiniteExact width C F)
    (hcode : s.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)))
    (horacle : ∀ i, ∀ e ∈ (s.compileOracle i).2.1, StackNoSt e.2 = true) :
    CodeNoSt s :=
  ⟨fun k p h => (liveTable_lookup_noSt arch prog wc ac perf dc k p (hcode ▸ h)).1, horacle⟩

/-- Fully unconditional when the oracle installs no code. -/
theorem codeNoSt_liveTable_emptyOracle {C F : Type} (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (s : StackSemStateFiniteExact width C F)
    (hcode : s.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)))
    (horacle : ∀ i, (s.compileOracle i).2.1 = []) :
    CodeNoSt s :=
  codeNoSt_liveTable arch prog wc ac perf dc s hcode (fun i e he => by simp [horacle i] at he)

/-- Removing section `6` drops only label `6`: every other label is looked up unchanged. -/
theorem liveTable_lookup_eq (l : List (Nat × HolProg width)) (k : Nat)
    (hk : k ≠ storeConstsStubLocation) :
    sptLookup k (sptFromAList (liveSections l)) = sptLookup k (sptFromAList l) := by
  rw [sptLookup_sptFromAList, sptLookup_sptFromAList]
  induction l with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨o, w⟩ := e
      by_cases ho : o = storeConstsStubLocation
      · subst ho
        have : (storeConstsStubLocation != storeConstsStubLocation) = false := by simp
        simp only [liveSections, List.filter, this] at ih ⊢
        rw [ih]; simp [sptAListLookup, hk]
      · have : (o != storeConstsStubLocation) = true := by simp [ho]
        simp only [liveSections, List.filter, this] at ih ⊢
        simp only [sptAListLookup]; rw [ih]

/-- And label `6` is absent from the live table. -/
theorem liveTable_lookup_six (l : List (Nat × HolProg width)) :
    sptLookup storeConstsStubLocation (sptFromAList (liveSections l)) = none := by
  rw [sptLookup_sptFromAList]
  induction l with
  | nil => rfl
  | cons e rest ih =>
      obtain ⟨o, w⟩ := e
      by_cases ho : o = storeConstsStubLocation
      · subst ho
        have : (storeConstsStubLocation != storeConstsStubLocation) = false := by simp
        simp only [liveSections, List.filter, this] at ih ⊢; exact ih
      · have : (o != storeConstsStubLocation) = true := by simp [ho]
        simp only [liveSections, List.filter, this] at ih ⊢
        simp only [sptAListLookup, Ne.symm ho, if_false]; exact ih

/-! ## Instantiation: zero extra clock without external `CodeNoSt` -/

/-- **Master.** For every Pancake program and every user body (label `≠ 6`), the StackRemove
simulation from a state whose code is the live table adds zero extra clock (at most one tick on
a final `halt`), assuming only a `storeConsts`-free run-time oracle. -/
theorem panToStackRemove_body_zeroExtraClock_liveTable {C F : Type}
    (arch : AsmArchitecture) (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config)
    (info : Spt Nat) :
    ∀ y ∈ (compileNative ac perf (WordToWord.compile wc ac
        (panToWordCompileProgHOL arch prog)).2).2.2.2,
      y.1 = storeConstsStubLocation ∨
      ∀ (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
        (postSource target : StackSemStateFiniteExact width C F)
        (ptr : Nat) (bd : BitVec width × BitVec width) (j : Bool),
        source.code = sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc)) →
        (∀ i, ∀ e ∈ (source.compileOracle i).2.1, StackNoSt e.2 = true) →
        StackSemEvaluate.evaluate ((StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2, source) =
            (result, postSource) ∧ result ≠ some .error ∧
          StackRemove.stateRelHOL j bd ptr source target ∧
          StackProps.regBound (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2 ptr →
        ∃ clock postTarget, ClockOk clock result ∧
          StackSemEvaluate.evaluate (StackRemove.comp j bd ptr
            (StackAlloc.progComp (y.1, StackRawCall.compTop info y.2)).2,
            {target with clock := clock + target.clock}) = (result, postTarget) := by
  intro y hy
  rcases Pancake.panToStackRemove_body_zeroExtraClock (C := C) (F := F) arch prog wc ac perf info y hy with h | h
  · exact Or.inl h
  · right
    intro source result postSource target ptr bd j hc ho hyp
    exact h source result postSource target ptr bd j
      (codeNoSt_liveTable arch prog wc ac perf dc source hc ho) hyp

/-! ## Tightness witnesses -/

/-- The full table really has a section at label `6` (the WordToStack `storeConsts` stub,
`storeConstsStub_not_noSt`), so filtering it out is not a no-op, and `liveSections` drops it. -/
theorem fullTable_has_label6 (arch : AsmArchitecture)
    (prog : List (Flapjack.Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool) (dc : DataToWord.Config) :
    (∃ e ∈ stackAllocSections arch prog wc ac perf dc, e.1 = storeConstsStubLocation) ∧
    sptLookup storeConstsStubLocation
      (sptFromAList (liveSections (stackAllocSections arch prog wc ac perf dc))) = none := by
  refine ⟨⟨StackAlloc.progComp (storeConstsStubLocation,
    StackRawCall.compTop (StackRawCall.collectInfo (compileNative ac perf (WordToWord.compile wc ac
      (panToWordCompileProgHOL arch prog)).2).2.2.2 .ln)
      (storeConstsStubNative (ac.regCount - (5 + ac.avoidRegs.length)))), ?_, rfl⟩,
    liveTable_lookup_six _⟩
  simp only [stackAllocSections, StackAlloc.compile, List.mem_append]
  right
  exact List.mem_map.2 ⟨_, List.mem_map.2 ⟨_, compileNative_has_stub6 ac perf _, rfl⟩, rfl⟩

end InitECandidate.Solver.StackRemoveDeadStub6AndUnconditionalCodeNoSt
