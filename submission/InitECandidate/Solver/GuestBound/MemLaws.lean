import InitECandidate.Solver.GuestBound.SymEval

/-!
# Word cells of memory

`MemEnv E` states what the memory-access model does with single words: a word
store rewrites exactly one cell, and a word load reads the cell it names.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Memory after writing the word `value` at `address`. -/
def setCell (memory : Word → Option (PanValue Word)) (address value : Word) :
    Word → Option (PanValue Word) :=
  fun a => if a == address then some (.word value) else memory a

/-- The word operations of the memory-access model. -/
structure MemEnv (E : Env σ) : Prop where
  access : ∃ access, E.memoryAccess = some access ∧
    (∀ memory b address value memory',
      access.storeWord access.domain memory b address value = some memory' →
        memory' = setCell memory address value) ∧
    (∀ memory b address v,
      access.readWord access.domain memory b address = some v →
        memory address = some (.word v))

/-- A one-word load reads a word cell. -/
theorem eval_load_one (hM : MemEnv E) {s : St σ} {a : Exp Word} {x : PanValue Word}
    (h : E.eval s (.load .one a) = some x) :
    ∃ addr v, E.eval s a = some (.word addr) ∧ x = .word v ∧
      s.memory addr = some (.word v) := by
  obtain ⟨access, hacc, -, hread⟩ := hM.access
  simp only [Env.eval, evalPanValueExp] at h
  cases ha : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord a E.memoryAccess with
  | none => rw [ha] at h; simp at h
  | some av =>
    rw [ha] at h
    cases av with
    | word addr =>
      simp only [Option.bind_eq_bind, Option.bind_some, panValueFlatLoad] at h
      split at h
      · rw [panValueFlatLoadFuel] at h
        rw [hacc] at h
        simp only [panValueFlatReadWord, Option.map_eq_some_iff] at h
        obtain ⟨v, hv, rfl⟩ := h
        exact ⟨addr, v, ha, rfl, hread _ _ _ _ hv⟩
      · cases h
    | _ => simp at h

/-- A store of a word value fails or rewrites one cell. -/
theorem store_word_inv (hM : MemEnv E) {fuel : Nat} {s : St σ} {a v : Exp Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.store a v) = some (r, n)) :
    r.isError = true ∨ ∃ addr val m, E.eval s a = some (.word addr) ∧ E.eval s v = some val ∧
      r = .normal s.locals s.globals m s.ffi ∧
      ∀ w, val = .word w → m = setCell s.memory addr w := by
  obtain ⟨access, hacc, hstore, -⟩ := hM.access
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueStoreResult, evalPanValueExpCounted] at h
    cases ha : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord a E.memoryAccess with
    | none =>
      rw [ha] at h
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inl rfl
    | some av =>
      rw [ha] at h
      simp only [Option.map_some] at h
      cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
          E.topAddress E.bytesInWord v E.memoryAccess with
      | none =>
        rw [hv] at h
        simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl rfl
      | some val =>
        rw [hv] at h
        simp only [Option.map_some] at h
        cases av with
        | word addr =>
          simp only at h
          cases hst : panValueStoreWithAccess s.memory E.bytesInWord addr val E.memoryAccess with
          | none =>
            rw [hst] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            exact Or.inl rfl
          | some m =>
            rw [hst] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            refine Or.inr ⟨addr, val, m, ha, hv, rfl, ?_⟩
            intro w hw
            subst hw
            rw [hacc] at hst
            simp only [panValueStoreWithAccess] at hst
            have hflat : panValueFlatWords (PanValue.word w : PanValue Word) = [w] := by
              simp [panValueFlatWords, panValueFlatWordsFuel]
            rw [hflat] at hst
            rw [panValueFlatStoreWords] at hst
            cases hs : access.storeWord access.domain s.memory E.bytesInWord addr w with
            | none => rw [hs] at hst; simp at hst
            | some m' =>
              rw [hs] at hst
              simp only [Option.bind_eq_bind, Option.bind_some] at hst
              rw [panValueFlatStoreWords] at hst
              simp only [Option.some.injEq] at hst
              rw [← hst]
              exact hstore _ _ _ _ _ hs
        | _ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact Or.inl rfl

end InitECandidate.Solver.GuestBound
