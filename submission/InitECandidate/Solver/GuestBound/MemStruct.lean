import InitECandidate.Solver.GuestBound.MemLaws
import InitECandidate.Solver.GuestBound.Htab

/-!
# Loads and stores of four-word values

A field element is four words. Storing one rewrites four consecutive cells;
loading one reads them.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem flat4 (w0 w1 w2 w3 : Word) :
    panValueFlatWords (PanValue.rStruct [.word w0, .word w1, .word w2, .word w3] : PanValue Word) =
      [w0, w1, w2, w3] := by
  simp [panValueFlatWords, panValueFlatWordsFuel, panValueFlatWordsFuel.panValueFlatWordsListFuel,
    panValueFlatValueFuel, panValueFlatValueFuel.panValueFlatValueListFuel]

/-- A store of a four-word value fails or rewrites four cells. -/
theorem store_four_inv (hE : GuestEnv E) {fuel : Nat} {s : St σ} {a v : Exp Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.store a v) = some (r, n)) :
    r.isError = true ∨ ∃ addr val m, E.eval s a = some (.word addr) ∧ E.eval s v = some val ∧
      r = .normal s.locals s.globals m s.ffi ∧
      ∀ w0 w1 w2 w3, val = .rStruct [.word w0, .word w1, .word w2, .word w3] →
        m = setCell (setCell (setCell (setCell s.memory addr w0) (addr + 8#64) w1)
          (addr + 8#64 + 8#64) w2) (addr + 8#64 + 8#64 + 8#64) w3 := by
  obtain ⟨access, hacc, hstore, -⟩ := hE.mem.access
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
            intro w0 w1 w2 w3 hw
            subst hw
            rw [hacc] at hst
            simp only [panValueStoreWithAccess] at hst
            rw [flat4, hE.bytes] at hst
            rw [panValueFlatStoreWords] at hst
            cases hs0 : access.storeWord access.domain s.memory 8#64 addr w0 with
            | none => rw [hs0] at hst; simp at hst
            | some m0 =>
              rw [hs0] at hst
              simp only [Option.bind_eq_bind, Option.bind_some] at hst
              rw [panValueFlatStoreWords] at hst
              cases hs1 : access.storeWord access.domain m0 8#64
                  (panValueFlatOffset 8#64 addr 1) w1 with
              | none => rw [hs1] at hst; simp at hst
              | some m1 =>
                rw [hs1] at hst
                simp only [Option.bind_eq_bind, Option.bind_some] at hst
                rw [panValueFlatStoreWords] at hst
                cases hs2 : access.storeWord access.domain m1 8#64
                    (panValueFlatOffset 8#64 (panValueFlatOffset 8#64 addr 1) 1) w2 with
                | none => rw [hs2] at hst; simp at hst
                | some m2 =>
                  rw [hs2] at hst
                  simp only [Option.bind_eq_bind, Option.bind_some] at hst
                  rw [panValueFlatStoreWords] at hst
                  cases hs3 : access.storeWord access.domain m2 8#64
                      (panValueFlatOffset 8#64 (panValueFlatOffset 8#64
                        (panValueFlatOffset 8#64 addr 1) 1) 1) w3 with
                  | none => rw [hs3] at hst; simp at hst
                  | some m3 =>
                    rw [hs3] at hst
                    simp only [Option.bind_eq_bind, Option.bind_some] at hst
                    rw [panValueFlatStoreWords] at hst
                    simp only [Option.some.injEq] at hst
                    rw [← hst, hstore _ _ _ _ _ hs3, hstore _ _ _ _ _ hs2, hstore _ _ _ _ _ hs1,
                      hstore _ _ _ _ _ hs0]
                    rfl
        | _ =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact Or.inl rfl

/-- A four-word load reads four consecutive cells. -/
theorem eval_load_four (hE : GuestEnv E) {s : St σ} {a : Exp Word} {x : PanValue Word}
    (h : E.eval s (.load (.comb [.one, .one, .one, .one]) a) = some x) :
    ∃ addr w0 w1 w2 w3, E.eval s a = some (.word addr) ∧
      x = .rStruct [.word w0, .word w1, .word w2, .word w3] ∧
      s.memory addr = some (.word w0) ∧ s.memory (addr + 8#64) = some (.word w1) ∧
      s.memory (addr + 8#64 + 8#64) = some (.word w2) ∧
      s.memory (addr + 8#64 + 8#64 + 8#64) = some (.word w3) := by
  obtain ⟨access, hacc, -, hread⟩ := hE.mem.access
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
      · obtain ⟨k, hk⟩ : ∃ k, panValueFlatContextFuel E.structs +
            panValueFlatShapeFuel (Shape.comb [.one, .one, .one, .one]) + 1 = k + 6 := by
          refine ⟨panValueFlatContextFuel E.structs +
            panValueFlatShapeFuel (Shape.comb [.one, .one, .one, .one]) + 1 - 6, ?_⟩
          have : 5 ≤ panValueFlatShapeFuel (Shape.comb [.one, .one, .one, .one]) := by decide
          omega
        rw [hk, hacc, hE.bytes] at h
        simp only [panValueFlatLoadFuel, panValueFlatLoadListFuel, panValueFlatReadWord,
          Option.bind_eq_bind, Option.pure_def, shapeSizeWithContext] at h
        cases h0 : access.readWord access.domain s.memory 8#64 addr with
        | none => rw [h0] at h; simp at h
        | some w0 =>
          cases h1 : access.readWord access.domain s.memory 8#64
              (panValueFlatOffset 8#64 addr 1) with
          | none => rw [h0, h1] at h; simp at h
          | some w1 =>
            cases h2 : access.readWord access.domain s.memory 8#64
                (panValueFlatOffset 8#64 (panValueFlatOffset 8#64 addr 1) 1) with
            | none => rw [h0, h1, h2] at h; simp at h
            | some w2 =>
              cases h3 : access.readWord access.domain s.memory 8#64
                  (panValueFlatOffset 8#64 (panValueFlatOffset 8#64
                    (panValueFlatOffset 8#64 addr 1) 1) 1) with
              | none => rw [h0, h1, h2, h3] at h; simp at h
              | some w3 =>
                rw [h0, h1, h2, h3] at h
                simp only [Option.map_some, Option.bind_some, Option.some.injEq] at h
                exact ⟨addr, w0, w1, w2, w3, ha, h.symm, hread _ _ _ _ h0, hread _ _ _ _ h1,
                  hread _ _ _ _ h2, hread _ _ _ _ h3⟩
      · cases h
    | _ => simp at h

end InitECandidate.Solver.GuestBound
