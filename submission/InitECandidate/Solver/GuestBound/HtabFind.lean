import InitECandidate.Solver.GuestBound.Htab

/-!
# Hash tables: `htab_find_leaf`

Under the table invariant, the descent from the root only visits live nodes
and ends at 0 or at a leaf, without changing the state.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem runs_break {s : St σ} {r : Result σ} :
    Runs E s .break r ↔ r = .broke s.locals s.globals s.memory s.ffi := by
  constructor
  · rintro ⟨fuel, n, h⟩
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
    | succ fuel =>
      simp only [Env.run, evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      exact h.1.symm
  · rintro rfl
    exact runs_of_map (fuel := 1) (by simp [Env.run, evalPanValueFfiProgSteps])

/-- A product of two expressions evaluates both to words. -/
theorem eval_mul_inv {s : St σ} {a b : Exp Word} {x : PanValue Word}
    (h : E.eval s (.panOp .mul [a, b]) = some x) :
    ∃ va vb, E.eval s a = some (.word va) ∧ E.eval s b = some (.word vb) ∧
      x = .word (va * vb) := by
  rw [evalF_panOp] at h
  simp only [evalArgs_cons, evalArgs_nil] at h
  cases ha : E.eval s a with
  | none => rw [ha] at h; cases h
  | some xa =>
    cases hb : E.eval s b with
    | none => rw [ha, hb] at h; cases h
    | some xb =>
      rw [ha, hb] at h
      cases xa <;> cases xb <;> simp at h
      rename_i va vb
      exact ⟨va, vb, rfl, rfl, h.symm⟩

/-- The address of a node field, as the guest computes it. -/
theorem nodeField_eq {t : Word} {v : HtabV} (hlay : HtabLayout t v) {nv : Word}
    (hn : nv.toNat ≤ v.nc.toNat) (off : Word) (hoff : off.toNat < 32) :
    v.nodes + (nv * 32#64 + off) = nodeField v nv.toNat off.toNat := by
  unfold nodeField
  congr 1
  apply BitVec.eq_of_toNat_eq
  obtain ⟨-, -, h3, h4⟩ := hlay
  have h32 : (32#64).toNat = 32 := by decide
  have hnl := nv.isLt
  have hmul : (nv * 32#64).toNat = nv.toNat * 32 := by
    rw [BitVec.toNat_mul, h32]
    apply Nat.mod_eq_of_lt
    omega
  have : nv.toNat * 32 + off.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, hmul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]

end InitECandidate.Solver.GuestBound
