import InitECandidate.Solver.GuestBound.RunFramesLoop

/-!
# The loop interface with a ghost measure

`RfSpec` wants the measure as a function of globals and memory. With a chain
of frames the natural measure is a sum over the frames of the invariant's
witness, so here the invariant is indexed by a number, `InvN n`, and each
block must re-establish it at a smaller index. `RfGhost.toSpec` turns this
into an `RfSpec` by taking the least index as the measure.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- What the loop needs of the two blocks, with the measure as an index of the invariant. -/
structure RfGhost (E : Env σ) where
  InvN : Nat → (VarName → Option (PanValue Word)) → (Word → Option (PanValue Word)) → Prop
  DispatchPre : St σ → Prop
  BD : Nat
  BF : Nat
  costD : Costs E rfDispatch BD
  costF : Costs E rfEnd BF
  pre : ∀ (a : St σ) (pcv : PanValue Word),
    E.eval ⟨updatePanValueMap a.locals "done" (.word 0#64), a.globals, a.memory, a.ffi⟩ rfC1 =
      some (.word 0#64) →
    E.eval ⟨updatePanValueMap a.locals "done" (.word 0#64), a.globals, a.memory, a.ffi⟩ rfC2 =
      some (.word 0#64) →
    E.eval ⟨updatePanValueMap a.locals "done" (.word 0#64), a.globals, a.memory, a.ffi⟩ rfPc =
      some pcv →
    E.eval ⟨updatePanValueMap (updatePanValueMap a.locals "done" (.word 0#64)) "pc" pcv,
      a.globals, a.memory, a.ffi⟩ rfC3 = some (.word 0#64) →
    DispatchPre ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap a.locals "done"
      (.word 0#64)) "pc" pcv) "err" (.word 0#64), a.globals, a.memory, a.ffi⟩
  dispatch : ∀ (a : St σ) (n : Nat), InvN n a.globals a.memory → DispatchPre a →
    WPs E a rfDispatch (fun r => ∃ l g m f, r = .normal l g m f ∧ (∃ n', n' < n ∧ InvN n' g m) ∧
      l "go" = a.locals "go" ∧ l "done" = a.locals "done")
  finish : ∀ (a : St σ) (n : Nat), InvN n a.globals a.memory →
    WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
      (l "go" = some (.word 0#64) ∨
        (l "go" = a.locals "go" ∧ ∃ n', n' < n ∧ InvN n' g m)))

open Classical in
/-- The least index at which the invariant holds. -/
noncomputable def RfGhost.mu (S : RfGhost E) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) : Nat :=
  if h : ∃ n, S.InvN n g m then Nat.find h else 0

theorem RfGhost.mu_le (S : RfGhost E) {n : Nat} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} (h : S.InvN n g m) : S.mu g m ≤ n := by
  classical
  unfold RfGhost.mu
  rw [dif_pos ⟨n, h⟩]
  exact Nat.find_min' _ h

theorem RfGhost.mu_inv (S : RfGhost E) {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} (h : ∃ n, S.InvN n g m) : S.InvN (S.mu g m) g m := by
  classical
  unfold RfGhost.mu
  rw [dif_pos h]
  exact Nat.find_spec h

/-- The loop interface with the least index as measure. -/
noncomputable def RfGhost.toSpec (S : RfGhost E) : RfSpec E where
  Inv := fun g m _ => ∃ n, S.InvN n g m
  μ := S.mu
  DispatchPre := S.DispatchPre
  BD := S.BD
  BF := S.BF
  costD := S.costD
  costF := S.costF
  pre := S.pre
  dispatch := fun a hI hpre =>
    WPs.conseq (S.dispatch a _ (S.mu_inv hI) hpre) (by
      rintro r ⟨l, g, m, f, rfl, ⟨n', hn', hI'⟩, hgo, hdone⟩
      exact ⟨l, g, m, f, rfl, ⟨n', hI'⟩, Nat.lt_of_le_of_lt (S.mu_le hI') hn', hgo, hdone⟩)
  finish := fun a hI =>
    WPs.conseq (S.finish a _ (S.mu_inv hI)) (by
      rintro r ⟨l, g, m, f, rfl, h0 | ⟨hgo, n', hn', hI'⟩⟩
      · exact ⟨l, g, m, f, rfl, Or.inl h0⟩
      · exact ⟨l, g, m, f, rfl, Or.inr ⟨hgo, ⟨n', hI'⟩,
          Nat.lt_of_le_of_lt (S.mu_le hI') hn'⟩⟩)

/-- `run_frames` from a state where the invariant holds at index `k`. -/
theorem run_frames_bound_ghost (hE : GuestEnv E) (S : RfGhost E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "run_frames" E.functions = some (parameters, body))
    (s : St σ) (k : Nat) (hI : S.InvN k s.globals s.memory) (fuel : Nat) (r : Result σ) (n : Nat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ (k + 1 + 1) * (expCost rfCond + (S.BD + S.BF + 200) + 1) + 10 := by
  have h := run_frames_bound hE S.toSpec parameters body hlookup s ⟨k, hI⟩ fuel r n hrun hne
  have hle : S.mu s.globals s.memory ≤ k := S.mu_le hI
  have hm : (S.mu s.globals s.memory + 1 + 1) * (expCost rfCond + (S.BD + S.BF + 200) + 1) ≤
      (k + 1 + 1) * (expCost rfCond + (S.BD + S.BF + 200) + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  exact Nat.le_trans h (Nat.add_le_add_right hm _)

end InitECandidate.Solver.GuestBound
