import InitECandidate.Solver.GuestBound.WorldRollback
import InitECandidate.Solver.GuestBound.HtabTruncate
import InitECandidate.Solver.GuestBound.CallAt
import InitECandidate.Solver.GuestBound.TrieSet

/-!
# Step bound of `rollback_child_access` under the world invariant

`htab_truncate` only terminates on a well-formed table; the world invariant
provides that for live tables, before and after the first truncation.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A step bound together with a separately proved result for normal outcomes. -/
theorem Triple.with_mid {P Mid : St σ → Prop} {Q : Result σ → Prop} {p : Prog Word} {B : Nat}
    (hc : Triple E P p B (fun _ => True)) (hQ : ∀ r, Q r)
    (hp : ∀ s, P s → WPs E s p (fun r => match r with
      | .normal l g m f => Mid ⟨l, g, m, f⟩
      | r => Q r)) :
    Triple E P p B (fun r => match r with
      | .normal l g m f => Mid ⟨l, g, m, f⟩
      | r => Q r) := by
  intro fuel s r n hP hrun hne
  refine ⟨(hc fuel s r n hP hrun hne).1, ?_⟩
  rcases hp s hP r (Runs.of_run hrun) with hst | hq
  · cases r with
    | normal l g m f => exact absurd hst Stopped.not_normal
    | _ => exact hQ _
  · exact hq

/-- `htab_truncate` on a live table is bounded for the call made from a world state. -/
theorem truncate_costAt (hE : GuestEnv E) {Rg : Reg} {a : St σ} {e1 e2 : Exp Word} {t : Word}
    (hW : WorldTJ Rg a.globals a.memory) (hD : Rg.live t)
    (h1 : ∀ y, E.eval a e1 = some y → y = .word t) :
    FunCostAt E "htab_truncate" 500000000000000000000000000000 a [e1, e2] := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hDT, -⟩ := hW
  obtain ⟨kl0, hD0⟩ := hD
  obtain ⟨v, hTt, -⟩ := hDT t kl0 hD0
  obtain ⟨kind, rep, hok⟩ := (hHW.tabs.at_ t v hTt).ok
  intro ps cbody values cl hlk hvalues hbind fuel r n' hrun hne
  have hparams := (fun_of_index 140 hE.functions (by guest_decl_at 140) (by decide +kernel)
    hlk).2
  obtain ⟨v1, v2, g1, g2, rfl⟩ := evalArgs2_inv hvalues
  have := h1 _ g1
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact htab_truncate_cost hE ps cbody hlk fuel ⟨cl, a.globals, a.memory, a.ffi⟩ r n' t v kind
    rep (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hok hrun hne

theorem rb_ret_cost (hE : GuestEnv E) :
    Costs E (Prog.return (Exp.const (BitVec.ofNat 64 0)) : Prog Word) 10 := by
  have h : ∃ B, Costs E (Prog.return (Exp.const (BitVec.ofNat 64 0)) : Prog Word) B ∧ B ≤ 10 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 8000000 in
/-- Step bound of `rollback_child_access` from a world-invariant state. -/
theorem rollback_cost (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "rollback_child_access" E.functions = some (parameters, body))
    (Rg : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (child t1 n1 t2 n2 : Word)
    (hc : s.locals "child" = some (.word child)) (hlo : 2952790016 ≤ child.toNat)
    (hhi : child.toNat + 280 ≤ 2 ^ 62)
    (r1 : Rd s.memory (child + 168#64) t1) (r2 : Rd s.memory (child + 264#64) n1)
    (r3 : Rd s.memory (child + 176#64) t2) (r4 : Rd s.memory (child + 272#64) n2)
    (hD1 : Rg.live t1) (hD2 : Rg.live t2) (hW : WorldTJ Rg s.globals s.memory)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 31 := by
  have hbody := (fun_of_index 593 hE.functions (by guest_decl_at 593) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have e176 : (child + 176#64).toNat = child.toNat + 176 := by bv_omega
  have e272 : (child + 272#64).toNat = child.toNat + 272 := by bv_omega
  have hall := Triple.seq (E := E) (P := fun a => a = s)
    (Mid := fun a => ∃ m1, a = ⟨s.locals, s.globals, m1, s.ffi⟩ ∧ WorldTJ Rg s.globals m1 ∧
      ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) → m1 x = s.memory x)
    (Q := fun _ => True)
    (Triple.with_mid (Q := fun _ => True)
      (Mid := fun a => ∃ m1, a = ⟨s.locals, s.globals, m1, s.ffi⟩ ∧ WorldTJ Rg s.globals m1 ∧
        ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) → m1 x = s.memory x)
      (call_cost_at (f := "htab_truncate") (B := 500000000000000000000000000000) (H := 0)
        (info := some (none, none))
        [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "child",
            Exp.const (BitVec.ofNat 64 168)]),
          Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "child",
            Exp.const (BitVec.ofNat 64 264)])]
        (truncate_costAt hE hW hD1 (eval_load_rd hE (eval_addc hE 168#64 hc) r1)) trivial)
      (fun _ => trivial) ?_)
    (Triple.seq (Mid := fun _ => True) (Q := fun _ => True)
      (Triple.of_at (B := panValueExpsStepCost
          [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "child",
            Exp.const (BitVec.ofNat 64 176)]),
          Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "child",
            Exp.const (BitVec.ofNat 64 272)])] + 500000000000000000000000000000 + 0 + 1)
        (fun a ha =>
        (call_cost_at (f := "htab_truncate") (B := 500000000000000000000000000000) (H := 0)
          (info := some (none, none))
          [Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "child",
              Exp.const (BitVec.ofNat 64 176)]),
            Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "child",
              Exp.const (BitVec.ofNat 64 272)])] ?_ trivial).consequence
          (fun _ h => h) (Nat.le_refl _) (fun r _ => by cases r <;> trivial)))
      (rb_ret_cost hE))
  · have hn' := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq, stepsCost_eq] at hn'
    refine Nat.le_trans hn' ?_
    decide +kernel
  · rintro a rfl
    exact WPs.call_truncate_world hE (eval_load_rd hE (eval_addc hE 168#64 hc) r1)
      (eval_load_rd hE (eval_addc hE 264#64 hc) r2) hD1 hW
      (fun m1 hW1 hf1 => ⟨m1, rfl, hW1, hf1⟩)
  · obtain ⟨m1, rfl, hW1, hf1⟩ := ha
    have r3' : Rd m1 (child + 176#64) t2 := by
      unfold Rd at r3 ⊢
      rw [hf1 _ (Or.inr (by omega))]
      exact r3
    exact truncate_costAt hE hW1 hD2 (eval_load_rd hE (eval_addc hE 176#64 hc) r3')

end InitECandidate.Solver.GuestBound
