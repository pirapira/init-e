import InitECandidate.Solver.GuestBound.RfGhost
import InitECandidate.Solver.GuestBound.WpcAt

/-!
# The loop of `run_frames` with step costs that depend on the invariant

`RfGhost` asks for unconditional step bounds of the dispatch block and the
end-of-frame block. The storage and trie code under them only terminates
under the world invariant, so here the two costs are assumed for invariant
states only (`CostAt`). `run_frames_bound_ghostC` is the same bound as
`run_frames_bound_ghost`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Every run of `p` from `s` that does not end in `.error` takes at most `B` steps. -/
def CostAt (E : Env σ) (s : St σ) (p : Prog Word) (B : Nat) : Prop :=
  Triple E (fun a => a = s) p B (fun _ => True)

theorem Costs.at {p : Prog Word} {B : Nat} (h : Costs E p B) (s : St σ) : CostAt E s p B :=
  h.consequence (fun _ _ => trivial) (Nat.le_refl _) (fun _ h => h)

/-- Conditional, with the bound of the whole statement given. -/
theorem WPc.ite_both_sub {c : Exp Word} {p q : Prog Word} {N : Nat} (hle : expCost c + 1 ≤ N)
    (h : ∀ w, E.eval s c = some (.word w) →
      if w = 0 then WPc E s q (N - (expCost c + 1)) Q else WPc E s p (N - (expCost c + 1)) Q) :
    WPc E s (.ite c p q) N Q :=
  (WPc.ite_both h).mono (by rw [Nat.max_self]; omega) (fun _ h => h)

/-- The loop interface with a ghost measure and invariant-relative costs. -/
structure RfGhostC (E : Env σ) where
  InvN : Nat → (VarName → Option (PanValue Word)) → (Word → Option (PanValue Word)) → Prop
  DispatchPre : St σ → Prop
  BD : Nat
  BF : Nat
  costD : ∀ (a : St σ) (n : Nat), InvN n a.globals a.memory → DispatchPre a →
    CostAt E a rfDispatch BD
  costF : ∀ (a : St σ) (n : Nat), InvN n a.globals a.memory → CostAt E a rfEnd BF
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

set_option hygiene false in
local macro "cst" : tactic => `(tactic| (
  simp only [stepCost_eq, rfC1, rfC2, rfC3, rfPc, rfDoneCond, expCost, expsCost]
  omega))

set_option maxHeartbeats 2000000 in
/-- One iteration from an invariant state with `go = 1`: cost and outcome. -/
theorem rf_bodyC (hE : GuestEnv E) (S : RfGhostC E) (a : St σ) (n : Nat)
    (hI : S.InvN n a.globals a.memory) (hgo : a.locals "go" = some (.word 1#64)) :
    WPc E a rfBody (S.BD + S.BF + 200) (fun r => ∃ l g m f, r = .normal l g m f ∧
      (l "go" = some (.word 0#64) ∨
        (l "go" = some (.word 1#64) ∧ ∃ n', n' < n ∧ S.InvN n' g m))) := by
  unfold rfBody
  refine WPc.dec_sub (by cst) (fun v hv => ?_)
  rw [eval_const] at hv
  cases hv
  refine WPc.seq_sub (B₁ := S.BD + 100) (fun s' => ∃ l g m f, s' = ⟨l, g, m, f⟩ ∧
      l "go" = some (.word 1#64) ∧
      ((l "done" = some (.word 1#64) ∧ S.InvN n g m) ∨
        (l "done" = some (.word 0#64) ∧ ∃ n', n' < n ∧ S.InvN n' g m))) ?_ (by cst) ?_
  · have hset : ∀ (l : VarName → Option (PanValue Word)) (N : Nat), 10 ≤ N →
        l "done" = some (.word 0#64) → ∀ Q' : Result σ → Prop,
        Q' (.normal (updatePanValueMap l "done" (.word 1#64)) a.globals a.memory a.ffi) →
        WPc E ⟨l, a.globals, a.memory, a.ffi⟩ (.assign .local "done" (.const 1#64)) N Q' :=
      fun l N hN hd Q' hq => WPc.of_costs_le (Costs.assignLocal "done" (.const 1#64)) (by cst)
        (WPs.assign (old := 0#64) (w := 1#64) hd (of_eval (eval_const _ _)) hq)
    refine WPc.ite_both_sub (by cst) (fun w1 hw1 => ?_)
    split
    · rename_i hz1
      rw [hz1] at hw1
      refine WPc.ite_both_sub (by cst) (fun w2 hw2 => ?_)
      split
      · rename_i hz2
        rw [hz2] at hw2
        refine WPc.dec_sub (by cst) (fun pcv hpc => ?_)
        refine WPc.ite_both_sub (by cst) (fun w3 hw3 => ?_)
        split
        · rename_i hz3
          rw [hz3] at hw3
          refine WPc.dec_sub (by cst) (fun ev0 hev0 => ?_)
          rw [eval_const] at hev0
          cases hev0
          have hpre := S.pre a pcv hw1 hw2 hpc hw3
          refine WPc.mono ⟨S.costD _ n hI hpre, S.dispatch _ n hI hpre⟩ (by cst) ?_
          rintro r ⟨l, g, m, f, rfl, hI', hgo', hdone'⟩
          simp only [restorePanValueFfiLocal]
          refine ⟨_, _, _, _, rfl, ?_, Or.inr ⟨?_, hI'⟩⟩
          · simp (config := { decide := true }) [restorePanValueLocal, hgo', update_lookup, hgo]
          · simp (config := { decide := true }) [restorePanValueLocal, hdone', update_lookup]
        · refine hset _ _ (by cst) (by simp (config := { decide := true }) [update_lookup]) _ ?_
          simp only [restorePanValueFfiLocal]
          refine ⟨_, _, _, _, rfl, ?_, Or.inl ⟨?_, hI⟩⟩
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hgo]
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      · refine hset _ _ (by cst) (by simp (config := { decide := true }) [update_lookup]) _ ?_
        refine ⟨_, _, _, _, rfl, ?_, Or.inl ⟨?_, hI⟩⟩
        · simp (config := { decide := true }) [update_lookup, hgo]
        · simp (config := { decide := true }) [update_lookup]
    · refine hset _ _ (by cst) (by simp (config := { decide := true }) [update_lookup]) _ ?_
      refine ⟨_, _, _, _, rfl, ?_, Or.inl ⟨?_, hI⟩⟩
      · simp (config := { decide := true }) [update_lookup, hgo]
      · simp (config := { decide := true }) [update_lookup]
  · rintro _ ⟨l, g, m, f, rfl, hgo1, hcase⟩
    refine WPc.ite_both_sub (by cst) (fun w hw => ?_)
    rcases hcase with ⟨hd, hI1⟩ | ⟨hd, n1, hn1, hI1⟩
    · have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := 1#64) (by lk [hd]))
        (of_eval (w := 0#64) (eval_const _ _)) _ hw
      simp only [PanValue.word.injEq] at hcv
      split
      · rename_i hz
        rw [hz] at hcv
        simp [evalPanCmp] at hcv
      · refine WPc.mono ⟨S.costF _ n hI1, S.finish _ n hI1⟩ (by cst) ?_
        rintro r ⟨l', g', m', f', rfl, hout⟩
        simp only [restorePanValueFfiLocal]
        refine ⟨_, _, _, _, rfl, ?_⟩
        rcases hout with h0 | ⟨hg, hI'⟩
        · left
          simp (config := { decide := true }) [restorePanValueLocal, h0]
        · right
          refine ⟨?_, hI'⟩
          simp (config := { decide := true }) [restorePanValueLocal, hg, hgo1]
    · have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := 0#64) (by lk [hd]))
        (of_eval (w := 0#64) (eval_const _ _)) _ hw
      simp only [PanValue.word.injEq] at hcv
      split
      · refine WPc.of_costs_le Costs.skip (by cst) (WPs.skip ?_)
        simp only [restorePanValueFfiLocal]
        refine ⟨_, _, _, _, rfl, Or.inr ⟨?_, n1, hn1, hI1⟩⟩
        simp (config := { decide := true }) [restorePanValueLocal, hgo1]
      · rename_i hnz
        exact absurd (by rw [hcv]; simp [evalPanCmp]) hnz

open Classical in
/-- The least index at which the invariant holds. -/
noncomputable def RfGhostC.mu (S : RfGhostC E) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) : Nat :=
  if h : ∃ n, S.InvN n g m then Nat.find h else 0

theorem RfGhostC.mu_le (S : RfGhostC E) {n : Nat} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} (h : S.InvN n g m) : S.mu g m ≤ n := by
  classical
  unfold RfGhostC.mu
  rw [dif_pos ⟨n, h⟩]
  exact Nat.find_min' _ h

theorem RfGhostC.mu_inv (S : RfGhostC E) {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} (h : ∃ n, S.InvN n g m) : S.InvN (S.mu g m) g m := by
  classical
  unfold RfGhostC.mu
  rw [dif_pos h]
  exact Nat.find_spec h

/-- The variant of the loop: zero once `go` is cleared. -/
noncomputable def rfNuC (S : RfGhostC E) (a : St σ) : Nat :=
  match a.locals "go" with
  | some (.word w) => if w = 0#64 then 0 else S.mu a.globals a.memory + 1
  | _ => 0

/-- The loop of `run_frames` from an invariant state. -/
theorem rf_loopC (hE : GuestEnv E) (S : RfGhostC E) (s : St σ) (k : Nat)
    (hI : S.InvN k s.globals s.memory) (hgo : s.locals "go" = some (.word 1#64)) :
    WPc E s (.while rfCond rfBody)
      ((k + 1 + 1) * (expCost rfCond + (S.BD + S.BF + 200) + 1)) (fun _ => True) := by
  refine WPc.while (I := fun a => a.locals "go" = some (.word 0#64) ∨
      (a.locals "go" = some (.word 1#64) ∧ ∃ n, S.InvN n a.globals a.memory)) (μ := rfNuC S)
    (k + 1) (Or.inr ⟨hgo, k, hI⟩) (by
      have := S.mu_le hI
      simp [rfNuC, hgo]
      omega) ?_ (fun _ _ _ _ => trivial)
  intro a hIa hct
  rcases hIa with h0 | ⟨h1, hIa⟩
  · obtain ⟨v, kk, hc, hv⟩ := hct
    rw [cond_eq] at hc
    simp [rfCond, evalF_cmp hE.word, h0, eval_const, evalPanCmp] at hc
    obtain ⟨rfl, -⟩ := hc
    simp at hv
  · refine (rf_bodyC hE S a (S.mu a.globals a.memory) (S.mu_inv hIa) h1).mono (Nat.le_refl _) ?_
    rintro r ⟨l, g, m, f, rfl, hout⟩
    rcases hout with h | ⟨h, n', hn', hI'⟩
    · exact ⟨Or.inl h, by simp [rfNuC, h, h1]⟩
    · refine ⟨Or.inr ⟨h, n', hI'⟩, ?_⟩
      have := S.mu_le hI'
      simp [rfNuC, h, h1]
      omega

/-- `run_frames` from a state where the invariant holds at index `k`. -/
theorem run_frames_bound_ghostC (hE : GuestEnv E) (S : RfGhostC E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "run_frames" E.functions = some (parameters, body))
    (s : St σ) (k : Nat) (hI : S.InvN k s.globals s.memory) (fuel : Nat) (r : Result σ) (n : Nat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ (k + 1 + 1) * (expCost rfCond + (S.BD + S.BF + 200) + 1) + 10 := by
  have hbody := (fun_of_index 584 hE.functions (by guest_decl_at 584) (by decide +kernel)
    hlookup).1
  subst hbody
  have hw : WPc E s rfProg (panValueExpStepCost (.const 1#64 : Exp Word) +
      ((k + 1 + 1) * (expCost rfCond + (S.BD + S.BF + 200) + 1) +
        (panValueExpStepCost (.const 0#64 : Exp Word) + 1) + 1) + 1) (fun _ => True) := by
    unfold rfProg
    refine WPc.dec (fun v hv => ?_)
    rw [eval_const] at hv
    cases hv
    refine WPc.seq (fun _ => True)
      ((rf_loopC hE S (⟨updatePanValueMap s.locals "go" (.word 1#64), s.globals, s.memory,
          s.ffi⟩ : St σ) k hI (by simp (config := { decide := true }) [update_lookup])).mono
        (Nat.le_refl _) (fun r _ => by cases r <;> exact True.intro))
      (fun s' _ => WPc.of_costs (Costs.return _) (WPs.of_true (fun _ => trivial)))
  have := hw.steps hrun hne
  simp only [stepCost_eq, expCost] at this
  omega

end InitECandidate.Solver.GuestBound
