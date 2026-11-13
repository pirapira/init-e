import InitECandidate.Solver.GuestBound.TrieWalkStep
import InitECandidate.Solver.GuestBound.TrieLoopCost
import InitECandidate.Solver.GuestBound.TrieLeafIns
import InitECandidate.Solver.GuestBound.Fns.L5C2
import InitECandidate.Solver.GuestBound.Fns.L4C3

/-!
# The hashing walk: step bound of one iteration

The body of the loop of `_node_rlp_fill` contains the slot loop of a branch,
which runs at most 16 times because the cursor of a frame is at most 16.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

local notation "WGUARD" => ((Exp.cmp Cmp.notEqual (Exp.var VarKind.local "top") (Exp.const (BitVec.ofNat 64 0))) : Exp Word)
local notation "WBODY" => ((Prog.dec "nd" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 8))]))
                      (Prog.dec "k" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 0))]))
                        (Prog.dec "child" Shape.one (Exp.const (BitVec.ofNat 64 0))
                          (Prog.dec "found" Shape.one (Exp.const (BitVec.ofNat 64 0))
                            (Prog.seq
                              (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 2)))
                                (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))])) (Exp.const (BitVec.ofNat 64 0)))
                                  (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 1)))
                                    (Prog.seq
                                    (Prog.assign VarKind.local "child" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 48))])))
                                    (Prog.call (some ((some (VarKind.local, "found")), none)) "_node_needs_rlp" [(Exp.var VarKind.local "child")])))
                                  Prog.skip)
                                (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 3)))
                                  (Prog.dec "i" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]))
                                    (Prog.seq
                                      (Prog.while (Exp.op BinOp.and [(Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.less (Exp.var VarKind.local "i") (Exp.const (BitVec.ofNat 64 16)))), (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.equal (Exp.var VarKind.local "found") (Exp.const (BitVec.ofNat 64 0))))])
                                        (Prog.seq
                                          (Prog.assign VarKind.local "child" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])])))
                                          (Prog.seq
                                          (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))
                                          (Prog.call (some ((some (VarKind.local, "found")), none)) "_node_needs_rlp" [(Exp.var VarKind.local "child")]))))
                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.var VarKind.local "i"))))
                                  Prog.skip))
                              (Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "found") (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.decCall "cf" Shape.one "scratch_alloc" [(Exp.const (BitVec.ofNat 64 48))]
                                  (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "cf"), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "top"))
                                    (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "cf"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "child"))
                                    (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "cf"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 0)))
                                    (Prog.seq
                                    (Prog.call (some (none, none)) "_node_rlp_begin" [(Exp.var VarKind.local "cf"), (Exp.var VarKind.local "child")])
                                    (Prog.assign VarKind.local "top" (Exp.var VarKind.local "cf")))))))
                                (Prog.seq
                                  (Prog.call (some (none, none)) "_node_rlp_finish" [(Exp.var VarKind.local "top"), (Exp.var VarKind.local "nd")])
                                  (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))])))))))))) : Prog Word)
local notation "SCAN" => ((Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 2)))
                                (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))])) (Exp.const (BitVec.ofNat 64 0)))
                                  (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 1)))
                                    (Prog.seq
                                    (Prog.assign VarKind.local "child" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 48))])))
                                    (Prog.call (some ((some (VarKind.local, "found")), none)) "_node_needs_rlp" [(Exp.var VarKind.local "child")])))
                                  Prog.skip)
                                (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 3)))
                                  (Prog.dec "i" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]))
                                    (Prog.seq
                                      (Prog.while (Exp.op BinOp.and [(Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.less (Exp.var VarKind.local "i") (Exp.const (BitVec.ofNat 64 16)))), (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.equal (Exp.var VarKind.local "found") (Exp.const (BitVec.ofNat 64 0))))])
                                        (Prog.seq
                                          (Prog.assign VarKind.local "child" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])])))
                                          (Prog.seq
                                          (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))
                                          (Prog.call (some ((some (VarKind.local, "found")), none)) "_node_needs_rlp" [(Exp.var VarKind.local "child")]))))
                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.var VarKind.local "i"))))
                                  Prog.skip)) : Prog Word)
local notation "THEN2" => ((Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))])) (Exp.const (BitVec.ofNat 64 0)))
                                  (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 1)))
                                    (Prog.seq
                                    (Prog.assign VarKind.local "child" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 48))])))
                                    (Prog.call (some ((some (VarKind.local, "found")), none)) "_node_needs_rlp" [(Exp.var VarKind.local "child")])))
                                  Prog.skip) : Prog Word)
local notation "INGUARD" => ((Exp.op BinOp.and [(Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.less (Exp.var VarKind.local "i") (Exp.const (BitVec.ofNat 64 16)))), (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.equal (Exp.var VarKind.local "found") (Exp.const (BitVec.ofNat 64 0))))]) : Exp Word)
local notation "INBODY" => ((Prog.seq
                                          (Prog.assign VarKind.local "child" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])])))
                                          (Prog.seq
                                          (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))
                                          (Prog.call (some ((some (VarKind.local, "found")), none)) "_node_needs_rlp" [(Exp.var VarKind.local "child")]))) : Prog Word)
local notation "STOREI" => ((Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.var VarKind.local "i")) : Prog Word)
local notation "ACT" => ((Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "found") (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.decCall "cf" Shape.one "scratch_alloc" [(Exp.const (BitVec.ofNat 64 48))]
                                  (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "cf"), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "top"))
                                    (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "cf"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "child"))
                                    (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "cf"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 0)))
                                    (Prog.seq
                                    (Prog.call (some (none, none)) "_node_rlp_begin" [(Exp.var VarKind.local "cf"), (Exp.var VarKind.local "child")])
                                    (Prog.assign VarKind.local "top" (Exp.var VarKind.local "cf")))))))
                                (Prog.seq
                                  (Prog.call (some (none, none)) "_node_rlp_finish" [(Exp.var VarKind.local "top"), (Exp.var VarKind.local "nd")])
                                  (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))]))))) : Prog Word)

theorem then2_cost (hE : GuestEnv E) : Costs E THEN2 (10 ^ 30) := by
  have h : ∃ B, Costs E THEN2 B ∧ B ≤ 10 ^ 30 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem inbody_cost (hE : GuestEnv E) : Costs E INBODY (10 ^ 30) := by
  have h : ∃ B, Costs E INBODY B ∧ B ≤ 10 ^ 30 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem storei_cost (hE : GuestEnv E) : Costs E STOREI 100 := by
  have h : ∃ B, Costs E STOREI B ∧ B ≤ 100 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem act_cost (hE : GuestEnv E) : Costs E ACT (10 ^ 61) := by
  have h : ∃ B, Costs E ACT B ∧ B ≤ 10 ^ 61 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

/-- Cost-side invariant of the slot loop. -/
def InC (a : St σ) : Prop :=
  ∃ (jj : Nat) (ndv cv : Word), a.locals "i" = some (.word (BitVec.ofNat 64 jj)) ∧ jj ≤ 16 ∧
    a.locals "nd" = some (.word ndv) ∧ a.locals "child" = some (.word cv)

/-- Measure of the slot loop. -/
def inMu (a : St σ) : Nat :=
  match a.locals "i" with
  | some (.word iv) => 16 - iv.toNat
  | _ => 0

theorem inMu_le (a : St σ) : inMu a ≤ 16 := by
  unfold inMu
  split <;> omega

set_option maxHeartbeats 4000000 in
theorem in_body (hE : GuestEnv E) {a : St σ} (hI : InC a) (hct : CondTrue E a INGUARD) :
    WPs E a INBODY (fun r => ∃ l g m f, r = .normal l g m f ∧ InC ⟨l, g, m, f⟩ ∧
      inMu ⟨l, g, m, f⟩ < inMu a) := by
  obtain ⟨la, ga, ma, fa⟩ := a
  obtain ⟨jj, ndv, cv, qi, hj, qn, qc⟩ := hI
  obtain ⟨w, cc, hcond, hw⟩ := hct
  dsimp only at qi qn qc
  obtain ⟨va, vb, w', ha, hb, hop, hxw⟩ := eval_op2_inv hE.word (cond_of_eval hcond)
  have h1 := eval_cmp_inv hE (op := .notEqual) (of_eval (eval_const _ 0#64))
    (eval_cmp_inv hE (op := .less) (of_eval (w := BitVec.ofNat 64 jj) (by lk [qi]))
      (of_eval (eval_const _ 16#64))) _ ha
  simp only [PanValue.word.injEq] at h1 hxw
  have hjlt : jj < 16 := by
    by_contra hge
    rw [less16 jj hj, if_neg hge] at h1
    subst h1 hxw
    simp [wordOp, evalPanCmp] at hop
    subst hop
    have hz : ∀ x : Word, (AndOp.and (0#64) x : Word) = 0#64 := fun x => by
      first
        | exact BitVec.zero_and
        | simp [AndOp.and]
    rw [hz] at hw
    exact absurd hw (by decide)
  have ej : (BitVec.ofNat 64 jj : Word).toNat = jj := by
    rw [BitVec.toNat_ofNat]
    omega
  have ej1 : (BitVec.ofNat 64 (jj + 1) : Word).toNat = jj + 1 := by
    rw [BitVec.toNat_ofNat]
    omega
  obtain ⟨c', hc'⟩ := eval_load_any hE
    (s := (⟨la, ga, ma, fa⟩ : St σ))
    (of_eval (eval_slot_idx hE (x := "nd") (ix := "i") qn qi (by omega)))
  refine WPs.seq_asg (old := cv) (w := c') qc hc' ?_
  refine WPs.seq_asg (old := BitVec.ofNat 64 jj) (w := BitVec.ofNat 64 (jj + 1))
    (by lk [qi]) (of_eval (by ev [qi, ofNat_add1])) ?_
  refine WPs.callA_ret (fun v g m ffi _ => ?_)
  refine ⟨_, _, _, _, rfl, ⟨jj + 1, ndv, c', by lk [], by omega, by lk [qn], by lk []⟩, ?_⟩
  unfold inMu
  dsimp only
  have q1 : updatePanValueMap (updatePanValueMap (updatePanValueMap la "child" (.word c')) "i"
      (.word (BitVec.ofNat 64 (jj + 1)))) "found" v "i" =
      some (.word (BitVec.ofNat 64 (jj + 1))) := by lk []
  rw [q1, qi]
  show 16 - (BitVec.ofNat 64 (jj + 1) : Word).toNat < 16 - (BitVec.ofNat 64 jj : Word).toNat
  rw [ej, ej1]
  omega

theorem in_loop_cost (hE : GuestEnv E) :
    Triple E (fun a => InC a ∧ inMu a ≤ 16) (.while INGUARD INBODY)
      ((16 + 1) * (expCost INGUARD + 10 ^ 30 + 1))
      (fun r => match r with
        | .normal _ _ _ _ => True
        | _ => True) := by
  refine (Triple.while_exit (I := InC) (μ := inMu) (Q := fun _ => True) 16 (condCost_exp _)
    (fun _ _ _ => trivial) ?_).consequence (fun _ h => h) (Nat.le_refl _)
    (fun r _ => by cases r <;> trivial)
  intro k
  refine Triple.of_costs (inbody_cost hE) ?_
  rintro fuel' a r' n' ⟨hI, hk, hct⟩ hrun' hne'
  rcases in_body hE hI hct r' (Runs.of_run hrun') with hst | ⟨l, g, m, f, rfl, hI', hlt⟩
  · cases r' with
    | error l g m f => cases hne'
    | raised l g m f ex val => trivial
    | finalFfi l g m f ev => trivial
    | _ => exact absurd hst (fun h => h)
  · exact ⟨hI', hk ▸ hlt⟩

/-- What the scan needs for its step bound. -/
def CP4 (a : St σ) : Prop :=
  ∃ topv cur ndv : Word, a.locals "top" = some (.word topv) ∧
    Rd a.memory (topv + 16#64) cur ∧ cur.toNat ≤ 16 ∧ a.locals "nd" = some (.word ndv) ∧
    a.locals "child" = some (.word 0#64)

theorem scan_cost (hE : GuestEnv E) :
    Triple E (CP4 (σ := σ)) SCAN (10 ^ 33) (fun _ => True) := by
  have h : ∃ B, Triple E (CP4 (σ := σ)) SCAN B (fun _ => True) ∧ B ≤ 10 ^ 33 := ?_
  · obtain ⟨B, hB, hle⟩ := h
    exact hB.consequence (fun _ h => h) hle (fun _ h => h)
  refine ⟨_, Triple.ite (condCost_exp _)
    (Triple.of_costs (then2_cost hE) (fun _ _ _ _ _ _ _ => trivial))
    (Triple.ite (condCost_exp _)
      (Triple.dec (P' := fun a => InC a ∧ inMu a ≤ 16) "i" Shape.one
        (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"),
          (Exp.const (BitVec.ofNat 64 16))])) ?_
        (Triple.seq (Mid := fun _ => True) (Q := fun _ => True) (in_loop_cost hE)
          (Triple.of_costs (storei_cost hE) (fun _ _ _ _ _ _ _ => trivial))))
      (Triple.skip.consequence (fun _ h => h) (Nat.le_refl _) (fun _ _ => trivial))), ?_⟩
  · rintro a v ⟨topv, cur, ndv, qt, rc, hcu, qn, qc⟩ hval -
    have := eval_load_rd hE (eval_addc hE 16#64 qt) rc v hval
    subst this
    exact ⟨⟨cur.toNat, ndv, 0#64, by rw [ofNat_toNat']; lk [], hcu, by lk [qn], by lk [qc]⟩,
      inMu_le _⟩
  · simp only [stepCost_eq]
    decide +kernel

/-- What an iteration needs for its step bound: a readable cursor that is at most 16. -/
def CP0 (a : St σ) : Prop :=
  ∃ topv cur : Word, a.locals "top" = some (.word topv) ∧
    Rd a.memory (topv + 16#64) cur ∧ cur.toNat ≤ 16

/-- The same with `nd` declared. -/
def CP1 (a : St σ) : Prop :=
  ∃ topv cur ndv : Word, a.locals "top" = some (.word topv) ∧
    Rd a.memory (topv + 16#64) cur ∧ cur.toNat ≤ 16 ∧ a.locals "nd" = some (.word ndv)

theorem wk_body_cost (hE : GuestEnv E) :
    Triple E (CP0 (σ := σ)) WBODY (10 ^ 62) (fun _ => True) := by
  have hscan := scan_cost (σ := σ) hE
  have h : ∃ B, Triple E (CP0 (σ := σ)) WBODY B (fun _ => True) ∧ B ≤ 10 ^ 62 := ?_
  · obtain ⟨B, hB, hle⟩ := h
    exact hB.consequence (fun _ h => h) hle (fun _ h => h)
  refine ⟨_, Triple.dec (P' := CP1) "nd" Shape.one
    (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"),
      (Exp.const (BitVec.ofNat 64 8))])) ?_
    (Triple.dec (P' := CP1) "k" Shape.one
      (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"),
        (Exp.const (BitVec.ofNat 64 0))])) ?_
      (Triple.dec (P' := CP4) "child" Shape.one (Exp.const (BitVec.ofNat 64 0)) ?_
        (Triple.dec (P' := CP4) "found" Shape.one (Exp.const (BitVec.ofNat 64 0)) ?_
          (Triple.seq (Mid := fun _ => True) (Q := fun _ => True)
            (hscan.consequence (fun _ h => h) (Nat.le_refl _)
              (fun r _ => by cases r <;> trivial))
            (Triple.of_costs (act_cost hE) (fun _ _ _ _ _ _ _ => trivial)))))), ?_⟩
  · rintro a v ⟨topv, cur, qt, rc, hcu⟩ - hsh
    obtain ⟨w, rfl⟩ := word_of_shape_one hsh
    exact ⟨topv, cur, w, by lk [qt], rc, hcu, by lk []⟩
  · rintro a v ⟨topv, cur, ndv, qt, rc, hcu, qn⟩ - -
    exact ⟨topv, cur, ndv, by lk [qt], rc, hcu, by lk [qn]⟩
  · rintro a v ⟨topv, cur, ndv, qt, rc, hcu, qn⟩ hval -
    have := of_eval (eval_const (E := E) _ 0#64) v hval
    subst this
    exact ⟨topv, cur, ndv, by lk [qt], rc, hcu, by lk [qn], by lk []⟩
  · rintro a v ⟨topv, cur, ndv, qt, rc, hcu, qn, qc⟩ - -
    exact ⟨topv, cur, ndv, by lk [qt], rc, hcu, by lk [qn], by lk [qc]⟩
  · simp only [stepCost_eq]
    decide +kernel

end InitECandidate.Solver.GuestBound
