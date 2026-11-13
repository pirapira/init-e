import InitECandidate.Solver.GuestBound.TrieNodeRlp
import InitECandidate.Solver.GuestBound.TrieMptCost

/-!
# Step bound of `node_rlp` (given the walk interface)
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

local notation "NR_ITE1" => ((Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "cached") (Exp.const (BitVec.ofNat 64 0)))
              (Prog.return (Exp.rStruct [(Exp.var VarKind.local "cached"), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 16))]))]))
              Prog.skip) : Prog Word)

local notation "NR_ITE2" => ((Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 0))])) (Exp.const (BitVec.ofNat 64 0)))
              (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 2))])
              Prog.skip) : Prog Word)

local notation "NR_RET" => ((Prog.return (Exp.rStruct [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 8))])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 16))]))])) : Prog Word)

theorem nr_ite1_cost (hE : GuestEnv E) : Costs E NR_ITE1 100 := by
  have h : ∃ B, Costs E NR_ITE1 B ∧ B ≤ 100 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem nr_ite2_cost (hE : GuestEnv E) : Costs E NR_ITE2 100 := by
  have h : ∃ B, Costs E NR_ITE2 B ∧ B ≤ 100 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem nr_ret_cost (hE : GuestEnv E) : Costs E NR_RET 100 := by
  have h : ∃ B, Costs E NR_RET B ∧ B ≤ 100 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 16000000 in
/-- Step bound of `node_rlp`, given the walk interface. -/
theorem node_rlp_cost (hE : GuestEnv E) (I : WalkIface E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "node_rlp" E.functions = some (parameters, body))
    (R : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (node k sp0 fv pv0 : Word)
    (ℓ0 : Nat)
    (hn : s.locals "node" = some (.word node)) (hW : WorldTJ R s.globals s.memory)
    (hPre : I.Pre R s.globals) (hgp : s.globals "heap_ptr" = some (.word pv0))
    (hK : R.Kd node k) (hLv : R.Lv node ℓ0)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 84 := by
  have hbody := (fun_of_index 285 hE.functions (by guest_decl_at 285) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  obtain ⟨-, hRdk, -, -, -⟩ := hW.kd hK
  have hall := Triple.dec (E := E) (P := fun a => a = s)
    (P' := fun a => ∃ cv : Word, a = ⟨updatePanValueMap s.locals "cached" (.word cv), s.globals,
      s.memory, s.ffi⟩ ∧ Rd s.memory (node + 8#64) cv) "cached" Shape.one
    (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"),
      (Exp.const (BitVec.ofNat 64 8))])) ?_
    (Triple.seq (Mid := fun a => a = ⟨updatePanValueMap s.locals "cached" (.word 0#64),
        s.globals, s.memory, s.ffi⟩ ∧ Rd s.memory (node + 8#64) 0#64) (Q := fun _ => True)
      (Triple.of_wps_mid (Q := fun _ => True) (Mid := fun a => a = ⟨updatePanValueMap s.locals
        "cached" (.word 0#64), s.globals, s.memory, s.ffi⟩ ∧ Rd s.memory (node + 8#64) 0#64)
        (nr_ite1_cost hE) (fun _ => trivial) ?_)
      (Triple.seq (Mid := fun a => (a = ⟨updatePanValueMap s.locals "cached" (.word 0#64),
          s.globals, s.memory, s.ffi⟩ ∧ Rd s.memory (node + 8#64) 0#64) ∧ k ≠ 0#64)
        (Q := fun _ => True)
        (Triple.of_wps_mid (Q := fun _ => True) (Mid := fun a => (a = ⟨updatePanValueMap
          s.locals "cached" (.word 0#64), s.globals, s.memory, s.ffi⟩ ∧
          Rd s.memory (node + 8#64) 0#64) ∧ k ≠ 0#64) (nr_ite2_cost hE) (fun _ => trivial) ?_)
        (Triple.seq (Mid := fun _ => True) (Q := fun _ => True)
          (Triple.of_at (B := panValueExpsStepCost [Exp.var VarKind.local "node"] + 10 ^ 83 +
            0 + 1) (fun a ha =>
            (call_cost_at (f := "_node_rlp_fill") (B := 10 ^ 83) (H := 0)
              (info := some (none, none)) [Exp.var VarKind.local "node"] ?_ trivial).consequence
              (fun _ h => h) (Nat.le_refl _) (fun r _ => by cases r <;> trivial)))
          (nr_ret_cost hE))))
  · have hn' := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq, stepsCost_eq] at hn'
    refine Nat.le_trans hn' ?_
    decide +kernel
  · rintro a v rfl hval -
    obtain ⟨addr, cv, ha, hv, hm⟩ := eval_load_one hE.mem hval
    rw [eval_addc hE 8#64 hn] at ha
    simp only [Option.some.injEq, PanValue.word.injEq] at ha
    subst ha hv
    exact ⟨cv, rfl, hm⟩
  · rintro a ⟨cv, rfl, hm⟩
    refine WPs.ite_both (fun w hw => ?_)
    obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    simp (config := { decide := true }) only [evalF_local, update_lookup, if_true, eval_const,
      Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i hw0
      have hcv : cv = 0#64 := by
        by_contra hne
        rw [hwv] at hw0
        simp [evalPanCmp, hne] at hw0
      subst hcv
      exact WPs.skip ⟨rfl, hm⟩
    · exact WPs.ret_ev (fun _ _ => trivial)
  · rintro a ⟨rfl, hm⟩
    refine WPs.ite_both (fun w hw => ?_)
    have hc := eval_cmp_inv hE (op := .equal)
      (eval_load_rd hE (eval_addc hE 0#64 (x := "node") (a := node) (by lk [hn]))
        (by rw [BitVec.add_zero]; exact hRdk))
      (of_eval (eval_const _ 0#64)) _ hw
    simp only [PanValue.word.injEq] at hc
    split
    · rename_i hw0
      exact WPs.skip ⟨⟨rfl, hm⟩, by
        rintro rfl
        rw [hc] at hw0
        simp [evalPanCmp] at hw0⟩
    · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
  · obtain ⟨⟨rfl, hm⟩, hk0⟩ := ha
    intro ps cbody values cl hlk hvalues hbind fuel' r' n' hrun' hne'
    have hparams := (fun_of_index 284 hE.functions (by guest_decl_at 284) (by decide +kernel)
      hlk).2
    simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, hn] at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact node_rlp_fill_cost hE I ps cbody hlk R fuel' ⟨cl, s.globals, s.memory, s.ffi⟩ r' n'
      node k sp0 fv pv0 ℓ0
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hW hPre hgp hK hk0 hLv hm hsp hfv hfs hF hrun' hne'

end InitECandidate.Solver.GuestBound
