import InitECandidate.Solver.GuestBound.TrieWalkFill
import InitECandidate.Solver.GuestBound.TrieWalkCost
import InitECandidate.Solver.GuestBound.TrieDelNode

/-!
# Step bound of `_node_rlp_fill`

The loop runs at most `2^65 + 1` times (the measure `wkMu`), each iteration
costing at most `10^62` steps.
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

/-- A statement with a known cost and a known effect, followed by the rest. -/
theorem Triple.wseq {P Mid : St σ → Prop} {p q : Prog Word} {B₁ B₂ : Nat} (hc : Costs E p B₁)
    (hp : ∀ s, P s → WPs E s p (fun r => ∃ l g m f, r = .normal l g m f ∧ Mid ⟨l, g, m, f⟩))
    (hq : Triple E Mid q B₂ (fun _ => True)) :
    Triple E P (.seq p q) (B₁ + B₂ + 1) (fun _ => True) :=
  Triple.seq (Mid := Mid) (Q := fun _ => True) (by
    intro fuel s r n hP hrun hne
    refine ⟨(hc fuel s r n trivial hrun hne).1, ?_⟩
    rcases hp s hP r (Runs.of_run hrun) with hst | ⟨l, g, m, f, rfl, hM⟩
    · cases r with
      | normal l g m f => exact absurd hst Stopped.not_normal
      | _ => trivial
    · exact hM) hq

/-- An iteration can be costed: the top frame's cursor is readable and at most 16. -/
theorem wk_cp (hE : GuestEnv E) (I : WalkIface E) {R : Reg}
    {G : VarName → Option (PanValue Word)} {M : Word → Option (PanValue Word)}
    {F : FfiState σ} {fv lim pv0 node : Word} {a : St σ}
    (hI : WkI I R G M F fv lim pv0 node a) (hct : CondTrue E a WGUARD) : CP0 a := by
  obtain ⟨la, ga, ma, fa⟩ := a
  obtain ⟨pv, sp, topv, S, hW, hf, hg, hgp, hpv0, hgs, hfs, hsl, hPre, qmark, qtop, hst, hbot,
    hM, hM0⟩ := hI
  obtain ⟨w, cc, hcond, hw⟩ := hct
  dsimp only at qtop hst
  have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := topv) (by lk [qtop]))
    (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hcond)
  simp only [PanValue.word.injEq] at hcv
  have ht0 : topv ≠ 0#64 := by
    rintro rfl
    rw [hcv] at hw
    simp [evalPanCmp] at hw
  cases hst with
  | nil => exact absurd rfl ht0
  | cons h1 h2 h3 h4 r0 r1 r2 hcu => exact ⟨topv, _, qtop, r2, hcu⟩

theorem wk_loop_cost (hE : GuestEnv E) (I : WalkIface E) {R : Reg}
    {G : VarName → Option (PanValue Word)} {M : Word → Option (PanValue Word)}
    {F : FfiState σ} {fv lim pv0 node : Word} (hGfv : G "frame_mem_ptr" = some (.word fv))
    (hFv : 2952790016 ≤ fv.toNat) :
    Triple E (fun a => WkI I R G M F fv lim pv0 node a ∧ wkMu R a ≤ 2 ^ 65)
      (.while WGUARD WBODY) ((2 ^ 65 + 1) * (expCost WGUARD + 10 ^ 62 + 1))
      (fun r => match r with
        | .normal _ _ _ _ => True
        | _ => True) := by
  refine (Triple.while_exit (I := WkI I R G M F fv lim pv0 node) (μ := wkMu R)
    (Q := fun _ => True) (2 ^ 65) (condCost_exp _) (fun _ _ _ => trivial) ?_).consequence
    (fun _ h => h) (Nat.le_refl _) (fun r _ => by cases r <;> trivial)
  intro k
  rintro fuel' a r' n' ⟨hI, hk, hct⟩ hrun' hne'
  refine ⟨(wk_body_cost hE fuel' a r' n' (wk_cp hE I hI hct) hrun' hne').1, ?_⟩
  rcases wk_body hE I hGfv hFv hI hct r' (Runs.of_run hrun') with
    hst | ⟨l, g, m, f, rfl, hI', hlt⟩
  · cases r' with
    | error l g m f => cases hne'
    | raised l g m f ex val => trivial
    | finalFfi l g m f ev => trivial
    | _ => exact absurd hst (fun h => h)
  · exact ⟨hI', hk ▸ hlt⟩

/-- After the first `_node_rlp_begin`, the loop invariant holds. -/
theorem fill_begin (hE : GuestEnv E) (I : WalkIface E) {R : Reg} {s : St σ}
    {node k sp0 fv pv0 q : Word} {ℓ0 : Nat} {L : VarName → Option (PanValue Word)}
    (hW : WorldTJ R s.globals s.memory)
    (hPre : I.Pre R s.globals) (hgp : s.globals "heap_ptr" = some (.word pv0))
    (hK : R.Kd node k) (hk0 : k ≠ 0#64) (hLv : R.Lv node ℓ0)
    (hc0 : Rd s.memory (node + 8#64) 0#64)
    (hF : 2952790016 ≤ fv.toNat)
    (hq1 : fv.toNat ≤ q.toNat) (hq2' : q.toNat + 48 ≤ sp0.toNat) (hq8 : q.toNat % 8 = 0)
    (qfr : L "fr" = some (.word q)) (qnode : L "node" = some (.word node))
    (qmark : L "mark" = some (.word sp0))
    {vs : List (PanValue Word)} {g3 : VarName → Option (PanValue Word)}
    {m3 : Word → Option (PanValue Word)} {ffi3 : FfiState σ}
    (hret : CalleeRet E ⟨L, updatePanValueMap s.globals "scratch_ptr" (.word q),
      setCell (setCell (setCell s.memory (q + 0#64) 0#64) (q + 8#64) node) (q + 16#64) 0#64,
      s.ffi⟩ "_node_rlp_begin" [.var .local "fr", .var .local "node"] vs g3 m3 ffi3) :
    ffi3 = s.ffi ∧ WkI I R s.globals s.memory s.ffi fv sp0 pv0 node
      ⟨updatePanValueMap L "top" (.word q), g3, m3, s.ffi⟩ := by
  have hsp0 := sp0.isLt
  obtain ⟨nend8, nendlt, hpvE⟩ := hW.cache_lt hgp hK
  obtain ⟨c0, c1, c2, hfr⟩ := rec3 s.memory q 0#64 node 0#64 (by omega)
  have hq0 : q ≠ 0#64 := by
    rintro rfl
    simp at hq1
    omega
  have hW2 := hW.scratch (g' := updatePanValueMap s.globals "scratch_ptr" (.word q))
    (fun x hx => by simp [update_lookup, hx]) (fun a ha => hfr a (by omega))
  obtain ⟨rfl, pv', hgp', hpv', hg3, hW3, hFr3, hheap, hscr⟩ :=
    I.begin R _ _ _ q node k pv0 _ _ _ _ hret (by lk [qfr]) (by lk [qnode]) hW2
      (I.pre_glob hPre (fun x h1 h2 => by simp [update_lookup, h2]))
      (by simp (config := { decide := true }) [update_lookup, hgp]) hK hk0 (by omega) hq8
      (by omega)
  dsimp only at hgp' hg3 hheap hscr
  have hsp3 : g3 "scratch_ptr" = some (.word q) :=
    (hg3 _ (by decide)).trans (by simp [update_lookup])
  have hlow : ∀ x : Word, x.toNat < pv0.toNat → m3 x = s.memory x := fun x hx =>
    (hheap x hx).trans (hfr x (by omega))
  exact ⟨rfl, pv', q, q, [node], hW3, rfl,
    fun x h1 h2 => (hg3 x h1).trans (by simp [update_lookup, h2]), hgp', hpv', hsp3, hq1,
    by omega,
    I.pre_glob hPre (fun x h1 h2 => (hg3 x h1).trans (by simp [update_lookup, h2])),
    by lk [qmark], by lk [],
    .cons (cur := 0#64) (prev := 0#64) hq0 hq8 (Nat.le_refl _) (by omega)
      (by unfold Rd; dsimp only; rw [hscr q (by omega) (by omega)]; exact c0)
      (by
        have e : (q + 8#64).toNat = q.toNat + 8 := by bv_omega
        unfold Rd
        dsimp only
        rw [hscr _ (by omega) (by omega)]
        exact c1)
      (by
        have e : (q + 16#64).toNat = q.toNat + 16 := by bv_omega
        unfold Rd
        dsimp only
        rw [hscr _ (by omega) (by omega)]
        exact c2)
      (by decide) hK hk0 hLv
      (by unfold Rd; dsimp only; rw [hlow _ (by omega)]; exact hc0) hFr3
      (fun x hx => absurd hx (List.not_mem_nil)) .nil,
    Or.inr ⟨[], rfl⟩,
    fun addr ha => (hscr addr (by omega) (by omega)).trans (hfr addr (by omega)),
    fun addr ha _ _ => hlow addr ha⟩

/-- The state between the stores of the first frame. -/
def FA (s : St σ) (sp0 fv : Word) (mf : Word → Word → Option (PanValue Word)) (a : St σ) :
    Prop :=
  ∃ q : Word, a = ⟨updatePanValueMap (updatePanValueMap s.locals "mark" (.word sp0)) "fr"
      (.word q), updatePanValueMap s.globals "scratch_ptr" (.word q), mf q, s.ffi⟩ ∧
    fv.toNat ≤ q.toNat ∧ q.toNat + 48 ≤ sp0.toNat ∧ q.toNat % 8 = 0

theorem fill_st_cost (hE : GuestEnv E) (c : Word) (v : Exp Word) (hv : expCost v ≤ 10) :
    Costs E (.store (.op .add [.var .local "fr", .const c]) v) 100 := by
  have h : ∃ B, Costs E (.store (.op .add [.var .local "fr", .const c]) v) B ∧ B ≤ 100 :=
    ⟨_, by cost_derive [], by simp only [stepCost_eq, expCost, expsCost]; omega⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem fill_begin_cost (hE : GuestEnv E) :
    Costs E (.call (some (none, none)) "_node_rlp_begin"
      [.var .local "fr", .var .local "node"] : Prog Word) (10 ^ 41) := by
  have h : ∃ B, Costs E (.call (some (none, none)) "_node_rlp_begin"
      [.var .local "fr", .var .local "node"] : Prog Word) B ∧ B ≤ 10 ^ 41 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem fill_tail_cost (hE : GuestEnv E) :
    Costs E (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.return (.const 0#64)) : Prog Word) (10 ^ 10) := by
  have h : ∃ B, Costs E (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.return (.const 0#64)) : Prog Word) B ∧ B ≤ 10 ^ 10 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 8000000 in
/-- Step bound of `_node_rlp_fill`, given the walk interface. -/
theorem node_rlp_fill_cost (hE : GuestEnv E) (I : WalkIface E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "_node_rlp_fill" E.functions = some (parameters, body))
    (R : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (node k sp0 fv pv0 : Word)
    (ℓ0 : Nat)
    (hn : s.locals "node" = some (.word node)) (hW : WorldTJ R s.globals s.memory)
    (hPre : I.Pre R s.globals) (hgp : s.globals "heap_ptr" = some (.word pv0))
    (hK : R.Kd node k) (hk0 : k ≠ 0#64) (hLv : R.Lv node ℓ0)
    (hc0 : Rd s.memory (node + 8#64) 0#64)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 83 := by
  have hbody := (fun_of_index 284 hE.functions (by guest_decl_at 284) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hall := Triple.decCallRun (E := E) (P := fun a => a = s)
    (P' := fun a => a = ⟨updatePanValueMap s.locals "mark" (.word sp0), s.globals, s.memory,
      s.ffi⟩) "mark" Shape.one ([] : List (Exp Word)) (Fn.scratch_mark hE) ?_
    (Triple.decCallRun (P' := FA s sp0 fv (fun _ => s.memory)) "fr" Shape.one
      [Exp.const (BitVec.ofNat 64 48)] (Fn.scratch_alloc hE) ?_
      (Triple.wseq (Mid := FA s sp0 fv (fun q => setCell s.memory (q + 0#64) 0#64))
        (fill_st_cost hE 0#64 (.const 0#64) (by decide)) ?_
        (Triple.wseq (Mid := FA s sp0 fv (fun q => setCell (setCell s.memory (q + 0#64) 0#64)
            (q + 8#64) node))
          (fill_st_cost hE 8#64 (.var .local "node") (by decide)) ?_
          (Triple.wseq (Mid := FA s sp0 fv (fun q => setCell (setCell (setCell s.memory
              (q + 0#64) 0#64) (q + 8#64) node) (q + 16#64) 0#64))
            (fill_st_cost hE 16#64 (.const 0#64) (by decide)) ?_
            (Triple.wseq (Mid := fun a => ∃ q : Word, a.locals "fr" = some (.word q) ∧
                WkI I R s.globals s.memory s.ffi fv sp0 pv0 node
                  ⟨updatePanValueMap a.locals "top" (.word q), a.globals, a.memory, a.ffi⟩)
              (fill_begin_cost hE) ?_
              (Triple.dec (P' := fun a => WkI I R s.globals s.memory s.ffi fv sp0 pv0 node a ∧
                  wkMu R a ≤ 2 ^ 65) "top" Shape.one (Exp.var VarKind.local "fr") ?_
                (Triple.seq (Mid := fun _ => True) (Q := fun _ => True)
                  (wk_loop_cost hE I hfv hF) (fill_tail_cost hE))))))))
  · have hn' := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq, stepsCost_eq] at hn'
    refine Nat.le_trans hn' ?_
    decide +kernel
  · rintro a v g m ffi rfl hret -
    obtain ⟨rfl, rfl, rfl, hv⟩ := scratch_mark_ret hE hret.ret hsp
    simp only [List.cons.injEq, and_true] at hv
    subst hv
    rfl
  · rintro a v g m ffi rfl hret -
    obtain ⟨hmq, hfq, q, rfl, rfl, hq1, hq2, hq8⟩ := scratchalloc_ret hE hret.ret (pv := sp0)
      (fv := fv) (nv := 48#64) (eval_const _ _) hsp hfv hfs
    subst hmq hfq
    exact ⟨q, rfl, hq1, by simpa using hq2, hq8⟩
  · rintro a ⟨q, rfl, b1, b2, b3⟩
    exact WPs.store hE (addr := q + 0#64) (w := 0#64) (eval_addc hE 0#64 (by lk []))
      (of_eval (eval_const _ _)) ⟨_, _, _, _, rfl, q, rfl, b1, b2, b3⟩
  · rintro a ⟨q, rfl, b1, b2, b3⟩
    exact WPs.store hE (addr := q + 8#64) (w := node) (eval_addc hE 8#64 (by lk []))
      (of_eval (by lk [hn])) ⟨_, _, _, _, rfl, q, rfl, b1, b2, b3⟩
  · rintro a ⟨q, rfl, b1, b2, b3⟩
    exact WPs.store hE (addr := q + 16#64) (w := 0#64) (eval_addc hE 16#64 (by lk []))
      (of_eval (eval_const _ _)) ⟨_, _, _, _, rfl, q, rfl, b1, b2, b3⟩
  · rintro a ⟨q, rfl, b1, b2, b3⟩
    refine WPs.call_ret (fun vs g m ffi hret => ?_)
    obtain ⟨rfl, hI⟩ := fill_begin hE I hW hPre hgp hK hk0 hLv hc0 hF b1 b2 b3 (by lk [])
      (by lk [hn]) (by lk []) hret
    exact ⟨_, _, _, _, rfl, q, by lk [], hI⟩
  · rintro a v ⟨q, qfr, hI⟩ hval -
    have := of_eval (w := q) (by lk [qfr]) v hval
    subst this
    exact ⟨hI, wkMu_le R _⟩

end InitECandidate.Solver.GuestBound
