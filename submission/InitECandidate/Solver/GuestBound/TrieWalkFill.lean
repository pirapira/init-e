import InitECandidate.Solver.GuestBound.TrieWalkStep
import InitECandidate.Solver.GuestBound.RlpCountFrame

/-!
# `_node_rlp_fill` against the world invariant

Given the interface `WalkIface` of the three functions it calls,
`_node_rlp_fill(node)` on a registered node with an empty RLP cache keeps the
world invariant (with the same registry), fills the cache of `node`, restores
the scratch pointer, and changes memory below the entry heap pointer only at
cache cells and at the cells `I.K`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- What `_node_rlp_fill` guarantees. -/
def FillQ (I : WalkIface E) (R : Reg) (s : St σ) (sp0 pv0 node : Word) (r : Result σ) : Prop :=
  ∃ l g m, r = .returned l g m s.ffi [.word 0#64] ∧ WorldTJ R g m ∧ I.Pre R g ∧
    (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧ Filled m node ∧
    (∀ addr : Word, sp0.toNat ≤ addr.toNat → m addr = s.memory addr) ∧
    ∀ addr : Word, addr.toNat < pv0.toNat → ¬ CacheC R addr → ¬ I.K addr →
      m addr = s.memory addr

set_option maxHeartbeats 16000000 in
theorem node_rlp_fill_world (hE : GuestEnv E) (I : WalkIface E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "_node_rlp_fill" E.functions = some (parameters, body))
    (R : Reg) (s : St σ) (r : Result σ) (node k sp0 fv pv0 : Word) (ℓ0 : Nat)
    (hn : s.locals "node" = some (.word node)) (hW : WorldTJ R s.globals s.memory)
    (hPre : I.Pre R s.globals) (hgp : s.globals "heap_ptr" = some (.word pv0))
    (hK : R.Kd node k) (hk0 : k ≠ 0#64) (hLv : R.Lv node ℓ0)
    (hc0 : Rd s.memory (node + 8#64) 0#64)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ FillQ I R s sp0 pv0 node r := by
  have hbody := (fun_of_index 284 hE.functions (by guest_decl_at 284) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (FillQ I R s sp0 pv0 node)) r h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hsp0 := sp0.isLt
  obtain ⟨nend8, nendlt, hpvE⟩ := hW.cache_lt hgp hK
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, hv⟩ := scratch_mark_ret hE hret hsp
  simp only [List.cons.injEq, and_true] at hv
  subst hg hm hf hv
  refine WPs.decCall_ret (fun vq g1 mq f1 hret1 => ?_)
  obtain ⟨hmq, hfq, q, rfl, rfl, hq1, hq2, hq8⟩ := scratchalloc_ret hE hret1 (pv := sp0)
    (fv := fv) (nv := 48#64) (eval_const _ _) hsp hfv hfs
  subst hmq hfq
  dsimp only
  have hq2' : q.toNat + 48 ≤ sp0.toNat := by simpa using hq2
  obtain ⟨c0, c1, c2, hfr⟩ := rec3 s.memory q 0#64 node 0#64 (by omega)
  have hq0 : q ≠ 0#64 := by
    rintro rfl
    simp at hq1
    omega
  refine WPs.seq_store hE (addr := q + 0#64) (w := 0#64) (eval_addc hE 0#64 (by lk []))
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := q + 8#64) (w := node) (eval_addc hE 8#64 (by lk []))
    (of_eval (by lk [hn])) ?_
  refine WPs.seq_store hE (addr := q + 16#64) (w := 0#64) (eval_addc hE 16#64 (by lk []))
    (of_eval (eval_const _ _)) ?_
  have hW2 := hW.scratch (g' := updatePanValueMap s.globals "scratch_ptr" (.word q))
    (fun x hx => by simp [update_lookup, hx]) (fun a ha => hfr a (by omega))
  refine WPs.seq_call_ret (fun vs g3 m3 ffi3 hret => ?_)
  obtain ⟨rfl, pv', hgp', hpv', hg3, hW3, hFr3, hheap, hscr⟩ :=
    I.begin R _ _ _ q node k pv0 _ _ _ _ hret (by lk []) (by lk [hn]) hW2
      (I.pre_glob hPre (fun x h1 h2 => by simp [update_lookup, h2]))
      (by simp (config := { decide := true }) [update_lookup, hgp]) hK hk0 (by omega) hq8
      (by omega)
  dsimp only at hgp' hg3 hheap hscr
  have hsp3 : g3 "scratch_ptr" = some (.word q) :=
    (hg3 _ (by decide)).trans (by simp [update_lookup])
  have hlow : ∀ x : Word, x.toNat < pv0.toNat → m3 x = s.memory x := fun x hx =>
    (hheap x hx).trans (hfr x (by omega))
  refine WPs.dec (w := q) (of_eval (by lk [])) ?_
  refine WPs.seqG (fun a => WkI I R s.globals s.memory s.ffi fv sp0 pv0 node a ∧
      ∃ kk, E.cond a (.cmp .notEqual (.var .local "top") (.const 0#64)) = some (0, kk))
    (WPs.loopG (I := WkI I R s.globals s.memory s.ffi fv sp0 pv0 node)
      ⟨pv', q, q, [node], hW3, rfl,
        fun x h1 h2 => (hg3 x h1).trans (by simp [update_lookup, h2]), hgp', hpv', hsp3, hq1,
        by omega,
        I.pre_glob hPre (fun x h1 h2 => (hg3 x h1).trans (by simp [update_lookup, h2])),
        by lk [], by lk [],
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
      (fun a hI hct => (wk_body hE I hfv hF hI hct).conseq (by
        rintro r ⟨l, g, m, f, rfl, hI', -⟩
        exact hI'))
      (fun a kk hI hk => ⟨hI, kk, hk⟩)) ?_
  rintro ⟨la, ga, ma, fa⟩ ⟨⟨pv, sp, topv, S, hW', hf, hg, hgpa, hpv0, hgs, hfs', hsl, hPre',
    qmark, qtop, hst, hbot, hM, hM0⟩, kk, hk⟩
  dsimp only at hW' hf hg hgpa hgs hPre' qmark qtop hst hbot hM hM0
  subst hf
  have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := topv) (by lk [qtop]))
    (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hk)
  simp only [PanValue.word.injEq] at hcv
  have ht0 : topv = 0#64 := by
    by_contra hne
    simp [evalPanCmp, hne] at hcv
  subst ht0
  have hfill : Filled ma node := by
    cases hst with
    | nil =>
      rcases hbot with ⟨-, hfl⟩ | ⟨S0, hS0⟩
      · exact hfl
      · simp at hS0
    | cons h1 => exact absurd rfl h1
  refine WPs.seq_call_ret (fun vs g5 m5 ffi5 hret5 => ?_)
  obtain ⟨hg5, hm5, hf5⟩ := scratch_release_ret hE hret5 (mv := sp0) (pv := sp)
    (by lk [qmark]) hgs
  have hm5' : ma = m5 := hm5.symm
  subst hg5 hm5' hf5
  refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  refine ⟨_, _, _, rfl, hW'.of_globals (fun x hx => by simp [update_lookup, hx]),
    I.pre_glob hPre' (fun x h1 h2 => by simp [update_lookup, h2]), fun x hx => ?_, hfill, hM,
    hM0⟩
  by_cases hxs : x = "scratch_ptr"
  · subst hxs
    simp [update_lookup, hsp]
  · simp [update_lookup, hxs]
    exact hg x hx hxs

end InitECandidate.Solver.GuestBound
