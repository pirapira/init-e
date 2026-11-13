import InitECandidate.Solver.GuestBound.TrieWalkFillCost
import InitECandidate.Solver.GuestBound.TrieNibKey
import InitECandidate.Solver.GuestBound.ResolveStep

/-!
# `node_rlp` against the world invariant (given the walk interface)

`node_rlp(node)` returns the cached RLP of a node, filling the cache with
`_node_rlp_fill` first when it is empty.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

/-- What a returning `_node_rlp_fill` leaves. -/
theorem node_rlp_fill_ret (hE : GuestEnv E) (I : WalkIface E) {e : Exp Word} {R : Reg}
    {node k sp0 fv pv0 : Word} {ℓ0 : Nat}
    (h : CalleeRet E s "_node_rlp_fill" [e] vs g m ffi) (he : E.eval s e = some (.word node))
    (hW : WorldTJ R s.globals s.memory) (hPre : I.Pre R s.globals)
    (hgp : s.globals "heap_ptr" = some (.word pv0))
    (hK : R.Kd node k) (hk0 : k ≠ 0#64) (hLv : R.Lv node ℓ0)
    (hc0 : Rd s.memory (node + 8#64) 0#64)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) :
    ffi = s.ffi ∧ WorldTJ R g m ∧ I.Pre R g ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      Filled m node ∧
      (∀ addr : Word, sp0.toNat ≤ addr.toNat → m addr = s.memory addr) ∧
      ∀ addr : Word, addr.toNat < pv0.toNat → ¬ CacheC R addr → ¬ I.K addr →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 284 hE.functions (by guest_decl_at 284) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, he, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases node_rlp_fill_world hE I parameters body hlookup R ⟨cl, s.globals, s.memory, s.ffi⟩ _
    node k sp0 fv pv0 ℓ0
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hPre hgp hK hk0 hLv hc0 hsp hfv hfs hF hrun with
    hst | ⟨l', g', m', heq, hW', hP', hg, hfl, hm1, hm2⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, hW', hP', hg, hfl, hm1, hm2⟩

end rets

/-- What `node_rlp` guarantees. -/
def NrQ (I : WalkIface E) (R : Reg) (s : St σ) (sp0 pv0 : Word) (r : Result σ) : Prop :=
  ∃ l g m, ∃ (p len : Word), r = .returned l g m s.ffi [.rStruct [.word p, .word len]] ∧
    WorldTJ R g m ∧ I.Pre R g ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
    (∀ addr : Word, sp0.toNat ≤ addr.toNat → m addr = s.memory addr) ∧
    ∀ addr : Word, addr.toNat < pv0.toNat → ¬ CacheC R addr → ¬ I.K addr →
      m addr = s.memory addr

theorem NrQ.restore {I : WalkIface E} {R : Reg} {sp0 pv0 : Word} {x : VarName}
    {old : Option (PanValue Word)} {r : Result σ} (h : NrQ I R s sp0 pv0 r) :
    NrQ I R s sp0 pv0 (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g, m, p, len, rfl, hk⟩ := h
  exact ⟨_, g, m, p, len, rfl, hk⟩

set_option maxHeartbeats 8000000 in
theorem node_rlp_world (hE : GuestEnv E) (I : WalkIface E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "node_rlp" E.functions = some (parameters, body))
    (R : Reg) (s : St σ) (r : Result σ) (node k sp0 fv pv0 : Word) (ℓ0 : Nat)
    (hn : s.locals "node" = some (.word node)) (hW : WorldTJ R s.globals s.memory)
    (hPre : I.Pre R s.globals) (hgp : s.globals "heap_ptr" = some (.word pv0))
    (hK : R.Kd node k) (hLv : R.Lv node ℓ0)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ NrQ I R s sp0 pv0 r := by
  have hbody := (fun_of_index 285 hE.functions (by guest_decl_at 285) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (NrQ I R s sp0 pv0)) r h
  obtain ⟨-, hRdk, -, -, -⟩ := hW.kd hK
  refine WPs.dec_ev (fun vc hvc => WPs.conseq (Q' := NrQ I R s sp0 pv0) ?_
    (fun r h => h.restore))
  obtain ⟨addr, cv, ha, hvc', hmc⟩ := eval_load_one hE.mem hvc
  rw [eval_addc hE 8#64 hn] at ha
  simp only [Option.some.injEq, PanValue.word.injEq] at ha
  subst ha hvc'
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qn : L "node" = some (.word node) := by rw [hLL]; lk [hn]
  have qc : L "cached" = some (.word cv) := by rw [hLL]; lk []
  clear hLL
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩ ∧ cv = 0#64)
    (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    simp only [evalF_local, qc, eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i hw0
      exact WPs.skip ⟨rfl, by
        by_contra hne
        rw [hwv] at hw0
        simp [evalPanCmp, hne] at hw0⟩
    · obtain ⟨w16, hw16⟩ := eval_load_any hE (s := (⟨L, s.globals, s.memory, s.ffi⟩ : St σ))
        (of_eval (eval_addc hE 16#64 qn))
      exact WPs.ret_pair (a := cv) (b := w16) (of_eval (by lk [qc])) hw16
        ⟨_, _, _, cv, w16, rfl, hW, hPre, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  intro a ha
  obtain ⟨ha, hcv⟩ := ha
  rw [ha]
  clear ha a
  subst hcv
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩ ∧ k ≠ 0#64)
    (WPs.ite_both (fun w hw => ?_)) ?_
  · have hc := eval_cmp_inv hE (op := .equal)
      (eval_load_rd hE (eval_addc hE 0#64 qn) (by rw [BitVec.add_zero]; exact hRdk))
      (of_eval (eval_const _ 0#64)) _ hw
    simp only [PanValue.word.injEq] at hc
    split
    · rename_i hw0
      exact WPs.skip ⟨rfl, by
        rintro rfl
        rw [hc] at hw0
        simp [evalPanCmp] at hw0⟩
    · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
  intro a ha
  obtain ⟨ha, hk0⟩ := ha
  rw [ha]
  clear ha a
  refine WPs.seq_call_ret (fun vs g m ffi hret => ?_)
  obtain ⟨rfl, hW', hP', hg, ⟨buf, off, rb, -, ro, -⟩, hm1, hm2⟩ := node_rlp_fill_ret hE I hret
    (node := node) (by lk [qn]) hW hPre hgp hK hk0 hLv hmc hsp hfv hfs hF
  exact WPs.ret_pair (a := buf) (b := off)
    (eval_load_rd hE (eval_addc hE 8#64 qn) rb) (eval_load_rd hE (eval_addc hE 16#64 qn) ro)
    ⟨_, _, _, buf, off, rfl, hW', hP', hg, hm1, hm2⟩

end InitECandidate.Solver.GuestBound
