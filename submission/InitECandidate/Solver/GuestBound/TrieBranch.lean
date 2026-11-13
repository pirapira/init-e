import InitECandidate.Solver.GuestBound.TrieNew
import InitECandidate.Solver.GuestBound.MemZero8

/-!
# `node_new_branch` against the world invariant

A fresh branch: 176 zeroed bytes with kind 3, so all sixteen child slots are
null. The new node is added to the registry.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

set_option maxHeartbeats 4000000 in
theorem node_new_branch_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "node_new_branch" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (hW : WorldTJ Rg s.globals s.memory)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' a, r = .returned l g' m' s.ffi [.word a] ∧
      WorldTJ (Rg.addNd a) g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 258 hE.functions (by guest_decl_at 258) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' a, r = .returned l g' m' s.ffi [.word a] ∧
    WorldTJ (Rg.addNd a) g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hDT, hBT, hCT, hNT, hIT⟩ := hW
  have hpE := hpH.1
  have hp8 := hpH.2
  have h176 : (176#64 : Word).toNat = 176 := by decide
  have hJlo := hHW.jrn.lo
  have hJhi := hHW.jrn.hi
  refine WPs.decCall_alloc hE (pv := pv) (nv := 176#64) (eval_const _ _) hp hpH
    (fun qv hq hqH => ?_)
  have hq' : pv.toNat + 176 ≤ qv.toNat := hq
  have hqE := hqH.1
  refine WPs.seqG (fun a => ∃ m1, a = ⟨updatePanValueMap s.locals "nd" (.word pv),
      updatePanValueMap s.globals "heap_ptr" (.word qv), m1, s.ffi⟩ ∧
      ZeroRel s.memory m1 pv (176#64 : Word).toNat)
    (WPs.call_runs (fun rb => ∃ l m', rb = .returned l
        (updatePanValueMap s.globals "heap_ptr" (.word qv)) m' s.ffi [.word 0#64] ∧
        ZeroRel s.memory m' pv (176#64 : Word).toNat) ?_ ?_ ?_) ?_
  · intro ps cbody values cl hlk hvalues hbind rb hrun
    have hparams := (fun_of_index 17 hE.functions (by guest_decl_at 17) (by decide +kernel)
      hlk).2
    simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, eval_const] at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact memzero_spec8 hE ps cbody hlk ⟨cl, _, s.memory, s.ffi⟩ rb pv 176#64
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hp8
      (by decide) (by omega) hrun
  · rintro rb ⟨l, m', rfl, -⟩
    exact ⟨_, _, _, _, _, rfl⟩
  · rintro l g m ffi v ⟨l', m', heq, hh⟩
    injection heq with _ hg hm hf _
    subst g m ffi
    exact ⟨m', rfl, hh⟩
  rintro _ ⟨m1, rfl, hz⟩
  rw [h176] at hz
  refine WPs.seq_store hE (addr := pv + 0#64) (w := 3#64) (eval_addc hE 0#64 (by lk []))
    (of_eval (eval_const _ _)) ?_
  refine WPs.ret (w := pv) (of_eval (by lk [])) ?_
  simp only [restorePanValueFfiLocal]
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have a0 : (pv + 0#64) = pv := by simp
  rw [a0]
  generalize hm' : setCell m1 pv 3#64 = m'
  have keep : ∀ a : Word, ¬ (pv.toNat ≤ a.toNat ∧ a.toNat < pv.toNat + 176) →
      m' a = s.memory a := by
    intro a ha
    rw [← hm', setCell_ne _ (NE (by omega)), hz a, if_neg (fun hc => ha ⟨hc.1, hc.2.1⟩)]
  have hkind : Rd m' pv 3#64 := by
    rw [← hm']
    exact Rd.here m1 pv 3#64
  have hpq : pv.toNat ≤ qv.toNat := by omega
  have hbase : HBASE ≤ pv.toNat := by omega
  have hbr : ∀ i : Nat, i < 16 → ∃ c : Word,
      Rd m' (pv + BitVec.ofNat 64 (32 + 8 * i)) c ∧ IsChild N c := by
    intro i hi
    have e : (pv + BitVec.ofNat 64 (32 + 8 * i)).toNat = pv.toNat + (32 + 8 * i) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    refine ⟨0#64, ?_, Or.inl rfl⟩
    rw [← hm']
    have hr1 : Rd m1 (pv + BitVec.ofNat 64 (32 + 8 * i)) 0#64 := by
      unfold Rd
      rw [hz, if_pos ⟨by omega, by omega, by omega⟩]
    exact hr1.frame _ (NE (by omega))
  have hW' : HeapW m' qv T (addN N pv 3#64) J C n :=
    hHW.node_add (fun x _ hlt => keep x (by omega))
      (fun x hx => keep x (by unfold HBASE at hx hbase; omega)) hp8 (Nat.le_refl _)
      (by show pv.toNat + nodeSize 3#64 ≤ qv.toNat; simp [nodeSize]; omega) hqE (by decide)
      hkind (fun hk => absurd hk (by decide)) (fun _ => hbr)
  refine ⟨_, _, m', pv, rfl, ⟨qv, T, addN N pv 3#64, J, C, n, by simp [updatePanValueMap], hqH,
    by simp (config := { decide := true }) [update_lookup, hJg],
    by simp (config := { decide := true }) [update_lookup, hCg],
    by simp (config := { decide := true }) [update_lookup, hng], hW', hDT,
    fun lo hi hb => (hBT lo hi hb).node_add (Nat.le_refl _) hpq, fun x w hc => ?_,
    fun a ha => ?_, hIT.node_add hHW (fun x _ hlt => keep x (by omega)) (Nat.le_refl _) hpq
      (fun hk => absurd hk (by decide))⟩, fun x hx => by simp [update_lookup, hx],
    fun addr ha => keep addr (by unfold HBASE at ha hbase; omega)⟩
  · obtain ⟨hr, h8, hi, hhi, hf⟩ := hCT x w hc
    refine ⟨?_, h8, hi, hhi, hf.node_add (Nat.le_refl _) hpq⟩
    have := hf.hi_
    unfold Rd at hr ⊢
    rw [keep x (by omega)]
    exact hr
  · classical
    unfold InitECandidate.Solver.GuestBound.addN
    rcases ha with ha | rfl
    · obtain ⟨k, hk⟩ := hNT a ha
      by_cases e : a = pv
      · exact ⟨3#64, by simp [e]⟩
      · exact ⟨k, by simp [e, hk]⟩
    · exact ⟨3#64, by simp⟩

end InitECandidate.Solver.GuestBound
