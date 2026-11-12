import InitECandidate.Solver.GuestBound.WorldRestore
import InitECandidate.Solver.GuestBound.HtabTruncate
import InitECandidate.Solver.GuestBound.RlpTotal

/-!
# `rollback_child_access` keeps the world

`rollback_child_access(child)` truncates the two transaction-wide access
tables to the sizes recorded in the child frame. The frame record lies
outside the heap, so its cells are not changed by the truncations.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `htab_truncate` as a step. -/
theorem TabStep.of_truncate {m m' : Word → Option (PanValue Word)} {pv t : Word}
    {T : Word → Option HtabV} {v v' : HtabV} (hT : TabsOK m pv T) (hTt : T t = some v)
    {kind kind' : Nat → NodeKind} {rep : KeyRep} (hok : HtabOK m t v kind rep)
    (hok' : HtabOK m' t v' kind' rep) (hs : SameBlocks v v')
    (hfr : ∀ a, Outside t v a → m' a = m a) : TabStep m pv T t v m' pv v' := by
  obtain ⟨e1, -, -, e4, e5, e6, e7, -⟩ := hs
  have hat := hT.at_ t v hTt
  obtain ⟨l1, l2, l3, l4⟩ := hok.wf.layout
  have hkn : v.keys.toNat ≤ v.nodes.toNat := Nat.le_trans (Nat.le_add_right _ _) l2
  have hlo := hat.lo
  have hfin := hat.fin
  refine ⟨hTt, Nat.le_refl _, e1, Or.inl ⟨e5, e6, e7, e4⟩,
    ⟨⟨kind', rep, hok'⟩, hat.t8, hlo, by rw [e7, e4]; exact hfin⟩,
    fun a ha8 hna hlt => hfr a ⟨?_, ?_⟩, fun a ha => hfr a ⟨?_, ?_⟩⟩
  · by_contra hc
    exact hna ⟨ha8, Or.inl (by omega)⟩
  · by_contra hc
    exact hna ⟨ha8, Or.inr (by omega)⟩
  · unfold HBASE at ha hlo
    omega
  · unfold HBASE at ha hlo
    omega

/-- `htab_truncate(e1, e2);` on a live table: the world is kept, globals are
unchanged, memory outside the heap is unchanged. -/
theorem WPs.call_truncate_world (hE : GuestEnv E) {e1 e2 : Exp Word} {t nv : Word}
    {Rg : Reg} (h1 : ∀ y, E.eval s e1 = some y → y = .word t)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word nv) (hD : Rg.live t)
    (hW : WorldTJ Rg s.globals s.memory)
    (h : ∀ m', WorldTJ Rg s.globals m' →
      (∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m' a = s.memory a) →
      Q (.normal s.locals s.globals m' s.ffi)) :
    WPs E s (.call (some (none, none)) "htab_truncate" [e1, e2]) Q := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hDT, hBT, hCT, hNT⟩ := hW
  obtain ⟨kl0, hD0⟩ := hD
  obtain ⟨v, hTt, -⟩ := hDT t kl0 hD0
  have hat := hHW.tabs.at_ t v hTt
  obtain ⟨kind, rep, hok⟩ := hat.ok
  refine WPs.call_runs (fun rb => ∃ l m' v' kind', rb = .returned l s.globals m' s.ffi
      [.word 0#64] ∧ HtabOK m' t v' kind' rep ∧ SameBlocks v v' ∧
      ∀ a, Outside t v a → m' a = s.memory a) ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind rb hrun
    have hparams := (fun_of_index 140 hE.functions (by guest_decl_at 140) (by decide +kernel)
      hlk).2
    obtain ⟨v1, v2, g1, g2, rfl⟩ := evalArgs2_inv hvalues
    have := h1 _ g1
    subst this
    have := h2 _ g2
    subst this
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    rcases htab_truncate_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ rb t nv v
      kind rep (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hok hrun with
      hst | ⟨l, m', v', kind', rfl, hok', hsb, -, -, hfr⟩
    · exact Or.inl hst
    · exact Or.inr ⟨l, m', v', kind', rfl, hok', hsb, hfr⟩
  · rintro rb ⟨l, m', v', kind', rfl, -⟩
    exact ⟨_, _, _, _, _, rfl⟩
  · rintro l g m ffi w ⟨l', m', v', kind', heq, hok', hsb, hfr⟩
    injection heq with _ hg hm hf _
    subst g m ffi
    have hs := TabStep.of_truncate hHW.tabs hTt hok hok' hsb hfr
    exact h m' ⟨pv, stepT T t v', N, J, C, n, hp, hpH, hJg, hCg, hng,
      hHW.tab_step hs (Nat.le_refl _) hpH.1, stepT_dom hDT hs.hT hs.kl,
      fun lo hi hb => (hBT lo hi hb).tab_step hs, fun x w hcn => by
        obtain ⟨hr, h8, hi, hhi, hf⟩ := hCT x w hcn
        refine ⟨?_, h8, hi, hhi, hf.tab_step hs⟩
        unfold Rd at hr ⊢
        rw [hs.frame x h8 (fun hfoot => ?_) (by have := hf.hi_; omega)]
        · exact hr
        · rcases hf.tab t v hs.hT x hfoot with h1 | h1 <;> omega, hNT⟩ hs.out

set_option maxHeartbeats 2000000 in
/-- `rollback_child_access(child)` for a frame record outside the heap whose
access-table fields name live tables. -/
theorem rollback_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "rollback_child_access" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (child t1 n1 t2 n2 : Word)
    (hc : s.locals "child" = some (.word child)) (hlo : 2952790016 ≤ child.toNat)
    (hhi : child.toNat + 280 ≤ 2 ^ 62)
    (r1 : Rd s.memory (child + 168#64) t1) (r2 : Rd s.memory (child + 264#64) n1)
    (r3 : Rd s.memory (child + 176#64) t2) (r4 : Rd s.memory (child + 272#64) n2)
    (hD1 : Rg.live t1) (hD2 : Rg.live t2) (hW : WorldTJ Rg s.globals s.memory) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      WorldTJ Rg s.globals m' ∧
      ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m' a = s.memory a := by
  have hbody := (fun_of_index 593 hE.functions (by guest_decl_at 593) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    WorldTJ Rg s.globals m' ∧
    ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m' a = s.memory a)) r h
  refine WPs.seqG (fun a => ∃ m1, a = ⟨s.locals, s.globals, m1, s.ffi⟩ ∧
      WorldTJ Rg s.globals m1 ∧
      ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) → m1 x = s.memory x)
    (WPs.call_truncate_world hE (eval_load_rd hE (eval_addc hE 168#64 hc) r1)
      (eval_load_rd hE (eval_addc hE 264#64 hc) r2) hD1 hW (fun m1 hW1 hf1 => ⟨m1, rfl, hW1, hf1⟩))
    ?_
  rintro _ ⟨m1, rfl, hW1, hf1⟩
  have e176 : (child + 176#64).toNat = child.toNat + 176 := by bv_omega
  have e272 : (child + 272#64).toNat = child.toNat + 272 := by bv_omega
  have r3' : Rd m1 (child + 176#64) t2 := by
    unfold Rd at r3 ⊢
    rw [hf1 _ (Or.inr (by omega))]
    exact r3
  have r4' : Rd m1 (child + 272#64) n2 := by
    unfold Rd at r4 ⊢
    rw [hf1 _ (Or.inr (by omega))]
    exact r4
  refine WPs.seqG (fun a => ∃ m2, a = ⟨s.locals, s.globals, m2, s.ffi⟩ ∧
      WorldTJ Rg s.globals m2 ∧
      ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) → m2 x = s.memory x)
    (WPs.call_truncate_world hE (s := ⟨s.locals, s.globals, m1, s.ffi⟩)
      (eval_load_rd hE (eval_addc hE 176#64 hc) r3')
      (eval_load_rd hE (eval_addc hE 272#64 hc) r4') hD2 hW1
      (fun m2 hW2 hf2 => ⟨m2, rfl, hW2, fun x hx => (hf2 x hx).trans (hf1 x hx)⟩)) ?_
  rintro _ ⟨m2, rfl, hW2, hf2⟩
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  exact ⟨_, m2, rfl, hW2, hf2⟩

end InitECandidate.Solver.GuestBound
