import InitECandidate.Solver.GuestBound.WorldJset

/-!
# `htab_set` at a call from a world state

`htab_set(t, key, value)` on a live table, with the key in a registered free
block or in the scratch arena, keeps the world invariant; only `heap_ptr`
changes among the globals, and no memory outside the heap changes.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

set_option maxHeartbeats 8000000 in
theorem htab_set_retW (hE : GuestEnv E) {Rg : Reg} {e1 e2 e3 : Exp Word} {t keyp val kl : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "htab_set" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word t)) (h2 : E.eval s e2 = some (.word keyp))
    (h3 : E.eval s e3 = some (.word val)) (hD : Rg.D t kl) (hkey : KeyLoc Rg keyp kl)
    (hk64 : keyp.toNat + kl.toNat < 2 ^ 64) (hW : WorldTJ Rg s.globals s.memory) :
    ffi = s.ffi ∧ WorldTJ Rg g m ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 138 hE.functions (by guest_decl_at 138) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hDT, hBT, hCT, hNT, hIT⟩ := hW
  obtain ⟨v, hTt, hvkl⟩ := hDT t kl hD
  subst kl
  have hat := hHW.tabs.at_ t v hTt
  obtain ⟨kind, rep, hok⟩ := hat.ok
  obtain ⟨l1, l2, l3, l4⟩ := id hok.wf.layout
  have hfin := hat.fin
  have hpE := hpH.1
  have hkeys : keyp.toNat + v.kl.toNat ≤ t.toNat ∨ t.toNat + 88 ≤ keyp.toNat := by
    rcases hkey with ⟨lo, hi, hb, a1, a2⟩ | hs
    · rcases ((hBT lo hi hb).tabI t v hTt).1 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hkB : keyp.toNat + v.kl.toNat ≤ v.keys.toNat ∨
      v.order.toNat + (v.nc.toNat + 1) * 8 ≤ keyp.toNat := by
    rcases hkey with ⟨lo, hi, hb, a1, a2⟩ | hs
    · rcases ((hBT lo hi hb).tabI t v hTt).2 with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  have hkP : keyp.toNat + v.kl.toNat ≤ pv.toNat ∨ 2952790016 ≤ keyp.toNat := by
    rcases hkey with ⟨lo, hi, hb, a1, a2⟩ | hs
    · have := (hBT lo hi hb).hi_
      exact Or.inl (by omega)
    · exact Or.inr hs
  have honly := htab_set_only hE parameters body hlookup
  rcases htab_set_exec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ t keyp val
    pv v kind rep (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hok hp hpH hfin hat.t8 hk64 hkeys hkB hkP hrun with hst | hsp
  · exact absurd hst (fun h => h)
  obtain ⟨fuel, k, hrun'⟩ := hrun
  have hrel := honly fuel ⟨cl, s.globals, s.memory, s.ffi⟩ _ k hrun'
  obtain ⟨l0, g0, m0, v', kind', rep', heq, rest⟩ := hsp
  injection heq with hl0 hg0 hm0 hf0 hv0
  subst hl0 hg0 hm0 hf0 hv0
  have hgl : ∀ x, x ≠ "heap_ptr" → g x = s.globals x := fun x hx => hrel x (by simp [hx])
  obtain ⟨pv', v'', hp', hpH', hs⟩ := TabStep.of_set hHW.tabs hTt hpH
    (⟨_, _, _, v', kind', rep', rfl, rest⟩ :
      SetPost s.memory t pv v s.ffi (.returned l g m s.ffi [.word 0#64]))
  exact ⟨rfl, worldTJ_step hp' hpH' hgl hJg hCg hng hHW hDT hBT hCT hNT hIT (Nat.le_refl _) hs,
    hgl, fun addr ha => hs.out addr ha⟩

end InitECandidate.Solver.GuestBound
