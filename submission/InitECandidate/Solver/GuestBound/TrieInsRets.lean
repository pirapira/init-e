import InitECandidate.Solver.GuestBound.TrieSplit

/-!
# Call adapters for the insertion loop

`CalleeRet` forms of `insert_leaf_world`, `split_ext_world` and
`node_invalidate_world`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {v : PanValue Word} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ} {Rg : Reg}

theorem insert_leaf_ret (hE : GuestEnv E) {e1 e2 e3 e4 e5 : Exp Word}
    {node rk rl vptr vlen : Word}
    (h : CalleeRet E s "_insert_into_leaf" [e1, e2, e3, e4, e5] [v] g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word node)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word rk)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word rl)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word vptr)
    (h5 : ∀ y, E.eval s e5 = some y → y = .word vlen)
    (hW : WorldTJ Rg s.globals s.memory) (hK : Rg.Kd node 1#64)
    (hseg : rl ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ rk.toNat ∧
      rk.toNat + rl.toNat ≤ hi.toNat) (L : Nat) (hL : Rg.Lv node L) :
    ∃ a R' k, v = .word a ∧ ffi = s.ffi ∧ Rg.Le R' ∧ R'.Kd a k ∧ k ≠ 0#64 ∧ R'.Lv a L ∧
      WorldTJ R' g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 273 hE.functions (by guest_decl_at 273) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  obtain ⟨y2, vs2, g2, hr2, rfl⟩ := evalArgs_cons_inv hr1
  obtain ⟨y3, vs3, g3, hr3, rfl⟩ := evalArgs_cons_inv hr2
  obtain ⟨y4, vs4, g4, hr4, rfl⟩ := evalArgs_cons_inv hr3
  obtain ⟨y5, vs5, g5, hr5, rfl⟩ := evalArgs_cons_inv hr4
  rw [evalArgs_nil] at hr5
  simp only [Option.some.injEq] at hr5
  subst hr5
  have := h1 _ g1
  subst this
  have := h2 _ g2
  subst this
  have := h3 _ g3
  subst this
  have := h4 _ g4
  subst this
  have := h5 _ g5
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases insert_leaf_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    node rk rl vptr vlen
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hK hseg L hL hrun with hst | ⟨l', g', m', a, R', k, heq, hle, hk, hk0, hlv, hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, R', k, rfl, rfl, hle, hk, hk0, hlv, hw, hg, hm⟩

theorem split_ext_ret (hE : GuestEnv E) {e1 e2 e3 e4 e5 e6 : Exp Word}
    {node rk rl vptr vlen pl sl : Word}
    (h : CalleeRet E s "_split_extension" [e1, e2, e3, e4, e5, e6] [v] g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word node)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word rk)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word rl)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word vptr)
    (h5 : ∀ y, E.eval s e5 = some y → y = .word vlen)
    (h6 : ∀ y, E.eval s e6 = some y → y = .word pl)
    (hW : WorldTJ Rg s.globals s.memory) (hK : Rg.Kd node 2#64)
    (hsl : Rd s.memory (node + 40#64) sl) (hlt : pl.toNat < sl.toNat)
    (hprl : pl.toNat ≤ rl.toNat)
    (hseg : rl ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ rk.toNat ∧
      rk.toNat + rl.toNat ≤ hi.toNat) (ℓ0 : Nat) (hL0 : Rg.Lv node ℓ0) :
    ∃ a R', v = .word a ∧ ffi = s.ffi ∧ Rg.Le R' ∧ R'.Kd a 3#64 ∧ R'.Lv a (ℓ0 + pl.toNat) ∧
      WorldTJ R' g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 274 hE.functions (by guest_decl_at 274) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  obtain ⟨y2, vs2, g2, hr2, rfl⟩ := evalArgs_cons_inv hr1
  obtain ⟨y3, vs3, g3, hr3, rfl⟩ := evalArgs_cons_inv hr2
  obtain ⟨y4, vs4, g4, hr4, rfl⟩ := evalArgs_cons_inv hr3
  obtain ⟨y5, vs5, g5, hr5, rfl⟩ := evalArgs_cons_inv hr4
  obtain ⟨y6, vs6, g6, hr6, rfl⟩ := evalArgs_cons_inv hr5
  rw [evalArgs_nil] at hr6
  simp only [Option.some.injEq] at hr6
  subst hr6
  have := h1 _ g1
  subst this
  have := h2 _ g2
  subst this
  have := h3 _ g3
  subst this
  have := h4 _ g4
  subst this
  have := h5 _ g5
  subst this
  have := h6 _ g6
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases split_ext_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    node rk rl vptr vlen pl sl
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hK hsl hlt hprl hseg ℓ0 hL0 hrun with
    hst | ⟨l', g', m', a, R', heq, hle, hk, hlv, hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, R', rfl, rfl, hle, hk, hlv, hw, hg, hm⟩

theorem node_invalidate_ret (hE : GuestEnv E) {e1 : Exp Word} {a k : Word}
    {vs : List (PanValue Word)} (h : CalleeRet E s "node_invalidate" [e1] vs g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word a)
    (hW : WorldTJ Rg s.globals s.memory) (ha : Rg.Nd a) (hk : Rd s.memory a k)
    (hk0 : k ≠ 0#64) :
    g = s.globals ∧ ffi = s.ffi ∧ WorldTJ Rg s.globals m ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 259 hE.functions (by guest_decl_at 259) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  rw [evalArgs_nil] at hr1
  simp only [Option.some.injEq] at hr1
  subst hr1
  have := h1 _ g1
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases node_invalidate_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    a k
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    ha hk hk0 hW hrun with hst | ⟨l', m', heq, hw, -, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hw, hm⟩

end InitECandidate.Solver.GuestBound
