import InitECandidate.Solver.GuestBound.TrieConcat

/-!
# `_delete_ext_finish` against the world invariant

After a deletion below an extension, the extension is relinked to the new
child when that is a branch, or merged with it (concatenated segment) when it
is a leaf or an extension; a null child makes the extension disappear.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Result of the deletion helpers: null, or a registered node of kind other
than 0 at level `L`, in a registry that grew. -/
def DelQ (Rg : Reg) (s : St σ) (L : Nat) (r : Result σ) : Prop :=
  ∃ l g' m' a R', r = .returned l g' m' s.ffi [.word a] ∧ Rg.Le R' ∧
    (a = 0#64 ∨ ∃ k, R'.Kd a k ∧ k ≠ 0#64 ∧ R'.Lv a L) ∧ WorldTJ R' g' m' ∧
    (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr

theorem DelQ.restore {Rg : Reg} {s : St σ} {L : Nat} {r : Result σ} (x : VarName)
    (old : Option (PanValue Word)) (h : DelQ Rg s L r) :
    DelQ Rg s L (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g', m', a, R', rfl, hq⟩ := h
  exact ⟨_, g', m', a, R', rfl, hq⟩

/-- A registered node lies below the heap pointer. -/
theorem WorldTJ.nd_below {Rg : Reg} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {a k pv : Word} (h : WorldTJ Rg g m)
    (hp : g "heap_ptr" = some (.word pv)) (hK : Rg.Kd a k) :
    a.toNat + nodeSize k ≤ pv.toNat ∧ a.toNat % 8 = 0 := by
  obtain ⟨pv', T, N, J, C, n, hp', hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have e : pv' = pv := by
    rw [hp] at hp'
    simpa using hp'.symm
  subst e
  have hat := hW.nodes.at_ a k (hIm.kd a k hK)
  exact ⟨hat.hi, hat.al⟩

section rets

variable {v : PanValue Word} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ} {Rg : Reg}

theorem nibbles_concat_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {a al b bl : Word}
    (h : CalleeRet E s "nibbles_concat" [e1, e2, e3, e4] [v] g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word a)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word al)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word b)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word bl)
    (hW : WorldTJ Rg s.globals s.memory)
    (haI : al ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ a.toNat ∧
      a.toNat + al.toNat ≤ hi.toNat)
    (hbI : bl ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ b.toNat ∧
      b.toNat + bl.toNat ≤ hi.toNat) :
    ∃ out, v = .word out ∧ ffi = s.ffi ∧ WorldTJ (Rg.addIm out (out + (al + bl))) g m ∧
      (out + (al + bl)).toNat = out.toNat + al.toNat + bl.toNat ∧
      s.globals "heap_ptr" = some (.word out) ∧
      (∀ A : Word, A.toNat % 8 = 0 → A.toNat + 8 ≤ out.toNat → m A = s.memory A) ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 252 hE.functions (by guest_decl_at 252) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  obtain ⟨y2, vs2, g2, hr2, rfl⟩ := evalArgs_cons_inv hr1
  obtain ⟨y3, vs3, g3, hr3, rfl⟩ := evalArgs_cons_inv hr2
  obtain ⟨y4, vs4, g4, hr4, rfl⟩ := evalArgs_cons_inv hr3
  rw [evalArgs_nil] at hr4
  simp only [Option.some.injEq] at hr4
  subst hr4
  have := h1 _ g1
  subst this
  have := h2 _ g2
  subst this
  have := h3 _ g3
  subst this
  have := h4 _ g4
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases nibbles_concat_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    a al b bl
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW haI hbI hrun with hst | ⟨l', g', m', out, heq, hw, he, hp, hk, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨out, rfl, rfl, hw, he, hp, hk, hg, hm⟩

/-- `node_new_leaf` as a tail call. -/
theorem node_new_leaf_retV (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {nib nlen vptr vlen : Word}
    {vs : List (PanValue Word)}
    (h : CalleeRet E s "node_new_leaf" [e1, e2, e3, e4] vs g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word nib)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word nlen)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word vptr)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word vlen)
    (hW : WorldTJ Rg s.globals s.memory)
    (hseg : nlen = 0#64 ∨ ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ nib.toNat ∧
      nib.toNat + nlen.toNat ≤ hi.toNat ∧ NibSeg s.memory nib nlen) (ℓ : Nat) :
    ∃ a, vs = [.word a] ∧ ffi = s.ffi ∧ WorldTJ (Rg.addNd a 1#64 ℓ ℓ) g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 256 hE.functions (by guest_decl_at 256) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  obtain ⟨y2, vs2, g2, hr2, rfl⟩ := evalArgs_cons_inv hr1
  obtain ⟨y3, vs3, g3, hr3, rfl⟩ := evalArgs_cons_inv hr2
  obtain ⟨y4, vs4, g4, hr4, rfl⟩ := evalArgs_cons_inv hr3
  rw [evalArgs_nil] at hr4
  simp only [Option.some.injEq] at hr4
  subst hr4
  have := h1 _ g1
  subst this
  have := h2 _ g2
  subst this
  have := h3 _ g3
  subst this
  have := h4 _ g4
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases node_new_leaf_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    nib nlen vptr vlen
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hseg ℓ hrun with hst | ⟨l', g', m', a, heq, hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, rfl, rfl, hw, hg, hm⟩

end rets

end InitECandidate.Solver.GuestBound
