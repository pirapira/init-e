import InitECandidate.Solver.GuestBound.TriePrefix
import InitECandidate.Solver.GuestBound.TrieIns

/-!
# More call adapters for the trie code

`WPs.tail_call` (a tail call), `evalArgs_cons_inv`, and the
`CalleeRet` forms of `node_new_ext_world`, `common_prefix_spec` and
`create_branch_world`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A tail call: the callee's result is the result. -/
theorem WPs.tail_call {f : FunName} {args : List (Exp Word)}
    (h : ∀ vs g m ffi, CalleeRet E s f args vs g m ffi → ∀ l, Q (.returned l g m ffi vs)) :
    WPs E s (.call none f args) Q := by
  intro r hr
  rcases runs_call_inv none hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  cases rb with
  | returned lr g m ffi vs =>
    simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    · exact Or.inr (h vs g m ffi ⟨parameters, body, values, cl, lr, hlookup, hvalues, hbind,
        hcallee⟩ l)
  | raised lr g m f ex v =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m f ev =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inl trivial
  | _ =>
    simp only [CallOutcome] at hout
    exact Or.inl (Stopped.of_error hout)

theorem evalArgs_cons_inv {e : Exp Word} {es : List (Exp Word)} {values : List (PanValue Word)}
    (h : E.evalArgs s (e :: es) = some values) :
    ∃ v vs, E.eval s e = some v ∧ E.evalArgs s es = some vs ∧ values = v :: vs := by
  rw [evalArgs_cons] at h
  cases he : E.eval s e with
  | none => rw [he] at h; cases h
  | some v =>
    rw [he] at h
    cases hes : E.evalArgs s es with
    | none => rw [hes] at h; cases h
    | some vs =>
      rw [hes] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨v, vs, rfl, rfl, h.symm⟩

section rets

variable {v : PanValue Word} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ} {Rg : Reg}

theorem node_new_ext_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {nib nlen child : Word}
    {vs : List (PanValue Word)}
    (h : CalleeRet E s "node_new_ext" [e1, e2, e3] vs g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word nib)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word nlen)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word child)
    (hlen : 1 ≤ nlen.toNat) (hch : child = 0#64 ∨ Rg.Nd child)
    (hW : WorldTJ Rg s.globals s.memory)
    (hseg : ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ nib.toNat ∧ nib.toNat + nlen.toNat ≤ hi.toNat ∧
      NibSeg s.memory nib nlen)
    (ℓ : Nat) (hchl : child ≠ 0#64 → Rg.Lv child (ℓ + nlen.toNat)) :
    ∃ a, vs = [.word a] ∧ ffi = s.ffi ∧ WorldTJ (Rg.addNd a 2#64 ℓ (ℓ + nlen.toNat)) g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 257 hE.functions (by guest_decl_at 257) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  obtain ⟨y2, vs2, g2, hr2, rfl⟩ := evalArgs_cons_inv hr1
  obtain ⟨y3, vs3, g3, hr3, rfl⟩ := evalArgs_cons_inv hr2
  rw [evalArgs_nil] at hr3
  simp only [Option.some.injEq] at hr3
  subst hr3
  have := h1 _ g1
  subst this
  have := h2 _ g2
  subst this
  have := h3 _ g3
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases node_new_ext_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    nib nlen child
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hlen hch hW hseg ℓ hchl hrun with hst | ⟨l', g', m', a, heq, hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, rfl, rfl, hw, hg, hm⟩

theorem common_prefix_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {a al b bl : Word}
    (h : CalleeRet E s "common_prefix_length" [e1, e2, e3, e4] [v] g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word a)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word al)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word b)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word bl) :
    ∃ p, v = .word p ∧ g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧
      p.toNat ≤ al.toNat ∧ p.toNat ≤ bl.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 251 hE.functions (by guest_decl_at 251) (by decide +kernel)
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
  rcases common_prefix_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ al bl
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hrun with hst | ⟨l', p, heq, h1', h2'⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨p, rfl, rfl, rfl, rfl, h1', h2'⟩

theorem create_branch_ret (hE : GuestEnv E) {e1 e2 e3 e4 e5 e6 e7 e8 : Exp Word}
    {k1 l1 v1 vl1 k2 l2 v2 vl2 : Word}
    (h : CalleeRet E s "_create_branch_from_two_leaves" [e1, e2, e3, e4, e5, e6, e7, e8] [v]
      g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word k1)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word l1)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word v1)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word vl1)
    (h5 : ∀ y, E.eval s e5 = some y → y = .word k2)
    (h6 : ∀ y, E.eval s e6 = some y → y = .word l2)
    (h7 : ∀ y, E.eval s e7 = some y → y = .word v2)
    (h8 : ∀ y, E.eval s e8 = some y → y = .word vl2)
    (hW : WorldTJ Rg s.globals s.memory)
    (hseg1 : l1 ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ k1.toNat ∧
      k1.toNat + l1.toNat ≤ hi.toNat)
    (hseg2 : l2 ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ k2.toNat ∧
      k2.toNat + l2.toNat ≤ hi.toNat) (ℓ : Nat) :
    ∃ a R', v = .word a ∧ ffi = s.ffi ∧ Rg.Le R' ∧ R'.Kd a 3#64 ∧ R'.Lv a ℓ ∧ WorldTJ R' g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 272 hE.functions (by guest_decl_at 272) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  obtain ⟨y2, vs2, g2, hr2, rfl⟩ := evalArgs_cons_inv hr1
  obtain ⟨y3, vs3, g3, hr3, rfl⟩ := evalArgs_cons_inv hr2
  obtain ⟨y4, vs4, g4, hr4, rfl⟩ := evalArgs_cons_inv hr3
  obtain ⟨y5, vs5, g5, hr5, rfl⟩ := evalArgs_cons_inv hr4
  obtain ⟨y6, vs6, g6, hr6, rfl⟩ := evalArgs_cons_inv hr5
  obtain ⟨y7, vs7, g7, hr7, rfl⟩ := evalArgs_cons_inv hr6
  obtain ⟨y8, vs8, g8, hr8, rfl⟩ := evalArgs_cons_inv hr7
  rw [evalArgs_nil] at hr8
  simp only [Option.some.injEq] at hr8
  subst hr8
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
  have := h7 _ g7
  subst this
  have := h8 _ g8
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases create_branch_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    k1 l1 v1 vl1 k2 l2 v2 vl2
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hseg1 hseg2 ℓ hrun with hst | ⟨l', g', m', a, R', heq, hle, hk, hlv, hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, R', rfl, rfl, hle, hk, hlv, hw, hg, hm⟩

end rets

end InitECandidate.Solver.GuestBound
