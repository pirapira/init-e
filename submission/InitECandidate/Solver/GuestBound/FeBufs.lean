import InitECandidate.Solver.GuestBound.FeMul

/-!
# Straight-line `Fq12` code: one invariant, one rule per operation

`Bufs pv0 m0 hp All Cn m`: `All` lists 384-byte buffers below the heap pointer
`hp`, aligned and pairwise equal or disjoint; the ones in `Cn` hold canonical
coefficients in `m`; cells below `pv0` are as in `m0`. Each `fe_*` call with
operands in `Cn` and destination in `All` (at or above `pv0`) adds the
destination to `Cn`. This is the separation-style layer of issue #20,
specialised to field buffers (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)}

structure Bufs (pv0 : Word) (m0 : Word → Option (PanValue Word)) (hp : Word)
    (All Cn : List Word) (m : Word → Option (PanValue Word)) : Prop where
  hpb : hp.toNat ≤ 2952790016
  hpa : hp.toNat % 8 = 0
  ple : pv0.toNat ≤ hp.toNat
  geo : ∀ B ∈ All, B.toNat % 8 = 0 ∧ B.toNat + 384 ≤ hp.toNat
  sep : ∀ B ∈ All, ∀ C ∈ All, B = C ∨ B.toNat + 384 ≤ C.toNat ∨ C.toNat + 384 ≤ B.toNat
  sub : ∀ B ∈ Cn, B ∈ All
  can : ∀ B ∈ Cn, CanonN m B 12
  low : ∀ x : Word, x.toNat < pv0.toNat → m x = m0 x

/-- A write into `D` that leaves the rest below `hp` alone and makes `D` canonical. -/
theorem Bufs.write {pv0 hp D : Word} {All Cn : List Word} (h : Bufs pv0 m0 hp All Cn m)
    (hD : D ∈ All) (hDl : pv0.toNat ≤ D.toNat)
    (hfr : ∀ x : Word, x.toNat < hp.toNat → (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) →
      m' x = m x) (hc : CanonN m' D 12) : Bufs pv0 m0 hp All (D :: Cn) m' := by
  refine ⟨h.hpb, h.hpa, h.ple, h.geo, h.sep, ?_, ?_, ?_⟩
  · intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hD
    · exact h.sub B hB
  · intro B hB
    by_cases hBD : B = D
    · rw [hBD]; exact hc
    · have hB' : B ∈ Cn := by
        rcases List.mem_cons.mp hB with rfl | hB
        · exact absurd rfl hBD
        · exact hB
      have hBA := h.sub B hB'
      have hg := h.geo B hBA
      rcases h.sep B hBA D hD with heq | hdis
      · exact absurd heq hBD
      · exact (h.can B hB').frame (by have := h.hpb; omega)
          (fun x h1 h2 => hfr x (by omega) (by omega))
  · intro x hx
    rw [hfr x (by have := (h.geo D hD).2; omega) (Or.inl (by omega))]
    exact h.low x hx

/-- A fresh block at the old heap pointer joins `All`. -/
theorem Bufs.alloc {pv0 hp hp' : Word} {All Cn : List Word} (h : Bufs pv0 m0 hp All Cn m)
    (hle : hp.toNat + 384 ≤ hp'.toNat) (hb : hp'.toNat ≤ 2952790016)
    (ha' : hp'.toNat % 8 = 0) : Bufs pv0 m0 hp' (hp :: All) Cn m := by
  have hal := h.hpa
  have hpl := h.ple
  refine ⟨hb, ha', by omega, ?_, ?_, fun B hB => List.mem_cons_of_mem _ (h.sub B hB), h.can, h.low⟩
  · intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact ⟨hal, hle⟩
    · have := h.geo B hB
      exact ⟨this.1, by omega⟩
  · intro B hB C hC
    rcases List.mem_cons.mp hB with hB0 | hB1
    · rcases List.mem_cons.mp hC with hC0 | hC1
      · exact Or.inl (hB0.trans hC0.symm)
      · rw [hB0]
        exact Or.inr (Or.inr (h.geo C hC1).2)
    · rcases List.mem_cons.mp hC with hC0 | hC1
      · rw [hC0]
        exact Or.inr (Or.inl (h.geo B hB1).2)
      · exact h.sep B hB1 C hC1

theorem Bufs.mono {pv0 hp : Word} {All Cn Cn' : List Word} (h : Bufs pv0 m0 hp All Cn m)
    (hsub : ∀ B ∈ Cn', B ∈ Cn) : Bufs pv0 m0 hp All Cn' m :=
  ⟨h.hpb, h.hpa, h.ple, h.geo, h.sep, fun B hB => h.sub B (hsub B hB), fun B hB => h.can B (hsub B hB), h.low⟩

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem feadd_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {F D A B : Word}
    (h : CalleeRet E s "fe_add" [e1, e2, e3, e4] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F))
    (h2 : E.eval s e2 = some (.word D))
    (h3 : E.eval s e3 = some (.word A))
    (h4 : E.eval s e4 = some (.word B))
    (hF : F.toNat ≤ 12) (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hAD : D = A ∨ D.toNat + 32 * F.toNat ≤ A.toNat ∨ A.toNat + 32 * F.toNat ≤ D.toNat)
    (cA : CanonN s.memory A F.toNat) (bB : B.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hBD : D = B ∨ D.toNat + 32 * F.toNat ≤ B.toNat ∨ B.toNat + 32 * F.toNat ≤ D.toNat)
    (cB : CanonN s.memory B F.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧ (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D F.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 663 hE.functions (by guest_decl_at 663) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_add_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ F A B D
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hF bA bD hAD cA bB hBD cB hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

theorem fesub_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {F D A B : Word}
    (h : CalleeRet E s "fe_sub" [e1, e2, e3, e4] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F))
    (h2 : E.eval s e2 = some (.word D))
    (h3 : E.eval s e3 = some (.word A))
    (h4 : E.eval s e4 = some (.word B))
    (hF : F.toNat ≤ 12) (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hAD : D = A ∨ D.toNat + 32 * F.toNat ≤ A.toNat ∨ A.toNat + 32 * F.toNat ≤ D.toNat)
    (cA : CanonN s.memory A F.toNat) (bB : B.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hBD : D = B ∨ D.toNat + 32 * F.toNat ≤ B.toNat ∨ B.toNat + 32 * F.toNat ≤ D.toNat)
    (cB : CanonN s.memory B F.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧ (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D F.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 664 hE.functions (by guest_decl_at 664) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_sub_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ F A B D
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hF bA bD hAD cA bB hBD cB hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

theorem feneg_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {F D A : Word}
    (h : CalleeRet E s "fe_neg" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F))
    (h2 : E.eval s e2 = some (.word D))
    (h3 : E.eval s e3 = some (.word A))
    (hF : F.toNat ≤ 12) (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hAD : D = A ∨ D.toNat + 32 * F.toNat ≤ A.toNat ∨ A.toNat + 32 * F.toNat ≤ D.toNat)
    (cA : CanonN s.memory A F.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧ (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D F.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 665 hE.functions (by guest_decl_at 665) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_neg_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ F A D
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hF bA bD hAD cA hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

theorem femulsmall_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {F D A K : Word}
    (h : CalleeRet E s "fe_mul_small" [e1, e2, e3, e4] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F))
    (h2 : E.eval s e2 = some (.word D))
    (h3 : E.eval s e3 = some (.word A))
    (h4 : E.eval s e4 = some (.word K))
    (hF : F.toNat ≤ 12) (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hAD : D = A ∨ D.toNat + 32 * F.toNat ≤ A.toNat ∨ A.toNat + 32 * F.toNat ≤ D.toNat)
    (cA : CanonN s.memory A F.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧ (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D F.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 666 hE.functions (by guest_decl_at 666) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_mul_small_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ F A D K
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hF bA bD hAD cA hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

theorem femul_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {D A B pv : Word}
    (h : CalleeRet E s "fe_mul" [e1, e2, e3, e4] vs g m ffi)
    (h1 : E.eval s e1 = some (.word 12#64))
    (h2 : E.eval s e2 = some (.word D))
    (h3 : E.eval s e3 = some (.word A))
    (h4 : E.eval s e4 = some (.word B))
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (bA : A.toNat + 384 ≤ pv.toNat) (bB : B.toNat + 384 ≤ pv.toNat)
    (bD : D.toNat + 384 ≤ pv.toNat) (alD : D.toNat % 8 = 0)
    (cA : CanonN s.memory A 12) (cB : CanonN s.memory B 12) :
    g = s.globals ∧ ffi = s.ffi ∧ (∀ x : Word, x.toNat < pv.toNat → (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) →
        m x = s.memory x) ∧ CanonN m D 12 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 661 hE.functions (by guest_decl_at 661) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_mul12_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A B D pv
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hp hpH bA bB bD alD cA cB hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

theorem fesqr_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {D A pv : Word}
    (h : CalleeRet E s "fe_sqr" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word 12#64))
    (h2 : E.eval s e2 = some (.word D))
    (h3 : E.eval s e3 = some (.word A))
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (bA : A.toNat + 384 ≤ pv.toNat)
    (bD : D.toNat + 384 ≤ pv.toNat) (alD : D.toNat % 8 = 0)
    (cA : CanonN s.memory A 12) :
    g = s.globals ∧ ffi = s.ffi ∧ (∀ x : Word, x.toNat < pv.toNat → (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) →
        m x = s.memory x) ∧ CanonN m D 12 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 662 hE.functions (by guest_decl_at 662) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_sqr12_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A D pv
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hp hpH bA bD alD cA hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

end rets

section steps


theorem WPs.fe_add_step (hE : GuestEnv E) {eF eD eA eB : Exp Word} {rest : Prog Word}
    {D A B hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s eF = some (.word 12#64)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A)) (h4 : E.eval s eB = some (.word B))
    (hB : Bufs pv0 m0 hp All Cn s.memory) (hD : D ∈ All) (hDl : pv0.toNat ≤ D.toNat)
    (hA : A ∈ Cn) (hBc : B ∈ Cn)
    (h : ∀ m', Bufs pv0 m0 hp All (D :: Cn) m' → WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_add" [eF, eD, eA, eB]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have h12 : (12#64 : Word).toNat = 12 := by decide
  have gA := hB.geo A (hB.sub A hA)
  have gB := hB.geo B (hB.sub B hBc)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := feadd_ret hE hret h1 h2 h3 h4 (by rw [h12]) (by rw [h12]; omega)
    (by rw [h12]; omega) (by rw [h12]; exact hB.sep D hD A (hB.sub A hA))
    (by rw [h12]; exact hB.can A hA) (by rw [h12]; omega)
    (by rw [h12]; exact hB.sep D hD B (hB.sub B hBc)) (by rw [h12]; exact hB.can B hBc)
  subst g ffi
  rw [h12] at hfr hc
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

theorem WPs.fe_sub_step (hE : GuestEnv E) {eF eD eA eB : Exp Word} {rest : Prog Word}
    {D A B hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s eF = some (.word 12#64)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A)) (h4 : E.eval s eB = some (.word B))
    (hB : Bufs pv0 m0 hp All Cn s.memory) (hD : D ∈ All) (hDl : pv0.toNat ≤ D.toNat)
    (hA : A ∈ Cn) (hBc : B ∈ Cn)
    (h : ∀ m', Bufs pv0 m0 hp All (D :: Cn) m' → WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_sub" [eF, eD, eA, eB]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have h12 : (12#64 : Word).toNat = 12 := by decide
  have gA := hB.geo A (hB.sub A hA)
  have gB := hB.geo B (hB.sub B hBc)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := fesub_ret hE hret h1 h2 h3 h4 (by rw [h12]) (by rw [h12]; omega)
    (by rw [h12]; omega) (by rw [h12]; exact hB.sep D hD A (hB.sub A hA))
    (by rw [h12]; exact hB.can A hA) (by rw [h12]; omega)
    (by rw [h12]; exact hB.sep D hD B (hB.sub B hBc)) (by rw [h12]; exact hB.can B hBc)
  subst g ffi
  rw [h12] at hfr hc
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

theorem WPs.fe_neg_step (hE : GuestEnv E) {eF eD eA : Exp Word} {rest : Prog Word}
    {D A hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s eF = some (.word 12#64)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A))
    (hB : Bufs pv0 m0 hp All Cn s.memory) (hD : D ∈ All) (hDl : pv0.toNat ≤ D.toNat)
    (hA : A ∈ Cn)
    (h : ∀ m', Bufs pv0 m0 hp All (D :: Cn) m' → WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_neg" [eF, eD, eA]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have h12 : (12#64 : Word).toNat = 12 := by decide
  have gA := hB.geo A (hB.sub A hA)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := feneg_ret hE hret h1 h2 h3 (by rw [h12]) (by rw [h12]; omega)
    (by rw [h12]; omega) (by rw [h12]; exact hB.sep D hD A (hB.sub A hA))
    (by rw [h12]; exact hB.can A hA)
  subst g ffi
  rw [h12] at hfr hc
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

theorem WPs.fe_mul_small_step (hE : GuestEnv E) {eF eD eA eK : Exp Word} {rest : Prog Word}
    {D A K hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s eF = some (.word 12#64)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A))
    (h5 : E.eval s eK = some (.word K))
    (hB : Bufs pv0 m0 hp All Cn s.memory) (hD : D ∈ All) (hDl : pv0.toNat ≤ D.toNat)
    (hA : A ∈ Cn)
    (h : ∀ m', Bufs pv0 m0 hp All (D :: Cn) m' → WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_mul_small" [eF, eD, eA, eK]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have h12 : (12#64 : Word).toNat = 12 := by decide
  have gA := hB.geo A (hB.sub A hA)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := femulsmall_ret hE hret h1 h2 h3 h5 (by rw [h12]) (by rw [h12]; omega)
    (by rw [h12]; omega) (by rw [h12]; exact hB.sep D hD A (hB.sub A hA))
    (by rw [h12]; exact hB.can A hA)
  subst g ffi
  rw [h12] at hfr hc
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

theorem WPs.fe_mul_step (hE : GuestEnv E) {eF eD eA eB : Exp Word} {rest : Prog Word}
    {D A B hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s eF = some (.word 12#64)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A)) (h4 : E.eval s eB = some (.word B))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : Bufs pv0 m0 hp All Cn s.memory) (hD : D ∈ All) (hDl : pv0.toNat ≤ D.toNat)
    (hA : A ∈ Cn) (hBc : B ∈ Cn)
    (h : ∀ m', Bufs pv0 m0 hp All (D :: Cn) m' → WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_mul" [eF, eD, eA, eB]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hfr, hc⟩ := femul_ret hE hret h1 h2 h3 h4 hg ⟨hB.hpb, hB.hpa⟩
    (hB.geo A (hB.sub A hA)).2 (hB.geo B (hB.sub B hBc)).2 (hB.geo D hD).2 (hB.geo D hD).1
    (hB.can A hA) (hB.can B hBc)
  subst g ffi
  exact h m1 (hB.write hD hDl hfr hc)

theorem WPs.fe_sqr_step (hE : GuestEnv E) {eF eD eA : Exp Word} {rest : Prog Word}
    {D A hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s eF = some (.word 12#64)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : Bufs pv0 m0 hp All Cn s.memory) (hD : D ∈ All) (hDl : pv0.toNat ≤ D.toNat)
    (hA : A ∈ Cn)
    (h : ∀ m', Bufs pv0 m0 hp All (D :: Cn) m' → WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_sqr" [eF, eD, eA]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hfr, hc⟩ := fesqr_ret hE hret h1 h2 h3 hg ⟨hB.hpb, hB.hpa⟩
    (hB.geo A (hB.sub A hA)).2 (hB.geo D hD).2 (hB.geo D hD).1 (hB.can A hA)
  subst g ffi
  exact h m1 (hB.write hD hDl hfr hc)

/-- `var x = alloc(384); body`: the block joins `All`. -/
theorem WPs.fe_alloc_step (hE : GuestEnv E) {x : VarName} {e : Exp Word} {body : Prog Word}
    {hp pv0 : Word} {All Cn : List Word}
    (he : E.eval s e = some (.word 384#64)) (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : Bufs pv0 m0 hp All Cn s.memory)
    (h : ∀ hp' : Word, pv0.toNat ≤ hp.toNat → Bufs pv0 m0 hp' (hp :: All) Cn s.memory →
      WPs E ⟨updatePanValueMap s.locals x (.word hp),
        updatePanValueMap s.globals "heap_ptr" (.word hp'), s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "alloc" [e] body) Q := by
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hv, hm, hf, qv, hg', h1, h2⟩ := alloc_ret hE hret he hg ⟨hB.hpb, hB.hpa⟩
  simp only [List.cons.injEq, and_true] at hv
  subst v m ffi g
  rw [show (384#64 : Word).toNat = 384 by decide] at h1
  exact h qv hB.ple (hB.alloc h1 h2.1 h2.2)

end steps

end InitECandidate.Solver.GuestBound
