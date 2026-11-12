import InitECandidate.Solver.GuestBound.BufsChain
import InitECandidate.Solver.GuestBound.WpcAt

/-!
# Pieces for `bn254_pairing_check`

Return lemmas for its callees, small facts about canonical buffers, and the
bound of `fq12_inv` at its call (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word} {K : Nat}

theorem ecp_is_inf_quiet : keepFn quietLeaf Guest.Software.guestAst 3 "ecp_is_inf" = true := by
  decide +kernel

/-- A buffer known canonical joins `Cn`. -/
theorem BufsK.addCn {pv0 hp B : Word} {All Cn : List Word} (h : BufsK K pv0 m0 Wr hp All Cn m)
    (hB : B ∈ All) (hc : CanonN m B K) : BufsK K pv0 m0 Wr hp All (B :: Cn) m :=
  ⟨h.hpb, h.hpa, h.ple, h.geo, h.sep,
    fun C hC => by
      rcases List.mem_cons.mp hC with rfl | hC
      · exact hB
      · exact h.sub C hC,
    fun C hC => by
      rcases List.mem_cons.mp hC with rfl | hC
      · exact hc
      · exact h.can C hC, h.low⟩

/-- Coefficient `i` of a buffer placed `32 * k` bytes into another one. -/
theorem canon_concat {G X : Word} {a b : Nat} (hX : X.toNat = G.toNat + 32 * a)
    (hb : G.toNat + 32 * (a + b) ≤ 2 ^ 63) (h1 : CanonN m G a) (h2 : CanonN m X b) :
    CanonN m G (a + b) := by
  intro i
  by_cases hi : i < a
  · obtain ⟨v, hv⟩ := h1 i
    exact ⟨v, fun _ => hv hi⟩
  · obtain ⟨v, hv⟩ := h2 (i - a)
    refine ⟨v, fun hi' => ?_⟩
    have hfe := hv (by omega)
    have e : coefAddr X (i - a) = coefAddr G i := by
      apply BitVec.eq_of_toNat_eq
      rw [coefAddr_toNat (by omega), coefAddr_toNat (by omega), hX]
      omega
    rw [e] at hfe
    exact hfe

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem initnoop_ret (hE : GuestEnv E) {Gt : Word}
    (h : CalleeRet E s "bn254_init" [] vs g m ffi)
    (hgm : s.globals "bn_gamma" = some (.word Gt)) (hne : Gt ≠ 0#64) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  rcases bn254_init_noop hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ Gt hgm hne
    hrun with hst | ⟨l', heq⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl⟩

theorem parseg1_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {D O hp pv0 : Word}
    {All Cn : List Word}
    (h : CalleeRet E s "bn254_parse_g1" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word D)) (h2 : E.eval s e2 = some (.word O))
    (hB : BufsK 1 pv0 m0 Wr hp All Cn s.memory)
    (hO0 : O ∈ All) (hO1 : O + 1#64 * 32#64 ∈ All) (hO2 : O + 2#64 * (1#64 * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 1#64 * 32#64).toNat ∨ O + 1#64 * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (1#64 * 32#64)).toNat ∨ O + 2#64 * (1#64 * 32#64) ∈ Wr) :
    g = s.globals ∧ ffi = s.ffi ∧ ∃ e : Word, vs = [.word e] ∧
      BufsK 1 pv0 m0 Wr hp All Cn m ∧ (e = 0#64 → BufsK 1 pv0 m0 Wr hp All
        ([O + 2#64 * (1#64 * 32#64), O + 1#64 * 32#64, O] ++ Cn) m) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 686 hE.functions (by guest_decl_at 686) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases bn254_parse_g1_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ O hp
    pv0 m0 Wr All Cn
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hB hO0 hO1 hO2 w0 w1 w2
    hrun with hst | ⟨l', m', e, heq, hB1, hB2⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, e, rfl, hB1, hB2⟩

theorem parseg2_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {D O hp pv0 : Word}
    {All Cn : List Word}
    (h : CalleeRet E s "bn254_parse_g2" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word D)) (h2 : E.eval s e2 = some (.word O))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : BufsK 2 pv0 m0 Wr hp All Cn s.memory)
    (hO0 : O ∈ All) (hO1 : O + 2#64 * 32#64 ∈ All) (hO2 : O + 2#64 * (2#64 * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 2#64 * 32#64).toNat ∨ O + 2#64 * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (2#64 * 32#64)).toNat ∨ O + 2#64 * (2#64 * 32#64) ∈ Wr) :
    g = s.globals ∧ ffi = s.ffi ∧ ∃ e : Word, vs = [.word e] ∧
      BufsK 2 pv0 m0 Wr hp All Cn m ∧ (e = 0#64 → BufsK 2 pv0 m0 Wr hp All
        ([O + 2#64 * (2#64 * 32#64), O + 2#64 * 32#64, O] ++ Cn) m) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 687 hE.functions (by guest_decl_at 687) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases bn254_parse_g2_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ O hp
    pv0 m0 Wr All Cn
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hg hB hO0 hO1 hO2 w0 w1 w2
    hrun with hst | ⟨l', m', e, heq, hB1, hB2⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, e, rfl, hB1, hB2⟩

theorem ecpmulK_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {F O P hp pv0 : Word}
    {All Cn : List Word} {nv : PanValue Word} (hF : F.toNat = K) (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (h : CalleeRet E s "ecp_mul" [e1, e2, e3, e4] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word O))
    (h3 : E.eval s e3 = some (.word P)) (h4 : E.eval s e4 = some nv)
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (hP0 : P ∈ Cn) (hP1 : P + F * 32#64 ∈ Cn) (hP2 : P + 2#64 * (F * 32#64) ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + F * 32#64 ∈ All) (hO2 : O + 2#64 * (F * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + F * 32#64).toNat ∨ O + F * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (F * 32#64)).toNat ∨ O + 2#64 * (F * 32#64) ∈ Wr) :
    g = s.globals ∧ ffi = s.ffi ∧ BufsK K pv0 m0 Wr hp All
      ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn) m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 675 hE.functions (by guest_decl_at 675) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases ecp_mulK_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ F O P hp
    pv0 m0 Wr All Cn hF hK
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hg hB0 hP0 hP1 hP2 hO0 hO1 hO2 w0 w1 w2
    hrun with hst | ⟨l', m', heq, hB⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hB⟩

theorem twist_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {O G2 : Word}
    (h : CalleeRet E s "fq12_twist" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word O)) (h2 : E.eval s e2 = some (.word G2))
    (alO : O.toNat % 8 = 0) (bO : O.toNat + 1152 ≤ 2 ^ 62) (bG : G2.toNat + 192 ≤ 2 ^ 62)
    (hdis : G2.toNat + 192 ≤ O.toNat ∨ O.toNat + 1152 ≤ G2.toNat)
    (cG : CanonN s.memory G2 6) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < O.toNat ∨ O.toNat + 1152 ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m O 12 ∧ CanonN m (O + 384#64) 12 ∧ CanonN m (O + 768#64) 12 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 677 hE.functions (by guest_decl_at 677) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq12_twist_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ O G2
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) alO bO bG hdis cG hrun with hst | ⟨l', m', heq, hfr, k0, k1, k2⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, k0, k1, k2⟩

theorem cast_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {O G1 : Word}
    (h : CalleeRet E s "fq12_cast" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word O)) (h2 : E.eval s e2 = some (.word G1))
    (alO : O.toNat % 8 = 0) (bO : O.toNat + 1152 ≤ 2 ^ 62) (bG : G1.toNat + 96 ≤ 2 ^ 62)
    (hdis : G1.toNat + 96 ≤ O.toNat ∨ O.toNat + 1152 ≤ G1.toNat)
    (cG : CanonN s.memory G1 3) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < O.toNat ∨ O.toNat + 1152 ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m O 12 ∧ CanonN m (O + 384#64) 12 ∧ CanonN m (O + 768#64) 12 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 678 hE.functions (by guest_decl_at 678) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq12_cast_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ O G1
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) alO bO bG hdis cG hrun with hst | ⟨l', m', heq, hfr, k0, k1, k2⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, k0, k1, k2⟩

theorem miller_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {Fn Fd Qp Pp hp pv0 : Word}
    {All Cn : List Word}
    (h : CalleeRet E s "bn254_miller_raw" [e1, e2, e3, e4] vs g m ffi)
    (h1 : E.eval s e1 = some (.word Fn)) (h2 : E.eval s e2 = some (.word Fd))
    (h3 : E.eval s e3 = some (.word Qp)) (h4 : E.eval s e4 = some (.word Pp))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : Bufs pv0 m0 Wr hp All Cn s.memory)
    (qa : Qp ∈ Cn) (qb : Qp + 384#64 ∈ Cn) (qc : Qp + 768#64 ∈ Cn)
    (pa : Pp ∈ Cn) (pb : Pp + 384#64 ∈ Cn) (pc : Pp + 768#64 ∈ Cn)
    (hFn : Fn ∈ All) (hFd : Fd ∈ All)
    (wFn : pv0.toNat ≤ Fn.toNat ∨ Fn ∈ Wr) (wFd : pv0.toNat ≤ Fd.toNat ∨ Fd ∈ Wr) :
    g = s.globals ∧ ffi = s.ffi ∧ Bufs pv0 m0 Wr hp All (Fn :: Fd :: Cn) m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 684 hE.functions (by guest_decl_at 684) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases bn254_miller_raw_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    Fn Fd Qp Pp hp pv0 m0 Wr All Cn
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hg hB0 qa qb qc pa pb pc hFn hFd wFn wFd
    hrun with hst | ⟨l', m', heq, hB⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hB⟩

end rets

/-- The bound of `fq12_inv(d, a)` at a call where `a` is canonical and below the heap pointer. -/
theorem fq12inv_costAt (hE : GuestEnv E) {e1 e2 : Exp Word} {D A pv : Word}
    (h1 : E.eval s e1 = some (.word D)) (h2 : E.eval s e2 = some (.word A))
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (halA : A.toNat % 8 = 0) (hAp : A.toNat + 384 ≤ pv.toNat) (cA : CanonN s.memory A 12) :
    FunCostAt E "fq12_inv"
      100000000000000000000000000000000000000000000000000000000000000000000000000000000000000
      s [e1, e2] := by
  intro parameters body values cl hlookup hvalues hbind fuel r n hrun hne
  have hparams := (fun_of_index 682 hE.functions (by guest_decl_at 682) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  obtain ⟨c, hpc, hlc⟩ := cA.poly
  exact fq12_inv_cost hE parameters body hlookup fuel ⟨cl, s.globals, s.memory, s.ffi⟩ r n A pv c
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hp hpH halA hAp hpc hlc hrun hne

end InitECandidate.Solver.GuestBound
