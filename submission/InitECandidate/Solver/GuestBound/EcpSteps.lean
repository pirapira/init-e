import InitECandidate.Solver.GuestBound.MemCpySelf

/-!
# Step rules for whole-point operations on `Fq12`

Copying a point (three coordinates, 1152 bytes), `ecp_double` and
`ecp_set_inf` as steps over the `Bufs` invariant. Used by `ecp_add` and
`bn254_miller_raw` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word}

/-- Several writes at once: the buffers of `Ds` become canonical, everything
else below `hp` outside them is untouched. -/
theorem Bufs.writeSet {pv0 hp : Word} {All Cn Ds : List Word} (h : Bufs pv0 m0 Wr hp All Cn m)
    (hD : ∀ D ∈ Ds, D ∈ All ∧ (pv0.toNat ≤ D.toNat ∨ D ∈ Wr))
    (hfr : ∀ x : Word, x.toNat < hp.toNat →
      (∀ D ∈ Ds, x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) → m' x = m x)
    (hc : ∀ D ∈ Ds, CanonN m' D 12) : Bufs pv0 m0 Wr hp All (Ds ++ Cn) m' := by
  refine ⟨h.hpb, h.hpa, h.ple, h.geo, h.sep, ?_, ?_, ?_⟩
  · intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact (hD B hB).1
    · exact h.sub B hB
  · intro B hB
    by_cases hBD : B ∈ Ds
    · exact hc B hBD
    · have hB' : B ∈ Cn := by
        rcases List.mem_append.mp hB with hB | hB
        · exact absurd hB hBD
        · exact hB
      have hBA := h.sub B hB'
      have hg := h.geo B hBA
      refine (h.can B hB').frame (by have := h.hpb; omega) (fun x h1 h2 => hfr x (by omega) ?_)
      intro D hDs
      rcases h.sep B hBA D (hD D hDs).1 with heq | hdis
      · exact absurd (heq ▸ hDs) hBD
      · omega
  · intro x hx hW
    rw [hfr x (by have := h.ple; omega) (fun D hDs => ?_)]
    · exact h.low x hx hW
    · rcases (hD D hDs).2 with hl | hw
      · exact Or.inl (by omega)
      · exact hW D hw

/-- A canonical coordinate carried across a copy, at byte offset `off`. -/
theorem canon_of_copy_off {O P X Y : Word} {n off : Nat} {m1 m2 : Word → Option (PanValue Word)}
    (hcopy : CopyInv m1 O P n m2) (alO : O.toNat % 8 = 0) (alP : P.toNat % 8 = 0)
    (bO : O.toNat + n < 2 ^ 63) (bP : P.toNat + n < 2 ^ 63)
    (hX : X.toNat = P.toNat + off) (hY : Y.toNat = O.toNat + off) (ho : off % 8 = 0)
    (hon : off + 384 ≤ n) (c : CanonN m1 X 12) : CanonN m2 Y 12 := by
  intro i
  obtain ⟨v, hv⟩ := c i
  refine ⟨v, fun hi => ⟨?_, (hv hi).2⟩⟩
  obtain ⟨w0, w1, w2, w3, c0, c1, c2, c3, hn⟩ := (hv hi).1
  have hcs := coefAddr_toNat (a := X) (i := i) (by omega)
  have hcd := coefAddr_toNat (a := Y) (i := i) (by omega)
  have hbs : (coefAddr X i).toNat + 32 ≤ 2 ^ 64 := by rw [hcs]; omega
  have hbd : (coefAddr Y i).toNat + 32 ≤ 2 ^ 64 := by rw [hcd]; omega
  refine ⟨w0, w1, w2, w3, ?_, ?_, ?_, ?_, hn⟩
  · exact hcopy.cell alO alP (by omega) (by omega) (o := off + 32 * i) (by rw [hcs]; omega)
      (by rw [hcd]; omega) (by omega) (by omega) c0
  · exact hcopy.cell alO alP (by omega) (by omega) (o := off + 32 * i + 8)
      (by rw [a8_toNat hbs, hcs]; omega) (by rw [a8_toNat hbd, hcd]; omega) (by omega) (by omega)
      c1
  · exact hcopy.cell alO alP (by omega) (by omega) (o := off + 32 * i + 16)
      (by rw [a16_toNat hbs, hcs]; omega) (by rw [a16_toNat hbd, hcd]; omega) (by omega)
      (by omega) c2
  · exact hcopy.cell alO alP (by omega) (by omega) (o := off + 32 * i + 24)
      (by rw [a24_toNat hbs, hcs]; omega) (by rw [a24_toNat hbd, hcd]; omega) (by omega)
      (by omega) c3

theorem memcpyself_ret (hE : GuestEnv E) {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} {e1 e2 e3 : Exp Word} {A nW : Word}
    (h : CalleeRet E s "memcpy" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word A)) (h2 : E.eval s e2 = some (.word A))
    (h3 : E.eval s e3 = some (.word nW)) (hal : A.toNat % 8 = 0) (hn32 : nW.toNat % 32 = 0)
    (h64 : A.toNat + nW.toNat + 32 < 2 ^ 64) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases memcpy_self hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A nW
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hal hn32 h64
    hrun with hst | ⟨l', heq⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl⟩

/-- `memcpy(out, p, 1152); rest`: a point copied onto itself or onto a disjoint point. -/
theorem WPs.pt_copy_step (hE : GuestEnv E) {eD eS eN : Exp Word} {rest : Prog Word}
    {O P hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s eD = some (.word O)) (h2 : E.eval s eS = some (.word P))
    (h3 : E.eval s eN = some (.word 1152#64))
    (hB : Bufs pv0 m0 Wr hp All Cn s.memory)
    (hP0 : P ∈ Cn) (hP1 : P + 384#64 ∈ Cn) (hP2 : P + 768#64 ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + 384#64 ∈ All) (hO2 : O + 768#64 ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 384#64).toNat ∨ O + 384#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 768#64).toNat ∨ O + 768#64 ∈ Wr)
    (hrel : O = P ∨ O.toNat + 1152 ≤ P.toNat ∨ P.toNat + 1152 ≤ O.toNat)
    (h : ∀ m', Bufs pv0 m0 Wr hp All ((O + 768#64) :: (O + 384#64) :: O :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "memcpy" [eD, eS, eN]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have hn : (1152#64 : Word).toNat = 1152 := by decide
  have hpb := hB.hpb
  have gP0 := hB.geo P (hB.sub P hP0)
  have gP1 := hB.geo _ (hB.sub _ hP1)
  have gP2 := hB.geo _ (hB.sub _ hP2)
  have gO0 := hB.geo O hO0
  have gO1 := hB.geo _ hO1
  have gO2 := hB.geo _ hO2
  have p1 : (P + 384#64).toNat = P.toNat + 384 := add_lit_toNat (k := 384) (by omega) (by omega)
  have p2 : (P + 768#64).toNat = P.toNat + 768 := add_lit_toNat (k := 768) (by omega) (by omega)
  have o1 : (O + 384#64).toNat = O.toNat + 384 := add_lit_toNat (k := 384) (by omega) (by omega)
  have o2 : (O + 768#64).toNat = O.toNat + 768 := add_lit_toNat (k := 768) (by omega) (by omega)
  rcases hrel with heq | hdis
  · subst heq
    obtain ⟨hg, hm, hf⟩ := memcpyself_ret hE hret h1 h2 h3 gO0.1 (by rw [hn]) (by rw [hn]; omega)
    subst g m1 ffi
    refine h _ (hB.mono (fun B hB' => ?_))
    simp only [List.mem_cons] at hB'
    rcases hB' with rfl | rfl | rfl | hB'
    · exact hP2
    · exact hP1
    · exact hP0
    · exact hB'
  · obtain ⟨hg, hf, hcopy⟩ := memcpy_ret hE hret h1 h2 h3
      ⟨by rw [hn]; omega, by rw [hn]; omega, by rw [hn]; omega, by rw [hn]; omega⟩
    subst g ffi
    rw [hn] at hcopy
    refine h m1 (hB.writeSet (Ds := [O + 768#64, O + 384#64, O]) ?_ ?_ ?_)
    · intro D hD
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl | rfl
      · exact ⟨hO2, w2⟩
      · exact ⟨hO1, w1⟩
      · exact ⟨hO0, w0⟩
    · intro x hx hout
      have x0 := hout O (by simp)
      have x1 := hout (O + 384#64) (by simp)
      have x2 := hout (O + 768#64) (by simp)
      rw [o1] at x1
      rw [o2] at x2
      exact hcopy.cells x (by omega)
    · intro D hD
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl | rfl
      · exact canon_of_copy_off hcopy gO0.1 gP0.1 (by omega) (by omega) (off := 768) p2 o2
          (by omega) (by omega) (hB.can _ hP2)
      · exact canon_of_copy_off hcopy gO0.1 gP0.1 (by omega) (by omega) (off := 384) p1 o1
          (by omega) (by omega) (hB.can _ hP1)
      · exact canon_of_copy_off hcopy gO0.1 gP0.1 (by omega) (by omega) (off := 0) rfl rfl
          (by omega) (by omega) (hB.can _ hP0)

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem ecpdouble_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {O P hp pv0 : Word}
    {All Cn : List Word}
    (h : CalleeRet E s "ecp_double" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word 12#64)) (h2 : E.eval s e2 = some (.word O))
    (h3 : E.eval s e3 = some (.word P)) (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : Bufs pv0 m0 Wr hp All Cn s.memory)
    (hP0 : P ∈ Cn) (hP1 : P + 384#64 ∈ Cn) (hP2 : P + 768#64 ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + 384#64 ∈ All) (hO2 : O + 768#64 ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 384#64).toNat ∨ O + 384#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 768#64).toNat ∨ O + 768#64 ∈ Wr) :
    g = s.globals ∧ ffi = s.ffi ∧
      Bufs pv0 m0 Wr hp All ((O + 768#64) :: (O + 384#64) :: O :: Cn) m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 673 hE.functions (by guest_decl_at 673) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases ecp_double12_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ P O hp
    pv0 m0 Wr All Cn
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hg hB0 hP0 hP1
    hP2 hO0 hO1 hO2 w0 w1 w2 hrun with hst | ⟨l', m', heq, hB⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hB⟩

theorem ecpsetinf_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {O hp pv0 : Word}
    {All Cn : List Word}
    (h : CalleeRet E s "ecp_set_inf" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word 12#64)) (h2 : E.eval s e2 = some (.word O))
    (hB0 : Bufs pv0 m0 Wr hp All Cn s.memory)
    (hO0 : O ∈ All) (hO1 : O + 384#64 ∈ All) (hO2 : O + 768#64 ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 384#64).toNat ∨ O + 384#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 768#64).toNat ∨ O + 768#64 ∈ Wr) :
    g = s.globals ∧ ffi = s.ffi ∧
      Bufs pv0 m0 Wr hp All ((O + 768#64) :: (O + 384#64) :: O :: Cn) m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 671 hE.functions (by guest_decl_at 671) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases ecp_set_inf12_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ O hp
    pv0 m0 Wr All Cn
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hB0 hO0 hO1 hO2
    w0 w1 w2 hrun with hst | ⟨l', m', heq, hB⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hB⟩

end rets

theorem WPs.ecp_double_step (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {rest : Prog Word}
    {O P hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s e1 = some (.word 12#64)) (h2 : E.eval s e2 = some (.word O))
    (h3 : E.eval s e3 = some (.word P)) (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : Bufs pv0 m0 Wr hp All Cn s.memory)
    (hP0 : P ∈ Cn) (hP1 : P + 384#64 ∈ Cn) (hP2 : P + 768#64 ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + 384#64 ∈ All) (hO2 : O + 768#64 ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 384#64).toNat ∨ O + 384#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 768#64).toNat ∨ O + 768#64 ∈ Wr)
    (h : ∀ m', Bufs pv0 m0 Wr hp All ((O + 768#64) :: (O + 384#64) :: O :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "ecp_double" [e1, e2, e3]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hB⟩ := ecpdouble_ret hE hret h1 h2 h3 hg hB0 hP0 hP1 hP2 hO0 hO1 hO2 w0 w1 w2
  subst g ffi
  exact h m1 hB

theorem WPs.ecp_set_inf_step (hE : GuestEnv E) {e1 e2 : Exp Word} {rest : Prog Word}
    {O hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s e1 = some (.word 12#64)) (h2 : E.eval s e2 = some (.word O))
    (hB0 : Bufs pv0 m0 Wr hp All Cn s.memory)
    (hO0 : O ∈ All) (hO1 : O + 384#64 ∈ All) (hO2 : O + 768#64 ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 384#64).toNat ∨ O + 384#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 768#64).toNat ∨ O + 768#64 ∈ Wr)
    (h : ∀ m', Bufs pv0 m0 Wr hp All ((O + 768#64) :: (O + 384#64) :: O :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "ecp_set_inf" [e1, e2]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hB⟩ := ecpsetinf_ret hE hret h1 h2 hB0 hO0 hO1 hO2 w0 w1 w2
  subst g ffi
  exact h m1 hB

end InitECandidate.Solver.GuestBound
