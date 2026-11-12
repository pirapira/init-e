import InitECandidate.Solver.GuestBound.EcpK

/-!
# Step rules for whole points of any field size

Copying a point (three coordinates), `ecp_double` and `ecp_set_inf` as steps
over `BufsK`; the generic versions of the rules in `EcpSteps.lean` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word} {K : Nat}

theorem add_toNat_small {P w : Word} (h : P.toNat + w.toNat < 2 ^ 64) :
    (P + w).toNat = P.toNat + w.toNat := by
  rw [BitVec.toNat_add]
  omega

theorem esz2_toNat {F : Word} (hF : F.toNat = K) (hK : K ≤ 12) :
    (2#64 * (F * 32#64) : Word).toNat = 64 * K := by
  rw [BitVec.toNat_mul, esz_toNat hF hK, show (2#64 : Word).toNat = 2 by decide]
  omega

theorem esz3_toNat {F : Word} (hF : F.toNat = K) (hK : K ≤ 12) :
    (3#64 * (F * 32#64) : Word).toNat = 96 * K := by
  rw [BitVec.toNat_mul, esz_toNat hF hK, show (3#64 : Word).toNat = 3 by decide]
  omega

/-- A canonical coordinate carried across a copy, at byte offset `off`. -/
theorem canon_of_copy_offK {O P X Y : Word} {n off : Nat}
    {m1 m2 : Word → Option (PanValue Word)}
    (hcopy : CopyInv m1 O P n m2) (alO : O.toNat % 8 = 0) (alP : P.toNat % 8 = 0)
    (bO : O.toNat + n < 2 ^ 63) (bP : P.toNat + n < 2 ^ 63)
    (hX : X.toNat = P.toNat + off) (hY : Y.toNat = O.toNat + off) (ho : off % 8 = 0)
    (hon : off + 32 * K ≤ n) (c : CanonN m1 X K) : CanonN m2 Y K := by
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

/-- `memcpy(out, p, 3 * esz); rest`: a point copied onto itself or onto a disjoint point. -/
theorem WPs.pt_copy_stepK (hE : GuestEnv E) {eD eS eN : Exp Word} {rest : Prog Word}
    {F O P hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K) (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (h1 : E.eval s eD = some (.word O)) (h2 : E.eval s eS = some (.word P))
    (h3 : E.eval s eN = some (.word (3#64 * (F * 32#64))))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (hP0 : P ∈ Cn) (hP1 : P + F * 32#64 ∈ Cn) (hP2 : P + 2#64 * (F * 32#64) ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + F * 32#64 ∈ All) (hO2 : O + 2#64 * (F * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + F * 32#64).toNat ∨ O + F * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (F * 32#64)).toNat ∨ O + 2#64 * (F * 32#64) ∈ Wr)
    (hrel : O = P ∨ O.toNat + 96 * K ≤ P.toNat ∨ P.toNat + 96 * K ≤ O.toNat)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "memcpy" [eD, eS, eN]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have hK12 : K ≤ 12 := by omega
  have hez := esz_toNat hF hK12
  have h2ez := esz2_toNat hF hK12
  have hn := esz3_toNat hF hK12
  have hpb := hB.hpb
  have gP0 := hB.geo P (hB.sub P hP0)
  have gP1 := hB.geo _ (hB.sub _ hP1)
  have gP2 := hB.geo _ (hB.sub _ hP2)
  have gO0 := hB.geo O hO0
  have gO1 := hB.geo _ hO1
  have gO2 := hB.geo _ hO2
  have p1 : (P + F * 32#64).toNat = P.toNat + 32 * K := by
    rw [add_toNat_small (by omega), hez]
  have p2 : (P + 2#64 * (F * 32#64)).toNat = P.toNat + 64 * K := by
    rw [add_toNat_small (by omega), h2ez]
  have o1 : (O + F * 32#64).toNat = O.toNat + 32 * K := by
    rw [add_toNat_small (by omega), hez]
  have o2 : (O + 2#64 * (F * 32#64)).toNat = O.toNat + 64 * K := by
    rw [add_toNat_small (by omega), h2ez]
  rcases hrel with heq | hdis
  · subst heq
    obtain ⟨hg, hm, hf⟩ := memcpyself_ret hE hret h1 h2 h3 gO0.1 (by rw [hn]; omega)
      (by rw [hn]; omega)
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
    refine h m1 (hB.writeSet (Ds := [O + 2#64 * (F * 32#64), O + F * 32#64, O]) ?_ ?_ ?_)
    · intro D hD
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl | rfl
      · exact ⟨hO2, w2⟩
      · exact ⟨hO1, w1⟩
      · exact ⟨hO0, w0⟩
    · intro x hx hout
      have x0 := hout O (by simp)
      have x1 := hout (O + F * 32#64) (by simp)
      have x2 := hout (O + 2#64 * (F * 32#64)) (by simp)
      rw [o1] at x1
      rw [o2] at x2
      exact hcopy.cells x (by omega)
    · intro D hD
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
      rcases hD with rfl | rfl | rfl
      · exact canon_of_copy_offK hcopy gO0.1 gP0.1 (by omega) (by omega) (off := 64 * K) p2 o2
          (by omega) (by omega) (hB.can _ hP2)
      · exact canon_of_copy_offK hcopy gO0.1 gP0.1 (by omega) (by omega) (off := 32 * K) p1 o1
          (by omega) (by omega) (hB.can _ hP1)
      · exact canon_of_copy_offK hcopy gO0.1 gP0.1 (by omega) (by omega) (off := 0) rfl rfl
          (by omega) (by omega) (hB.can _ hP0)

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem ecpdoubleK_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {F O P hp pv0 : Word}
    {All Cn : List Word} (hF : F.toNat = K) (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (h : CalleeRet E s "ecp_double" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word O))
    (h3 : E.eval s e3 = some (.word P)) (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (hP0 : P ∈ Cn) (hP1 : P + F * 32#64 ∈ Cn) (hP2 : P + 2#64 * (F * 32#64) ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + F * 32#64 ∈ All) (hO2 : O + 2#64 * (F * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + F * 32#64).toNat ∨ O + F * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (F * 32#64)).toNat ∨ O + 2#64 * (F * 32#64) ∈ Wr) :
    g = s.globals ∧ ffi = s.ffi ∧
      BufsK K pv0 m0 Wr hp All ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn) m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 673 hE.functions (by guest_decl_at 673) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases ecp_doubleK_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ F P O hp
    pv0 m0 Wr All Cn hF hK
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hg hB0 hP0 hP1
    hP2 hO0 hO1 hO2 w0 w1 w2 hrun with hst | ⟨l', m', heq, hB⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hB⟩

theorem ecpsetinfK_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {F O hp pv0 : Word}
    {All Cn : List Word} (hF : F.toNat = K) (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (h : CalleeRet E s "ecp_set_inf" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word O))
    (hB0 : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (hO0 : O ∈ All) (hO1 : O + F * 32#64 ∈ All) (hO2 : O + 2#64 * (F * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + F * 32#64).toNat ∨ O + F * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (F * 32#64)).toNat ∨ O + 2#64 * (F * 32#64) ∈ Wr) :
    g = s.globals ∧ ffi = s.ffi ∧
      BufsK K pv0 m0 Wr hp All ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn) m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 671 hE.functions (by guest_decl_at 671) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases ecp_set_infK_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ F O hp
    pv0 m0 Wr All Cn hF hK
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hB0 hO0 hO1 hO2
    w0 w1 w2 hrun with hst | ⟨l', m', heq, hB⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hB⟩

end rets

theorem WPs.ecp_double_stepK (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {rest : Prog Word}
    {F O P hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K) (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word O))
    (h3 : E.eval s e3 = some (.word P)) (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (hP0 : P ∈ Cn) (hP1 : P + F * 32#64 ∈ Cn) (hP2 : P + 2#64 * (F * 32#64) ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + F * 32#64 ∈ All) (hO2 : O + 2#64 * (F * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + F * 32#64).toNat ∨ O + F * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (F * 32#64)).toNat ∨ O + 2#64 * (F * 32#64) ∈ Wr)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "ecp_double" [e1, e2, e3]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hB⟩ := ecpdoubleK_ret hE hF hK hret h1 h2 h3 hg hB0 hP0 hP1 hP2 hO0 hO1 hO2
    w0 w1 w2
  subst g ffi
  exact h m1 hB

theorem WPs.ecp_set_inf_stepK (hE : GuestEnv E) {e1 e2 : Exp Word} {rest : Prog Word}
    {F O hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K) (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word O))
    (hB0 : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (hO0 : O ∈ All) (hO1 : O + F * 32#64 ∈ All) (hO2 : O + 2#64 * (F * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + F * 32#64).toNat ∨ O + F * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (F * 32#64)).toNat ∨ O + 2#64 * (F * 32#64) ∈ Wr)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "ecp_set_inf" [e1, e2]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hB⟩ := ecpsetinfK_ret hE hF hK hret h1 h2 hB0 hO0 hO1 hO2 w0 w1 w2
  subst g ffi
  exact h m1 hB

end InitECandidate.Solver.GuestBound
