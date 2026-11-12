import InitECandidate.Solver.GuestBound.BufsK

/-!
# Step rules over `BufsK` for the coefficientwise field operations

`fe_add`, `fe_sub`, `fe_neg`, `fe_mul_small`, `fe_set_zero`, `fe_set_one`,
allocation and copying of one field element, for any field size (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word} {K : Nat}

theorem fmul32_toNat {F : Word} (hF : F.toNat ≤ 12) : (F * 32#64 : Word).toNat = 32 * F.toNat := by
  rw [BitVec.toNat_mul, show (32#64 : Word).toNat = 32 by decide]
  omega

theorem WPs.fe_add_stepK (hE : GuestEnv E) {eF eD eA eB : Exp Word} {rest : Prog Word}
    {F D A B hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K) (hK : K ≤ 12)
    (h1 : E.eval s eF = some (.word F)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A)) (h4 : E.eval s eB = some (.word B))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hA : A ∈ Cn) (hBc : B ∈ Cn)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_add" [eF, eD, eA, eB]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gA := hB.geo A (hB.sub A hA)
  have gB := hB.geo B (hB.sub B hBc)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := feadd_ret hE hret h1 h2 h3 h4 (by rw [hF]; exact hK)
    (by rw [hF]; omega) (by rw [hF]; omega) (by rw [hF]; exact hB.sep D hD A (hB.sub A hA))
    (by rw [hF]; exact hB.can A hA) (by rw [hF]; omega)
    (by rw [hF]; exact hB.sep D hD B (hB.sub B hBc)) (by rw [hF]; exact hB.can B hBc)
  subst g ffi
  rw [hF] at hfr hc
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

theorem WPs.fe_sub_stepK (hE : GuestEnv E) {eF eD eA eB : Exp Word} {rest : Prog Word}
    {F D A B hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K) (hK : K ≤ 12)
    (h1 : E.eval s eF = some (.word F)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A)) (h4 : E.eval s eB = some (.word B))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hA : A ∈ Cn) (hBc : B ∈ Cn)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_sub" [eF, eD, eA, eB]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gA := hB.geo A (hB.sub A hA)
  have gB := hB.geo B (hB.sub B hBc)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := fesub_ret hE hret h1 h2 h3 h4 (by rw [hF]; exact hK)
    (by rw [hF]; omega) (by rw [hF]; omega) (by rw [hF]; exact hB.sep D hD A (hB.sub A hA))
    (by rw [hF]; exact hB.can A hA) (by rw [hF]; omega)
    (by rw [hF]; exact hB.sep D hD B (hB.sub B hBc)) (by rw [hF]; exact hB.can B hBc)
  subst g ffi
  rw [hF] at hfr hc
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

theorem WPs.fe_neg_stepK (hE : GuestEnv E) {eF eD eA : Exp Word} {rest : Prog Word}
    {F D A hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K) (hK : K ≤ 12)
    (h1 : E.eval s eF = some (.word F)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hA : A ∈ Cn)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_neg" [eF, eD, eA]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gA := hB.geo A (hB.sub A hA)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := feneg_ret hE hret h1 h2 h3 (by rw [hF]; exact hK)
    (by rw [hF]; omega) (by rw [hF]; omega) (by rw [hF]; exact hB.sep D hD A (hB.sub A hA))
    (by rw [hF]; exact hB.can A hA)
  subst g ffi
  rw [hF] at hfr hc
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

theorem WPs.fe_mul_small_stepK (hE : GuestEnv E) {eF eD eA eK : Exp Word} {rest : Prog Word}
    {F D A Kw hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K) (hK : K ≤ 12)
    (h1 : E.eval s eF = some (.word F)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A))
    (h5 : E.eval s eK = some (.word Kw))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hA : A ∈ Cn)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_mul_small" [eF, eD, eA, eK]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gA := hB.geo A (hB.sub A hA)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := femulsmall_ret hE hret h1 h2 h3 h5 (by rw [hF]; exact hK)
    (by rw [hF]; omega) (by rw [hF]; omega) (by rw [hF]; exact hB.sep D hD A (hB.sub A hA))
    (by rw [hF]; exact hB.can A hA)
  subst g ffi
  rw [hF] at hfr hc
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

set_option maxHeartbeats 4000000 in
theorem fe_set_zeroK_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_set_zero" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (F D : Word) (hfld : s.locals "fld" = some (.word F))
    (hd : s.locals "d" = some (.word D)) (hF : F.toNat ≤ 12) (al : D.toNat % 8 = 0)
    (b : D.toNat + 32 * F.toNat ≤ 2 ^ 62) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat := by
  have hbody := (fun_of_index 669 hE.functions (by guest_decl_at 669) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat)) r h
  have hn : (F * 32#64 : Word).toNat = 32 * F.toNat := fmul32_toNat hF
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hz⟩ := memzero_ret hE hret (dst := D) (nW := F * 32#64) (by lk [hd])
    (by ev [evalPanOp, hfld]) al (by rw [hn]; omega) (by rw [hn]; omega)
  subst g ffi
  rw [hn] at hz
  exact WPs.ret (of_eval (eval_const _ _)) ⟨_, m1, rfl,
    fun x hx => by rw [hz x, if_neg (by omega)],
    CanonN.of_poly (PolyAt.of_zero (n := F.toNat) al (by omega) hz) (fun _ _ => by decide)⟩

theorem fesetzeroK_ret (hE : GuestEnv E) {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} {e1 e2 : Exp Word} {F D : Word}
    (h : CalleeRet E s "fe_set_zero" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word D))
    (hF : F.toNat ≤ 12) (al : D.toNat % 8 = 0) (b : D.toNat + 32 * F.toNat ≤ 2 ^ 62) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D F.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 669 hE.functions (by guest_decl_at 669) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_set_zeroK_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ F D
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hF al b
    hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

theorem WPs.fe_set_zero_stepK (hE : GuestEnv E) {eF eD : Exp Word} {rest : Prog Word}
    {F D hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K) (hK : K ≤ 12)
    (h1 : E.eval s eF = some (.word F)) (h2 : E.eval s eD = some (.word D))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_set_zero" [eF, eD]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := fesetzeroK_ret hE hret h1 h2 (by rw [hF]; exact hK) gD.1
    (by rw [hF]; omega)
  subst g ffi
  rw [hF] at hfr hc
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

set_option maxHeartbeats 4000000 in
theorem fe_set_oneK_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_set_one" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (F D : Word) (hfld : s.locals "fld" = some (.word F))
    (hd : s.locals "d" = some (.word D)) (hF : F.toNat ≤ 12) (hF1 : 1 ≤ F.toNat) (al : D.toNat % 8 = 0)
    (b : D.toNat + 32 * F.toNat ≤ 2 ^ 62) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat := by
  have hbody := (fun_of_index 670 hE.functions (by guest_decl_at 670) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat)) r h
  have hn : (F * 32#64 : Word).toNat = 32 * F.toNat := fmul32_toNat hF
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hz⟩ := memzero_ret hE hret (dst := D) (nW := F * 32#64) (by lk [hd])
    (by ev [evalPanOp, hfld]) al (by rw [hn]; omega) (by rw [hn]; omega)
  subst g ffi
  rw [hn] at hz
  have hc1 : CanonN m1 D F.toNat :=
    CanonN.of_poly (PolyAt.of_zero (n := F.toNat) al (by omega) hz) (fun _ _ => by decide)
  refine WPs.seq_store4 hE (addr := coefAddr D 0)
    (w0 := 15230403791020821917#64) (w1 := 754611498739239741#64)
    (w2 := 7381016538464732716#64) (w3 := 1011752739694698287#64)
    (of_eval (by rw [coefAddr_zero]; lk [hd]))
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) ?_
  refine WPs.ret (of_eval (eval_const _ _)) ⟨_, _, rfl, fun x hx => ?_,
    hc1.set4 (n := F.toNat) (by omega) (by omega) cone_lt⟩
  show set4 m1 (coefAddr D 0) _ _ _ _ x = s.memory x
  rw [set4_outN (n := F.toNat) (by omega) (by omega) (by omega), hz x, if_neg (by omega)]

theorem fesetoneK_ret (hE : GuestEnv E) {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} {e1 e2 : Exp Word} {F D : Word}
    (h : CalleeRet E s "fe_set_one" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word D))
    (hF : F.toNat ≤ 12) (hF1 : 1 ≤ F.toNat) (al : D.toNat % 8 = 0) (b : D.toNat + 32 * F.toNat ≤ 2 ^ 62) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D F.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 670 hE.functions (by guest_decl_at 670) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_set_oneK_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ F D
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hF hF1 al b
    hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

theorem WPs.fe_set_one_stepK (hE : GuestEnv E) {eF eD : Exp Word} {rest : Prog Word}
    {F D hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K) (hK : K ≤ 12) (hK1 : 1 ≤ K)
    (h1 : E.eval s eF = some (.word F)) (h2 : E.eval s eD = some (.word D))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_set_one" [eF, eD]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := fesetoneK_ret hE hret h1 h2 (by rw [hF]; exact hK) (by rw [hF]; exact hK1) gD.1
    (by rw [hF]; omega)
  subst g ffi
  rw [hF] at hfr hc
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

/-- `var x = alloc(esz); body`: the block joins `All`. -/
theorem WPs.fe_alloc_stepK (hE : GuestEnv E) {x : VarName} {e : Exp Word} {body : Prog Word}
    {ez hp pv0 : Word} {All Cn : List Word} (hez : ez.toNat = 32 * K)
    (he : E.eval s e = some (.word ez)) (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (h : ∀ hp' : Word, pv0.toNat ≤ hp.toNat → hp.toNat + 32 * K ≤ hp'.toNat →
      BufsK K pv0 m0 Wr hp' (hp :: All) Cn s.memory →
      WPs E ⟨updatePanValueMap s.locals x (.word hp),
        updatePanValueMap s.globals "heap_ptr" (.word hp'), s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "alloc" [e] body) Q := by
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hv, hm, hf, qv, hg', h1, h2⟩ := alloc_ret hE hret he hg ⟨hB.hpb, hB.hpa⟩
  simp only [List.cons.injEq, and_true] at hv
  subst v m ffi g
  rw [hez] at h1
  exact h qv hB.ple h1 (hB.alloc h1 h2.1 h2.2)

/-- `memcpy(d, s, esz); rest` between two different buffers. -/
theorem WPs.fe_copy_stepK (hE : GuestEnv E) {eD eS eN : Exp Word} {rest : Prog Word}
    {D S ez hp pv0 : Word} {All Cn : List Word} (hez : ez.toNat = 32 * K)
    (h1 : E.eval s eD = some (.word D)) (h2 : E.eval s eS = some (.word S))
    (h3 : E.eval s eN = some (.word ez))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hS : S ∈ Cn) (hne : D ≠ S)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "memcpy" [eD, eS, eN]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gS := hB.geo S (hB.sub S hS)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  have hdis : D.toNat + 32 * K ≤ S.toNat ∨ S.toNat + 32 * K ≤ D.toNat := by
    rcases hB.sep D hD S (hB.sub S hS) with heq | hd
    · exact absurd heq hne
    · exact hd
  obtain ⟨hg, hf, hcopy⟩ := memcpy_ret hE hret h1 h2 h3
    ⟨by rw [hez]; omega, by rw [hez]; omega, by rw [hez]; omega, by rw [hez]; omega⟩
  subst g ffi
  rw [hez] at hcopy
  obtain ⟨c, hpc, hlc⟩ := (hB.can S hS).poly
  exact h m1 (hB.write hD hDl (fun x _ hx => hcopy.cells x (by omega))
    (CanonN.of_poly (PolyAt.of_copy (n := K) hcopy gD.1 gS.1 (by omega) (by omega) hpc) hlc))

end InitECandidate.Solver.GuestBound
