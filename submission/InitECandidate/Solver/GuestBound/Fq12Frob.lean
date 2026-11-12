import InitECandidate.Solver.GuestBound.EcpAdd

/-!
# `fq12_frob` keeps coefficients below `p`

Six rounds, each reading coefficients `k`, `k + 6` of the operand and two
entries of the `bn_gamma` table and writing coefficients `k`, `k + 6` of the
destination (which may be the operand). The table entries are only ever the
second operand of `fq_mul`, whose result is canonical as soon as the first
operand is, so nothing is assumed about the table: not where it is, nor what
it holds, nor that `bn_gamma` is a word (a failed load ends the run). Part of the canonicity chain for `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word}

/-- The cells of `D` selected by `S` hold canonical values. -/
def CellsOk (m : Word → Option (PanValue Word)) (D : Word) (S : Nat → Prop) : Prop :=
  ∀ i, i < 12 → S i → ∃ v, Fe m (coefAddr D i) v ∧ v < bnP

theorem CellsOk.set4 {D w0 w1 w2 w3 : Word} {S : Nat → Prop} {j : Nat}
    (h64 : D.toNat + 384 ≤ 2 ^ 64) (hj : j < 12) (hc : CellsOk m D S)
    (hv : limbsVal [w0, w1, w2, w3] < bnP) :
    CellsOk (InitECandidate.Solver.GuestBound.set4 m (coefAddr D j) w0 w1 w2 w3) D
      (fun i => S i ∨ i = j) := by
  have hck := coefAddr_toNat (a := D) (i := j) (by omega)
  have hb : (coefAddr D j).toNat + 32 ≤ 2 ^ 64 := by rw [hck]; omega
  intro i hi hS
  by_cases hij : i = j
  · subst hij
    exact ⟨_, fe_set4 hb, hv⟩
  · obtain ⟨v, hfe, hlt⟩ := hc i hi (hS.resolve_right hij)
    refine ⟨v, fe_congr (by rw [coefAddr_toNat (by omega)]; omega)
      (fun x h1 h2 => set4_other hb ?_) hfe, hlt⟩
    rw [coefAddr_toNat (by omega)] at h1 h2
    rw [hck]
    omega

/-- Leaving the scope of a declaration of `x`, for locals other than `k`. -/
theorem restore_step {li lo : VarName → Option (PanValue Word)} {x k : VarName}
    {v : PanValue Word} (h : ∀ y, y ≠ k → li y = updatePanValueMap lo x v y) :
    ∀ y, y ≠ k → restorePanValueLocal li x (lo x) y = lo y := by
  intro y hy
  unfold restorePanValueLocal
  by_cases hyx : (y == x) = true
  · rw [if_pos hyx, beq_iff_eq.mp hyx]
  · rw [if_neg hyx, h y hy, update_lookup, if_neg hyx]

/-- Invariant of the loop of `fq12_frob`. -/
def FrobI (L : VarName → Option (PanValue Word)) (s : St σ) (A D : Word) (st : St σ) :
    Prop :=
  st.globals = s.globals ∧ st.ffi = s.ffi ∧ (∀ x, x ≠ "k" → st.locals x = L x) ∧
    (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) → st.memory x = s.memory x) ∧
    CanonN st.memory A 12 ∧
    ∃ kk, st.locals "k" = some (.word (BitVec.ofNat 64 kk)) ∧ kk ≤ 6 ∧
      CellsOk st.memory D (fun i => i < kk ∨ (6 ≤ i ∧ i < 6 + kk))

set_option maxHeartbeats 16000000 in
theorem fq12_frob_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq12_frob" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A D : Word)
    (ha : s.locals "a" = some (.word A)) (hd : s.locals "d" = some (.word D))
    (bA : A.toNat + 384 ≤ 2 ^ 63) (bD : D.toNat + 384 ≤ 2 ^ 63)
    (hAD : D = A ∨ D.toNat + 384 ≤ A.toNat ∨ A.toNat + 384 ≤ D.toNat)
    (cA : CanonN s.memory A 12) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D 12 := by
  have hbody := (fun_of_index 679 hE.functions (by guest_decl_at 679) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpp : 0 < bnP := by decide
  have hnat : ∀ n : Nat, n < 100 → (BitVec.ofNat 64 n : Word).toNat = n := by
    intro n hn
    rw [BitVec.toNat_ofNat]
    omega
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D 12)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  obtain ⟨L, hL⟩ : ∃ L, L = updatePanValueMap s.locals "k" (.word 0#64) := ⟨_, rfl⟩
  rw [← hL]
  have La : L "a" = some (.word A) := by rw [hL]; lk [ha]
  have Ld : L "d" = some (.word D) := by rw [hL]; lk [hd]
  refine WPs.seqG (fun st => FrobI L s A D st ∧ CanonN st.memory D 12)
    (WPs.loopG (I := FrobI L s A D)
      ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, cA, 0, by rw [hL]; lk [], by omega,
        fun i _ hS => by omega⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, hfr, hcA, kk, hk, hk6, hcD⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hloc hfr hcA hk hcD
    subst ga fa
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 kk) (by lk [hk]))
      (of_eval (w := 6#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hklt : kk < 6 := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 kk : Word) < 6#64 := by
        rw [BitVec.lt_def, hnat kk (by omega)]
        have : (6#64 : Word).toNat = 6 := by decide
        omega
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have laa : la "a" = some (.word A) := (hloc _ (by decide)).trans La
    have lad : la "d" = some (.word D) := (hloc _ (by decide)).trans Ld
    have hk6' : (BitVec.ofNat 64 kk : Word) + 6#64 = BitVec.ofNat 64 (kk + 6) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    obtain ⟨vk, hfk, hvk⟩ := hcA.get (i := kk) (by omega)
    obtain ⟨vk6, hfk6, hvk6⟩ := hcA.get (i := kk + 6) (by omega)
    refine WPs.dec_load4 hE (addr := coefAddr A kk)
      (of_eval (by unfold coefAddr; ev [evalPanOp, laa, hk])) hfk (fun c0 c1 c2 c3 hck => ?_)
    refine WPs.dec_load4 hE (addr := coefAddr A (kk + 6))
      (of_eval (by unfold coefAddr; ev [evalPanOp, laa, hk, hk6'])) hfk6
      (fun e0 e1 e2 e3 hck6 => ?_)
    -- n9 = 9 ck6
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, n0, n1, n2, n3, hv, hn9⟩ := mulsmall_ret hE hret (a0 := e0) (a1 := e1)
      (a2 := e2) (a3 := e3) (k := 9#64) (by lk []) (eval_const _ _) (by rw [hck6]; exact hvk6)
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    -- d0 = ck + n9
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, p0, p1, p2, p3, hv, hd0⟩ := fqadd_ret hE hret (a0 := c0) (a1 := c1)
      (a2 := c2) (a3 := c3) (b0 := n0) (b1 := n1) (b2 := n2) (b3 := n3) (by lk []) (by lk [])
      (by rw [hck]; exact hvk) hn9
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hd0l : limbsVal [p0, p1, p2, p3] < bnP := by rw [hd0]; exact Nat.mod_lt _ hpp
    -- d1 = -ck6
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, q0, q1, q2, q3, hv, hd1l⟩ := fqneg_ret hE hret (a0 := e0) (a1 := e1)
      (a2 := e2) (a3 := e3) (by lk []) (by rw [hck6]; exact hvk6)
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    try dsimp only
    refine WPs.dec_load4_any hE (fun g00 g01 g02 g03 => ?_)
    refine WPs.dec_load4_any hE (fun g10 g11 g12 g13 => ?_)
    refine WPs.decCall_fqmul1 hE (a0 := p0) (a1 := p1) (a2 := p2) (a3 := p3) (b0 := g00)
      (b1 := g01) (b2 := g02) (b3 := g03) (by lk []) (by lk []) hd0l
      (fun t00 t01 t02 t03 ht0 _ => ?_)
    refine WPs.decCall_fqmul1 hE (a0 := q0) (a1 := q1) (a2 := q2) (a3 := q3) (b0 := g10)
      (b1 := g11) (b2 := g12) (b3 := g13) (by lk []) (by lk []) hd1l
      (fun t10 t11 t12 t13 ht1 _ => ?_)
    refine WPs.decCall_fqmul1 hE (a0 := p0) (a1 := p1) (a2 := p2) (a3 := p3) (b0 := g10)
      (b1 := g11) (b2 := g12) (b3 := g13) (by lk []) (by lk []) hd0l
      (fun t20 t21 t22 t23 ht2 _ => ?_)
    refine WPs.decCall_fqmul1 hE (a0 := q0) (a1 := q1) (a2 := q2) (a3 := q3) (b0 := g00)
      (b1 := g01) (b2 := g02) (b3 := g03) (by lk []) (by lk []) hd1l
      (fun t30 t31 t32 t33 ht3 _ => ?_)
    try dsimp only
    -- u = t0 - t1
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, u0, u1, u2, u3, hv, hu⟩ := fqsub_ret hE hret (a0 := t00) (a1 := t01)
      (a2 := t02) (a3 := t03) (b0 := t10) (b1 := t11) (b2 := t12) (b3 := t13) (by lk [])
      (by lk []) ht0 ht1
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hul : limbsVal [u0, u1, u2, u3] < bnP := by rw [hu]; exact Nat.mod_lt _ hpp
    -- v = t2 + t3
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, v0, v1, v2, v3, hv, hvv⟩ := fqadd_ret hE hret (a0 := t20) (a1 := t21)
      (a2 := t22) (a3 := t23) (b0 := t30) (b1 := t31) (b2 := t32) (b3 := t33) (by lk [])
      (by lk []) ht2 ht3
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hvl : limbsVal [v0, v1, v2, v3] < bnP := by rw [hvv]; exact Nat.mod_lt _ hpp
    -- v9 = 9 v
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, w0, w1, w2, w3, hv, hv9⟩ := mulsmall_ret hE hret (a0 := v0) (a1 := v1)
      (a2 := v2) (a3 := v3) (k := 9#64) (by lk []) (eval_const _ _) hvl
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    -- r0 = u - v9
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, r0, r1, r2, r3, hv, hr0⟩ := fqsub_ret hE hret (a0 := u0) (a1 := u1)
      (a2 := u2) (a3 := u3) (b0 := w0) (b1 := w1) (b2 := w2) (b3 := w3) (by lk []) (by lk [])
      hul hv9
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hr0l : limbsVal [r0, r1, r2, r3] < bnP := by rw [hr0]; exact Nat.mod_lt _ hpp
    try dsimp only
    refine WPs.seq_store4 hE (addr := coefAddr D kk) (w0 := r0) (w1 := r1) (w2 := r2) (w3 := r3)
      (of_eval (by unfold coefAddr; ev [evalPanOp, lad, hk])) (by lk []) ?_
    refine WPs.seq_store4 hE (addr := coefAddr D (kk + 6)) (w0 := v0) (w1 := v1) (w2 := v2)
      (w3 := v3) (of_eval (by unfold coefAddr; ev [evalPanOp, lad, hk, hk6'])) (by lk []) ?_
    refine WPs.assign (old := BitVec.ofNat 64 kk) (by lk [hk])
      (of_eval (w := BitVec.ofNat 64 (kk + 1)) (by ev [hk, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨rfl, rfl, ?_, ?_,
      (hcA.store_alias hAD (by omega) (by omega) (j := kk) (by omega) hr0l).store_alias hAD
        (by omega) (by omega) (j := kk + 6) (by omega) hvl,
      kk + 1, ?_, by omega, ?_⟩
    · intro x hx
      refine Eq.trans ?_ (hloc x hx)
      revert x
      repeat apply restore_step
      intro y hy
      rw [update_lookup, if_neg (by simpa using hy)]
    · intro x hx
      show set4 (set4 ma _ _ _ _ _) _ _ _ _ _ x = _
      rw [set4_outN (n := 12) (by omega) (by omega) (by omega),
        set4_outN (n := 12) (by omega) (by omega) (by omega)]
      exact hfr x hx
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
    · have h2 := ((hcD.set4 (by omega) (j := kk) (by omega) hr0l).set4 (by omega)
        (j := kk + 6) (by omega) hvl)
      intro i hi hS
      exact h2 i hi (by omega)
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hf, hloc, hfr, hcA, kk, hk, hk6, hcD⟩ hcond
    simp only at hg hf hloc hfr hcA hk hcD
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 kk) (by lk [hk]))
      (of_eval (w := 6#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge : ¬ kk < 6 := by
      intro hlt
      have hl : (BitVec.ofNat 64 kk : Word) < 6#64 := by
        rw [BitVec.lt_def, hnat kk (by omega)]
        have : (6#64 : Word).toNat = 6 := by decide
        omega
      simp [evalPanCmp, hl] at hcv
    have : kk = 6 := by omega
    subst this
    refine ⟨⟨hg, hf, hloc, hfr, hcA, 6, hk, hk6, hcD⟩, fun i => ?_⟩
    by_cases hi : i < 12
    · obtain ⟨v, hfe, hlt⟩ := hcD i hi (by omega)
      exact ⟨v, fun _ => ⟨hfe, hlt⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  · rintro ⟨la, ga, ma, fa⟩ ⟨⟨hg, hf, -, hfr, -⟩, hcD⟩
    simp only at hg hf hfr hcD
    subst ga fa
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, ma, rfl, hfr, hcD⟩

theorem fq12frob_ret (hE : GuestEnv E) {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} {e1 e2 : Exp Word} {A D : Word}
    (h : CalleeRet E s "fq12_frob" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word D)) (h2 : E.eval s e2 = some (.word A))
    (bA : A.toNat + 384 ≤ 2 ^ 63) (bD : D.toNat + 384 ≤ 2 ^ 63)
    (hAD : D = A ∨ D.toNat + 384 ≤ A.toNat ∨ A.toNat + 384 ≤ D.toNat)
    (cA : CanonN s.memory A 12) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D 12 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 679 hE.functions (by guest_decl_at 679) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq12_frob_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A D
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) bA bD hAD
    cA hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

/-- `fq12_frob(d, a); rest` over the `Bufs` invariant. -/
theorem WPs.fq12_frob_step (hE : GuestEnv E) {eD eA : Exp Word} {rest : Prog Word}
    {D A hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s eD = some (.word D)) (h2 : E.eval s eA = some (.word A))
    (hB : Bufs pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hA : A ∈ Cn)
    (h : ∀ m', Bufs pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fq12_frob" [eD, eA]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gA := hB.geo A (hB.sub A hA)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := fq12frob_ret hE hret h1 h2 (by omega) (by omega)
    (hB.sep D hD A (hB.sub A hA)) (hB.can A hA)
  subst g ffi
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

end InitECandidate.Solver.GuestBound
