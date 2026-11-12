import InitECandidate.Solver.GuestBound.StepsK

/-!
# `fe_mul` and `fe_sqr` for the small fields

`fq2_mul`, and the dispatchers `fe_mul`, `fe_sqr` for field sizes 1 and 2,
keep coefficients below `p`; step rules over `BufsK` for sizes 1, 2 and 12
(issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word} {K : Nat}

theorem CanonN.nil (m : Word → Option (PanValue Word)) (D : Word) : CanonN m D 0 :=
  fun _ => ⟨0, fun h => absurd h (Nat.not_lt_zero _)⟩

/-- What a small-field operation with destination `D` returns. -/
def FeRet (s : St σ) (D : Word) (k : Nat) (r : Result σ) : Prop :=
  ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * k ≤ x.toNat) → m' x = s.memory x) ∧
    CanonN m' D k

set_option maxHeartbeats 8000000 in
theorem fq2_mul_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq2_mul" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A B D : Word)
    (ha : s.locals "a" = some (.word A)) (hb : s.locals "b" = some (.word B))
    (hd : s.locals "d" = some (.word D))
    (bA : A.toNat + 64 ≤ 2 ^ 62) (bB : B.toNat + 64 ≤ 2 ^ 62) (bD : D.toNat + 64 ≤ 2 ^ 62)
    (cA : CanonN s.memory A 2) (cB : CanonN s.memory B 2) (h : Runs E s body r) :
    Stopped r ∨ FeRet s D 2 r := by
  have hbody := (fun_of_index 657 hE.functions (by guest_decl_at 657) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpp : 0 < bnP := by decide
  refine (?_ : WPs E s _ (FeRet s D 2)) r h
  obtain ⟨va0, fa0, la0⟩ := cA.get (i := 0) (by omega)
  obtain ⟨va1, fa1, la1⟩ := cA.get (i := 1) (by omega)
  obtain ⟨vb0, fb0, lb0⟩ := cB.get (i := 0) (by omega)
  obtain ⟨vb1, fb1, lb1⟩ := cB.get (i := 1) (by omega)
  refine WPs.dec_load4 hE (addr := coefAddr A 0) (of_eval (by lk [ha, coefAddr_zero])) fa0
    (fun a00 a01 a02 a03 h0 => ?_)
  refine WPs.dec_load4 hE (addr := coefAddr A 1)
    (of_eval (by show E.eval _ _ = some (.word (A + 32#64)); ev [ha])) fa1
    (fun a10 a11 a12 a13 h1 => ?_)
  refine WPs.dec_load4 hE (addr := coefAddr B 0) (of_eval (by lk [hb, coefAddr_zero])) fb0
    (fun b00 b01 b02 b03 h2 => ?_)
  refine WPs.dec_load4 hE (addr := coefAddr B 1)
    (of_eval (by show E.eval _ _ = some (.word (B + 32#64)); ev [hb])) fb1
    (fun b10 b11 b12 b13 h3 => ?_)
  try dsimp only
  refine WPs.decCall_fqmul hE (a0 := a00) (a1 := a01) (a2 := a02) (a3 := a03) (b0 := b00)
    (b1 := b01) (b2 := b02) (b3 := b03) (by lk []) (by lk []) (by rw [h0]; exact la0)
    (by rw [h2]; exact lb0) (fun t00 t01 t02 t03 ht0 _ => ?_)
  refine WPs.decCall_fqmul hE (a0 := a10) (a1 := a11) (a2 := a12) (a3 := a13) (b0 := b10)
    (b1 := b11) (b2 := b12) (b3 := b13) (by lk []) (by lk []) (by rw [h1]; exact la1)
    (by rw [h3]; exact lb1) (fun t10 t11 t12 t13 ht1 _ => ?_)
  refine WPs.decCall_fqmul hE (a0 := a00) (a1 := a01) (a2 := a02) (a3 := a03) (b0 := b10)
    (b1 := b11) (b2 := b12) (b3 := b13) (by lk []) (by lk []) (by rw [h0]; exact la0)
    (by rw [h3]; exact lb1) (fun t20 t21 t22 t23 ht2 _ => ?_)
  refine WPs.decCall_fqmul hE (a0 := a10) (a1 := a11) (a2 := a12) (a3 := a13) (b0 := b00)
    (b1 := b01) (b2 := b02) (b3 := b03) (by lk []) (by lk []) (by rw [h1]; exact la1)
    (by rw [h2]; exact lb0) (fun t30 t31 t32 t33 ht3 _ => ?_)
  try dsimp only
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, r00, r01, r02, r03, hv, hr0⟩ := fqsub_ret hE hret (a0 := t00) (a1 := t01)
    (a2 := t02) (a3 := t03) (b0 := t10) (b1 := t11) (b2 := t12) (b3 := t13) (by lk []) (by lk [])
    ht0 ht1
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, r10, r11, r12, r13, hv, hr1⟩ := fqadd_ret hE hret (a0 := t20) (a1 := t21)
    (a2 := t22) (a3 := t23) (b0 := t30) (b1 := t31) (b2 := t32) (b3 := t33) (by lk []) (by lk [])
    ht2 ht3
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  try dsimp only
  refine WPs.seq_store4 hE (addr := coefAddr D 0) (w0 := r00) (w1 := r01) (w2 := r02) (w3 := r03)
    (of_eval (by lk [hd, coefAddr_zero])) (by lk []) ?_
  refine WPs.seq_store4 hE (addr := coefAddr D 1) (w0 := r10) (w1 := r11) (w2 := r12) (w3 := r13)
    (of_eval (by show E.eval _ _ = some (.word (D + 32#64)); ev [hd])) (by lk []) ?_
  try dsimp only
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  refine ⟨_, _, rfl, fun x hx => ?_, ?_⟩
  · show set4 (set4 s.memory _ _ _ _ _) _ _ _ _ _ x = _
    rw [set4_outN (n := 2) (by omega) (by omega) (by omega),
      set4_outN (n := 2) (by omega) (by omega) (by omega)]
  · exact CanonN.snoc (k := 1) (by omega)
      (CanonN.snoc (k := 0) (by omega) (CanonN.nil _ _) (by rw [hr0]; exact Nat.mod_lt _ hpp))
      (by rw [hr1]; exact Nat.mod_lt _ hpp)

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem fq2mul_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {A B D : Word}
    (h : CalleeRet E s "fq2_mul" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word D)) (h2 : E.eval s e2 = some (.word A))
    (h3 : E.eval s e3 = some (.word B))
    (bA : A.toNat + 64 ≤ 2 ^ 62) (bB : B.toNat + 64 ≤ 2 ^ 62) (bD : D.toNat + 64 ≤ 2 ^ 62)
    (cA : CanonN s.memory A 2) (cB : CanonN s.memory B 2) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * 2 ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D 2 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 657 hE.functions (by guest_decl_at 657) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq2_mul_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A B D
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) bA bB bD cA cB hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

end rets

set_option maxHeartbeats 4000000 in
theorem fe_mul1_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_mul" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A B D : Word)
    (hfld : s.locals "fld" = some (.word 1#64))
    (ha : s.locals "a" = some (.word A)) (hb : s.locals "b" = some (.word B))
    (hd : s.locals "d" = some (.word D))
    (bA : A.toNat + 32 ≤ 2 ^ 62) (bB : B.toNat + 32 ≤ 2 ^ 62) (bD : D.toNat + 32 ≤ 2 ^ 62)
    (cA : CanonN s.memory A 1) (cB : CanonN s.memory B 1) (h : Runs E s body r) :
    Stopped r ∨ FeRet s D 1 r := by
  have hbody := (fun_of_index 661 hE.functions (by guest_decl_at 661) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (FeRet s D 1)) r h
  have e1 : evalPanCmp .equal (1#64 : Word) 1#64 = 1#64 := by decide
  refine WPs.seqG (fun _ => False) (WPs.ite (w := 1#64) (fun x hx => by
    rw [eval_cmp_inv hE (of_eval (w := 1#64) (by lk [hfld])) (of_eval (eval_const _ _)) x hx, e1])
    ?_) (fun _ hf => hf.elim)
  rw [if_neg (by decide)]
  obtain ⟨va, fa, la⟩ := cA.get (i := 0) (by omega)
  obtain ⟨vb, fb, lb⟩ := cB.get (i := 0) (by omega)
  refine WPs.dec_load4 hE (addr := coefAddr A 0) (of_eval (by lk [ha, coefAddr_zero])) fa
    (fun a0 a1 a2 a3 h0 => ?_)
  refine WPs.dec_load4 hE (addr := coefAddr B 0) (of_eval (by lk [hb, coefAddr_zero])) fb
    (fun b0 b1 b2 b3 h1 => ?_)
  refine WPs.decCall_fqmul hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b0 := b0)
    (b1 := b1) (b2 := b2) (b3 := b3) (by lk []) (by lk []) (by rw [h0]; exact la)
    (by rw [h1]; exact lb) (fun t0 t1 t2 t3 ht _ => ?_)
  try dsimp only
  refine WPs.seq_store4 hE (addr := coefAddr D 0) (w0 := t0) (w1 := t1) (w2 := t2) (w3 := t3)
    (of_eval (by lk [hd, coefAddr_zero])) (by lk []) ?_
  try dsimp only
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  refine ⟨_, _, rfl, fun x hx => ?_, CanonN.snoc (k := 0) (by omega) (CanonN.nil _ _) ht⟩
  show set4 s.memory _ _ _ _ _ x = _
  rw [set4_outN (n := 1) (by omega) (by omega) (by omega)]

set_option maxHeartbeats 4000000 in
theorem fe_mul2_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_mul" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A B D : Word)
    (hfld : s.locals "fld" = some (.word 2#64))
    (ha : s.locals "a" = some (.word A)) (hb : s.locals "b" = some (.word B))
    (hd : s.locals "d" = some (.word D))
    (bA : A.toNat + 64 ≤ 2 ^ 62) (bB : B.toNat + 64 ≤ 2 ^ 62) (bD : D.toNat + 64 ≤ 2 ^ 62)
    (cA : CanonN s.memory A 2) (cB : CanonN s.memory B 2) (h : Runs E s body r) :
    Stopped r ∨ FeRet s D 2 r := by
  have hbody := (fun_of_index 661 hE.functions (by guest_decl_at 661) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (FeRet s D 2)) r h
  have e1 : evalPanCmp .equal (2#64 : Word) 1#64 = 0#64 := by decide
  have e2 : evalPanCmp .equal (2#64 : Word) 2#64 = 1#64 := by decide
  refine WPs.guard0 (fun x hx => by
    rw [eval_cmp_inv hE (of_eval (w := 2#64) (by lk [hfld])) (of_eval (eval_const _ _)) x hx, e1])
    ?_
  refine WPs.seqG (fun _ => False) (WPs.ite (w := 1#64) (fun x hx => by
    rw [eval_cmp_inv hE (of_eval (w := 2#64) (by lk [hfld])) (of_eval (eval_const _ _)) x hx, e2])
    ?_) (fun _ hf => hf.elim)
  rw [if_neg (by decide)]
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hfr, hc⟩ := fq2mul_ret hE hret (A := A) (B := B) (D := D) (by lk [hd])
    (by lk [ha]) (by lk [hb]) bA bB bD cA cB
  subst g ffi
  exact WPs.ret (of_eval (eval_const _ _)) ⟨_, m1, rfl, hfr, hc⟩

section rets2

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

/-- `fe_mul` for field size 1 or 2, as a fact about a returned call. -/
theorem femul_small_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {F A B D : Word}
    (h : CalleeRet E s "fe_mul" [e1, e2, e3, e4] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word D))
    (h3 : E.eval s e3 = some (.word A)) (h4 : E.eval s e4 = some (.word B))
    (hF : F.toNat = 1 ∨ F.toNat = 2)
    (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 62) (bB : B.toNat + 32 * F.toNat ≤ 2 ^ 62)
    (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 62)
    (cA : CanonN s.memory A F.toNat) (cB : CanonN s.memory B F.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D F.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 661 hE.functions (by guest_decl_at 661) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases hF with hF | hF
  · have hFw : F = 1#64 := BitVec.eq_of_toNat_eq (by rw [hF]; rfl)
    subst hFw
    rcases fe_mul1_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A B D
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) bA bB bD cA cB hrun with hst | ⟨l', m', heq, hfr, hc⟩
    · exact absurd hst (fun h => h)
    · cases heq
      exact ⟨rfl, rfl, hfr, hc⟩
  · have hFw : F = 2#64 := BitVec.eq_of_toNat_eq (by rw [hF]; rfl)
    subst hFw
    rcases fe_mul2_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A B D
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) bA bB bD cA cB hrun with hst | ⟨l', m', heq, hfr, hc⟩
    · exact absurd hst (fun h => h)
    · cases heq
      exact ⟨rfl, rfl, hfr, hc⟩

end rets2

set_option maxHeartbeats 4000000 in
/-- `fe_sqr` for field size 1 or 2 is `fe_mul(fld, d, a, a)`. -/
theorem fe_sqr_small_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_sqr" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (F A D : Word)
    (hfld : s.locals "fld" = some (.word F))
    (ha : s.locals "a" = some (.word A)) (hd : s.locals "d" = some (.word D))
    (hF : F.toNat = 1 ∨ F.toNat = 2)
    (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 62) (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 62)
    (cA : CanonN s.memory A F.toNat) (h : Runs E s body r) :
    Stopped r ∨ FeRet s D F.toNat r := by
  have hbody := (fun_of_index 662 hE.functions (by guest_decl_at 662) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (FeRet s D F.toNat)) r h
  have hne : evalPanCmp .equal F 12#64 = 0#64 := by
    have : F ≠ 12#64 := by
      intro e
      rw [e] at hF
      revert hF
      decide
    simp [evalPanCmp, this]
  refine WPs.guard0 (fun x hx => by
    rw [eval_cmp_inv hE (of_eval (w := F) (by lk [hfld])) (of_eval (eval_const _ _)) x hx, hne])
    ?_
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hfr, hc⟩ := femul_small_ret hE hret (F := F) (A := A) (B := A) (D := D)
    (by lk [hfld]) (by lk [hd]) (by lk [ha]) (by lk [ha]) hF bA bA bD cA cA
  subst g ffi
  exact WPs.ret (of_eval (eval_const _ _)) ⟨_, m1, rfl, hfr, hc⟩

theorem fesqr_small_ret (hE : GuestEnv E) {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} {e1 e2 e3 : Exp Word} {F A D : Word}
    (h : CalleeRet E s "fe_sqr" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word D))
    (h3 : E.eval s e3 = some (.word A)) (hF : F.toNat = 1 ∨ F.toNat = 2)
    (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 62) (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 62)
    (cA : CanonN s.memory A F.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D F.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 662 hE.functions (by guest_decl_at 662) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_sqr_small_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ F A D
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hF bA bD cA hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

/-- `fe_mul(fld, d, a, b); rest` over `BufsK`, for field sizes 1, 2 and 12. -/
theorem WPs.fe_mul_stepK (hE : GuestEnv E) {eF eD eA eB : Exp Word} {rest : Prog Word}
    {F D A B hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K)
    (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (h1 : E.eval s eF = some (.word F)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A)) (h4 : E.eval s eB = some (.word B))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hA : A ∈ Cn) (hBc : B ∈ Cn)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_mul" [eF, eD, eA, eB]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gA := hB.geo A (hB.sub A hA)
  have gB := hB.geo B (hB.sub B hBc)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  by_cases h12 : K = 12
  · subst h12
    have hFw : F = 12#64 := BitVec.eq_of_toNat_eq (by rw [hF]; rfl)
    subst hFw
    obtain ⟨hg', hf, hfr, hc⟩ := femul_ret hE hret h1 h2 h3 h4 hg ⟨hB.hpb, hB.hpa⟩
      (by omega) (by omega) (by omega) gD.1 (hB.can A hA) (hB.can B hBc)
    subst g ffi
    exact h m1 (hB.write hD hDl (fun x hx hxD => hfr x hx (by omega)) hc)
  · have hF' : F.toNat = 1 ∨ F.toNat = 2 := by omega
    obtain ⟨hg', hf, hfr, hc⟩ := femul_small_ret hE hret h1 h2 h3 h4 hF' (by rw [hF]; omega)
      (by rw [hF]; omega) (by rw [hF]; omega) (by rw [hF]; exact hB.can A hA)
      (by rw [hF]; exact hB.can B hBc)
    subst g ffi
    rw [hF] at hfr hc
    exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

/-- `fe_sqr(fld, d, a); rest` over `BufsK`, for field sizes 1, 2 and 12. -/
theorem WPs.fe_sqr_stepK (hE : GuestEnv E) {eF eD eA : Exp Word} {rest : Prog Word}
    {F D A hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K)
    (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (h1 : E.eval s eF = some (.word F)) (h2 : E.eval s eD = some (.word D))
    (h3 : E.eval s eA = some (.word A))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hA : A ∈ Cn)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_sqr" [eF, eD, eA]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gA := hB.geo A (hB.sub A hA)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  by_cases h12 : K = 12
  · subst h12
    have hFw : F = 12#64 := BitVec.eq_of_toNat_eq (by rw [hF]; rfl)
    subst hFw
    obtain ⟨hg', hf, hfr, hc⟩ := fesqr_ret hE hret h1 h2 h3 hg ⟨hB.hpb, hB.hpa⟩
      (by omega) (by omega) gD.1 (hB.can A hA)
    subst g ffi
    exact h m1 (hB.write hD hDl (fun x hx hxD => hfr x hx (by omega)) hc)
  · have hF' : F.toNat = 1 ∨ F.toNat = 2 := by omega
    obtain ⟨hg', hf, hfr, hc⟩ := fesqr_small_ret hE hret h1 h2 h3 hF' (by rw [hF]; omega)
      (by rw [hF]; omega) (by rw [hF]; exact hB.can A hA)
    subst g ffi
    rw [hF] at hfr hc
    exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

end InitECandidate.Solver.GuestBound
