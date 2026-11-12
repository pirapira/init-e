import InitECandidate.Solver.GuestBound.Fq12Sqr

/-!
# Coefficientwise field operations keep coefficients below `p`

`fe_add`, `fe_sub`, `fe_neg`, `fe_mul_small` on `fld` coefficients: canonical
operands give a canonical result, and only the destination is written. The
destination may be one of the operands (the loops work in place). Part of the
canonicity chain for `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' : Word → Option (PanValue Word)}

/-- A store into coefficient `j` of `D` keeps `A` canonical when `D` is `A` or
disjoint from it. -/
theorem CanonN.store_alias {A D w0 w1 w2 w3 : Word} {n j : Nat}
    (hAD : D = A ∨ D.toNat + 32 * n ≤ A.toNat ∨ A.toNat + 32 * n ≤ D.toNat)
    (bA : A.toNat + 32 * n ≤ 2 ^ 64) (bD : D.toNat + 32 * n ≤ 2 ^ 64) (hj : j < n)
    (hc : CanonN m A n) (hv : limbsVal [w0, w1, w2, w3] < bnP) :
    CanonN (InitECandidate.Solver.GuestBound.set4 m (coefAddr D j) w0 w1 w2 w3) A n := by
  rcases hAD with rfl | h
  · exact hc.set4 bA hj hv
  · exact hc.frame bA (fun x h1 h2 => set4_outN (n := n) bD hj (by omega))

theorem fqneg_ret (hE : GuestEnv E) {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} {e1 : Exp Word} {a0 a1 a2 a3 : Word}
    (h : CalleeRet E s "fq_neg" [e1] vs g m ffi)
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ d0 d1 d2 d3 : Word,
      vs = [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] < bnP := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 651 hE.functions (by guest_decl_at 651) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq_neg_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    a0 a1 a2 a3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hA hrun with
    hst | ⟨l', d0, d1, d2, d3, heq, hd⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, d0, d1, d2, d3, rfl, hd⟩

/-- Invariant of the coefficient loops, relative to the entry state `s`. -/
def FeI (L : VarName → Option (PanValue Word)) (s : St σ) (A B D : Word) (n : Nat)
    (st : St σ) : Prop :=
  st.globals = s.globals ∧ st.ffi = s.ffi ∧ (∀ x, x ≠ "i" → st.locals x = L x) ∧
    (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * n ≤ x.toNat) → st.memory x = s.memory x) ∧
    CanonN st.memory A n ∧ CanonN st.memory B n ∧
    ∃ j, st.locals "i" = some (.word (BitVec.ofNat 64 j)) ∧ j ≤ n ∧ CanonN st.memory D j

set_option maxHeartbeats 8000000 in
theorem fe_add_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_add" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (F A B D : Word)
    (hfld : s.locals "fld" = some (.word F)) (ha : s.locals "a" = some (.word A))
    (hb : s.locals "b" = some (.word B)) (hd : s.locals "d" = some (.word D))
    (hF : F.toNat ≤ 12) (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hAD : D = A ∨ D.toNat + 32 * F.toNat ≤ A.toNat ∨ A.toNat + 32 * F.toNat ≤ D.toNat)
    (cA : CanonN s.memory A F.toNat) (bB : B.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hBD : D = B ∨ D.toNat + 32 * F.toNat ≤ B.toNat ∨ B.toNat + 32 * F.toNat ≤ D.toNat)
    (cB : CanonN s.memory B F.toNat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat := by
  have hbody := (fun_of_index 663 hE.functions (by guest_decl_at 663) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpp : 0 < bnP := by decide
  have hnat : ∀ n : Nat, n < 100 → (BitVec.ofNat 64 n : Word).toNat = n := by
    intro n hn
    rw [BitVec.toNat_ofNat]
    omega
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  obtain ⟨L, hL⟩ : ∃ L, L = updatePanValueMap s.locals "i" (.word 0#64) := ⟨_, rfl⟩
  rw [← hL]
  have La : L "a" = some (.word A) := by rw [hL]; lk [ha]
  have Ld : L "d" = some (.word D) := by rw [hL]; lk [hd]
  have Lf : L "fld" = some (.word F) := by rw [hL]; lk [hfld]
  have Lb : L "b" = some (.word B) := by rw [hL]; lk [hb]
  refine WPs.seqG (fun st => FeI L s A B D F.toNat st ∧ CanonN st.memory D F.toNat)
    (WPs.loopG (I := FeI L s A B D F.toNat)
      ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, cA, cB, 0, by rw [hL]; lk [], by omega,
        fun i => ⟨0, fun h => absurd h (Nat.not_lt_zero _)⟩⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, hfr, hcA, hcB, j, hj, hjn, hcD⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hloc hfr hcA hcB hj hcD
    subst ga fa
    have laf : la "fld" = some (.word F) := (hloc _ (by decide)).trans Lf
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := F) (by lk [laf])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hjlt : j < F.toNat := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 j : Word) < F := by
        rw [BitVec.lt_def, hnat j (by omega)]
        exact hge
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have laa : la "a" = some (.word A) := (hloc _ (by decide)).trans La
    have lad : la "d" = some (.word D) := (hloc _ (by decide)).trans Ld
    obtain ⟨va, hfa, hva⟩ := hcA.get (i := j) hjlt
    refine WPs.dec_load4 hE (addr := coefAddr A j)
      (of_eval (by unfold coefAddr; ev [evalPanOp, laa, hj])) hfa (fun a0 a1 a2 a3 hav => ?_)
    have lab : la "b" = some (.word B) := (hloc _ (by decide)).trans Lb
    obtain ⟨vb, hfb, hvb⟩ := hcB.get (i := j) hjlt
    refine WPs.dec_load4 hE (addr := coefAddr B j)
      (of_eval (by unfold coefAddr; ev [evalPanOp, lab, hj])) hfb (fun b0 b1 b2 b3 hbv => ?_)
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, d0, d1, d2, d3, hv, hd'⟩ := fqadd_ret hE hret (a0 := a0) (a1 := a1)
      (a2 := a2) (a3 := a3) (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
      (by lk []) (by lk []) (by rw [hav]; exact hva) (by rw [hbv]; exact hvb)
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hdl : limbsVal [d0, d1, d2, d3] < bnP := by rw [hd']; exact Nat.mod_lt _ hpp
    refine WPs.seq_store4 hE (addr := coefAddr D j) (w0 := d0) (w1 := d1) (w2 := d2) (w3 := d3)
      (of_eval (by unfold coefAddr; ev [evalPanOp, lad, hj])) (by lk []) ?_
    refine WPs.assign (old := BitVec.ofNat 64 j) (by lk [hj])
      (of_eval (w := BitVec.ofNat 64 (j + 1)) (by ev [hj, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨rfl, rfl, ?_, ?_, hcA.store_alias hAD (by omega) (by omega) hjlt hdl,
      hcB.store_alias hBD (by omega) (by omega) hjlt hdl, j + 1, ?_, by omega,
      CanonN.snoc (by omega) hcD hdl⟩
    · intro x hx
      refine Eq.trans ?_ (hloc x hx)
      show restorePanValueLocal _ _ _ x = la x
      by_cases h3 : x = "r"
      · subst h3
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h4 : x = "y"
      · subst h4
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h5 : x = "x"
      · subst h5
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, h3, h4, h5, hx]
    · intro x hx
      show set4 ma (coefAddr D j) d0 d1 d2 d3 x = s.memory x
      rw [set4_outN (n := F.toNat) (by omega) hjlt hx]
      exact hfr x hx
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hf, hloc, hfr, hcA, hcB, j, hj, hjn, hcD⟩ hcond
    simp only at hg hf hloc hfr hcA hcB hj hcD
    have laf : la "fld" = some (.word F) := (hloc _ (by decide)).trans Lf
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := F) (by lk [laf])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge : ¬ j < F.toNat := by
      intro hlt
      have hl : (BitVec.ofNat 64 j : Word) < F := by
        rw [BitVec.lt_def, hnat j (by omega)]
        exact hlt
      simp [evalPanCmp, hl] at hcv
    have : j = F.toNat := by omega
    subst this
    exact ⟨⟨hg, hf, hloc, hfr, hcA, hcB, _, hj, hjn, hcD⟩, hcD⟩
  · rintro ⟨la, ga, ma, fa⟩ ⟨⟨hg, hf, -, hfr, -⟩, hcD⟩
    simp only at hg hf hfr hcD
    subst ga fa
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, ma, rfl, hfr, hcD⟩

set_option maxHeartbeats 8000000 in
theorem fe_sub_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_sub" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (F A B D : Word)
    (hfld : s.locals "fld" = some (.word F)) (ha : s.locals "a" = some (.word A))
    (hb : s.locals "b" = some (.word B)) (hd : s.locals "d" = some (.word D))
    (hF : F.toNat ≤ 12) (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hAD : D = A ∨ D.toNat + 32 * F.toNat ≤ A.toNat ∨ A.toNat + 32 * F.toNat ≤ D.toNat)
    (cA : CanonN s.memory A F.toNat) (bB : B.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hBD : D = B ∨ D.toNat + 32 * F.toNat ≤ B.toNat ∨ B.toNat + 32 * F.toNat ≤ D.toNat)
    (cB : CanonN s.memory B F.toNat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat := by
  have hbody := (fun_of_index 664 hE.functions (by guest_decl_at 664) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpp : 0 < bnP := by decide
  have hnat : ∀ n : Nat, n < 100 → (BitVec.ofNat 64 n : Word).toNat = n := by
    intro n hn
    rw [BitVec.toNat_ofNat]
    omega
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  obtain ⟨L, hL⟩ : ∃ L, L = updatePanValueMap s.locals "i" (.word 0#64) := ⟨_, rfl⟩
  rw [← hL]
  have La : L "a" = some (.word A) := by rw [hL]; lk [ha]
  have Ld : L "d" = some (.word D) := by rw [hL]; lk [hd]
  have Lf : L "fld" = some (.word F) := by rw [hL]; lk [hfld]
  have Lb : L "b" = some (.word B) := by rw [hL]; lk [hb]
  refine WPs.seqG (fun st => FeI L s A B D F.toNat st ∧ CanonN st.memory D F.toNat)
    (WPs.loopG (I := FeI L s A B D F.toNat)
      ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, cA, cB, 0, by rw [hL]; lk [], by omega,
        fun i => ⟨0, fun h => absurd h (Nat.not_lt_zero _)⟩⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, hfr, hcA, hcB, j, hj, hjn, hcD⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hloc hfr hcA hcB hj hcD
    subst ga fa
    have laf : la "fld" = some (.word F) := (hloc _ (by decide)).trans Lf
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := F) (by lk [laf])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hjlt : j < F.toNat := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 j : Word) < F := by
        rw [BitVec.lt_def, hnat j (by omega)]
        exact hge
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have laa : la "a" = some (.word A) := (hloc _ (by decide)).trans La
    have lad : la "d" = some (.word D) := (hloc _ (by decide)).trans Ld
    obtain ⟨va, hfa, hva⟩ := hcA.get (i := j) hjlt
    refine WPs.dec_load4 hE (addr := coefAddr A j)
      (of_eval (by unfold coefAddr; ev [evalPanOp, laa, hj])) hfa (fun a0 a1 a2 a3 hav => ?_)
    have lab : la "b" = some (.word B) := (hloc _ (by decide)).trans Lb
    obtain ⟨vb, hfb, hvb⟩ := hcB.get (i := j) hjlt
    refine WPs.dec_load4 hE (addr := coefAddr B j)
      (of_eval (by unfold coefAddr; ev [evalPanOp, lab, hj])) hfb (fun b0 b1 b2 b3 hbv => ?_)
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, d0, d1, d2, d3, hv, hd'⟩ := fqsub_ret hE hret (a0 := a0) (a1 := a1)
      (a2 := a2) (a3 := a3) (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
      (by lk []) (by lk []) (by rw [hav]; exact hva) (by rw [hbv]; exact hvb)
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hdl : limbsVal [d0, d1, d2, d3] < bnP := by rw [hd']; exact Nat.mod_lt _ hpp
    refine WPs.seq_store4 hE (addr := coefAddr D j) (w0 := d0) (w1 := d1) (w2 := d2) (w3 := d3)
      (of_eval (by unfold coefAddr; ev [evalPanOp, lad, hj])) (by lk []) ?_
    refine WPs.assign (old := BitVec.ofNat 64 j) (by lk [hj])
      (of_eval (w := BitVec.ofNat 64 (j + 1)) (by ev [hj, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨rfl, rfl, ?_, ?_, hcA.store_alias hAD (by omega) (by omega) hjlt hdl,
      hcB.store_alias hBD (by omega) (by omega) hjlt hdl, j + 1, ?_, by omega,
      CanonN.snoc (by omega) hcD hdl⟩
    · intro x hx
      refine Eq.trans ?_ (hloc x hx)
      show restorePanValueLocal _ _ _ x = la x
      by_cases h3 : x = "r"
      · subst h3
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h4 : x = "y"
      · subst h4
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h5 : x = "x"
      · subst h5
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, h3, h4, h5, hx]
    · intro x hx
      show set4 ma (coefAddr D j) d0 d1 d2 d3 x = s.memory x
      rw [set4_outN (n := F.toNat) (by omega) hjlt hx]
      exact hfr x hx
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hf, hloc, hfr, hcA, hcB, j, hj, hjn, hcD⟩ hcond
    simp only at hg hf hloc hfr hcA hcB hj hcD
    have laf : la "fld" = some (.word F) := (hloc _ (by decide)).trans Lf
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := F) (by lk [laf])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge : ¬ j < F.toNat := by
      intro hlt
      have hl : (BitVec.ofNat 64 j : Word) < F := by
        rw [BitVec.lt_def, hnat j (by omega)]
        exact hlt
      simp [evalPanCmp, hl] at hcv
    have : j = F.toNat := by omega
    subst this
    exact ⟨⟨hg, hf, hloc, hfr, hcA, hcB, _, hj, hjn, hcD⟩, hcD⟩
  · rintro ⟨la, ga, ma, fa⟩ ⟨⟨hg, hf, -, hfr, -⟩, hcD⟩
    simp only at hg hf hfr hcD
    subst ga fa
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, ma, rfl, hfr, hcD⟩

set_option maxHeartbeats 8000000 in
theorem fe_neg_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_neg" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (F A D : Word)
    (hfld : s.locals "fld" = some (.word F)) (ha : s.locals "a" = some (.word A))
    (hd : s.locals "d" = some (.word D))
    (hF : F.toNat ≤ 12) (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hAD : D = A ∨ D.toNat + 32 * F.toNat ≤ A.toNat ∨ A.toNat + 32 * F.toNat ≤ D.toNat)
    (cA : CanonN s.memory A F.toNat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat := by
  have hbody := (fun_of_index 665 hE.functions (by guest_decl_at 665) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpp : 0 < bnP := by decide
  have hnat : ∀ n : Nat, n < 100 → (BitVec.ofNat 64 n : Word).toNat = n := by
    intro n hn
    rw [BitVec.toNat_ofNat]
    omega
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  obtain ⟨L, hL⟩ : ∃ L, L = updatePanValueMap s.locals "i" (.word 0#64) := ⟨_, rfl⟩
  rw [← hL]
  have La : L "a" = some (.word A) := by rw [hL]; lk [ha]
  have Ld : L "d" = some (.word D) := by rw [hL]; lk [hd]
  have Lf : L "fld" = some (.word F) := by rw [hL]; lk [hfld]
  refine WPs.seqG (fun st => FeI L s A A D F.toNat st ∧ CanonN st.memory D F.toNat)
    (WPs.loopG (I := FeI L s A A D F.toNat)
      ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, cA, cA, 0, by rw [hL]; lk [], by omega,
        fun i => ⟨0, fun h => absurd h (Nat.not_lt_zero _)⟩⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, hfr, hcA, hcB, j, hj, hjn, hcD⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hloc hfr hcA hcB hj hcD
    subst ga fa
    have laf : la "fld" = some (.word F) := (hloc _ (by decide)).trans Lf
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := F) (by lk [laf])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hjlt : j < F.toNat := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 j : Word) < F := by
        rw [BitVec.lt_def, hnat j (by omega)]
        exact hge
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have laa : la "a" = some (.word A) := (hloc _ (by decide)).trans La
    have lad : la "d" = some (.word D) := (hloc _ (by decide)).trans Ld
    obtain ⟨va, hfa, hva⟩ := hcA.get (i := j) hjlt
    refine WPs.dec_load4 hE (addr := coefAddr A j)
      (of_eval (by unfold coefAddr; ev [evalPanOp, laa, hj])) hfa (fun a0 a1 a2 a3 hav => ?_)
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, d0, d1, d2, d3, hv, hd'⟩ := fqneg_ret hE hret (a0 := a0) (a1 := a1)
      (a2 := a2) (a3 := a3) (by lk []) (by rw [hav]; exact hva)
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hdl : limbsVal [d0, d1, d2, d3] < bnP := hd'
    refine WPs.seq_store4 hE (addr := coefAddr D j) (w0 := d0) (w1 := d1) (w2 := d2) (w3 := d3)
      (of_eval (by unfold coefAddr; ev [evalPanOp, lad, hj])) (by lk []) ?_
    refine WPs.assign (old := BitVec.ofNat 64 j) (by lk [hj])
      (of_eval (w := BitVec.ofNat 64 (j + 1)) (by ev [hj, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨rfl, rfl, ?_, ?_, hcA.store_alias hAD (by omega) (by omega) hjlt hdl,
      hcB.store_alias hAD (by omega) (by omega) hjlt hdl, j + 1, ?_, by omega,
      CanonN.snoc (by omega) hcD hdl⟩
    · intro x hx
      refine Eq.trans ?_ (hloc x hx)
      show restorePanValueLocal _ _ _ x = la x
      by_cases h3 : x = "r"
      · subst h3
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h4 : x = "y"
      · subst h4
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h5 : x = "x"
      · subst h5
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, h3, h4, h5, hx]
    · intro x hx
      show set4 ma (coefAddr D j) d0 d1 d2 d3 x = s.memory x
      rw [set4_outN (n := F.toNat) (by omega) hjlt hx]
      exact hfr x hx
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hf, hloc, hfr, hcA, hcB, j, hj, hjn, hcD⟩ hcond
    simp only at hg hf hloc hfr hcA hcB hj hcD
    have laf : la "fld" = some (.word F) := (hloc _ (by decide)).trans Lf
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := F) (by lk [laf])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge : ¬ j < F.toNat := by
      intro hlt
      have hl : (BitVec.ofNat 64 j : Word) < F := by
        rw [BitVec.lt_def, hnat j (by omega)]
        exact hlt
      simp [evalPanCmp, hl] at hcv
    have : j = F.toNat := by omega
    subst this
    exact ⟨⟨hg, hf, hloc, hfr, hcA, hcB, _, hj, hjn, hcD⟩, hcD⟩
  · rintro ⟨la, ga, ma, fa⟩ ⟨⟨hg, hf, -, hfr, -⟩, hcD⟩
    simp only at hg hf hfr hcD
    subst ga fa
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, ma, rfl, hfr, hcD⟩

set_option maxHeartbeats 8000000 in
theorem fe_mul_small_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_mul_small" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (F A D K : Word)
    (hfld : s.locals "fld" = some (.word F)) (ha : s.locals "a" = some (.word A))
    (hd : s.locals "d" = some (.word D)) (hk : s.locals "k" = some (.word K))
    (hF : F.toNat ≤ 12) (bA : A.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (bD : D.toNat + 32 * F.toNat ≤ 2 ^ 63)
    (hAD : D = A ∨ D.toNat + 32 * F.toNat ≤ A.toNat ∨ A.toNat + 32 * F.toNat ≤ D.toNat)
    (cA : CanonN s.memory A F.toNat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat := by
  have hbody := (fun_of_index 666 hE.functions (by guest_decl_at 666) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpp : 0 < bnP := by decide
  have hnat : ∀ n : Nat, n < 100 → (BitVec.ofNat 64 n : Word).toNat = n := by
    intro n hn
    rw [BitVec.toNat_ofNat]
    omega
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 32 * F.toNat ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' D F.toNat)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  obtain ⟨L, hL⟩ : ∃ L, L = updatePanValueMap s.locals "i" (.word 0#64) := ⟨_, rfl⟩
  rw [← hL]
  have La : L "a" = some (.word A) := by rw [hL]; lk [ha]
  have Ld : L "d" = some (.word D) := by rw [hL]; lk [hd]
  have Lf : L "fld" = some (.word F) := by rw [hL]; lk [hfld]
  have Lk : L "k" = some (.word K) := by rw [hL]; lk [hk]
  refine WPs.seqG (fun st => FeI L s A A D F.toNat st ∧ CanonN st.memory D F.toNat)
    (WPs.loopG (I := FeI L s A A D F.toNat)
      ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, cA, cA, 0, by rw [hL]; lk [], by omega,
        fun i => ⟨0, fun h => absurd h (Nat.not_lt_zero _)⟩⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, hfr, hcA, hcB, j, hj, hjn, hcD⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hloc hfr hcA hcB hj hcD
    subst ga fa
    have laf : la "fld" = some (.word F) := (hloc _ (by decide)).trans Lf
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := F) (by lk [laf])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hjlt : j < F.toNat := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 j : Word) < F := by
        rw [BitVec.lt_def, hnat j (by omega)]
        exact hge
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have laa : la "a" = some (.word A) := (hloc _ (by decide)).trans La
    have lad : la "d" = some (.word D) := (hloc _ (by decide)).trans Ld
    have lak : la "k" = some (.word K) := (hloc _ (by decide)).trans Lk
    obtain ⟨va, hfa, hva⟩ := hcA.get (i := j) hjlt
    refine WPs.dec_load4 hE (addr := coefAddr A j)
      (of_eval (by unfold coefAddr; ev [evalPanOp, laa, hj])) hfa (fun a0 a1 a2 a3 hav => ?_)
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, d0, d1, d2, d3, hv, hd'⟩ := mulsmall_ret hE hret (a0 := a0) (a1 := a1)
      (a2 := a2) (a3 := a3) (k := K) (by lk []) (by lk [lak])
      (by rw [hav]; exact hva)
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hdl : limbsVal [d0, d1, d2, d3] < bnP := hd'
    refine WPs.seq_store4 hE (addr := coefAddr D j) (w0 := d0) (w1 := d1) (w2 := d2) (w3 := d3)
      (of_eval (by unfold coefAddr; ev [evalPanOp, lad, hj])) (by lk []) ?_
    refine WPs.assign (old := BitVec.ofNat 64 j) (by lk [hj])
      (of_eval (w := BitVec.ofNat 64 (j + 1)) (by ev [hj, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨rfl, rfl, ?_, ?_, hcA.store_alias hAD (by omega) (by omega) hjlt hdl,
      hcB.store_alias hAD (by omega) (by omega) hjlt hdl, j + 1, ?_, by omega,
      CanonN.snoc (by omega) hcD hdl⟩
    · intro x hx
      refine Eq.trans ?_ (hloc x hx)
      show restorePanValueLocal _ _ _ x = la x
      by_cases h3 : x = "r"
      · subst h3
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h4 : x = "y"
      · subst h4
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h5 : x = "x"
      · subst h5
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, h3, h4, h5, hx]
    · intro x hx
      show set4 ma (coefAddr D j) d0 d1 d2 d3 x = s.memory x
      rw [set4_outN (n := F.toNat) (by omega) hjlt hx]
      exact hfr x hx
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hf, hloc, hfr, hcA, hcB, j, hj, hjn, hcD⟩ hcond
    simp only at hg hf hloc hfr hcA hcB hj hcD
    have laf : la "fld" = some (.word F) := (hloc _ (by decide)).trans Lf
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := F) (by lk [laf])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge : ¬ j < F.toNat := by
      intro hlt
      have hl : (BitVec.ofNat 64 j : Word) < F := by
        rw [BitVec.lt_def, hnat j (by omega)]
        exact hlt
      simp [evalPanCmp, hl] at hcv
    have : j = F.toNat := by omega
    subst this
    exact ⟨⟨hg, hf, hloc, hfr, hcA, hcB, _, hj, hjn, hcD⟩, hcD⟩
  · rintro ⟨la, ga, ma, fa⟩ ⟨⟨hg, hf, -, hfr, -⟩, hcD⟩
    simp only at hg hf hfr hcD
    subst ga fa
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, ma, rfl, hfr, hcD⟩

end InitECandidate.Solver.GuestBound
