import InitECandidate.Solver.GuestBound.FqSmall

/-!
# `fq12_reduce` keeps coefficients below `p`

The 23 product coefficients at `t` stay canonical, and only that buffer is
written. Part of the canonicity chain for `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' : Word → Option (PanValue Word)}

/-- The `n` coefficients at `A` are field elements below `p`. -/
def CanonN (m : Word → Option (PanValue Word)) (A : Word) (n : Nat) : Prop :=
  ∀ i, ∃ v, i < n → Fe m (coefAddr A i) v ∧ v < bnP

theorem CanonN.get {A : Word} {n i : Nat} (h : CanonN m A n) (hi : i < n) :
    ∃ v, Fe m (coefAddr A i) v ∧ v < bnP := by
  obtain ⟨v, hv⟩ := h i
  exact ⟨v, hv hi⟩

theorem set4_outN {A x w0 w1 w2 w3 : Word} {n k : Nat} (h64 : A.toNat + 32 * n ≤ 2 ^ 64)
    (hk : k < n) (hx : x.toNat < A.toNat ∨ A.toNat + 32 * n ≤ x.toNat) :
    set4 m (coefAddr A k) w0 w1 w2 w3 x = m x := by
  have hck := coefAddr_toNat (a := A) (i := k) (by omega)
  refine set4_other (by rw [hck]; omega) ?_
  rw [hck]
  omega

theorem CanonN.set4 {A w0 w1 w2 w3 : Word} {n k : Nat} (h64 : A.toNat + 32 * n ≤ 2 ^ 64)
    (hk : k < n) (hc : CanonN m A n) (hv : limbsVal [w0, w1, w2, w3] < bnP) :
    CanonN (set4 m (coefAddr A k) w0 w1 w2 w3) A n := by
  have hck := coefAddr_toNat (a := A) (i := k) (by omega)
  have hb : (coefAddr A k).toNat + 32 ≤ 2 ^ 64 := by rw [hck]; omega
  intro i
  by_cases hi : i = k
  · subst hi
    exact ⟨_, fun _ => ⟨fe_set4 hb, hv⟩⟩
  · obtain ⟨v, hv'⟩ := hc i
    refine ⟨v, fun hin => ⟨fe_congr (by rw [coefAddr_toNat (by omega)]; omega)
      (fun x h1 h2 => set4_other hb ?_) (hv' hin).1, (hv' hin).2⟩⟩
    rw [coefAddr_toNat (by omega)] at h1 h2
    rw [hck]
    omega

/-- `x = f(args); rest` for a local `x`. -/
theorem WPs.seq_callA_ret {f : FunName} {args : List (Exp Word)} {x : VarName} {q : Prog Word}
    (h : ∀ v g m ffi, CalleeRet E s f args [v] g m ffi →
      WPs E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ q Q) :
    WPs E s (.seq (.call (some (some (.local, x), none)) f args) q) Q :=
  WPs.seq (fun st => ∃ v g m ffi, CalleeRet E s f args [v] g m ffi ∧
      st = ⟨updatePanValueMap s.locals x v, g, m, ffi⟩)
    (WPs.callA_ret (fun v g m ffi hr => ⟨_, _, _, _, rfl, v, g, m, ffi, hr, rfl⟩))
    (by rintro _ ⟨v, g, m, ffi, hr, rfl⟩; exact h v g m ffi hr)

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem fqsub_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : CalleeRet E s "fq_sub" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (h2 : E.eval s e2 = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) (hB : limbsVal [b0, b1, b2, b3] < bnP) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ d0 d1 d2 d3 : Word,
      vs = [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] =
        (limbsVal [a0, a1, a2, a3] + bnP - limbsVal [b0, b1, b2, b3]) % bnP := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 650 hE.functions (by guest_decl_at 650) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq_sub_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hA hB hrun with
    hst | ⟨l', d0, d1, d2, d3, heq, hd⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, d0, d1, d2, d3, rfl, hd⟩

theorem mulsmall_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {a0 a1 a2 a3 k : Word}
    (h : CalleeRet E s "fq_mul_small" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (h2 : E.eval s e2 = some (.word k)) (hA : limbsVal [a0, a1, a2, a3] < bnP) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ d0 d1 d2 d3 : Word,
      vs = [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] < bnP := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 656 hE.functions (by guest_decl_at 656) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq_mul_small_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    a0 a1 a2 a3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hA hrun with
    hst | ⟨l', d0, d1, d2, d3, heq, hd⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, d0, d1, d2, d3, rfl, hd⟩

end rets

/-- Invariant of the loop of `fq12_reduce`. -/
def ReduceI (s : St σ) (T : Word) (st : St σ) : Prop :=
  st.globals = s.globals ∧ st.ffi = s.ffi ∧ st.locals "t" = some (.word T) ∧
    (∃ j, st.locals "e" = some (.word (BitVec.ofNat 64 j)) ∧ j ≤ 11) ∧
    (∀ x : Word, (x.toNat < T.toNat ∨ T.toNat + 736 ≤ x.toNat) → st.memory x = s.memory x) ∧
    CanonN st.memory T 23

set_option maxHeartbeats 8000000 in
theorem fq12_reduce_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq12_reduce" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (T : Word) (ht : s.locals "t" = some (.word T))
    (h64 : T.toNat + 736 ≤ 2 ^ 63) (hc : CanonN s.memory T 23) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < T.toNat ∨ T.toNat + 736 ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' T 23 := by
  have hbody := (fun_of_index 658 hE.functions (by guest_decl_at 658) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpp : 0 < bnP := by decide
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, (x.toNat < T.toNat ∨ T.toNat + 736 ≤ x.toNat) → m' x = s.memory x) ∧
      CanonN m' T 23)) r h
  refine WPs.dec (w := 11#64) (of_eval (eval_const _ _)) ?_
  refine WPs.seqG (ReduceI s T) (WPs.loopG (I := ReduceI s T)
    ⟨rfl, rfl, by lk [ht], ⟨11, by lk [], by omega⟩, fun _ _ => rfl, hc⟩ ?_
    (fun a k hI _ => hI)) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hlt, ⟨j, hj, hj11⟩, hfr, hca⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hlt hj hfr hca
    subst hg hf
    have hjt : (BitVec.ofNat 64 j : Word).toNat = j := by
      rw [BitVec.toNat_ofNat]
      omega
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := 0#64) (eval_const _ _))
      (of_eval (w := BitVec.ofNat 64 j) (by lk [hj])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hj1 : 1 ≤ j := by
      by_contra hlt0
      have hl : ¬ (0#64 : Word) < BitVec.ofNat 64 j := by
        rw [BitVec.lt_def, hjt]
        simp
        omega
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk12 : (BitVec.ofNat 64 k : Word) + 12#64 = BitVec.ofNat 64 (k + 12) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hk6 : (BitVec.ofNat 64 k : Word) + 6#64 = BitVec.ofNat 64 (k + 6) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have hpred : (BitVec.ofNat 64 (k + 1) : Word) - 1#64 = BitVec.ofNat 64 k := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
      omega
    refine WPs.seq_assign (old := BitVec.ofNat 64 (k + 1)) (w := BitVec.ofNat 64 k) hj
      (of_eval (by ev [hj, hpred])) ?_
    obtain ⟨vt, hft, hvt⟩ := hca.get (i := k + 12) (by omega)
    refine WPs.dec_load4 hE (addr := coefAddr T (k + 12))
      (of_eval (by unfold coefAddr; ev [evalPanOp, hlt, hk12])) hft (fun t0 t1 t2 t3 htv => ?_)
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, x0, x1, x2, x3, hv, hx⟩ := mulsmall_ret hE hret (a0 := t0) (a1 := t1)
      (a2 := t2) (a3 := t3) (k := 82#64) (by lk []) (eval_const _ _) (by rw [htv]; exact hvt)
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, y0, y1, y2, y3, hv, hy⟩ := mulsmall_ret hE hret (a0 := t0) (a1 := t1)
      (a2 := t2) (a3 := t3) (k := 18#64) (by lk []) (eval_const _ _) (by rw [htv]; exact hvt)
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    obtain ⟨v0, hf0, hv0⟩ := hca.get (i := k) (by omega)
    refine WPs.dec_load4 hE (addr := coefAddr T k)
      (of_eval (by unfold coefAddr; ev [evalPanOp, hlt])) hf0 (fun c0 c1 c2 c3 hcv0 => ?_)
    refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, d0, d1, d2, d3, hv, hd⟩ := fqsub_ret hE hret (a0 := c0) (a1 := c1)
      (a2 := c2) (a3 := c3) (b0 := x0) (b1 := x1) (b2 := x2) (b3 := x3) (by lk []) (by lk [])
      (by rw [hcv0]; exact hv0) hx
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hdl : limbsVal [d0, d1, d2, d3] < bnP := by rw [hd]; exact Nat.mod_lt _ hpp
    refine WPs.seq_store4 hE (addr := coefAddr T k) (w0 := d0) (w1 := d1) (w2 := d2) (w3 := d3)
      (of_eval (by unfold coefAddr; ev [evalPanOp, hlt])) (by lk []) ?_
    have hca1 : CanonN (set4 ma (coefAddr T k) d0 d1 d2 d3) T 23 :=
      hca.set4 (by omega) (by omega) hdl
    obtain ⟨v6, hf6, hv6⟩ := hca1.get (i := k + 6) (by omega)
    refine WPs.dec_load4 hE (addr := coefAddr T (k + 6))
      (of_eval (by unfold coefAddr; ev [evalPanOp, hlt, hk6])) hf6 (fun s0 s1 s2 s3 hsv => ?_)
    refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, z0, z1, z2, z3, hv, hz⟩ := fqadd_ret hE hret (a0 := s0) (a1 := s1)
      (a2 := s2) (a3 := s3) (b0 := y0) (b1 := y1) (b2 := y2) (b3 := y3) (by lk []) (by lk [])
      (by rw [hsv]; exact hv6) hy
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hzl : limbsVal [z0, z1, z2, z3] < bnP := by rw [hz]; exact Nat.mod_lt _ hpp
    refine WPs.store4 hE (addr := coefAddr T (k + 6)) (w0 := z0) (w1 := z1) (w2 := z2)
      (w3 := z3) (of_eval (by unfold coefAddr; ev [evalPanOp, hlt, hk6])) (by lk []) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨rfl, rfl, ?_, ⟨k, ?_, by omega⟩, ?_, hca1.set4 (by omega) (by omega) hzl⟩
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hlt]
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
    · intro x hx
      show set4 (set4 ma _ _ _ _ _) _ _ _ _ _ x = _
      rw [set4_outN (n := 23) (by omega) (by omega) (by omega),
        set4_outN (n := 23) (by omega) (by omega) (by omega)]
      exact hfr x hx
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hlt, -, hfr, hca⟩
    simp only at hg hf hfr hca
    subst hg hf
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, ma, rfl, hfr, hca⟩

end InitECandidate.Solver.GuestBound
