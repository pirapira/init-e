import InitECandidate.Solver.GuestBound.Fq12Mul

/-!
# `fq12_sqr` keeps coefficients below `p`

Same statement as for `fq12_mul`, with one operand. Part of the canonicity
chain for `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' : Word → Option (PanValue Word)}

theorem lsr1 {kk : Nat} (h : kk < 100) :
    RiscV.panRiscVShift .lsr (BitVec.ofNat 64 kk : Word) 1#64 =
      some (BitVec.ofNat 64 (kk / 2)) := by
  unfold RiscV.panRiscVShift
  rw [if_pos (by decide)]
  simp only [Option.some.injEq]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.reducePow, Nat.reduceMod, Nat.pow_one]
  omega

/-- Invariant of the inner loop of `fq12_sqr`, relative to its entry state. -/
def SqrInI (a : St σ) (kk : Nat) (st : St σ) : Prop :=
  st.globals = a.globals ∧ st.memory = a.memory ∧ st.ffi = a.ffi ∧
    (∀ x, x ≠ "i" → x ≠ "acc" → st.locals x = a.locals x) ∧
    (∃ ii, st.locals "i" = some (.word (BitVec.ofNat 64 ii)) ∧ kk ≤ ii + 11 ∧ ii ≤ kk) ∧
    ∃ c0 c1 c2 c3 : Word, st.locals "acc" = some (.rStruct [.word c0, .word c1, .word c2,
      .word c3]) ∧ limbsVal [c0, c1, c2, c3] < bnP

set_option maxHeartbeats 8000000 in
theorem sqr_inner (hE : GuestEnv E) {a : St σ} {A : Word} {kk ii0 : Nat} {c0 c1 c2 c3 : Word}
    (hA : a.locals "a" = some (.word A))
    (hk : a.locals "k" = some (.word (BitVec.ofNat 64 kk)))
    (hi : a.locals "i" = some (.word (BitVec.ofNat 64 ii0)))
    (hacc : a.locals "acc" = some (.rStruct [.word c0, .word c1, .word c2, .word c3]))
    (hcl : limbsVal [c0, c1, c2, c3] < bnP)
    (hkk : kk < 23) (h1 : kk ≤ ii0 + 11) (h2 : ii0 ≤ kk)
    (bA : A.toNat + 384 ≤ 2 ^ 63) (cA : CanonN a.memory A 12) :
    WPs E a FQS_INNER (fun r => ∃ l, r = .normal l a.globals a.memory a.ffi ∧
      SqrInI a kk ⟨l, a.globals, a.memory, a.ffi⟩) := by
  have hpp : 0 < bnP := by decide
  have hnat : ∀ n : Nat, n < 100 → (BitVec.ofNat 64 n : Word).toNat = n := by
    intro n hn
    rw [BitVec.toNat_ofNat]
    omega
  refine WPs.loopG (I := SqrInI a kk)
    ⟨rfl, rfl, rfl, fun _ _ _ => rfl, ⟨ii0, hi, h1, h2⟩, c0, c1, c2, c3, hacc, hcl⟩ ?_ ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, hloc, ⟨ii, hii, k1, k2⟩, d0, d1, d2, d3, hac, hdl⟩
      ⟨w, cc, hcond, hw⟩
    simp only at hg hm hf hloc hii hac
    subst ga ma fa
    have hla : la "a" = some (.word A) := (hloc _ (by decide) (by decide)).trans hA
    have hlk : la "k" = some (.word (BitVec.ofNat 64 kk)) :=
      (hloc _ (by decide) (by decide)).trans hk
    have hsub : (BitVec.ofNat 64 kk : Word) - BitVec.ofNat 64 ii = BitVec.ofNat 64 (kk - ii) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, hnat kk (by omega), hnat ii (by omega), hnat (kk - ii) (by omega)]
      omega
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 ii)
      (by lk [hii])) (of_eval (w := BitVec.ofNat 64 (kk - ii)) (by ev [hlk, hii, hsub])) _
      (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hilt : ii < kk - ii := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 ii : Word) < BitVec.ofNat 64 (kk - ii) := by
        rw [BitVec.lt_def, hnat ii (by omega), hnat (kk - ii) (by omega)]
        exact hge
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    obtain ⟨va, hfa, hva⟩ := cA.get (i := ii) (by omega)
    obtain ⟨vb, hfb, hvb⟩ := cA.get (i := kk - ii) (by omega)
    refine WPs.dec_load4 hE (addr := coefAddr A ii)
      (of_eval (by unfold coefAddr; ev [evalPanOp, hla, hii])) hfa (fun a0 a1 a2 a3 hav => ?_)
    refine WPs.dec_load4 hE (addr := coefAddr A (kk - ii))
      (of_eval (by unfold coefAddr; ev [evalPanOp, hla, hlk, hii, hsub])) hfb
      (fun b0 b1 b2 b3 hbv => ?_)
    refine WPs.decCall_fqmul hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b0 := b0) (b1 := b1)
      (b2 := b2) (b3 := b3) (by lk []) (by lk []) (by rw [hav]; exact hva)
      (by rw [hbv]; exact hvb) (fun p0 p1 p2 p3 hplt _ => ?_)
    refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, e0, e1, e2, e3, hv, he⟩ := fqadd_ret hE hret (a0 := d0) (a1 := d1)
      (a2 := d2) (a3 := d3) (b0 := p0) (b1 := p1) (b2 := p2) (b3 := p3) (by lk [hac]) (by lk [])
      hdl hplt
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    refine WPs.assign (old := BitVec.ofNat 64 ii) (by lk [hii])
      (of_eval (w := BitVec.ofNat 64 (ii + 1)) (by ev [hii, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨rfl, rfl, rfl, ?_, ⟨ii + 1, ?_, by omega, by omega⟩, e0, e1, e2, e3, ?_,
      by rw [he]; exact Nat.mod_lt _ hpp⟩
    · intro x hx1 hx2
      refine Eq.trans ?_ (hloc x hx1 hx2)
      show restorePanValueLocal _ _ _ x = la x
      by_cases h3 : x = "p"
      · subst h3
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h4 : x = "aj"
      · subst h4
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h5 : x = "ai"
      · subst h5
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, h3, h4, h5, hx1,
        hx2]
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hm, hf, rest⟩ -
    simp only at hg hm hf
    subst ga ma fa
    exact ⟨la, rfl, rfl, rfl, rfl, rest⟩

set_option maxHeartbeats 16000000 in
theorem fq12_sqr_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq12_sqr" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A D pv : Word)
    (ha : s.locals "a" = some (.word A)) (hd : s.locals "d" = some (.word D))
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (bA : A.toNat + 384 ≤ pv.toNat) (bD : D.toNat + 384 ≤ pv.toNat) (alD : D.toNat % 8 = 0)
    (cA : CanonN s.memory A 12) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, x.toNat < pv.toNat → (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) →
        m' x = s.memory x) ∧ CanonN m' D 12 := by
  have hbody := (fun_of_index 660 hE.functions (by guest_decl_at 660) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpp : 0 < bnP := by decide
  have hpH' := hpH
  unfold InHeap at hpH'
  have h384 : (384#64 : Word).toNat = 384 := by decide
  have hnat : ∀ n : Nat, n < 100 → (BitVec.ofNat 64 n : Word).toNat = n := by
    intro n hn
    rw [BitVec.toNat_ofNat]
    omega
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, x.toNat < pv.toNat → (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) →
        m' x = s.memory x) ∧ CanonN m' D 12)) r h
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, hv⟩ := heap_mark_ret hE hret hp
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hv, hm, hf, qv, hg, hq1, hq2⟩ := alloc_ret hE hret (nv := 23#64 * 32#64)
    (by ev [evalPanOp]) hp hpH
  simp only [List.cons.injEq, and_true] at hv
  subst v m ffi g
  rw [show (23#64 * 32#64 : Word).toNat = 736 by decide] at hq1
  unfold InHeap at hq2
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 = updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals
      "mark" (.word pv)) "t" (.word pv)) "k" (.word 0#64) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = updatePanValueMap s.globals "heap_ptr" (.word qv) := ⟨_, rfl⟩
  rw [← hL0, ← hG]
  have La : L0 "a" = some (.word A) := by rw [hL0]; lk [ha]
  have Ld : L0 "d" = some (.word D) := by rw [hL0]; lk [hd]
  have Lt : L0 "t" = some (.word pv) := by rw [hL0]; lk []
  have Lm : L0 "mark" = some (.word pv) := by rw [hL0]; lk []
  have hGs : updatePanValueMap G "heap_ptr" (.word pv) = s.globals := by
    rw [hG]
    funext y
    simp only [update_lookup]
    split
    · rename_i hy
      have : y = "heap_ptr" := by simpa using hy
      rw [this, hp]
    · rfl
  refine WPs.seqG (fun st => MulOutI L0 G s.ffi s.memory pv st ∧ CanonN st.memory pv 23)
    (WPs.loopG (I := MulOutI L0 G s.ffi s.memory pv)
      ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, 0, by rw [hL0]; lk [], by omega,
        fun i => ⟨0, fun h => absurd h (Nat.not_lt_zero _)⟩⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, hlow, kk, hkk, hk23, hct⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hloc hlow hkk hct
    subst ga fa
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 kk) (by lk [hkk]))
      (of_eval (w := 23#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hklt : kk < 23 := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 kk : Word) < 23#64 := by
        rw [BitVec.lt_def, hnat kk (by omega)]
        have : (23#64 : Word).toNat = 23 := by decide
        omega
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have lat : la "t" = some (.word pv) := (hloc _ (by decide)).trans Lt
    have laa : la "a" = some (.word A) := (hloc _ (by decide)).trans La
    have cAa : CanonN ma A 12 := cA.frame (by omega) (fun x h1 h2 => hlow x (by omega))
    refine WPs.dec_val (v := .rStruct [.word 0#64, .word 0#64, .word 0#64, .word 0#64])
      (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) ?_
    refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
    have hl11 := lower11 (kk := kk) (by omega)
    refine WPs.seq_ite_assign (old := 0#64) (w := BitVec.ofNat 64 (kk - 11))
      (wc := evalPanCmp .lower (11#64 : Word) (BitVec.ofNat 64 kk)) (by lk [])
      (eval_cmp_inv hE (of_eval (eval_const _ _)) (of_eval (by lk [hkk]))) ?_ ?_ ?_
    · intro hne
      have h11 : 11 < kk := by
        by_contra hn
        rw [hl11, if_neg hn] at hne
        exact hne rfl
      have hsub : (BitVec.ofNat 64 kk : Word) - 11#64 = BitVec.ofNat 64 (kk - 11) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, hnat kk (by omega), hnat (kk - 11) (by omega)]
        have : (11#64 : Word).toNat = 11 := by decide
        omega
      exact of_eval (by ev [hkk, hsub])
    · intro h0
      have h11 : ¬ 11 < kk := by
        intro hn
        rw [hl11, if_pos hn] at h0
        exact absurd h0 (by decide)
      have : kk - 11 = 0 := by omega
      rw [this]
    -- the inner loop
    refine WPs.seq (fun st => st.globals = G ∧ st.memory = ma ∧ st.ffi = s.ffi ∧
        (∀ x, x ≠ "i" → x ≠ "acc" → st.locals x = la x) ∧
        ∃ c0 c1 c2 c3 : Word, st.locals "acc" = some (.rStruct [.word c0, .word c1, .word c2,
          .word c3]) ∧ limbsVal [c0, c1, c2, c3] < bnP)
      (WPs.conseq (sqr_inner hE (A := A) (kk := kk) (ii0 := kk - 11)
        (c0 := 0#64) (c1 := 0#64) (c2 := 0#64) (c3 := 0#64) (by lk [laa]) (by lk [hkk])
        (by lk []) (by lk []) (by decide) hklt (by omega) (by omega) (by omega) cAa) ?_) ?_
    · rintro r ⟨l, rfl, -, -, -, hloc', -, c0, c1, c2, c3, hacc', hc'⟩
      refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, fun x h1 h2 => (hloc' x h1 h2).trans ?_,
        c0, c1, c2, c3, hacc', hc'⟩
      simp [update_lookup, h1, h2]
    rintro ⟨l3, g3, m3, f3⟩ ⟨hg, hm, hf, hloc3, e0, e1, e2, e3, hacc3, hc3⟩
    simp only at hg hm hf hloc3 hacc3
    subst g3 m3 f3
    -- acc = fq_add(acc, acc)
    refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, u0, u1, u2, u3, hv, hu⟩ := fqadd_ret hE hret (a0 := e0) (a1 := e1)
      (a2 := e2) (a3 := e3) (b0 := e0) (b1 := e1) (b2 := e2) (b3 := e3) (by lk [hacc3])
      (by lk [hacc3]) hc3 hc3
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hul : limbsVal [u0, u1, u2, u3] < bnP := by rw [hu]; exact Nat.mod_lt _ hpp
    have l3a : l3 "a" = some (.word A) := (hloc3 _ (by decide) (by decide)).trans laa
    have l3t : l3 "t" = some (.word pv) := (hloc3 _ (by decide) (by decide)).trans lat
    have l3k : l3 "k" = some (.word (BitVec.ofNat 64 kk)) :=
      (hloc3 _ (by decide) (by decide)).trans hkk
    -- the middle term for even k
    refine WPs.seq (fun st => st.globals = G ∧ st.memory = ma ∧ st.ffi = s.ffi ∧
        (∀ x, x ≠ "i" → x ≠ "acc" → st.locals x = la x) ∧
        ∃ c0 c1 c2 c3 : Word, st.locals "acc" = some (.rStruct [.word c0, .word c1, .word c2,
          .word c3]) ∧ limbsVal [c0, c1, c2, c3] < bnP)
      (WPs.ite_both (fun w _ => ?_)) ?_
    · split
      · refine WPs.skip ⟨_, _, _, _, rfl, rfl, rfl, rfl, fun x h1 h2 => ?_, u0, u1, u2, u3,
          by lk [], hul⟩
        show updatePanValueMap l3 "acc" _ x = la x
        rw [update_lookup, if_neg (by simpa using h2)]
        exact hloc3 x h1 h2
      · obtain ⟨vm, hfm, hvm⟩ := cAa.get (i := kk / 2) (by omega)
        refine WPs.dec_load4 hE (addr := coefAddr A (kk / 2))
          (of_eval (by
            unfold coefAddr
            simp (config := { decide := true }) [evalF_op hE.word, evalF_panOp, evalArgs_cons,
              evalArgs_nil, evalF_local, update_lookup, wordsProj_cons, wordsProj_nil, wordOp,
              evalPanOp, evalF_shift hE.word, l3a, l3k, lsr1 (show kk < 100 by omega)])) hfm
          (fun a0 a1 a2 a3 hav => ?_)
        refine WPs.decCall_fqmul hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b0 := a0)
          (b1 := a1) (b2 := a2) (b3 := a3) (by lk []) (by lk []) (by rw [hav]; exact hvm)
          (by rw [hav]; exact hvm) (fun p0 p1 p2 p3 hplt _ => ?_)
        refine WPs.callA_ret (fun v g m ffi hret => ?_)
        obtain ⟨hg, hm, hf, y0, y1, y2, y3, hv, hy⟩ := fqadd_ret hE hret (a0 := u0) (a1 := u1)
          (a2 := u2) (a3 := u3) (b0 := p0) (b1 := p1) (b2 := p2) (b3 := p3) (by lk []) (by lk [])
          hul hplt
        simp only [List.cons.injEq, and_true] at hv
        subst g m ffi v
        simp only [restorePanValueFfiLocal]
        refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, fun x h1 h2 => ?_, y0, y1, y2, y3, ?_,
          by rw [hy]; exact Nat.mod_lt _ hpp⟩
        · refine Eq.trans ?_ (hloc3 x h1 h2)
          show restorePanValueLocal _ _ _ x = l3 x
          by_cases h3 : x = "sq"
          · subst h3
            simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
          by_cases h4 : x = "am"
          · subst h4
            simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
          simp (config := { decide := true }) [restorePanValueLocal, update_lookup, h3, h4, h1,
            h2]
        · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
    rintro ⟨l4, g4, m4, f4⟩ ⟨hg, hm, hf, hloc4, z0, z1, z2, z3, hacc4, hc4⟩
    simp only at hg hm hf hloc4 hacc4
    subst g4 m4 f4
    have l4t : l4 "t" = some (.word pv) := (hloc4 _ (by decide) (by decide)).trans lat
    have l4k : l4 "k" = some (.word (BitVec.ofNat 64 kk)) :=
      (hloc4 _ (by decide) (by decide)).trans hkk
    refine WPs.seq_store4 hE (addr := coefAddr pv kk) (w0 := z0) (w1 := z1) (w2 := z2) (w3 := z3)
      (of_eval (by unfold coefAddr; ev [evalPanOp, l4t, l4k])) (by lk [hacc4]) ?_
    refine WPs.assign (old := BitVec.ofNat 64 kk) (by lk [l4k])
      (of_eval (w := BitVec.ofNat 64 (kk + 1)) (by ev [l4k, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨rfl, rfl, ?_, ?_, kk + 1, ?_, by omega, CanonN.snoc (by omega) hct hc4⟩
    · intro x hx
      refine Eq.trans ?_ (hloc x hx)
      show restorePanValueLocal _ _ _ x = la x
      by_cases h4 : x = "i"
      · subst h4
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h5 : x = "acc"
      · subst h5
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, h4, h5, hx]
      exact hloc4 x h4 h5
    · intro x hx
      show set4 ma (coefAddr pv kk) z0 z1 z2 z3 x = s.memory x
      rw [set4_outN (n := 23) (by omega) (by omega) (Or.inl hx)]
      exact hlow x hx
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hf, hloc, hlow, kk, hkk, hk23, hct⟩ hcond
    simp only at hg hf hloc hlow hkk hct
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 kk) (by lk [hkk]))
      (of_eval (w := 23#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge : ¬ kk < 23 := by
      intro hlt
      have hl : (BitVec.ofNat 64 kk : Word) < 23#64 := by
        rw [BitVec.lt_def, hnat kk (by omega)]
        have : (23#64 : Word).toNat = 23 := by decide
        omega
      simp [evalPanCmp, hl] at hcv
    have : kk = 23 := by omega
    subst this
    exact ⟨⟨hg, hf, hloc, hlow, 23, hkk, hk23, hct⟩, hct⟩
  · rintro ⟨la, ga, ma, fa⟩ ⟨⟨hg, hf, hloc, hlow, -⟩, hct⟩
    simp only at hg hf hloc hlow hct
    subst ga fa
    have lat : la "t" = some (.word pv) := (hloc _ (by decide)).trans Lt
    have lad : la "d" = some (.word D) := (hloc _ (by decide)).trans Ld
    have lam : la "mark" = some (.word pv) := (hloc _ (by decide)).trans Lm
    refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
    obtain ⟨hg, hf, hfr1, hc1⟩ := reduce_ret hE hret (T := pv) (by lk [lat]) (by omega) hct
    subst g ffi
    refine WPs.seq_call_ret (fun vs g m2 ffi hret => ?_)
    obtain ⟨hg, hf, hcopy⟩ := memcpy_ret hE hret (dst := D) (src := pv) (nW := 384#64)
      (by lk [lad]) (by lk [lat]) (eval_const _ _)
      ⟨by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega⟩
    subst g ffi
    rw [h384] at hcopy
    refine WPs.seq_call_ret (fun vs g m3 ffi hret => ?_)
    obtain ⟨hg, hm, hf⟩ := release_ret hE hret (mv := pv) (pv := qv) (by lk [lam])
      (by rw [hG]; lk [])
    subst g m3 ffi
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    rw [hGs]
    refine ⟨_, m2, rfl, ?_, ?_⟩
    · intro x hx hxD
      exact (hcopy.cells x (by omega)).trans ((hfr1 x (Or.inl hx)).trans (hlow x hx))
    · obtain ⟨c, hpc, hlc⟩ := (hc1.mono (k := 12) (by omega)).poly
      exact CanonN.of_poly (PolyAt.of_copy (n := 12) hcopy alD hpH'.2 (by omega) (by omega) hpc)
        hlc

end InitECandidate.Solver.GuestBound
