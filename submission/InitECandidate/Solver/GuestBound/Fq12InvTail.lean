import InitECandidate.Solver.GuestBound.Fq12InvLoop

/-!
# `fq12_inv`: the rest of an outer round

`tmp = s0 - q * s1` (a copy and 13 conditional `fq_poly_submul`s), then the
buffers swap roles. Only `tmp` is written, and it stays canonical.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' : Word → Option (PanValue Word)}

theorem u256_is_zero_quiet :
    keepFn quietLeaf Guest.Software.guestAst 1 "u256_is_zero" = true := by
  decide +kernel

/-- `x = e; rest` for a local word `x`. -/
theorem WPs.seq_assign {x : VarName} {e : Exp Word} {q : Prog Word} {w old : Word}
    (hx : s.locals x = some (.word old)) (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : WPs E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩ q Q) :
    WPs E s (.seq (.assign .local x e) q) Q :=
  WPs.seq (fun st => st = ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩)
    (WPs.assign hx he ⟨_, _, _, _, rfl, rfl⟩) (by rintro _ rfl; exact h)

/-- Invariant of the `j` loop, relative to the state `a` at its entry. -/
def JI (a : St σ) (T : Word) (st : St σ) : Prop :=
  st.globals = a.globals ∧ st.ffi = a.ffi ∧ (∀ x, x ≠ "j" → st.locals x = a.locals x) ∧
    (∀ x, ¬ InB T x → st.memory x = a.memory x) ∧ CanonAt st.memory T ∧
    ∃ j, st.locals "j" = some (.word (BitVec.ofNat 64 j)) ∧ j ≤ 13

set_option maxHeartbeats 8000000 in
theorem tail_spec (hE : GuestEnv E) {a : St σ} {R0 R1 S0 S1 Qb T : Word}
    (hr0 : a.locals "r0" = some (.word R0)) (hr1 : a.locals "r1" = some (.word R1))
    (hs0 : a.locals "s0" = some (.word S0)) (hs1 : a.locals "s1" = some (.word S1))
    (hq : a.locals "q" = some (.word Qb)) (ht : a.locals "tmp" = some (.word T))
    (bT : T.toNat + 416 ≤ 2 ^ 62) (b0 : S0.toNat + 416 ≤ 2 ^ 62) (b1 : S1.toNat + 416 ≤ 2 ^ 62)
    (bq : Qb.toNat + 416 ≤ 2 ^ 62) (alT : T.toNat % 8 = 0) (al0 : S0.toNat % 8 = 0)
    (sT0 : T.toNat + 416 ≤ S0.toNat ∨ S0.toNat + 416 ≤ T.toNat)
    (sT1 : T.toNat + 416 ≤ S1.toNat ∨ S1.toNat + 416 ≤ T.toNat)
    (sTq : T.toNat + 416 ≤ Qb.toNat ∨ Qb.toNat + 416 ≤ T.toNat)
    (hc0 : CanonAt a.memory S0) (hc1 : CanonAt a.memory S1) (hcq : CanonAt a.memory Qb) :
    WPs E a FQI_TAIL (fun r => ∃ l' m', r = .normal l' a.globals m' a.ffi ∧
      l' "r0" = some (.word R1) ∧ l' "r1" = some (.word R0) ∧ l' "s0" = some (.word S1) ∧
      l' "s1" = some (.word T) ∧ l' "tmp" = some (.word S0) ∧ l' "q" = some (.word Qb) ∧
      (∀ x, ¬ InB T x → m' x = a.memory x) ∧ CanonAt m' T) := by
  have hpp : 0 < bnP := by decide
  have h416 : (416#64 : Word).toNat = 416 := by decide
  obtain ⟨cs0, hps0, hls0⟩ := hc0.poly
  obtain ⟨cs1, hps1, hls1⟩ := hc1.poly
  obtain ⟨cq, hpq, hlq⟩ := hcq.poly
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hcopy⟩ := memcpy_ret hE hret (dst := T) (src := S0) (nW := 416#64)
    (by lk [ht]) (by lk [hs0]) (eval_const _ _)
    ⟨by rw [h416]; omega, by rw [h416]; omega, by rw [h416]; omega, by rw [h416]; omega⟩
  subst hg hf
  rw [h416] at hcopy
  have hfr1 : ∀ x, ¬ InB T x → m1 x = a.memory x := by
    intro x hx
    refine hcopy.cells x ?_
    unfold InB at hx
    omega
  have hcT1 : CanonAt m1 T :=
    CanonAt.of_poly (PolyAt.of_copy (n := 13) hcopy alT al0 (by omega) (by omega) hps0) hls0
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.seqG (fun st => JI ⟨updatePanValueMap a.locals "j" (.word 0#64), a.globals, m1,
      a.ffi⟩ T st ∧ st.locals "j" = some (.word (BitVec.ofNat 64 13)))
    (WPs.loopG (I := JI ⟨updatePanValueMap a.locals "j" (.word 0#64), a.globals, m1, a.ffi⟩ T)
      ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, hcT1, 0, by lk [], by omega⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, hfr, hcT, j, hj, hj13⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hloc hfr hcT hj
    subst hg hf
    have hjt : (BitVec.ofNat 64 j : Word).toNat = j := by
      rw [BitVec.toNat_ofNat]
      omega
    have hc := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := 13#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hjlt : j < 13 := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 j : Word) < 13#64 := by
        rw [BitVec.lt_def, hjt]
        have : (13#64 : Word).toNat = 13 := by decide
        omega
      rw [hc] at hw
      simp [evalPanCmp, hl] at hw
    have hlq' : la "q" = some (.word Qb) := by
      rw [hloc _ (by decide)]
      lk [hq]
    have hlt' : la "tmp" = some (.word T) := by
      rw [hloc _ (by decide)]
      lk [ht]
    have hls1' : la "s1" = some (.word S1) := by
      rw [hloc _ (by decide)]
      lk [hs1]
    have hmq : ∀ x, ¬ InB T x → ma x = a.memory x := fun x hx => (hfr x hx).trans (hfr1 x hx)
    have hpqa : PolyAt ma Qb cq 13 :=
      hpq.frame (by omega) (fun x h1 h2 => hmq x (by unfold InB; omega))
    have hps1a : PolyAt ma S1 cs1 13 :=
      hps1.frame (by omega) (fun x h1 h2 => hmq x (by unfold InB; omega))
    obtain ⟨ct, hpt, hlt⟩ := hcT.poly
    refine WPs.dec_load4 hE (addr := coefAddr Qb j)
      (of_eval (by unfold coefAddr; ev [evalPanOp, hlq', hj])) (hpqa j hjlt)
      (fun q0 q1 q2 q3 hqv => ?_)
    refine WPs.decCall_ret (fun v g m2 ffi hret => ?_)
    obtain ⟨hg, hm, hf⟩ := hret.quiet
      (keepFn_sound (quietKeeper E) hE.functions 1 "u256_is_zero" u256_is_zero_quiet)
    subst hg hm hf
    have hsub : (12#64 - BitVec.ofNat 64 j : Word).toNat = 12 - j := by
      rw [BitVec.toNat_sub, hjt, show (12#64 : Word).toNat = 12 by decide]
      omega
    refine WPs.seq (fun st2 => st2.locals = updatePanValueMap (updatePanValueMap la "qj"
        (.rStruct [.word q0, .word q1, .word q2, .word q3])) "qz" v ∧ st2.globals = a.globals ∧
        st2.ffi = a.ffi ∧ (∀ x, ¬ InB T x → st2.memory x = m2 x) ∧ CanonAt st2.memory T)
      (WPs.ite_both (fun w _ => ?_)) ?_
    · split
      · exact WPs.skip ⟨_, _, _, _, rfl, rfl, rfl, rfl, fun _ _ => rfl, hcT⟩
      · refine WPs.call_ret (fun vs g m3 ffi hret => ?_)
        obtain ⟨hg, hf, hfr3, hent⟩ := submul_ret hE hret (A := T) (B := S1)
          (sW := BitVec.ofNat 64 j) (dbW := 12#64 - BitVec.ofNat 64 j)
          (q0 := q0) (q1 := q1) (q2 := q2) (q3 := q3) (ca := fun i => ct (j + i)) (cb := cs1)
          (by lk [hlt']) (by lk [hls1']) (by lk []) (by lk [hj]) (by ev [hj])
          (by rw [hqv]; exact hlq j hjlt) (by rw [hjt, hsub]; omega) (by rw [hsub]; omega)
          (by rw [hjt, hsub]; omega)
          (fun i hi => ⟨hps1a i (by rw [hsub] at hi; omega), hls1 i (by rw [hsub] at hi; omega)⟩)
          (fun i hi => by
            rw [hjt]
            exact ⟨hpt _ (by rw [hsub] at hi; omega), hlt _ (by rw [hsub] at hi; omega)⟩)
        subst hg hf
        rw [hjt, hsub] at hfr3 hent
        refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, fun x hx => hfr3 x (by unfold InB at hx; omega),
          ?_⟩
        intro i
        by_cases hi : j ≤ i ∧ i < 13
        · obtain ⟨v', P, hfe, hP, hPeq, hv⟩ := hent (i - j) (by omega)
          have e : j + (i - j) = i := by omega
          rw [e] at hfe
          exact ⟨v', fun _ => ⟨hfe, by rw [hv]; exact Nat.mod_lt _ hpp⟩⟩
        · refine ⟨ct i, fun hi13 => ⟨fe_congr (by rw [coefAddr_toNat (by omega)]; omega)
            (fun x h1 h2 => hfr3 x (by rw [coefAddr_toNat (by omega)] at h1 h2; omega))
            (hpt i hi13), hlt i hi13⟩⟩
    · rintro ⟨l2, g2, m2, f2⟩ ⟨hl2, hg2, hf2, hfr2, hcT2⟩
      simp only at hl2 hg2 hf2 hfr2 hcT2
      subst hl2 hg2 hf2
      refine WPs.assign (old := BitVec.ofNat 64 j) (by lk [hj])
        (of_eval (w := BitVec.ofNat 64 (j + 1)) (by ev [hj, ofNat_succ])) ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨rfl, rfl, ?_, fun x hx => (hfr2 x hx).trans (hfr x hx), hcT2, j + 1, ?_, by omega⟩
      · intro x hx
        refine Eq.trans ?_ (hloc x hx)
        show restorePanValueLocal _ _ _ x = la x
        by_cases hz : x = "qz"
        · subst hz
          simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
        by_cases hqj : x = "qj"
        · subst hqj
          simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hz, hqj, hx]
      · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hf, hloc, hfr, hcT, j, hj, hj13⟩ hcond
    simp only at hg hf hloc hfr hcT hj
    have hjt : (BitVec.ofNat 64 j : Word).toNat = j := by
      rw [BitVec.toNat_ofNat]
      omega
    have hc := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := 13#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hge : ¬ j < 13 := by
      intro hlt
      have hl : (BitVec.ofNat 64 j : Word) < 13#64 := by
        rw [BitVec.lt_def, hjt]
        have : (13#64 : Word).toNat = 13 := by decide
        omega
      simp [evalPanCmp, hl] at hc
    have : j = 13 := by omega
    subst this
    exact ⟨⟨hg, hf, hloc, hfr, hcT, 13, hj, hj13⟩, hj⟩
  · rintro ⟨la, ga, ma, fa⟩ ⟨⟨hg, hf, hloc, hfr, hcT, -⟩, hj⟩
    simp only at hg hf hloc hfr hcT hj
    subst hg hf
    have e0 : la "r0" = some (.word R0) := by rw [hloc _ (by decide)]; lk [hr0]
    have e1 : la "r1" = some (.word R1) := by rw [hloc _ (by decide)]; lk [hr1]
    have e2 : la "s0" = some (.word S0) := by rw [hloc _ (by decide)]; lk [hs0]
    have e3 : la "s1" = some (.word S1) := by rw [hloc _ (by decide)]; lk [hs1]
    have e4 : la "q" = some (.word Qb) := by rw [hloc _ (by decide)]; lk [hq]
    have e5 : la "tmp" = some (.word T) := by rw [hloc _ (by decide)]; lk [ht]
    refine WPs.dec (w := R0) (of_eval (by lk [e0])) ?_
    refine WPs.seq_assign (old := R0) (w := R1) (by lk [e0]) (of_eval (by lk [e1])) ?_
    refine WPs.seq_assign (old := R1) (w := R0) (by lk [e1]) (of_eval (by lk [])) ?_
    refine WPs.seq_assign (old := R0) (w := S0) (by lk []) (of_eval (by lk [e2])) ?_
    refine WPs.seq_assign (old := S0) (w := S1) (by lk [e2]) (of_eval (by lk [e3])) ?_
    refine WPs.seq_assign (old := S1) (w := T) (by lk [e3]) (of_eval (by lk [e5])) ?_
    refine WPs.assign (old := T) (w := S0) (by lk [e5]) (of_eval (by lk [])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => (hfr x hx).trans (hfr1 x hx), hcT⟩ <;>
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, e4]

end InitECandidate.Solver.GuestBound
