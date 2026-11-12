import InitECandidate.Solver.GuestBound.Fq12InvTail
import InitECandidate.Solver.GuestBound.HtabSetWalk

/-!
# `fq12_inv`: the outer loop

Each round ends with `r1` holding the old `r0`, whose degree the inner loop
has pushed below the old degree of `r1`. So at most 13 rounds run.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' : Word → Option (PanValue Word)}

def Sep (A B : Word) : Prop := A.toNat + 416 ≤ B.toNat ∨ B.toNat + 416 ≤ A.toNat

theorem Sep.symm {A B : Word} (h : Sep A B) : Sep B A := Or.symm h

def BufOk (A : Word) : Prop := A.toNat % 8 = 0 ∧ A.toNat + 416 ≤ 2 ^ 62

/-- Six aligned, pairwise disjoint 416-byte buffers. -/
structure Geo (R0 R1 S0 S1 T Qb : Word) : Prop where
  o0 : BufOk R0
  o1 : BufOk R1
  oS0 : BufOk S0
  oS1 : BufOk S1
  oT : BufOk T
  oQ : BufOk Qb
  r01 : Sep R0 R1
  r0s0 : Sep R0 S0
  r0s1 : Sep R0 S1
  r0t : Sep R0 T
  r0q : Sep R0 Qb
  r1s0 : Sep R1 S0
  r1s1 : Sep R1 S1
  r1t : Sep R1 T
  r1q : Sep R1 Qb
  s01 : Sep S0 S1
  s0t : Sep S0 T
  s0q : Sep S0 Qb
  s1t : Sep S1 T
  s1q : Sep S1 Qb
  tq : Sep T Qb

theorem Geo.swap {R0 R1 S0 S1 T Qb : Word} (h : Geo R0 R1 S0 S1 T Qb) :
    Geo R1 R0 S1 T S0 Qb :=
  ⟨h.o1, h.o0, h.oS1, h.oT, h.oS0, h.oQ, h.r01.symm, h.r1s1, h.r1t, h.r1s0, h.r1q, h.r0s1,
    h.r0t, h.r0s0, h.r0q, h.s1t, h.s01.symm, h.s1q, h.s0t.symm, h.tq, h.s0q⟩

/-- Invariant of the outer loop, relative to the state `a` at its entry. -/
def OuterI (a : St σ) (Qb : Word) (st : St σ) : Prop :=
  st.globals = a.globals ∧ st.ffi = a.ffi ∧ ∃ R0 R1 S0 S1 T : Word,
    st.locals "r0" = some (.word R0) ∧ st.locals "r1" = some (.word R1) ∧
    st.locals "s0" = some (.word S0) ∧ st.locals "s1" = some (.word S1) ∧
    st.locals "q" = some (.word Qb) ∧ st.locals "tmp" = some (.word T) ∧
    Geo R0 R1 S0 S1 T Qb ∧ CanonAt st.memory R0 ∧ CanonAt st.memory R1 ∧
    CanonAt st.memory S0 ∧ CanonAt st.memory S1

/-- The variant of the outer loop: the degree of the polynomial at `r1`. -/
noncomputable def r1Meas (st : St σ) : Nat :=
  match st.locals "r1" with
  | some (.word A) => topIdx st.memory A
  | _ => 0

open Classical in
theorem topIdx_le (m : Word → Option (PanValue Word)) (A : Word) : topIdx m A ≤ 12 := by
  unfold topIdx
  exact Nat.findGreatest_le _

theorem sless_zero {d : Word} (h : RiscV.signedLess 0#64 d = true) :
    1 ≤ d.toNat ∧ d.toNat < 2 ^ 63 := by
  simp only [RiscV.signedLess, show (2 : Nat) ^ (64 - 1) = 2 ^ 63 from rfl,
    show (0#64 : Word).toNat = 0 from rfl] at h
  split_ifs at h <;> simp at h <;> omega

theorem fqi_brk_cost (hE : GuestEnv E) : Costs E FQI_BRK 100 := by
  have h : ∃ B, Costs E FQI_BRK B ∧ B ≤ 100 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem fqi_mzq_cost (hE : GuestEnv E) : Costs E FQI_MZQ 10000000000000000000000000 := by
  have h : ∃ B, Costs E FQI_MZQ B ∧ B ≤ 10000000000000000000000000 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem fqi_tail_cost (hE : GuestEnv E) :
    Costs E FQI_TAIL 1000000000000000000000000000000000000000000000000000000000000 := by
  have h : ∃ B, Costs E FQI_TAIL B ∧
      B ≤ 1000000000000000000000000000000000000000000000000000000000000 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 16000000 in
theorem fqi_outer_loop (hE : GuestEnv E) {Qb : Word} (hI : OuterI s Qb s) :
    WPc E s (.while (.const (BitVec.ofNat 64 1)) FQI_OB)
      ((12 + 1) * (expCost (.const (BitVec.ofNat 64 1) : Exp Word) +
        1000000000000000000000000000000000000000000000000000000000000000000000000000000000000 + 1))
      (fun _ => True) := by
  have hpp : 0 < bnP := by decide
  have h13 : (13#64 : Word).toNat = 13 := by decide
  have h416 : (416#64 : Word).toNat = 416 := by decide
  have hm1 : (0#64 - 1#64 : Word).toNat = 2 ^ 64 - 1 := by decide
  refine WPc.while (I := OuterI s Qb) (μ := r1Meas) 12 hI ?_ ?_ (fun _ _ _ _ => trivial)
  · unfold r1Meas
    split
    · exact topIdx_le _ _
    · omega
  rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, R0, R1, S0, S1, T, e0, e1, e2, e3, e4, e5, geo, k0, k1, k2,
    k3⟩ -
  simp only at hg hf e0 e1 e2 e3 e4 e5 k0 k1 k2 k3
  subst hg hf
  obtain ⟨c1, hp1, hl1⟩ := k1.poly
  obtain ⟨c0, hp0, hl0⟩ := k0.poly
  have g0 := geo.o0
  have g1 := geo.o1
  have gS0 := geo.oS0
  have gS1 := geo.oS1
  have gT := geo.oT
  have gQ := geo.oQ
  unfold BufOk at g0 g1 gS0 gS1 gT gQ
  have x01 := geo.r01
  have x0q := geo.r0q
  have x1q := geo.r1q
  have x0s0 := geo.r0s0
  have x0s1 := geo.r0s1
  have x0t := geo.r0t
  have x1s0 := geo.r1s0
  have x1s1 := geo.r1s1
  have x1t := geo.r1t
  have xs0q := geo.s0q
  have xs1q := geo.s1q
  have xs0t := geo.s0t
  have xs1t := geo.s1t
  have xtq := geo.tq
  unfold Sep at x01 x0q x1q x0s0 x0s1 x0t x1s0 x1s1 x1t xs0q xs1q xs0t xs1t xtq
  -- d1 = deg r1
  refine WPc.decCall_sub (Fn.«fq_poly_deg» hE) (by budget) (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, d1, hv, hdeg1⟩ := deg_ret hE hret.ret (A := R1) (nW := 13#64) (c := c1)
    (by lk [e1]) (eval_const _ _) g1.1 (by rw [h13]; omega) hp1
  subst g m ffi
  simp only [List.cons.injEq, and_true] at hv
  subst v
  rw [h13] at hdeg1
  -- if d1 <= 0 break
  refine WPc.seq_sub (fun st2 => st2 = ⟨updatePanValueMap la "d1" (.word d1), s.globals, ma, s.ffi⟩ ∧
      RiscV.signedLess 0#64 d1 = true)
    (WPc.of_costs (fqi_brk_cost hE) (WPs.ite (w := evalPanCmp .notLess 0#64 d1)
      (eval_cmp_inv hE (of_eval (eval_const _ _)) (of_eval (by lk []))) ?_)) (by budget) ?_
  · rw [notLess_eq]
    by_cases hs : RiscV.signedLess 0#64 d1 = true
    · rw [if_pos hs, if_pos rfl]
      exact WPs.skip ⟨rfl, hs⟩
    · rw [if_neg hs, if_neg (by decide)]
      exact WPs.brk trivial
  rintro _ ⟨rfl, hs⟩
  have hd1pos := sless_zero hs
  obtain ⟨hd1r, hnz, hz1⟩ : d1.toNat < 13 ∧ c1 d1.toNat ≠ 0 ∧
      ∀ i, d1.toNat < i → i < 13 → c1 i = 0 := by
    rcases hdeg1 with ⟨h, -⟩ | h
    · rw [h, hm1] at hd1pos
      omega
    · exact h
  -- d0 = deg r0
  refine WPc.decCall_sub (Fn.«fq_poly_deg» hE) (by budget) (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, d0, hv, hdeg0⟩ := deg_ret hE hret.ret (A := R0) (nW := 13#64) (c := c0)
    (by lk [e0]) (eval_const _ _) g0.1 (by rw [h13]; omega) hp0
  subst g m ffi
  simp only [List.cons.injEq, and_true] at hv
  subst v
  rw [h13] at hdeg0
  -- memzero(q, 416)
  refine WPc.seq_sub (fun st4 => ∃ m4, st4 = ⟨updatePanValueMap (updatePanValueMap la "d1"
      (.word d1)) "d0" (.word d0), s.globals, m4, s.ffi⟩ ∧ ZeroRel ma m4 Qb 416)
    (WPc.of_costs (fqi_mzq_cost hE) (WPs.call_ret (fun vs g m4 ffi hret => ?_))) (by budget) ?_
  · obtain ⟨hg, hf, hz⟩ := memzero_ret hE hret (dst := Qb) (nW := 416#64) (by lk [e4])
      (eval_const _ _) gQ.1 (by decide) (by rw [h416]; omega)
    subst g ffi
    rw [h416] at hz
    exact ⟨m4, rfl, hz⟩
  rintro _ ⟨m4, rfl, hz⟩
  have hfr4 : ∀ x, ¬ InB Qb x → m4 x = ma x := by
    intro x hx
    rw [hz x, if_neg (by unfold InB at hx; omega)]
  have hcq4 : CanonAt m4 Qb :=
    CanonAt.of_poly (PolyAt.of_zero (n := 13) gQ.1 (by omega) hz) (fun _ _ => hpp)
  have hp1' : PolyAt m4 R1 c1 13 :=
    hp1.frame (by omega) (fun x h1 h2 => hfr4 x (by unfold InB; omega))
  have hp0' : PolyAt m4 R0 c0 13 :=
    hp0.frame (by omega) (fun x h1 h2 => hfr4 x (by unfold InB; omega))
  -- lead = r1[d1]
  refine WPc.dec_sub (by budget) (fun v hv => ?_)
  obtain ⟨addr, w0, w1, w2, w3, haddr, rfl, y0, y1, y2, y3⟩ := eval_load_four hE hv
  have haddr' : addr = coefAddr R1 d1.toNat := by
    have : E.eval ⟨updatePanValueMap (updatePanValueMap la "d1" (.word d1)) "d0" (.word d0),
        s.globals, m4, s.ffi⟩ (.op .add [.var .local "r1", .panOp .mul [.var .local "d1",
          .const (BitVec.ofNat 64 32)]]) = some (.word (coefAddr R1 d1.toNat)) := by
      unfold coefAddr
      rw [ofNat_toNat']
      ev [evalPanOp, e1]
    rw [this] at haddr
    simpa using haddr.symm
  subst haddr'
  have hlead : limbsVal [w0, w1, w2, w3] = c1 d1.toNat :=
    Fe.unique ⟨w0, w1, w2, w3, y0, y1, y2, y3, rfl⟩ (hp1' _ hd1r)
  -- linv = fq_inv(lead)
  refine WPc.decCall_sub (Fn.«fq_inv» hE) (by budget) (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, i0, i1, i2, i3, hv, hilt, hieq⟩ := fqinv_ret hE hret.ret (a0 := w0)
    (a1 := w1) (a2 := w2) (a3 := w3) (by lk []) (by rw [hlead]; exact hnz)
  subst g m ffi
  simp only [List.cons.injEq, and_true] at hv
  subst v
  rw [hlead] at hieq
  obtain ⟨L7, hL7⟩ : ∃ L7, L7 = updatePanValueMap (updatePanValueMap (updatePanValueMap
      (updatePanValueMap la "d1" (.word d1)) "d0" (.word d0)) "lead"
      (.rStruct [.word w0, .word w1, .word w2, .word w3])) "linv"
      (.rStruct [.word i0, .word i1, .word i2, .word i3]) := ⟨_, rfl⟩
  rw [← hL7]
  have q0 : L7 "r0" = some (.word R0) := by rw [hL7]; lk [e0]
  have q1 : L7 "r1" = some (.word R1) := by rw [hL7]; lk [e1]
  have q2 : L7 "s0" = some (.word S0) := by rw [hL7]; lk [e2]
  have q3 : L7 "s1" = some (.word S1) := by rw [hL7]; lk [e3]
  have q4 : L7 "q" = some (.word Qb) := by rw [hL7]; lk [e4]
  have q5 : L7 "tmp" = some (.word T) := by rw [hL7]; lk [e5]
  have q6 : L7 "d0" = some (.word d0) := by rw [hL7]; lk []
  have q7 : L7 "d1" = some (.word d1) := by rw [hL7]; lk []
  have q8 : L7 "linv" = some (.rStruct [.word i0, .word i1, .word i2, .word i3]) := by
    rw [hL7]; lk []
  -- the inner loop, then the rest of the round
  refine WPc.seq_sub (fun st7 => ∃ l7 m7, st7 = ⟨l7, s.globals, m7, s.ffi⟩ ∧
      InnerI ⟨L7, s.globals, m4, s.ffi⟩ R0 Qb st7 ∧
      ∃ d, l7 "d0" = some (.word d) ∧ (d = 0#64 - 1#64 ∨ d.toNat < d1.toNat))
    (WPc.mono (inner_loop hE (a := ⟨L7, s.globals, m4, s.ffi⟩) (R0 := R0) (R1 := R1) (Qb := Qb)
      (d0 := d0) (d1 := d1) (c0 := c0) (c1 := c1) q0 q1 q4 q6 q7 q8 (by omega) (by omega)
      (by omega) g0.1 x01 x0q x1q hp0' hl0 hdeg0 hp1' hl1 hcq4 hd1r hilt hieq) (Nat.le_refl _)
      (by rintro r ⟨l, mm, rfl, hI7, hd⟩; exact ⟨l, mm, rfl, hI7, hd⟩)) (by budget) ?_
  rintro _ ⟨l7, m7, rfl, ⟨-, -, hloc7, hfr7, hcq7, dd, cc, hdd, hpc, hlc, hdegc⟩, d, hd, hdlt⟩
  simp only at hloc7 hfr7 hcq7 hdd hpc
  have hdd' : dd = d := by
    rw [hdd] at hd
    simpa using hd
  subst hdd'
  have hm7 : ∀ x, ¬ InB R0 x → ¬ InB Qb x → m7 x = ma x :=
    fun x h0 hq => (hfr7 x h0 hq).trans (hfr4 x hq)
  refine WPc.of_costs_le (fqi_tail_cost hE) (by budget) (WPs.conseq (tail_spec hE
    (a := ⟨l7, s.globals, m7, s.ffi⟩) (R0 := R0) (R1 := R1) (S0 := S0) (S1 := S1) (Qb := Qb)
    (T := T) ((hloc7 _ (by decide)).trans q0) ((hloc7 _ (by decide)).trans q1)
    ((hloc7 _ (by decide)).trans q2) ((hloc7 _ (by decide)).trans q3)
    ((hloc7 _ (by decide)).trans q4) ((hloc7 _ (by decide)).trans q5) gT.2 gS0.2 gS1.2 gQ.2
    gT.1 gS0.1 (by omega) (by omega) (by omega)
    (k2.frame (by omega) (fun x hx => hm7 x (by unfold InB at hx ⊢; omega)
      (by unfold InB at hx ⊢; omega)))
    (k3.frame (by omega) (fun x hx => hm7 x (by unfold InB at hx ⊢; omega)
      (by unfold InB at hx ⊢; omega))) hcq7) ?_)
  rintro r ⟨l', m', rfl, f0, f1, f2, f3, f4, f5, hfr', hcT'⟩
  simp only at hfr' hcT'
  simp only [restorePanValueFfiLocal]
  have hpc' : PolyAt m' R0 cc 13 :=
    hpc.frame (by omega) (fun x h1 h2 => hfr' x (by unfold InB; omega))
  have hr1' : restorePanValueLocal (restorePanValueLocal (restorePanValueLocal
      (restorePanValueLocal l' "linv" (updatePanValueMap (updatePanValueMap (updatePanValueMap
        la "d1" (.word d1)) "d0" (.word d0)) "lead"
        (.rStruct [.word w0, .word w1, .word w2, .word w3]) "linv")) "lead"
      (updatePanValueMap (updatePanValueMap la "d1" (.word d1)) "d0" (.word d0) "lead")) "d0"
      (updatePanValueMap la "d1" (.word d1) "d0")) "d1" (la "d1") "r1" = some (.word R0) := by
    simp (config := { decide := true }) [restorePanValueLocal, f1]
  refine ⟨⟨rfl, rfl, R1, R0, S1, T, S0, ?_, hr1', ?_, ?_, ?_, ?_, geo.swap, ?_, ?_, ?_, hcT'⟩, ?_⟩
  · simp (config := { decide := true }) [restorePanValueLocal, f0]
  · simp (config := { decide := true }) [restorePanValueLocal, f2]
  · simp (config := { decide := true }) [restorePanValueLocal, f3]
  · simp (config := { decide := true }) [restorePanValueLocal, f5]
  · simp (config := { decide := true }) [restorePanValueLocal, f4]
  · exact k1.frame (by omega) (fun x hx => (hfr' x (by unfold InB at hx ⊢; omega)).trans
      (hm7 x (by unfold InB at hx ⊢; omega) (by unfold InB at hx ⊢; omega)))
  · exact CanonAt.of_poly hpc' hlc
  · exact k3.frame (by omega) (fun x hx => (hfr' x (by unfold InB at hx ⊢; omega)).trans
      (hm7 x (by unfold InB at hx ⊢; omega) (by unfold InB at hx ⊢; omega)))
  · show r1Meas _ < r1Meas _
    unfold r1Meas
    simp only [hr1', e1]
    rw [topIdx_eq hp1 hd1r hnz hz1]
    rcases hdegc with ⟨-, hzero⟩ | ⟨hlt, hne, hzz⟩
    · rw [topIdx_zero hpc' hzero]
      omega
    · rw [topIdx_eq hpc' hlt hne hzz]
      rcases hdlt with h | h
      · rw [h, hm1] at hlt
        omega
      · exact h

end InitECandidate.Solver.GuestBound
