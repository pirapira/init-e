import InitECandidate.Solver.GuestBound.PointIn

/-!
# `fq12_twist` gives canonical `Fq12` coordinates

A parsed G2 point (three `Fq2` elements, six canonical field elements) becomes
an `Fq12` point: each coordinate is zero except two coefficients. Part of the
canonicity chain for `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)}

theorem equalNat {j c : Nat} (hj : j < 100) (hc : c < 100) :
    evalPanCmp .equal (BitVec.ofNat 64 j : Word) (BitVec.ofNat 64 c) = if j = c then 1 else 0 := by
  by_cases h : j = c
  · subst h
    simp [evalPanCmp]
  · have hne : (BitVec.ofNat 64 j : Word) ≠ BitVec.ofNat 64 c := by
      intro e
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      omega
    simp [evalPanCmp, hne, h]

/-- Coordinate `k` of the point at `O`. -/
def coordAddr (O : Word) (k : Nat) : Word := O + BitVec.ofNat 64 k * 384#64

theorem coordAddr_toNat {O : Word} {k : Nat} (hk : k < 3) (h : O.toNat + 1152 ≤ 2 ^ 63) :
    (coordAddr O k).toNat = O.toNat + 384 * k := by
  unfold coordAddr
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show (384#64 : Word).toNat = 384 by decide]
  omega

/-- Invariant of the loop of `fq12_twist`. -/
def TwistI (L : VarName → Option (PanValue Word)) (s : St σ) (O G2 : Word) (st : St σ) : Prop :=
  st.globals = s.globals ∧ st.ffi = s.ffi ∧ (∀ x, x ≠ "j" → st.locals x = L x) ∧
    (∀ x : Word, (x.toNat < O.toNat ∨ O.toNat + 1152 ≤ x.toNat) → st.memory x = s.memory x) ∧
    (∀ k, k < 3 → CanonN st.memory (coordAddr O k) 12) ∧ CanonN st.memory G2 6 ∧
    ∃ j, st.locals "j" = some (.word (BitVec.ofNat 64 j)) ∧ j ≤ 3

set_option maxHeartbeats 16000000 in
theorem fq12_twist_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq12_twist" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (O G2 : Word)
    (hout : s.locals "out" = some (.word O)) (hg2 : s.locals "g2" = some (.word G2))
    (alO : O.toNat % 8 = 0) (bO : O.toNat + 1152 ≤ 2 ^ 62) (bG : G2.toNat + 192 ≤ 2 ^ 62)
    (hdis : G2.toNat + 192 ≤ O.toNat ∨ O.toNat + 1152 ≤ G2.toNat)
    (cG : CanonN s.memory G2 6) (h : Runs E s body r) : Stopped r ∨ PointRet s O r := by
  have hbody := (fun_of_index 677 hE.functions (by guest_decl_at 677) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (PointRet s O)) r h
  have hpp : 0 < bnP := by decide
  have hn : (1152#64 : Word).toNat = 1152 := by decide
  have hnat : ∀ n : Nat, n < 100 → (BitVec.ofNat 64 n : Word).toNat = n := by
    intro n hn
    rw [BitVec.toNat_ofNat]
    omega
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hz⟩ := memzero_ret hE hret (dst := O) (nW := 1152#64) (by lk [hout])
    (eval_const _ _) alO (by rw [hn]) (by rw [hn]; omega)
  subst g ffi
  rw [hn] at hz
  have hz' : ∀ x : Word, (x.toNat < O.toNat ∨ O.toNat + 1152 ≤ x.toNat) → m1 x = s.memory x :=
    fun x hx => by rw [hz x, if_neg (by omega)]
  try dsimp only
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  obtain ⟨L, hL⟩ : ∃ L, L = updatePanValueMap s.locals "j" (.word 0#64) := ⟨_, rfl⟩
  rw [← hL]
  have Lo : L "out" = some (.word O) := by rw [hL]; lk [hout]
  have Lg : L "g2" = some (.word G2) := by rw [hL]; lk [hg2]
  refine WPs.seqG (TwistI L s O G2) (WPs.loopG (I := TwistI L s O G2)
    ⟨rfl, rfl, fun _ _ => rfl, hz', fun k hk => CanonN.of_zero_sub hz alO (off := 384 * k)
        (coordAddr_toNat hk (by omega)) (by omega) (by omega) (by omega),
      cG.frame (by omega) (fun x h1 h2 => hz' x (by omega)), 0, by rw [hL]; lk [], by omega⟩
    ?_ (fun a k hI _ => hI)) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, hfr, hcO, hcG, j, hj, hj3⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hloc hfr hcO hcG hj
    subst ga fa
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hj]))
      (of_eval (w := 3#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hjlt : j < 3 := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 j : Word) < 3#64 := by
        rw [BitVec.lt_def, hnat j (by omega)]
        have : (3#64 : Word).toNat = 3 := by decide
        omega
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have lao : la "out" = some (.word O) := (hloc _ (by decide)).trans Lo
    have lag : la "g2" = some (.word G2) := (hloc _ (by decide)).trans Lg
    have hg0 : coefAddr G2 (2 * j) = G2 + BitVec.ofNat 64 j * 64#64 := by
      unfold coefAddr
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
    have hg1 : coefAddr G2 (2 * j + 1) = G2 + BitVec.ofNat 64 j * 64#64 + 32#64 := by
      unfold coefAddr
      rw [BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    obtain ⟨v0, f0, l0⟩ := hcG.get (i := 2 * j) (by omega)
    obtain ⟨v1, f1, l1⟩ := hcG.get (i := 2 * j + 1) (by omega)
    refine WPs.dec_load4 hE (addr := coefAddr G2 (2 * j))
      (of_eval (by rw [hg0]; ev [evalPanOp, lag, hj])) f0 (fun c00 c01 c02 c03 hc0 => ?_)
    refine WPs.dec_load4 hE (addr := coefAddr G2 (2 * j + 1))
      (of_eval (by rw [hg1]; ev [evalPanOp, lag, hj, BitVec.add_assoc])) f1
      (fun c10 c11 c12 c13 hc1 => ?_)
    have hc1l : limbsVal [c10, c11, c12, c13] < bnP := by rw [hc1]; exact l1
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, n0, n1, n2, n3, hv, hn9⟩ := mulsmall_ret hE hret (a0 := c10) (a1 := c11)
      (a2 := c12) (a3 := c13) (k := 9#64) (by lk []) (eval_const _ _) hc1l
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, e0, e1, e2, e3, hv, he⟩ := fqsub_ret hE hret (a0 := c00) (a1 := c01)
      (a2 := c02) (a3 := c03) (b0 := n0) (b1 := n1) (b2 := n2) (b3 := n3) (by lk []) (by lk [])
      (by rw [hc0]; exact l0) hn9
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    have hel : limbsVal [e0, e1, e2, e3] < bnP := by rw [he]; exact Nat.mod_lt _ hpp
    try dsimp only
    refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
    have hq0 := equalNat (j := j) (c := 0) (by omega) (by omega)
    have hq1 := equalNat (j := j) (c := 1) (by omega) (by omega)
    refine WPs.seq_ite_assign (old := 0#64) (w := BitVec.ofNat 64 (if j = 0 then 2 else 0))
      (wc := evalPanCmp .equal (BitVec.ofNat 64 j : Word) (BitVec.ofNat 64 0)) (by lk [])
      (eval_cmp_inv hE (of_eval (by lk [hj])) (of_eval (eval_const _ _))) ?_ ?_ ?_
    · intro hne
      have : j = 0 := by
        by_contra hn0
        rw [hq0, if_neg hn0] at hne
        exact hne rfl
      rw [if_pos this]
      exact of_eval (by simp)
    · intro h0
      have : j ≠ 0 := by
        intro hn0
        rw [hq0, if_pos hn0] at h0
        exact absurd h0 (by decide)
      rw [if_neg this]
    try dsimp only
    obtain ⟨sh, hsh⟩ : ∃ sh : Nat, sh = (if j = 0 then 2 else if j = 1 then 3 else 0) := ⟨_, rfl⟩
    refine WPs.seq_ite_assign (old := BitVec.ofNat 64 (if j = 0 then 2 else 0))
      (w := BitVec.ofNat 64 sh)
      (wc := evalPanCmp .equal (BitVec.ofNat 64 j : Word) (BitVec.ofNat 64 1)) (by lk [])
      (eval_cmp_inv hE (of_eval (by lk [hj])) (of_eval (eval_const _ _))) ?_ ?_ ?_
    · intro hne
      have : j = 1 := by
        by_contra hn0
        rw [hq1, if_neg hn0] at hne
        exact hne rfl
      subst this
      rw [hsh]
      exact of_eval (by simp)
    · intro h0
      have : j ≠ 1 := by
        intro hn0
        rw [hq1, if_pos hn0] at h0
        exact absurd h0 (by decide)
      rw [hsh]
      by_cases hj0 : j = 0
      · rw [if_pos hj0, if_pos hj0]
      · rw [if_neg hj0, if_neg hj0, if_neg this]
    try dsimp only
    have hsh3 : sh ≤ 3 := by
      rw [hsh]
      split_ifs <;> omega
    refine WPs.dec (w := coordAddr O j) (of_eval (by unfold coordAddr; ev [evalPanOp, lao, hj])) ?_
    have hBj := coordAddr_toNat (O := O) hjlt (by omega)
    have hsh6 : (BitVec.ofNat 64 sh : Word) + 6#64 = BitVec.ofNat 64 (sh + 6) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    refine WPs.seq_store4 hE (addr := coefAddr (coordAddr O j) sh) (w0 := e0) (w1 := e1)
      (w2 := e2) (w3 := e3) (of_eval (by unfold coefAddr; ev [evalPanOp])) (by lk []) ?_
    refine WPs.seq_store4 hE (addr := coefAddr (coordAddr O j) (sh + 6)) (w0 := c10) (w1 := c11)
      (w2 := c12) (w3 := c13) (of_eval (by unfold coefAddr; ev [evalPanOp, hsh6])) (by lk []) ?_
    refine WPs.assign (old := BitVec.ofNat 64 j) (by lk [hj])
      (of_eval (w := BitVec.ofNat 64 (j + 1)) (by ev [hj, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    have hout1 : ∀ x : Word, (x.toNat < O.toNat + 384 * j ∨ O.toNat + 384 * j + 384 ≤ x.toNat) →
        set4 (set4 ma (coefAddr (coordAddr O j) sh) e0 e1 e2 e3)
          (coefAddr (coordAddr O j) (sh + 6)) c10 c11 c12 c13 x = ma x := by
      intro x hx
      rw [set4_outN (n := 12) (by rw [hBj]; omega) (by omega) (by rw [hBj]; omega),
        set4_outN (n := 12) (by rw [hBj]; omega) (by omega) (by rw [hBj]; omega)]
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, j + 1, ?_, by omega⟩
    · intro x hx
      refine Eq.trans ?_ (hloc x hx)
      show restorePanValueLocal _ _ _ x = la x
      by_cases h1 : x = "c0"
      · subst h1
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h2 : x = "c1"
      · subst h2
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h3 : x = "n9"
      · subst h3
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h4 : x = "e0"
      · subst h4
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h5 : x = "shift"
      · subst h5
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h6 : x = "base"
      · subst h6
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, h1, h2, h3, h4,
        h5, h6, hx]
    · intro x hx
      exact (hout1 x (by omega)).trans (hfr x hx)
    · intro k hk
      by_cases hkj : k = j
      · subst hkj
        exact ((hcO k hk).set4 (n := 12) (k := sh) (by rw [hBj]; omega) (by omega) hel).set4
          (n := 12) (k := sh + 6) (by rw [hBj]; omega) (by omega) hc1l
      · have hBk := coordAddr_toNat (O := O) hk (by omega)
        exact (hcO k hk).frame (by rw [hBk]; omega) (fun x h1 h2 => hout1 x (by
          rw [hBk] at h1 h2
          rcases Nat.lt_or_gt_of_ne hkj with hlt | hgt <;> omega))
    · exact hcG.frame (by omega) (fun x h1 h2 => hout1 x (by
        rcases hdis with hd | hd
        · left; omega
        · right; omega))
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, -, hfr, hcO, -⟩
    simp only at hg hf hfr hcO
    subst ga fa
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨_, ma, rfl, hfr, ?_, ?_, ?_⟩
    · have := hcO 0 (by omega)
      rwa [show coordAddr O 0 = O by unfold coordAddr; simp] at this
    · have := hcO 1 (by omega)
      rwa [show coordAddr O 1 = O + 384#64 by unfold coordAddr; rfl] at this
    · have := hcO 2 (by omega)
      rwa [show coordAddr O 2 = O + 768#64 by unfold coordAddr; rfl] at this

end InitECandidate.Solver.GuestBound
