import InitECandidate.Solver.GuestBound.Fq12InvAst

/-!
# `fq12_inv`: one round of the inner loop

`r0 -= cf * x^(d0-d1) * r1` with `cf = top / lead` clears the coefficient at
`d0`, so the degree of `r0` drops.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' : Word → Option (PanValue Word)}

/-- `x` lies in the 416-byte buffer at `A`. -/
def InB (A x : Word) : Prop := A.toNat ≤ x.toNat ∧ x.toNat < A.toNat + 416

/-- The 13 coefficients at `A` are field elements below `p`. -/
def CanonAt (m : Word → Option (PanValue Word)) (A : Word) : Prop :=
  ∀ i, ∃ v, i < 13 → Fe m (coefAddr A i) v ∧ v < bnP

theorem CanonAt.poly {A : Word} (h : CanonAt m A) :
    ∃ c, PolyAt m A c 13 ∧ ∀ i, i < 13 → c i < bnP := by
  choose c hc using h
  exact ⟨c, fun i hi => (hc i hi).1, fun i hi => (hc i hi).2⟩

theorem CanonAt.of_poly {A : Word} {c : Nat → Nat} (hp : PolyAt m A c 13)
    (hc : ∀ i, i < 13 → c i < bnP) : CanonAt m A :=
  fun i => ⟨c i, fun hi => ⟨hp i hi, hc i hi⟩⟩

theorem CanonAt.frame {A : Word} (h64 : A.toNat + 416 ≤ 2 ^ 64)
    (h : ∀ x, InB A x → m' x = m x) (hc : CanonAt m A) : CanonAt m' A := by
  obtain ⟨c, hp, hlt⟩ := hc.poly
  exact CanonAt.of_poly (hp.frame (by omega) (fun x h1 h2 => h x ⟨h1, by omega⟩)) hlt

/-- `d` is the degree of `c` as `fq_poly_deg` reports it. -/
def DegRel (d : Word) (c : Nat → Nat) : Prop :=
  (d = 0#64 - 1#64 ∧ ∀ i, i < 13 → c i = 0) ∨
    (d.toNat < 13 ∧ c d.toNat ≠ 0 ∧ ∀ i, d.toNat < i → i < 13 → c i = 0)

/-- A call statement followed by the rest. -/
theorem WPs.seq_call_ret {f : FunName} {args : List (Exp Word)} {q : Prog Word}
    (h : ∀ vs g m ffi, CalleeRet E s f args vs g m ffi → WPs E ⟨s.locals, g, m, ffi⟩ q Q) :
    WPs E s (.seq (.call (some (none, none)) f args) q) Q :=
  WPs.seq (fun st => ∃ vs g m ffi, CalleeRet E s f args vs g m ffi ∧ st = ⟨s.locals, g, m, ffi⟩)
    (WPs.call_ret (fun vs g m ffi hr => ⟨_, _, _, _, rfl, vs, g, m, ffi, hr, rfl⟩))
    (by rintro _ ⟨vs, g, m, ffi, hr, rfl⟩; exact h vs g m ffi hr)

theorem ofNat_toNat' (w : Word) : BitVec.ofNat 64 w.toNat = w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt w.isLt

set_option maxHeartbeats 4000000 in
theorem inner_body (hE : GuestEnv E) {a : St σ} {R0 R1 Qb d0 d1 l0 l1 l2 l3 : Word}
    {c0 c1 : Nat → Nat}
    (hr0 : a.locals "r0" = some (.word R0)) (hr1 : a.locals "r1" = some (.word R1))
    (hq : a.locals "q" = some (.word Qb)) (hd0 : a.locals "d0" = some (.word d0))
    (hd1 : a.locals "d1" = some (.word d1))
    (hlinv : a.locals "linv" = some (.rStruct [.word l0, .word l1, .word l2, .word l3]))
    (b0 : R0.toNat + 416 ≤ 2 ^ 63) (b1 : R1.toNat + 416 ≤ 2 ^ 63) (bq : Qb.toNat + 416 ≤ 2 ^ 63)
    (al0 : R0.toNat % 8 = 0)
    (s01 : R0.toNat + 416 ≤ R1.toNat ∨ R1.toNat + 416 ≤ R0.toNat)
    (s0q : R0.toNat + 416 ≤ Qb.toNat ∨ Qb.toNat + 416 ≤ R0.toNat)
    (s1q : R1.toNat + 416 ≤ Qb.toNat ∨ Qb.toNat + 416 ≤ R1.toNat)
    (hp0 : PolyAt a.memory R0 c0 13) (hc0 : ∀ i, i < 13 → c0 i < bnP)
    (hp1 : PolyAt a.memory R1 c1 13) (hc1 : ∀ i, i < 13 → c1 i < bnP)
    (hcq : CanonAt a.memory Qb)
    (h1le : d1.toNat ≤ d0.toNat) (hd0r : d0.toNat < 13)
    (hz : ∀ i, d0.toNat < i → i < 13 → c0 i = 0)
    (hl : limbsVal [l0, l1, l2, l3] < bnP)
    (hl3 : limbsVal [l0, l1, l2, l3] * c1 d1.toNat * 2 ^ 256 % bnP = bnR3 % bnP) :
    WPs E a FQI_IB (fun r => ∃ l' m' d', r = .normal l' a.globals m' a.ffi ∧
      (∀ x, x ≠ "d0" → l' x = a.locals x) ∧ l' "d0" = some (.word d') ∧
      (∀ x, ¬ InB R0 x → ¬ InB Qb x → m' x = a.memory x) ∧ CanonAt m' Qb ∧
      ∃ c0', PolyAt m' R0 c0' 13 ∧ (∀ i, i < 13 → c0' i < bnP) ∧ DegRel d' c0' ∧
        (d' = 0#64 - 1#64 ∨ d'.toNat < d0.toNat)) := by
  have hpp : 0 < bnP := by decide
  have hsW : (d0 - d1).toNat = d0.toNat - d1.toNat := by
    rw [BitVec.toNat_sub]
    have := d0.isLt
    have := d1.isLt
    omega
  have hcA0 := coefAddr_toNat (a := R0) (i := d0.toNat) (by omega)
  have hcQ := coefAddr_toNat (a := Qb) (i := (d0 - d1).toNat) (by omega)
  have hQ64 : (coefAddr Qb (d0 - d1).toNat).toNat + 32 ≤ 2 ^ 64 := by rw [hcQ]; omega
  refine WPs.dec_load4 hE (addr := coefAddr R0 d0.toNat)
    (of_eval (by unfold coefAddr; rw [ofNat_toNat']; ev [evalPanOp, hr0, hd0])) (hp0 _ hd0r)
    (fun t0 t1 t2 t3 ht => ?_)
  refine WPs.decCall_fqmul hE (a0 := t0) (a1 := t1) (a2 := t2) (a3 := t3) (b0 := l0) (b1 := l1)
    (b2 := l2) (b3 := l3) (by lk []) (by lk [hlinv]) (by rw [ht]; exact hc0 _ hd0r) hl
    (fun f0 f1 f2 f3 hflt hfeq => ?_)
  refine WPs.seq_store4 hE (addr := coefAddr Qb (d0 - d1).toNat) (w0 := f0) (w1 := f1)
    (w2 := f2) (w3 := f3)
    (of_eval (by unfold coefAddr; rw [ofNat_toNat']; ev [evalPanOp, hq, hd0, hd1])) (by lk []) ?_
  -- memory after the store
  have hS : ∀ x, ¬ InB Qb x →
      set4 a.memory (coefAddr Qb (d0 - d1).toNat) f0 f1 f2 f3 x = a.memory x := by
    intro x hx
    refine set4_other hQ64 ?_
    rw [hcQ]
    unfold InB at hx
    omega
  refine WPs.seq_call_ret (fun vs g m2 ffi hret => ?_)
  obtain ⟨hg, hf, hrel⟩ := submul_ret hE hret (A := R0) (B := R1) (sW := d0 - d1) (dbW := d1)
    (q0 := f0) (q1 := f1) (q2 := f2) (q3 := f3) (ca := fun i => c0 ((d0 - d1).toNat + i))
    (cb := c1) (by lk [hr0]) (by lk [hr1]) (by lk []) (by ev [hd0, hd1]) (by lk [hd1]) hflt
    (by omega) (by omega) (by omega)
    (fun i hi => ⟨fe_congr (by rw [coefAddr_toNat (by omega)]; omega)
      (fun x h1 h2 => hS x (by
        rw [coefAddr_toNat (by omega)] at h1 h2
        unfold InB
        omega)) (hp1 i (by omega)), hc1 i (by omega)⟩)
    (fun i hi => ⟨fe_congr (by rw [coefAddr_toNat (by omega)]; omega)
      (fun x h1 h2 => hS x (by
        rw [coefAddr_toNat (by omega)] at h1 h2
        unfold InB
        omega)) (hp0 _ (by omega)), hc0 _ (by omega)⟩)
  subst hg hf
  obtain ⟨hfr, hent⟩ := hrel
  -- memory after the subtraction, on cells outside the rewritten range of r0
  have hM2 : ∀ x : Word, (x.toNat < R0.toNat + 32 * (d0 - d1).toNat ∨
      R0.toNat + 32 * (d0.toNat + 1) ≤ x.toNat) → ¬ InB Qb x → m2 x = a.memory x := by
    intro x hx hxq
    rw [hfr x (by omega)]
    exact hS x hxq
  -- the cleared coefficient
  have hclear : Fe m2 (coefAddr R0 d0.toNat) 0 := by
    obtain ⟨v, P, hfe, hP, hPeq, hv⟩ := hent d1.toNat (Nat.le_refl _)
    have e : (d0 - d1).toNat + d1.toNat = d0.toNat := by omega
    rw [e] at hfe
    simp only [e] at hv
    have hPt : P = c0 d0.toNat :=
      mont_cancel (top := c0 d0.toNat) (lead := c1 d1.toNat)
        (linv := limbsVal [l0, l1, l2, l3]) (d1 := limbsVal [f0, f1, f2, f3]) (d2 := P)
        (hc0 _ hd0r) hP (by rw [hfeq, ht]) hPeq hl3
    have : v = 0 := by
      rw [hv, hPt, show c0 d0.toNat + bnP - c0 d0.toNat = bnP by omega, Nat.mod_self]
    rw [this] at hfe
    exact hfe
  have hcan : CanonAt m2 R0 := by
    intro i
    by_cases hi : (d0 - d1).toNat ≤ i ∧ i ≤ d0.toNat
    · obtain ⟨v, P, hfe, hP, hPeq, hv⟩ := hent (i - (d0 - d1).toNat) (by omega)
      have e : (d0 - d1).toNat + (i - (d0 - d1).toNat) = i := by omega
      rw [e] at hfe
      exact ⟨v, fun _ => ⟨hfe, by rw [hv]; exact Nat.mod_lt _ hpp⟩⟩
    · refine ⟨c0 i, fun hi13 => ⟨fe_congr (by rw [coefAddr_toNat (by omega)]; omega)
        (fun x h1 h2 => hM2 x (by rw [coefAddr_toNat (by omega)] at h1 h2; omega) (by
          rw [coefAddr_toNat (by omega)] at h1 h2
          unfold InB
          omega)) (hp0 i hi13), hc0 i hi13⟩⟩
  obtain ⟨c2, hp2, hc2⟩ := hcan.poly
  have hc2z : ∀ i, d0.toNat ≤ i → i < 13 → c2 i = 0 := by
    intro i hi hi13
    by_cases he : i = d0.toNat
    · subst he
      exact (hp2 _ hi13).unique hclear
    · have : Fe m2 (coefAddr R0 i) (c0 i) :=
        fe_congr (by rw [coefAddr_toNat (by omega)]; omega)
          (fun x h1 h2 => hM2 x (by rw [coefAddr_toNat (by omega)] at h1 h2; omega) (by
            rw [coefAddr_toNat (by omega)] at h1 h2
            unfold InB
            omega)) (hp0 i hi13)
      rw [(hp2 i hi13).unique this]
      exact hz i (by omega) hi13
  have hcq2 : CanonAt m2 Qb := by
    intro i
    by_cases he : i = (d0 - d1).toNat
    · subst he
      refine ⟨limbsVal [f0, f1, f2, f3], fun _ => ⟨fe_congr hQ64 (fun x h1 h2 => hfr x (by
        rw [hcQ] at h1 h2
        omega)) (fe_set4 hQ64), hflt⟩⟩
    · obtain ⟨cq, hpq, hcq'⟩ := hcq.poly
      refine ⟨cq i, fun hi13 => ⟨fe_congr (by rw [coefAddr_toNat (by omega)]; omega)
        (fun x h1 h2 => ?_) (hpq i hi13), hcq' i hi13⟩⟩
      rw [coefAddr_toNat (by omega)] at h1 h2
      rw [hfr x (by omega)]
      refine set4_other hQ64 ?_
      rw [hcQ]
      omega
  refine WPs.callA_ret (fun v g m3 ffi hret => ?_)
  obtain ⟨hg, hm, hf, d', hv, hdeg⟩ := deg_ret hE hret (A := R0) (nW := 13#64) (c := c2)
    (by lk [hr0]) (eval_const _ _) al0 (by
      have : (13#64 : Word).toNat = 13 := by decide
      omega) hp2
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv
  subst hv
  simp only [restorePanValueFfiLocal]
  refine ⟨_, _, d', rfl, ?_, ?_, ?_, hcq2, c2, hp2, hc2, hdeg, ?_⟩
  · intro x hx
    simp only [restorePanValueLocal, update_lookup]
    split_ifs <;> simp_all
  · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · intro x h0 hq'
    exact hM2 x (by unfold InB at h0; omega) hq'
  · rcases hdeg with ⟨h, -⟩ | ⟨h1, h2, -⟩
    · exact Or.inl h
    · right
      by_contra hge
      exact h2 (hc2z _ (by omega) h1)

end InitECandidate.Solver.GuestBound
