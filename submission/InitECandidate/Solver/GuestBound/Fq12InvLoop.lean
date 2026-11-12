import InitECandidate.Solver.GuestBound.Fq12InvInner
import InitECandidate.Solver.GuestBound.Fns.L4

/-!
# `fq12_inv`: the inner loop

`while d0 >= d1` runs at most 13 rounds: every round lowers the degree of `r0`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' : Word → Option (PanValue Word)}

theorem notLess_eq (d d1 : Word) :
    evalPanCmp .notLess d d1 = if RiscV.signedLess d d1 = true then 0 else 1 := rfl

theorem sless_iff {d d1 : Word} (h1 : d1.toNat < 2 ^ 63) :
    RiscV.signedLess d d1 = true ↔ (2 ^ 63 ≤ d.toNat ∨ d.toNat < d1.toNat) := by
  simp only [RiscV.signedLess, show (2 : Nat) ^ (64 - 1) = 2 ^ 63 from rfl]
  split_ifs <;> simp <;> omega

theorem fqi_ib_cost (hE : GuestEnv E) :
    Costs E FQI_IB 10000000000000000000000000000000000000000 := by
  have h : ∃ B, Costs E FQI_IB B ∧ B ≤ 10000000000000000000000000000000000000000 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

/-- The variant of the inner loop: the degree in `d0`, plus one (0 for -1). -/
def d0Meas (st : St σ) : Nat :=
  match st.locals "d0" with
  | some (.word d) => if d = 0#64 - 1#64 then 0 else d.toNat + 1
  | _ => 0

/-- Invariant of the inner loop, relative to the state `a` at its entry. -/
def InnerI (a : St σ) (R0 Qb : Word) (st : St σ) : Prop :=
  st.globals = a.globals ∧ st.ffi = a.ffi ∧ (∀ x, x ≠ "d0" → st.locals x = a.locals x) ∧
    (∀ x, ¬ InB R0 x → ¬ InB Qb x → st.memory x = a.memory x) ∧ CanonAt st.memory Qb ∧
    ∃ d c, st.locals "d0" = some (.word d) ∧ PolyAt st.memory R0 c 13 ∧
      (∀ i, i < 13 → c i < bnP) ∧ DegRel d c

set_option maxHeartbeats 4000000 in
theorem inner_loop (hE : GuestEnv E) {a : St σ} {R0 R1 Qb d0 d1 l0 l1 l2 l3 : Word}
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
    (hp0 : PolyAt a.memory R0 c0 13) (hc0 : ∀ i, i < 13 → c0 i < bnP) (hdeg : DegRel d0 c0)
    (hp1 : PolyAt a.memory R1 c1 13) (hc1 : ∀ i, i < 13 → c1 i < bnP)
    (hcq : CanonAt a.memory Qb) (hd1r : d1.toNat < 13)
    (hl : limbsVal [l0, l1, l2, l3] < bnP)
    (hl3 : limbsVal [l0, l1, l2, l3] * c1 d1.toNat * 2 ^ 256 % bnP = bnR3 % bnP) :
    WPc E a (.while FQI_IG FQI_IB)
      ((13 + 1) * (expCost FQI_IG + 10000000000000000000000000000000000000000 + 1))
      (fun r => ∃ l mm, r = .normal l a.globals mm a.ffi ∧
        InnerI a R0 Qb ⟨l, a.globals, mm, a.ffi⟩ ∧
        ∃ d, l "d0" = some (.word d) ∧ (d = 0#64 - 1#64 ∨ d.toNat < d1.toNat)) := by
  have hm1 : (0#64 - 1#64 : Word).toNat = 2 ^ 64 - 1 := by decide
  refine WPc.while (I := InnerI a R0 Qb) (μ := d0Meas) 13
    ⟨rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, hcq, d0, c0, hd0, hp0, hc0, hdeg⟩ ?_ ?_ ?_
  · unfold d0Meas
    rw [hd0]
    simp only
    rcases hdeg with ⟨h, -⟩ | ⟨h, -⟩
    · rw [if_pos h]
      omega
    · split_ifs <;> omega
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, hfr, hcqa, d, c, hda, hpa, hca, hdega⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hloc hfr hcqa hda hpa
    subst hg hf
    have hc := eval_cmp_inv hE (op := .notLess) (of_eval (w := d) (by lk [hda]))
      (of_eval (w := d1) (by lk [hloc, hd1])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hnl : ¬ (2 ^ 63 ≤ d.toNat ∨ d.toNat < d1.toNat) := by
      intro hlt
      rw [hc, notLess_eq, if_pos ((sless_iff (by omega)).mpr hlt)] at hw
      simp at hw
    have hdr : d.toNat < 13 ∧ ∀ i, d.toNat < i → i < 13 → c i = 0 := by
      rcases hdega with ⟨h, -⟩ | ⟨h1, -, h3⟩
      · rw [h, hm1] at hnl
        omega
      · exact ⟨h1, h3⟩
    have hp1a : PolyAt ma R1 c1 13 :=
      hp1.frame (by omega) (fun x h1 h2 => hfr x (by unfold InB; omega) (by unfold InB; omega))
    refine WPc.of_costs (fqi_ib_cost hE) (WPs.conseq
      (inner_body hE (a := ⟨la, a.globals, ma, a.ffi⟩) (R0 := R0) (R1 := R1) (Qb := Qb)
        (d0 := d) (d1 := d1) (l0 := l0) (l1 := l1) (l2 := l2) (l3 := l3) (c0 := c) (c1 := c1)
        ((hloc _ (by decide)).trans hr0) ((hloc _ (by decide)).trans hr1)
        ((hloc _ (by decide)).trans hq) hda ((hloc _ (by decide)).trans hd1)
        ((hloc _ (by decide)).trans hlinv) b0 b1 bq al0 s01 s0q s1q hpa hca hp1a hc1
        hcqa (by omega) hdr.1 hdr.2 hl hl3) ?_)
    rintro r ⟨l', m2, d', rfl, hl', hd', hfr', hcq', c', hp', hc', hdeg', hlt⟩
    refine ⟨⟨rfl, rfl, fun x hx => (hl' x hx).trans (hloc x hx),
      fun x h0 hq' => (hfr' x h0 hq').trans (hfr x h0 hq'), hcq', d', c', hd', hp', hc', hdeg'⟩,
      ?_⟩
    show d0Meas ⟨l', a.globals, m2, a.ffi⟩ < d0Meas ⟨la, a.globals, ma, a.ffi⟩
    unfold d0Meas
    simp only [hd', hda]
    have hdne : d ≠ 0#64 - 1#64 := by
      intro h
      rw [h, hm1] at hdr
      omega
    rw [if_neg hdne]
    rcases hlt with h | h
    · rw [if_pos h]
      omega
    · split_ifs <;> omega
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hf, hloc, hfr, hcqa, d, c, hda, hpa, hca, hdega⟩ hcond
    simp only at hg hf hloc hfr hcqa hda hpa
    subst hg hf
    have hc := eval_cmp_inv hE (op := .notLess) (of_eval (w := d) (by lk [hda]))
      (of_eval (w := d1) (by lk [hloc, hd1])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    refine ⟨la, ma, rfl, ⟨rfl, rfl, hloc, hfr, hcqa, d, c, hda, hpa, hca, hdega⟩, d, hda, ?_⟩
    have hsl : RiscV.signedLess d d1 = true := by
      by_contra hn
      rw [notLess_eq, if_neg hn] at hc
      exact absurd hc (by decide)
    rcases (sless_iff (by omega)).mp hsl with h | h
    · rcases hdega with ⟨h', -⟩ | ⟨h', -⟩
      · exact Or.inl h'
      · omega
    · exact Or.inr h

end InitECandidate.Solver.GuestBound
