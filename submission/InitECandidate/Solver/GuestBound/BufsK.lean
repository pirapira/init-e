import InitECandidate.Solver.GuestBound.Miller

/-!
# The buffer invariant for any field size

`BufsK K` is `Bufs` with buffers of `K` coefficients (`32 * K` bytes), for the
point code on `Fq` (`K = 1`) and `Fq2` (`K = 2`) that `bn254_pairing_check`
runs before entering `Fq12`. Same lemmas and step rules as in `FeBufs.lean`
(issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word} {K : Nat}

structure BufsK (K : Nat) (pv0 : Word) (m0 : Word → Option (PanValue Word)) (Wr : List Word) (hp : Word)
    (All Cn : List Word) (m : Word → Option (PanValue Word)) : Prop where
  hpb : hp.toNat ≤ 2952790016
  hpa : hp.toNat % 8 = 0
  ple : pv0.toNat ≤ hp.toNat
  geo : ∀ B ∈ All, B.toNat % 8 = 0 ∧ B.toNat + 32 * K ≤ hp.toNat
  sep : ∀ B ∈ All, ∀ C ∈ All, B = C ∨ B.toNat + 32 * K ≤ C.toNat ∨ C.toNat + 32 * K ≤ B.toNat
  sub : ∀ B ∈ Cn, B ∈ All
  can : ∀ B ∈ Cn, CanonN m B K
  low : ∀ x : Word, x.toNat < pv0.toNat →
    (∀ B ∈ Wr, x.toNat < B.toNat ∨ B.toNat + 32 * K ≤ x.toNat) → m x = m0 x

/-- A write into `D` that leaves the rest below `hp` alone and makes `D` canonical. -/
theorem BufsK.write {pv0 hp D : Word} {All Cn : List Word} (h : BufsK K pv0 m0 Wr hp All Cn m)
    (hD : D ∈ All) (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr)
    (hfr : ∀ x : Word, x.toNat < hp.toNat → (x.toNat < D.toNat ∨ D.toNat + 32 * K ≤ x.toNat) →
      m' x = m x) (hc : CanonN m' D K) : BufsK K pv0 m0 Wr hp All (D :: Cn) m' := by
  refine ⟨h.hpb, h.hpa, h.ple, h.geo, h.sep, ?_, ?_, ?_⟩
  · intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact hD
    · exact h.sub B hB
  · intro B hB
    by_cases hBD : B = D
    · rw [hBD]; exact hc
    · have hB' : B ∈ Cn := by
        rcases List.mem_cons.mp hB with rfl | hB
        · exact absurd rfl hBD
        · exact hB
      have hBA := h.sub B hB'
      have hg := h.geo B hBA
      rcases h.sep B hBA D hD with heq | hdis
      · exact absurd heq hBD
      · exact (h.can B hB').frame (by have := h.hpb; omega)
          (fun x h1 h2 => hfr x (by omega) (by omega))
  · intro x hx hW
    have hxD : x.toNat < D.toNat ∨ D.toNat + 32 * K ≤ x.toNat := by
      rcases hDl with hl | hw
      · exact Or.inl (by omega)
      · exact hW D hw
    rw [hfr x (by have := h.ple; omega) hxD]
    exact h.low x hx hW

/-- A fresh block at the old heap pointer joins `All`. -/
theorem BufsK.alloc {pv0 hp hp' : Word} {All Cn : List Word} (h : BufsK K pv0 m0 Wr hp All Cn m)
    (hle : hp.toNat + 32 * K ≤ hp'.toNat) (hb : hp'.toNat ≤ 2952790016)
    (ha' : hp'.toNat % 8 = 0) : BufsK K pv0 m0 Wr hp' (hp :: All) Cn m := by
  have hal := h.hpa
  have hpl := h.ple
  refine ⟨hb, ha', by omega, ?_, ?_, fun B hB => List.mem_cons_of_mem _ (h.sub B hB), h.can, h.low⟩
  · intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact ⟨hal, hle⟩
    · have := h.geo B hB
      exact ⟨this.1, by omega⟩
  · intro B hB C hC
    rcases List.mem_cons.mp hB with hB0 | hB1
    · rcases List.mem_cons.mp hC with hC0 | hC1
      · exact Or.inl (hB0.trans hC0.symm)
      · rw [hB0]
        exact Or.inr (Or.inr (h.geo C hC1).2)
    · rcases List.mem_cons.mp hC with hC0 | hC1
      · rw [hC0]
        exact Or.inr (Or.inl (h.geo B hB1).2)
      · exact h.sep B hB1 C hC1

theorem BufsK.mono {pv0 hp : Word} {All Cn Cn' : List Word} (h : BufsK K pv0 m0 Wr hp All Cn m)
    (hsub : ∀ B ∈ Cn', B ∈ Cn) : BufsK K pv0 m0 Wr hp All Cn' m :=
  ⟨h.hpb, h.hpa, h.ple, h.geo, h.sep, fun B hB => h.sub B (hsub B hB), fun B hB => h.can B (hsub B hB), h.low⟩

/-- Back to the caller's view: its buffers and heap pointer, with whatever the
callee made canonical among them. -/
theorem BufsK.restrict {pv0 hp hp' : Word} {All All' Cn Cn' Cn2 : List Word}
    (h0 : BufsK K pv0 m0 Wr hp All Cn m) (h1 : BufsK K pv0 m0 Wr hp' All' Cn' m')
    (hsub : ∀ B ∈ Cn2, B ∈ All ∧ B ∈ Cn') : BufsK K pv0 m0 Wr hp All Cn2 m' :=
  ⟨h0.hpb, h0.hpa, h0.ple, h0.geo, h0.sep, fun B hB => (hsub B hB).1,
    fun B hB => h1.can B (hsub B hB).2, h1.low⟩


/-- Several writes at once: the buffers of `Ds` become canonical, everything
else below `hp` outside them is untouched. -/
theorem BufsK.writeSet {pv0 hp : Word} {All Cn Ds : List Word} (h : BufsK K pv0 m0 Wr hp All Cn m)
    (hD : ∀ D ∈ Ds, D ∈ All ∧ (pv0.toNat ≤ D.toNat ∨ D ∈ Wr))
    (hfr : ∀ x : Word, x.toNat < hp.toNat →
      (∀ D ∈ Ds, x.toNat < D.toNat ∨ D.toNat + 32 * K ≤ x.toNat) → m' x = m x)
    (hc : ∀ D ∈ Ds, CanonN m' D K) : BufsK K pv0 m0 Wr hp All (Ds ++ Cn) m' := by
  refine ⟨h.hpb, h.hpa, h.ple, h.geo, h.sep, ?_, ?_, ?_⟩
  · intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact (hD B hB).1
    · exact h.sub B hB
  · intro B hB
    by_cases hBD : B ∈ Ds
    · exact hc B hBD
    · have hB' : B ∈ Cn := by
        rcases List.mem_append.mp hB with hB | hB
        · exact absurd hB hBD
        · exact hB
      have hBA := h.sub B hB'
      have hg := h.geo B hBA
      refine (h.can B hB').frame (by have := h.hpb; omega) (fun x h1 h2 => hfr x (by omega) ?_)
      intro D hDs
      rcases h.sep B hBA D (hD D hDs).1 with heq | hdis
      · exact absurd (heq ▸ hDs) hBD
      · omega
  · intro x hx hW
    rw [hfr x (by have := h.ple; omega) (fun D hDs => ?_)]
    · exact h.low x hx hW
    · rcases (hD D hDs).2 with hl | hw
      · exact Or.inl (by omega)
      · exact hW D hw


end InitECandidate.Solver.GuestBound
