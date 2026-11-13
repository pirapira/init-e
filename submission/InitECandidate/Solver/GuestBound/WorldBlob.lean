import InitECandidate.Solver.GuestBound.WorldAssn

/-!
# Buffers in the heap

Facts about heap blocks that belong to no structure:

* `WorldTJ.alloc`  – after `alloc`, the new block is a free range;
* `WorldTJ.write_free` – writing inside a free range keeps the world, as long
  as no protected cell (`Rg.Cn`) lies in the written part;
* `WorldTJ.release` – the `heap_mark … heap_release` pattern: if nothing below
  the mark changed, the world at the mark still holds;
* `WorldTJ.weaken` – a smaller registry.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {Rg : Reg} {g g' : VarName → Option (PanValue Word)}
  {m m' : Word → Option (PanValue Word)}

/-- After an allocation `[pv, pv1)`: the world with that block registered as free. -/
theorem WorldTJ.alloc {pv pv1 : Word} (h : WorldTJ Rg g m)
    (hp : g "heap_ptr" = some (.word pv)) (hp1 : g' "heap_ptr" = some (.word pv1))
    (hpH1 : InHeap pv1) (hle : pv.toNat ≤ pv1.toNat)
    (hg : ∀ x, x ≠ "heap_ptr" → g' x = g x) :
    WorldTJ { Rg with B := fun lo hi => Rg.B lo hi ∨ (lo = pv ∧ hi = pv1) } g' m := by
  obtain ⟨pv0, T, N, J, C, n, hp0, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have e : pv0 = pv := by
    rw [hp] at hp0
    simpa using hp0.symm
  subst e
  have hJlo := hW.jrn.lo
  have hJhi := hW.jrn.hi
  refine ⟨pv1, T, N, J, C, n, hp1, hpH1, by rw [hg _ (by decide)]; exact hJg,
    by rw [hg _ (by decide)]; exact hCg, by rw [hg _ (by decide)]; exact hng,
    hW.mono hle hpH1.1, hD, fun lo hi hb => ?_, fun x w hc => ?_, hNd,
    ⟨fun lo hi hI => ⟨(hIm.free lo hi hI).1, (hIm.free lo hi hI).2.mono hle⟩,
      fun lo hi a b hb hI => ?_, hIm.segs, hIm.nib, hIm.kd, hIm.kn, hIm.full,
      fun u hu => ⟨(hIm.trf u hu).1, by
        obtain ⟨hi, e, hf⟩ := (hIm.trf u hu).2
        exact ⟨hi, e, hf.mono hle⟩⟩, hIm.trv,
      fun lo hi u hb hu => by
        rcases hb with hb | ⟨rfl, rfl⟩
        · exact hIm.offT lo hi u hb hu
        · obtain ⟨hi', e, hf⟩ := (hIm.trf u hu).2
          have := hf.hi_
          exact Or.inr (by omega), hIm.offC, hIm.offI, hIm.offTT, hIm.lvk, hIm.lvu, hIm.lvx,
      hIm.lvb, hIm.cvk, hIm.cvu, hIm.cvx, hIm.cvb, hIm.lvc, hIm.sg⟩⟩
  · rcases hb with hb | ⟨rfl, rfl⟩
    · exact (hB lo hi hb).mono hle
    · exact FreeOK.fresh hW (Nat.le_refl _) (Nat.le_refl _) (by omega)
  · obtain ⟨hr, h8, hi, hhi, hf⟩ := hCn x w hc
    exact ⟨hr, h8, hi, hhi, hf.mono hle⟩
  · rcases hb with hb | ⟨rfl, rfl⟩
    · exact hIm.offB lo hi a b hb hI
    · have := (hIm.free a b hI).2.hi_
      exact Or.inr (by omega)

/-- A change confined to a registered free range that holds no protected cell. -/
theorem WorldTJ.write_free {lo hi : Word} (h : WorldTJ Rg g m) (hb : Rg.B lo hi)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → ¬ (lo.toNat ≤ a.toNat ∧ a.toNat < hi.toNat) →
      a.toNat < 2952790016 → m' a = m a)
    (hout : ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m' a = m a)
    (hcn : ∀ x w, Rg.Cn x w → ¬ (lo.toNat ≤ x.toNat ∧ x.toNat < hi.toNat)) :
    WorldTJ Rg g m' := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have hpE := hpH.1
  refine ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng,
    hW.change_free (hB lo hi hb) (fun a h8 hn hlt => hm a h8 hn (by omega)) hout, hD, hB,
    fun x w hc => ?_, hNd, hIm.frame (Nat.le_refl _) (fun x hx => ?_)⟩
  rotate_left
  · obtain ⟨b1, b2, b3⟩ := hIm.cell_bounds hW hx
    refine hm x b1 (fun hin => ?_) (by omega)
    rcases hx with (⟨a, k, hN, hk, hx⟩ | ⟨-, a, b, hI, h1, h2⟩) | ⟨u, hu, hx⟩ | ⟨a, k, hN, hsx⟩
    rotate_right
    · have hin' := hsx.inside (hW.nodes.at_ a k hN)
      rcases (hB lo hi hb).node a k hN with h3 | h3 <;> omega
    · have hin' := seg_cell_in (hW.nodes.at_ a k hN) hk hx
      rcases (hB lo hi hb).node a k hN with h3 | h3 <;> omega
    · rcases hIm.offB lo hi a b hb hI with h3 | h3 <;> omega
    · obtain ⟨-, c1, c2, -⟩ := tr_cell_in hIm hu hx
      rcases hIm.offT lo hi u hb hu with h3 | h3 <;> omega
  obtain ⟨hr, h8, hi', hhi', hf⟩ := hCn x w hc
  refine ⟨?_, h8, hi', hhi', hf⟩
  unfold Rd at hr ⊢
  rw [hm x h8 (hcn x w hc) (by have := hf.hi_; omega)]
  exact hr

/-- The world at a heap mark, after temporary allocations above it were
dropped: nothing below the mark changed and the heap pointer is back. -/
theorem WorldTJ.release {pv : Word} (h : WorldTJ Rg g m)
    (hp : g "heap_ptr" = some (.word pv)) (hp' : g' "heap_ptr" = some (.word pv))
    (hg : ∀ x, x ≠ "heap_ptr" → g' x = g x)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → HBASE ≤ a.toNat → a.toNat < pv.toNat → m' a = m a) :
    WorldTJ Rg g' m' := by
  obtain ⟨pv0, T, N, J, C, n, hp0, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have e : pv0 = pv := by
    rw [hp] at hp0
    simpa using hp0.symm
  subst e
  refine ⟨pv0, T, N, J, C, n, hp', hpH, by rw [hg _ (by decide)]; exact hJg,
    by rw [hg _ (by decide)]; exact hCg, by rw [hg _ (by decide)]; exact hng, hW.frame hm, hD,
    hB, fun x w hc => ?_, hNd, hIm.frame (Nat.le_refl _) (fun x hx => by
      obtain ⟨b1, b2, b3⟩ := hIm.cell_bounds hW hx
      exact hm x b1 b2 b3)⟩
  obtain ⟨hr, h8, hi, hhi, hf⟩ := hCn x w hc
  refine ⟨?_, h8, hi, hhi, hf⟩
  unfold Rd at hr ⊢
  rw [hm x h8 hf.lo_ (by have := hf.hi_; omega)]
  exact hr

/-- A smaller registry. -/
theorem WorldTJ.weaken {Rg' : Reg} (h : WorldTJ Rg g m) (hD : ∀ t kl, Rg'.D t kl → Rg.D t kl)
    (hB : ∀ lo hi, Rg'.B lo hi → Rg.B lo hi) (hC : ∀ x w, Rg'.Cn x w → Rg.Cn x w)
    (hN : ∀ a, Rg'.Nd a → Rg.Nd a) (hI : Rg'.Im = Rg.Im)
    (hK : ∀ a k, Rg'.Kd a k → Rg.Kd a k ∧ Rg'.Nd a) (hK2 : ∀ a k, Rg.Kd a k → Rg'.Kd a k)
    (hT : ∀ t, Rg'.Tr t → Rg.Tr t) (hL : Rg'.Lv = Rg.Lv) (hV : Rg'.Cv = Rg.Cv)
    (hS : ∀ a sp nl, Rg'.Sg a sp nl → Rg.Sg a sp nl) :
    WorldTJ Rg' g m := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hDT, hBT, hCT, hNT, hIT⟩ := h
  exact ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, fun t kl ht => hDT t kl (hD t kl ht),
    fun lo hi hb => hBT lo hi (hB lo hi hb), fun x w hc => hCT x w (hC x w hc),
    fun a ha => hNT a (hN a ha),
    ⟨fun lo hi h => hIT.free lo hi (hI ▸ h), fun lo hi a b hb h => hIT.offB lo hi a b (hB lo hi hb)
      (hI ▸ h), by rw [hI]; exact hIT.segs, fun lo hi h => hIT.nib lo hi (hI ▸ h),
      fun a k h => hIT.kd a k (hK a k h).1, fun a k h => (hK a k h).2,
      fun a k h => hK2 a k (hIT.full a k h), fun u hu => hIT.trf u (hT u hu),
      fun u hu => by
        obtain ⟨root, sec, r1, r2, hc, hl0⟩ := hIT.trv u (hT u hu)
        exact ⟨root, sec, r1, r2, hc, by rw [hL]; exact hl0⟩,
      fun lo hi u hb hu => hIT.offT lo hi u (hB lo hi hb) (hT u hu),
      fun x w u hc hu => hIT.offC x w u (hC x w hc) (hT u hu),
      fun lo hi u h hu => hIT.offI lo hi u (hI ▸ h) (hT u hu),
      fun t u ht hu => hIT.offTT t u (hT t ht) (hT u hu),
      fun a ℓ h => hIT.lvk a ℓ (hL ▸ h), fun a ℓ ℓ' h h' => hIT.lvu a ℓ ℓ' (hL ▸ h) (hL ▸ h'),
      by unfold LvX; rw [hL, hV]; exact hIT.lvx, by unfold LvB; rw [hL, hV]; exact hIT.lvb,
      fun a ℓc h => hIT.cvk a ℓc (hV ▸ h), fun a x y h h' => hIT.cvu a x y (hV ▸ h) (hV ▸ h'),
      by unfold CvX; rw [hL, hV]; exact hIT.cvx,
      fun a ℓ ℓc h h' => hIT.cvb a ℓ ℓc (hL ▸ h) (hV ▸ h'),
      fun a ℓ k h hN hk => by rw [hV]; exact hIT.lvc a ℓ k (hL ▸ h) hN hk,
      fun a sp nl h => hIT.sg a sp nl (hS a sp nl h)⟩⟩

/-- A protected cell can be read. -/
theorem WorldTJ.cell {x w : Word} (h : WorldTJ Rg g m) (hc : Rg.Cn x w) : Rd m x w := by
  obtain ⟨pv, T, N, J, C, n, -, -, -, -, -, -, -, -, hCT, -, -⟩ := h
  exact (hCT x w hc).1

end InitECandidate.Solver.GuestBound
