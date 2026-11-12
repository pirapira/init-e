import InitECandidate.Solver.GuestBound.WorldAssn

/-!
# Buffers in the heap

Three facts about heap blocks that belong to no structure:

* `WorldTJ.alloc`  – after `alloc`, the new block is a free range;
* `WorldTJ.write_free` – writing inside a free range keeps the world;
* `WorldTJ.release` – the `heap_mark … heap_release` pattern: if nothing below
  the mark changed, the world at the mark still holds.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {D : Word → Prop} {B : Word → Word → Prop}
  {g g' : VarName → Option (PanValue Word)} {m m' : Word → Option (PanValue Word)}

/-- After an allocation `[pv, pv1)`: the world with that block registered as free. -/
theorem WorldTJ.alloc {pv pv1 : Word} (h : WorldTJ D B g m)
    (hp : g "heap_ptr" = some (.word pv)) (hp1 : g' "heap_ptr" = some (.word pv1))
    (hpH1 : InHeap pv1) (hle : pv.toNat ≤ pv1.toNat)
    (hg : ∀ x, x ≠ "heap_ptr" → g' x = g x) :
    WorldTJ D (fun lo hi => B lo hi ∨ (lo = pv ∧ hi = pv1)) g' m := by
  obtain ⟨pv0, T, N, J, C, n, hp0, hpH, hJg, hCg, hng, hW, hD, hB⟩ := h
  have e : pv0 = pv := by
    rw [hp] at hp0
    simpa using hp0.symm
  subst e
  have hJlo := hW.jrn.lo
  have hJhi := hW.jrn.hi
  refine ⟨pv1, T, N, J, C, n, hp1, hpH1, by rw [hg _ (by decide)]; exact hJg,
    by rw [hg _ (by decide)]; exact hCg, by rw [hg _ (by decide)]; exact hng,
    hW.mono hle hpH1.1, hD, fun lo hi hb => ?_⟩
  rcases hb with hb | ⟨rfl, rfl⟩
  · exact (hB lo hi hb).mono hle
  · exact FreeOK.fresh hW (Nat.le_refl _) (Nat.le_refl _) (by omega)

/-- A change confined to a registered free range. -/
theorem WorldTJ.write_free {lo hi : Word} (h : WorldTJ D B g m) (hb : B lo hi)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → ¬ (lo.toNat ≤ a.toNat ∧ a.toNat < hi.toNat) →
      a.toNat < 2952790016 → m' a = m a)
    (hout : ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m' a = m a) :
    WorldTJ D B g m' := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB⟩ := h
  have hpE := hpH.1
  exact ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng,
    hW.change_free (hB lo hi hb) (fun a h8 hn hlt => hm a h8 hn (by omega)) hout, hD, hB⟩

/-- The world at a heap mark, after temporary allocations above it were
dropped: nothing below the mark changed and the heap pointer is back. -/
theorem WorldTJ.release {pv : Word} (h : WorldTJ D B g m)
    (hp : g "heap_ptr" = some (.word pv)) (hp' : g' "heap_ptr" = some (.word pv))
    (hg : ∀ x, x ≠ "heap_ptr" → g' x = g x)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → HBASE ≤ a.toNat → a.toNat < pv.toNat → m' a = m a) :
    WorldTJ D B g' m' := by
  obtain ⟨pv0, T, N, J, C, n, hp0, hpH, hJg, hCg, hng, hW, hD, hB⟩ := h
  have e : pv0 = pv := by
    rw [hp] at hp0
    simpa using hp0.symm
  subst e
  exact ⟨pv0, T, N, J, C, n, hp', hpH, by rw [hg _ (by decide)]; exact hJg,
    by rw [hg _ (by decide)]; exact hCg, by rw [hg _ (by decide)]; exact hng, hW.frame hm, hD,
    hB⟩

/-- Fewer registered tables and free ranges. -/
theorem WorldTJ.weaken {D' : Word → Prop} {B' : Word → Word → Prop} (h : WorldTJ D B g m)
    (hD : ∀ t, D' t → D t) (hB : ∀ lo hi, B' lo hi → B lo hi) : WorldTJ D' B' g m := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hDT, hBT⟩ := h
  exact ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, fun t ht => hDT t (hD t ht),
    fun lo hi hb => hBT lo hi (hB lo hi hb)⟩

end InitECandidate.Solver.GuestBound
