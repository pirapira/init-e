import InitECandidate.Solver.GuestBound.TrieHandle

/-!
# A fresh immutable nibble block

`WorldTJ.fresh_nibs`: after an allocation `[pv, pv1)` and writes confined to
it that leave nibbles in `[pv, hi')`, the world invariant holds with
`[pv, hi')` registered as an immutable block. The writable blocks of the
registry are unchanged, so the result is a `Reg.Le` extension.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {Rg : Reg} {g g' : VarName → Option (PanValue Word)}
  {m m' : Word → Option (PanValue Word)}

/-- The registry with one more immutable block. -/
def Reg.addIm (Rg : Reg) (lo hi : Word) : Reg :=
  { Rg with Im := fun a b => Rg.Im a b ∨ (a = lo ∧ b = hi) }

theorem Reg.Le.addIm (Rg : Reg) (lo hi : Word) : Rg.Le (Rg.addIm lo hi) :=
  ⟨rfl, rfl, rfl, fun _ _ h => Or.inl h, fun _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h⟩

theorem WorldTJ.fresh_nibs {pv pv1 hi' : Word} (h : WorldTJ Rg g m)
    (hp : g "heap_ptr" = some (.word pv)) (hp1 : g' "heap_ptr" = some (.word pv1))
    (hpH1 : InHeap pv1) (hle : pv.toNat ≤ pv1.toNat)
    (hg : ∀ x, x ≠ "heap_ptr" → g' x = g x)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → a.toNat < pv.toNat → m' a = m a)
    (hout : ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m' a = m a)
    (hhi : hi'.toNat ≤ pv1.toNat) (hnib : Nibs m' pv (hi'.toNat - pv.toNat)) :
    WorldTJ (Rg.addIm pv hi') g' m' := by
  obtain ⟨pv0, T, N, J, C, n, hp0, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have e : pv0 = pv := by
    rw [hp] at hp0
    simpa using hp0.symm
  subst e
  have hpE := hpH.1
  have hpE1 := hpH1.1
  have hJlo := hW.jrn.lo
  have hJhi := hW.jrn.hi
  have hbase : HBASE ≤ pv0.toNat := by omega
  have hW1 : HeapW m' pv1 T N J C n :=
    (hW.frame (fun a h8 _ hlt => hm a h8 hlt)).mono hle hpE1
  have hI1 : ImOK Rg m' pv1 T N J C := hIm.frame hle (fun x hx => by
    obtain ⟨b1, b2, b3⟩ := hIm.cell_bounds hW hx
    exact hm x b1 b3)
  refine ⟨pv1, T, N, J, C, n, hp1, hpH1, by rw [hg _ (by decide)]; exact hJg,
    by rw [hg _ (by decide)]; exact hCg, by rw [hg _ (by decide)]; exact hng, hW1, hD,
    fun lo hi hb => (hB lo hi hb).mono hle, fun x w hc => ?_, hNd,
    { hI1 with
      free := fun a b hI => ?_
      offB := fun lo hi a b hb hI => ?_
      segs := hI1.segs.mono (fun a b hI => Or.inl hI)
      nib := fun a b hI => ?_
      offI := fun a b t hI ht => ?_ }⟩
  · obtain ⟨hr, h8, hi, hhi', hf⟩ := hCn x w hc
    refine ⟨?_, h8, hi, hhi', hf.mono hle⟩
    have := hf.hi_
    unfold Rd at hr ⊢
    rw [hm x h8 (by omega)]
    exact hr
  · rcases hI with hI | ⟨rfl, rfl⟩
    · exact hI1.free a b hI
    · exact ⟨hpH.2, FreeOK.fresh hW (Nat.le_refl _) hhi hbase⟩
  · rcases hI with hI | ⟨rfl, rfl⟩
    · exact hI1.offB lo hi a b hb hI
    · have := (hB lo hi hb).hi_
      exact Or.inl this
  · rcases hI with hI | ⟨rfl, rfl⟩
    · exact hI1.nib a b hI
    · exact hnib
  · rcases hI with hI | ⟨rfl, rfl⟩
    · exact hI1.offI a b t hI ht
    · obtain ⟨-, hi, e, hf⟩ := hIm.trf t ht
      have := hf.hi_
      exact Or.inr (by omega)

end InitECandidate.Solver.GuestBound
