import InitECandidate.Solver.GuestBound.TrieFresh
import InitECandidate.Solver.GuestBound.TrieDelPush

/-!
# Freezing freshly written cells

`Reg.Cn x w` says that the aligned cell `x` holds the word `w` and that no
registered structure covers it, so every world-preserving step keeps its
content.  The registry order `Reg.Le` lets the set of such cells grow, and
`WorldTJ.fresh_cn` registers the aligned cells of a block that was allocated at
the heap pointer and filled.  This is the mechanism for data that must not
change later: value bytes of leaves, slice arrays, encoded buffers.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {Rg : Reg} {g g' : VarName → Option (PanValue Word)}
  {m m' : Word → Option (PanValue Word)}

/-- The registry with the aligned cells of `[lo, hi)` frozen at their content in `m'`. -/
def Reg.addCn (Rg : Reg) (lo hi : Word) (m' : Word → Option (PanValue Word)) : Reg :=
  { Rg with Cn := fun x w => Rg.Cn x w ∨
      (lo.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ hi.toNat ∧ x.toNat % 8 = 0 ∧ Rd m' x w) }

theorem Reg.Le.addCn (Rg : Reg) (lo hi : Word) (m' : Word → Option (PanValue Word)) :
    Rg.Le (Rg.addCn lo hi m') :=
  ⟨rfl, rfl, fun _ _ h => Or.inl h, fun _ _ h => h, fun _ h => h, fun _ _ h => h,
    fun _ _ h => h, fun _ _ h => h, fun _ _ _ h => h, fun _ h => h⟩

/-- A block allocated at the heap pointer and filled: its aligned cells are frozen. -/
theorem WorldTJ.fresh_cn {pv pv1 hi' : Word} (h : WorldTJ Rg g m)
    (hp : g "heap_ptr" = some (.word pv)) (hp1 : g' "heap_ptr" = some (.word pv1))
    (hpH1 : InHeap pv1) (hle : pv.toNat ≤ pv1.toNat)
    (hg : ∀ x, x ≠ "heap_ptr" → g' x = g x)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → a.toNat < pv.toNat → m' a = m a)
    (hout : ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m' a = m a)
    (hhi : hi'.toNat ≤ pv1.toNat) :
    WorldTJ (Rg.addCn pv hi' m') g' m' := by
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
      offC := fun x w t hc ht => ?_ }⟩
  · rcases hc with hc | ⟨a1, a2, a3, hr⟩
    · obtain ⟨hr, h8, hi, hhi', hf⟩ := hCn x w hc
      refine ⟨?_, h8, hi, hhi', hf.mono hle⟩
      have := hf.hi_
      unfold Rd at hr ⊢
      rw [hm x h8 (by omega)]
      exact hr
    · have hx8 : (x + 8#64).toNat = x.toNat + 8 := by
        rw [BitVec.toNat_add, show (8#64 : Word).toNat = 8 from rfl]
        omega
      exact ⟨hr, a3, x + 8#64, hx8, FreeOK.fresh hW a1 (by omega) (by omega)⟩
  · rcases hc with hc | ⟨a1, a2, a3, hr⟩
    · exact hI1.offC x w t hc ht
    · obtain ⟨-, hi, e, hf⟩ := hIm.trf t ht
      have := hf.hi_
      exact Or.inr (by omega)

/-- A frozen cell keeps its content along the registry order. -/
theorem WorldTJ.cn_rd {Rg' : Reg} {x w : Word} (hle : Rg.Le Rg') (h : WorldTJ Rg' g m)
    (hc : Rg.Cn x w) : Rd m x w :=
  h.cell (hle.Cn x w hc)

end InitECandidate.Solver.GuestBound

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {Rg : Reg} {g g' : VarName → Option (PanValue Word)}
  {m m' : Word → Option (PanValue Word)}

/-- The heap pointer moved up and nothing below the old pointer changed: the world is kept,
whatever was written above it (unregistered allocations, the scratch arena). -/
theorem WorldTJ.grow {pv pv1 : Word} (h : WorldTJ Rg g m)
    (hp : g "heap_ptr" = some (.word pv)) (hp1 : g' "heap_ptr" = some (.word pv1))
    (hpH1 : InHeap pv1) (hle : pv.toNat ≤ pv1.toNat)
    (hg : ∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g' x = g x)
    (hm : ∀ a : Word, a.toNat < pv.toNat → m' a = m a) :
    WorldTJ Rg g' m' := by
  classical
  -- first the scratch arena and the scratch pointer, then the heap above the old pointer
  let ms : Word → Option (PanValue Word) := fun a => if a.toNat < 2952790016 then m a else m' a
  let gs : VarName → Option (PanValue Word) := fun x => if x = "scratch_ptr" then g' x else g x
  have hpv : pv.toNat ≤ 2952790016 := by
    obtain ⟨pv0, T, N, J, C, n, hp0, hpH, -⟩ := h
    rw [hp] at hp0
    simp only [Option.some.injEq, PanValue.word.injEq] at hp0
    subst hp0
    exact hpH.1
  have hWs : WorldTJ Rg gs ms :=
    h.scratch (fun x hx => if_neg hx) (fun a ha => if_pos ha)
  obtain ⟨pv0, T, N, J, C, n, hp0, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := hWs
  have e : pv0 = pv := by
    have : gs "heap_ptr" = g "heap_ptr" := if_neg (by decide)
    rw [this, hp] at hp0
    simpa using hp0.symm
  subst e
  have hpE1 := hpH1.1
  have hms : ∀ a : Word, a.toNat < pv0.toNat → m' a = ms a := fun a ha => by
    show m' a = if a.toNat < 2952790016 then m a else m' a
    rw [if_pos (by omega)]
    exact hm a ha
  have hgs : ∀ x, x ≠ "heap_ptr" → g' x = gs x := fun x hx => by
    show g' x = if x = "scratch_ptr" then g' x else g x
    by_cases hs : x = "scratch_ptr"
    · rw [if_pos hs]
    · rw [if_neg hs]
      exact hg x hx hs
  have hW1 : HeapW m' pv1 T N J C n :=
    (hW.frame (fun a h8 _ hlt => hms a hlt)).mono hle hpE1
  have hI1 : ImOK Rg m' pv1 T N J C := hIm.frame hle (fun x hx => by
    obtain ⟨b1, b2, b3⟩ := hIm.cell_bounds hW hx
    exact hms x b3)
  refine ⟨pv1, T, N, J, C, n, hp1, hpH1, by rw [hgs _ (by decide)]; exact hJg,
    by rw [hgs _ (by decide)]; exact hCg, by rw [hgs _ (by decide)]; exact hng, hW1, hD,
    fun lo hi hb => (hB lo hi hb).mono hle, fun x w hc => ?_, hNd, hI1⟩
  obtain ⟨hr, h8, hi, hhi', hf⟩ := hCn x w hc
  refine ⟨?_, h8, hi, hhi', hf.mono hle⟩
  have := hf.hi_
  unfold Rd at hr ⊢
  rw [hms x (by omega)]
  exact hr

end InitECandidate.Solver.GuestBound
