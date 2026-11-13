import InitECandidate.Solver.GuestBound.TrieLoop

/-!
# Trie handles

A handle (`mpt_new`) is 16 bytes: the root pointer at `+0` and the `secured`
flag at `+8`. `Rg.Tr t` registers one; the root pointer is null or a
registered node in every invariant state (`WorldTJ.root`), may be replaced by
null or a registered node (`WorldTJ.set_root`), and a freshly written block
becomes a handle with `WorldTJ.add_handle`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {Rg : Reg} {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}

/-- The root of a registered handle. -/
theorem WorldTJ.root {t : Word} (h : WorldTJ Rg g m) (ht : Rg.Tr t) :
    ∃ root sec : Word, Rd m t root ∧ Rd m (t + 8#64) sec ∧ (root = 0#64 ∨ ∃ k, Rg.Kd root k) ∧
      HBASE ≤ t.toNat ∧ t.toNat + 16 ≤ 2952790016 ∧ t.toNat % 8 = 0 ∧
      (root ≠ 0#64 → Rg.Lv root 0) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  obtain ⟨root, sec, r1, r2, hc, hl0⟩ := hIm.trv t ht
  obtain ⟨h8, hi, e, hf⟩ := hIm.trf t ht
  have := hf.lo_
  have := hf.hi_
  have := hpH.1
  refine ⟨root, sec, r1, r2, ?_, by omega, by omega, h8, hl0⟩
  rcases hc with rfl | ⟨j, hj⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨j, hIm.full root j hj⟩

/-- Replacing the root of a handle by null or a registered node. -/
theorem WorldTJ.set_root {t c : Word} (h : WorldTJ Rg g m) (ht : Rg.Tr t)
    (hc : c = 0#64 ∨ Rg.Nd c) (hl0 : c ≠ 0#64 → Rg.Lv c 0) : WorldTJ Rg g (setCell m t c) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  obtain ⟨h8, hi, e, hf⟩ := hIm.trf t ht
  have hflo := hf.lo_
  have hfhi := hf.hi_
  have hpE := hpH.1
  have hseg : ∀ x, SegCell Rg.Im N x → setCell m t c x = m x := by
    intro x hx
    refine setCell_ne _ ?_
    rintro rfl
    rcases hx with ⟨a, k, hN, hk, hx⟩ | ⟨-, lo, hi', hI, h1, h2⟩
    · have hin := seg_cell_in (hW.nodes.at_ a k hN) hk hx
      rcases hf.node a k hN with h3 | h3 <;> omega
    · rcases hIm.offI lo hi' x hI ht with h3 | h3 <;> omega
  have hlv : ∀ x, LvCell N x → setCell m t c x = m x := by
    rintro x ⟨a, k, hN, hsx⟩
    refine setCell_ne _ ?_
    rintro rfl
    have hin := hsx.inside (hW.nodes.at_ a k hN)
    rcases hf.node a k hN with h3 | h3 <;> omega
  refine ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng,
    hW.change_free hf (fun a _ hn _ => setCell_ne _ (NE (by omega)))
      (fun a ha => setCell_ne _ (NE (by unfold HBASE at ha hflo; omega))), hD, hB,
    fun x w hcn => ?_, hNd,
    ⟨hIm.free, hIm.offB, hIm.segs.frame hseg,
      nib_frame (fun lo hi hI => (hIm.free lo hi hI).1) hIm.nib hseg, hIm.kd, hIm.kn, hIm.full,
      hIm.trf, fun u hu => ?_, hIm.offT, hIm.offC, hIm.offI, hIm.offTT, hIm.lvk, hIm.lvu,
      hIm.lvx.frame hlv, hIm.lvb.frame hlv, hIm.cvk, hIm.cvu, hIm.cvx.frame hlv, hIm.cvb,
      hIm.lvc, hIm.sg.frame hseg⟩⟩
  · obtain ⟨hr, hx8, hi', hhi', hf'⟩ := hCn x w hcn
    refine ⟨hr.frame _ (NE ?_), hx8, hi', hhi', hf'⟩
    rcases hIm.offC x w t hcn ht with h3 | h3 <;> omega
  · obtain ⟨root, sec, r1, r2, hch⟩ := hIm.trv u hu
    obtain ⟨-, hiu, eu, hfu⟩ := hIm.trf u hu
    have hfuhi := hfu.hi_
    have e8u : (u + 8#64).toNat = u.toNat + 8 := by
      rw [BitVec.toNat_add, show (8#64 : Word).toNat = 8 by decide]
      omega
    by_cases e' : u = t
    · subst e'
      refine ⟨c, sec, Rd.here m u c, r2.frame _ (NE (by omega)), ?_, hl0⟩
      rcases hc with rfl | hc
      · exact Or.inl rfl
      · exact Or.inr (hNd c hc)
    · rcases hIm.offTT u t hu ht with hd | hd
      · exact absurd hd e'
      · exact ⟨root, sec, r1.frame _ (NE (by omega)), r2.frame _ (NE (by omega)), hch⟩

/-- The registry with a handle at `[lo, hi)`; writable blocks overlapping it are dropped. -/
def Reg.addTr (Rg : Reg) (lo hi : Word) : Reg :=
  { Rg with
    B := fun a b => Rg.B a b ∧ (b.toNat ≤ lo.toNat ∨ hi.toNat ≤ a.toNat)
    Tr := fun t => Rg.Tr t ∨ t = lo }

/-- A written 16-byte block becomes a handle. -/
theorem WorldTJ.add_handle {lo hi root sec : Word} (h : WorldTJ Rg g m) (hb : Rg.B lo hi)
    (h8 : lo.toNat % 8 = 0) (hhi : hi.toNat = lo.toNat + 16) (r1 : Rd m lo root)
    (r2 : Rd m (lo + 8#64) sec) (hc : root = 0#64 ∨ Rg.Nd root)
    (hl0 : root ≠ 0#64 → Rg.Lv root 0)
    (hcn : ∀ x w, Rg.Cn x w → ¬ (lo.toNat ≤ x.toNat ∧ x.toNat < hi.toNat)) :
    WorldTJ (Rg.addTr lo hi) g m := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  refine ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, fun a b hab => hB a b hab.1, hCn,
    hNd, ⟨hIm.free, fun a b c d hab hI => hIm.offB a b c d hab.1 hI, hIm.segs, hIm.nib, hIm.kd,
      hIm.kn, hIm.full, fun u hu => ?_, fun u hu => ?_, fun a b u hab hu => ?_,
      fun x w u hcx hu => ?_, fun a b u hI hu => ?_, fun t u ht hu => ?_, hIm.lvk, hIm.lvu,
      hIm.lvx, hIm.lvb, hIm.cvk, hIm.cvu, hIm.cvx, hIm.cvb, hIm.lvc, hIm.sg⟩⟩
  · rcases hu with hu | rfl
    · exact hIm.trf u hu
    · exact ⟨h8, hi, hhi, hB _ _ hb⟩
  · rcases hu with hu | rfl
    · exact hIm.trv u hu
    · refine ⟨root, sec, r1, r2, ?_, hl0⟩
      rcases hc with rfl | hc
      · exact Or.inl rfl
      · exact Or.inr (hNd root hc)
  · rcases hu with hu | rfl
    · exact hIm.offT a b u hab.1 hu
    · rcases hab.2 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by omega)
  · rcases hu with hu | rfl
    · exact hIm.offC x w u hcx hu
    · have hx8 := (hCn x w hcx).2.1
      have := hcn x w hcx
      by_cases hlt : x.toNat < u.toNat
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  · rcases hu with hu | rfl
    · exact hIm.offI a b u hI hu
    · rcases hIm.offB _ _ a b hb hI with h1 | h1
      · exact Or.inr (by omega)
      · exact Or.inl h1
  · rcases ht with ht | rfl
    · rcases hu with hu | rfl
      · exact hIm.offTT t u ht hu
      · rcases hIm.offT _ _ t hb ht with h1 | h1
        · exact Or.inr (Or.inr (by omega))
        · exact Or.inr (Or.inl h1)
    · rcases hu with hu | rfl
      · rcases hIm.offT _ _ u hb hu with h1 | h1
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr h1)
      · exact Or.inl rfl

end InitECandidate.Solver.GuestBound
