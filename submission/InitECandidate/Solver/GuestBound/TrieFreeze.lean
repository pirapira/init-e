import InitECandidate.Solver.GuestBound.WorldNode

/-!
# Freezing a buffer into an immutable block, and reading a node's segment

`Reg.freeze lo hi hi'` moves the prefix `[lo, hi')` of the writable block
`[lo, hi)` to the immutable blocks, dropping every writable block that
overlaps `[lo, hi)`. Immutable blocks consist of nibbles (`WorldTJ.im_nibs`). `WorldTJ.freeze`: the
world invariant is kept. After freezing, nibble arrays written into the block
can be handed to `node_new_leaf` / `node_new_ext` (`ImOK.node_add`).

`WorldTJ.seg`: the segment of a known leaf or extension is empty or a nibble
array (bytes below 16), which is what bounds the branch-slot index computed
from it.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {Rg : Reg} {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}

/-- A sub-range `[lo, hi')` of a free range that starts at the same address. -/
theorem FreeOK.prefix {pv : Word} {T : Word → Option HtabV} {N : Word → Option Word}
    {J C lo hi hi' : Word} (h : FreeOK pv T N J C lo hi) (hle : hi'.toNat ≤ hi.toNat) :
    FreeOK pv T N J C lo hi' := by
  have := h.hi_
  refine ⟨h.lo_, by omega, fun t v ht x hx => ?_, fun t v ht => ?_, fun a k hN => ?_, ?_⟩
  · rcases h.tab t v ht x hx with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by omega)
  · obtain ⟨h1, h2⟩ := h.tabI t v ht
    refine ⟨?_, ?_⟩
    · rcases h1 with h1 | h1
      · exact Or.inl (by omega)
      · exact Or.inr h1
    · rcases h2 with h2 | h2
      · exact Or.inl (by omega)
      · exact Or.inr h2
  · rcases h.node a k hN with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by omega)
  · rcases h.jrn with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by omega)

/-- The registry with the prefix `[lo, hi')` of the writable block `[lo, hi)`
frozen; every writable block overlapping `[lo, hi)` is dropped. -/
def Reg.freeze (Rg : Reg) (lo hi hi' : Word) : Reg :=
  { Rg with
    B := fun a b => Rg.B a b ∧ (b.toNat ≤ lo.toNat ∨ hi.toNat ≤ a.toNat)
    Im := fun a b => Rg.Im a b ∨ (a = lo ∧ b = hi') }

theorem WorldTJ.freeze {lo hi hi' : Word} (h : WorldTJ Rg g m) (hb : Rg.B lo hi)
    (h8 : lo.toNat % 8 = 0) (hle : hi'.toNat ≤ hi.toNat)
    (hnib : Nibs m lo (hi'.toNat - lo.toNat)) : WorldTJ (Rg.freeze lo hi hi') g m := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  refine ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, fun a b hab => hB a b hab.1, hCn,
    hNd, ⟨fun a b hI => ?_, fun a b c d hab hI => ?_, hIm.segs.mono (fun a b hI => Or.inl hI),
      fun a b hI => ?_, ?_, ?_⟩⟩
  · rcases hI with hI | ⟨rfl, rfl⟩
    · exact hIm.free a b hI
    · exact ⟨h8, (hB _ _ hb).prefix hle⟩
  · rcases hI with hI | ⟨rfl, rfl⟩
    · exact hIm.offB a b c d hab.1 hI
    · rcases hab.2 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by omega)
  · rcases hI with hI | ⟨rfl, rfl⟩
    · exact hIm.nib a b hI
    · exact hnib
  · exact hIm.kd
  · exact hIm.kn

/-- A node registered with its kind: the kind cell, and the node's bounds. -/
theorem WorldTJ.kd {a k : Word} (h : WorldTJ Rg g m) (hK : Rg.Kd a k) :
    Rg.Nd a ∧ Rd m a k ∧ HBASE ≤ a.toNat ∧ a.toNat + nodeSize k ≤ 2952790016 ∧
      a.toNat % 8 = 0 := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have hat := hW.nodes.at_ a k (hIm.kd a k hK)
  have := hat.hi
  have := hpH.1
  exact ⟨hIm.kn a k hK, hat.kind, hat.lo, by omega, hat.al⟩

/-- Any sub-range of an immutable block is a nibble array. -/
theorem WorldTJ.im_nibs {lo hi p : Word} {c : Nat} (h : WorldTJ Rg g m) (hI : Rg.Im lo hi)
    (hlo : lo.toNat ≤ p.toNat) (hhi : p.toNat + c ≤ hi.toNat) : Nibs m p c := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have := hi.isLt
  exact (hIm.nib lo hi hI).sub hlo (by omega) (by omega)

/-- The segment of a known leaf or extension. -/
theorem WorldTJ.seg {a k : Word} (h : WorldTJ Rg g m) (ha : Rg.Nd a) (hk : Rd m a k)
    (hk12 : k = 1#64 ∨ k = 2#64) :
    ∃ sp nl : Word, Rd m (a + 32#64) sp ∧ Rd m (a + 40#64) nl ∧
      (nl = 0#64 ∨ ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ sp.toNat ∧
        sp.toNat + nl.toNat ≤ hi.toNat ∧ NibSeg m sp nl) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  obtain ⟨k', hk'⟩ := hNd a ha
  have : k' = k := Rd.inj (hW.nodes.at_ a k' hk').kind hk
  subst this
  obtain ⟨sp, nl, r1, r2, hc⟩ := hIm.segs a k' hk' hk12
  refine ⟨sp, nl, r1, r2, ?_⟩
  rcases hc with h0 | ⟨lo, hi, hI, -, h1, h2, hn⟩
  · exact Or.inl h0
  · exact Or.inr ⟨lo, hi, hI, h1, h2, hn⟩

/-- A byte of a nibble array, as a branch-slot offset: `32 + 8 * b` stays
inside a branch node (`nodeSize 3 = 176`). -/
theorem NibSeg.slot {p n : Word} (h : NibSeg m p n) {i : Nat} (hi : i < n.toNat) :
    ∃ b : Word, byteAt m (off p i) = some b ∧ 32 + 8 * b.toNat + 8 ≤ 160 :=
  let ⟨b, hb, h16⟩ := h i hi
  ⟨b, hb, by omega⟩

end InitECandidate.Solver.GuestBound
