import InitECandidate.Solver.GuestBound.WorldNode

/-!
# Freezing a buffer into an immutable block, and reading a node's segment

`Reg.freeze lo hi` moves the writable block `[lo, hi)` to the immutable
blocks, dropping every writable block that overlaps it. `WorldTJ.freeze`: the
world invariant is kept. After freezing, nibble arrays written into the block
can be handed to `node_new_leaf` / `node_new_ext` (`ImOK.node_add`).

`WorldTJ.seg`: the segment of a known leaf or extension is empty or a nibble
array (bytes below 16), which is what bounds the branch-slot index computed
from it.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {Rg : Reg} {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}

/-- The registry with `[lo, hi)` frozen. -/
def Reg.freeze (Rg : Reg) (lo hi : Word) : Reg :=
  { Rg with
    B := fun a b => Rg.B a b ∧ (b.toNat ≤ lo.toNat ∨ hi.toNat ≤ a.toNat)
    Im := fun a b => Rg.Im a b ∨ (a = lo ∧ b = hi) }

theorem WorldTJ.freeze {lo hi : Word} (h : WorldTJ Rg g m) (hb : Rg.B lo hi)
    (h8 : lo.toNat % 8 = 0) : WorldTJ (Rg.freeze lo hi) g m := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  refine ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, fun a b hab => hB a b hab.1, hCn,
    hNd, ⟨fun a b hI => ?_, fun a b c d hab hI => ?_, hIm.segs.mono (fun a b hI => Or.inl hI)⟩⟩
  · rcases hI with hI | ⟨rfl, rfl⟩
    · exact hIm.free a b hI
    · exact ⟨h8, hB _ _ hb⟩
  · rcases hI with hI | ⟨rfl, rfl⟩
    · exact hIm.offB a b c d hab.1 hI
    · exact hab.2

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
