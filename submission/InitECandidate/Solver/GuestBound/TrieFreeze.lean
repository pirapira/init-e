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
      fun a b hI => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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
  · exact hIm.full
  · exact hIm.trf
  · exact hIm.trv
  · exact fun a b u hab hu => hIm.offT a b u hab.1 hu
  · exact hIm.offC
  · intro a b u hI hu
    rcases hI with hI | ⟨rfl, rfl⟩
    · exact hIm.offI a b u hI hu
    · rcases hIm.offT _ _ u hb hu with h1 | h1
      · exact Or.inl (by omega)
      · exact Or.inr h1
  · exact hIm.offTT
  · exact hIm.lvk
  · exact hIm.lvu
  · exact hIm.lvx
  · exact hIm.lvb
  · exact hIm.cvk
  · exact hIm.cvu
  · exact hIm.cvx
  · exact hIm.cvb
  · exact hIm.lvc

/-- A node registered with its kind: the kind cell, and the node's bounds. -/
theorem WorldTJ.kd {a k : Word} (h : WorldTJ Rg g m) (hK : Rg.Kd a k) :
    Rg.Nd a ∧ Rd m a k ∧ HBASE ≤ a.toNat ∧ a.toNat + nodeSize k ≤ 2952790016 ∧
      a.toNat % 8 = 0 := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have hat := hW.nodes.at_ a k (hIm.kd a k hK)
  have := hat.hi
  have := hpH.1
  exact ⟨hIm.kn a k hK, hat.kind, hat.lo, by omega, hat.al⟩

/-- The child of a registered extension: its segment is not empty and its
child is null or a registered node. -/
theorem WorldTJ.ext {a : Word} (h : WorldTJ Rg g m) (hK : Rg.Kd a 2#64) :
    ∃ nl c : Word, Rd m (a + 40#64) nl ∧ 1 ≤ nl.toNat ∧ Rd m (a + 48#64) c ∧
      (c = 0#64 ∨ ∃ k, Rg.Kd c k) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  obtain ⟨nl, c, r1, h1, r2, hc⟩ := (hW.nodes.at_ a 2#64 (hIm.kd a _ hK)).ext rfl
  refine ⟨nl, c, r1, h1, r2, ?_⟩
  rcases hc with rfl | ⟨j, hj⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨j, hIm.full c j hj⟩

/-- A child slot of a registered branch holds null or a registered node. -/
theorem WorldTJ.slot {a : Word} {i : Nat} (h : WorldTJ Rg g m) (hK : Rg.Kd a 3#64)
    (hi : i < 16) :
    ∃ c : Word, Rd m (a + BitVec.ofNat 64 (32 + 8 * i)) c ∧ (c = 0#64 ∨ ∃ k, Rg.Kd c k) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  obtain ⟨c, r1, hc⟩ := (hW.nodes.at_ a 3#64 (hIm.kd a _ hK)).br rfl i hi
  refine ⟨c, r1, ?_⟩
  rcases hc with rfl | ⟨j, hj⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨j, hIm.full c j hj⟩

/-- The child of an extension sits at the extension's child level. -/
theorem WorldTJ.ext_lv {a c : Word} {ℓc : Nat} (h : WorldTJ Rg g m) (hK : Rg.Kd a 2#64)
    (hcv : Rg.Cv a ℓc) (r2 : Rd m (a + 48#64) c) (hc : c ≠ 0#64) : Rg.Lv c ℓc := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  exact hIm.lvx a ℓc c (hIm.kd a _ hK) hcv r2 hc

/-- A child of a branch sits at the branch's child level. -/
theorem WorldTJ.slot_lv {a c : Word} {i ℓc : Nat} (h : WorldTJ Rg g m) (hK : Rg.Kd a 3#64)
    (hcv : Rg.Cv a ℓc) (hi : i < 16) (r1 : Rd m (a + BitVec.ofNat 64 (32 + 8 * i)) c)
    (hc : c ≠ 0#64) : Rg.Lv c ℓc := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  exact hIm.lvb a ℓc i c (hIm.kd a _ hK) hcv hi r1 hc

/-- A levelled extension or branch has a child level: level plus segment
length for an extension, level plus one for a branch. -/
theorem WorldTJ.cv_ext {a nl : Word} {ℓ : Nat} (h : WorldTJ Rg g m) (hK : Rg.Kd a 2#64)
    (hl : Rg.Lv a ℓ) (r1 : Rd m (a + 40#64) nl) : Rg.Cv a (ℓ + nl.toNat) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have hN := hIm.kd a _ hK
  obtain ⟨ℓc, hcv⟩ := hIm.lvc a ℓ _ hl hN (Or.inl rfl)
  rw [← hIm.cvx a ℓ ℓc nl hl hcv hN r1]
  exact hcv

theorem WorldTJ.cv_br {a : Word} {ℓ : Nat} (h : WorldTJ Rg g m) (hK : Rg.Kd a 3#64)
    (hl : Rg.Lv a ℓ) : Rg.Cv a (ℓ + 1) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have hN := hIm.kd a _ hK
  obtain ⟨ℓc, hcv⟩ := hIm.lvc a ℓ _ hl hN (Or.inr rfl)
  rw [← hIm.cvb a ℓ ℓc hl hcv hN]
  exact hcv

theorem WorldTJ.cv_unique {a : Word} {x y : Nat} (h : WorldTJ Rg g m) (h1 : Rg.Cv a x)
    (h2 : Rg.Cv a y) : x = y := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  exact hIm.cvu a x y h1 h2

/-- A node has at most one level. -/
theorem WorldTJ.lv_unique {a : Word} {ℓ ℓ' : Nat} (h : WorldTJ Rg g m) (h1 : Rg.Lv a ℓ)
    (h2 : Rg.Lv a ℓ') : ℓ = ℓ' := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  exact hIm.lvu a ℓ ℓ' h1 h2

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
