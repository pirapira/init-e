import InitECandidate.Solver.GuestBound.HtabDel

/-!
# Hash tables: `htab_del` keeps the invariant

The memory `delFinal` left by deleting a stored key satisfies `HtabOK` again,
with the count decreased by one.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m : Word → Option (PanValue Word)} {t : Word} {v : HtabV}

theorem setCell_ne {a a' : Word} (x : Word) (h : a ≠ a') : setCell m a' x a = m a := by
  unfold setCell
  have : (a == a') = false := by simpa using h
  rw [this]
  rfl

theorem setCell_key_hdr (hlay : HtabLayout t v) {k : Nat} (hk : k < 88) {a : Word} (x : Word)
    (ha : v.keys.toNat ≤ a.toNat) : setCell m (t + BitVec.ofNat 64 k) x a = m a := by
  apply setCell_ne
  intro h
  have := congrArg BitVec.toNat h
  rw [hdr_toNat hlay hk] at this
  obtain ⟨h1, -⟩ := hlay
  omega

theorem setCell_key_node (hlay : HtabLayout t v) {i o : Nat} (hi : i ≤ v.nc.toNat) (ho : o < 32)
    {a : Word} (x : Word) (ha : a.toNat < v.nodes.toNat) :
    setCell m (nodeField v i o) x a = m a := by
  apply setCell_ne
  intro h
  have := congrArg BitVec.toNat h
  rw [node_toNat hlay hi ho] at this
  omega

theorem setCell_key_ord (hlay : HtabLayout t v) {p : Nat} (hp : p ≤ v.nc.toNat) {a : Word}
    (x : Word) (ha : a.toNat < v.nodes.toNat) : setCell m (orderSlot v p) x a = m a := by
  apply setCell_ne
  intro h
  have := congrArg BitVec.toNat h
  rw [ord_toNat hlay hp] at this
  obtain ⟨-, -, h3, -⟩ := hlay
  omega

/-- `htab_del` writes nothing into the key block. -/
theorem del_keys_frame (hlay : HtabLayout t v) {Lw pos moved p g lc rc gl : Word}
    (hL : Lw.toNat ≤ v.nc.toNat) (hpos : pos.toNat ≤ v.nc.toNat)
    (hmoved : moved.toNat ≤ v.nc.toNat) (hp : p.toNat ≤ v.nc.toNat) (hg : g.toNat ≤ v.nc.toNat)
    (hs : (if lc = Lw then rc else lc).toNat ≤ v.nc.toNat) (a : Word)
    (ha : v.keys.toNat ≤ a.toNat) (ha' : a.toNat < v.nodes.toNat) :
    delFinal m t v Lw pos moved p g lc rc gl a = m a := by
  unfold delFinal delB delA delX
  generalize (if lc = Lw then rc else lc) = sb at hs ⊢
  split_ifs <;>
    simp (disch := omega) only [setCell_key_hdr hlay, setCell_key_node hlay, setCell_key_ord hlay]

theorem toNat_of_eq_ofNat {x : Word} {n : Nat} (hn : n < 2 ^ 64) (h : x = BitVec.ofNat 64 n) :
    x.toNat = n := by
  rw [h, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hn

variable {kind : Nat → NodeKind} {rep : KeyRep}

/-- Address of the key of node `i`, inside the key block. -/
theorem keyptr_bounds (hlay : HtabLayout t v) {i : Nat} (hi : i ≤ v.nc.toNat) :
    (v.keys + BitVec.ofNat 64 i * v.st).toNat = v.keys.toNat + i * v.st.toNat ∧
      v.keys.toNat + i * v.st.toNat + v.st.toNat ≤ v.nodes.toNat := by
  obtain ⟨h1, h2, h3, h4⟩ := hlay
  have hle : (i + 1) * v.st.toNat ≤ (v.nc.toNat + 1) * v.st.toNat :=
    Nat.mul_le_mul_right _ (by omega)
  have hexp : (i + 1) * v.st.toNat = i * v.st.toNat + v.st.toNat := by ring
  have hi64 : i < 2 ^ 64 := by have := v.nc.isLt; omega
  have hmul : (BitVec.ofNat 64 i * v.st).toNat = i * v.st.toNat := by
    rw [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨?_, by omega⟩
  rw [BitVec.toNat_add, hmul]
  exact Nat.mod_eq_of_lt (by omega)

/-- Stored key bits survive any change outside the key block. -/
theorem leaf_key_frame (hok : HtabOK m t v kind rep) {m' : Word → Option (PanValue Word)}
    (hK : ∀ a : Word, v.keys.toNat ≤ a.toNat → a.toNat < v.nodes.toNat → m' a = m a)
    (i : Nat) (hi1 : 1 ≤ i) (hi2 : i < v.next.toNat) (hk : kind i = .leaf) (j : Word)
    (hj : j.toNat < (v.kl * 8#64).toNat) :
    KeyBitIs 8#64 m' (v.keys + BitVec.ofNat 64 i * v.st) j (rep i j) := by
  have hlay := hok.wf.layout
  have hnl := hok.wf.next_le
  obtain ⟨hkp, hkp'⟩ := keyptr_bounds hlay (i := i) (by omega)
  have h8 : (8#64 : Word).toNat = 8 := by decide
  have hkl8 : (v.kl * 8#64).toNat = v.kl.toNat * 8 := by
    rw [BitVec.toNat_mul, h8]
    exact Nat.mod_eq_of_lt hok.kl8
  have := hok.kl_st
  have := hok.keys8
  obtain ⟨-, -, -, h4⟩ := hlay
  exact KeyBitIs.frame (lo := v.keys.toNat) (hi := v.nodes.toNat) hok.keys8 (by omega) (by omega)
    (by omega) hK (hok.leaf_key i hi1 hi2 hk j hj)

end InitECandidate.Solver.GuestBound
