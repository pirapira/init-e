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

end InitECandidate.Solver.GuestBound
