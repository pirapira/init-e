import InitECandidate.Solver.GuestBound.HtabKeys

/-!
# Hash tables: cells and stores

The header fields, node fields and order slots of a table are distinct cells.
`rd_setCell` reduces a read after a store to an address comparison, and the
`*_eq_*` lemmas decide those comparisons from the layout.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m : Word → Option (PanValue Word)} {t : Word} {v : HtabV}

theorem rd_setCell (a a' x w : Word) :
    Rd (setCell m a' x) a w ↔ if a = a' then x = w else Rd m a w := by
  unfold Rd setCell
  by_cases h : a = a'
  · simp [h]
  · have : (a == a') = false := by simpa using h
    simp [h, this]

theorem hdr_toNat (hlay : HtabLayout t v) {k : Nat} (hk : k < 88) :
    (t + BitVec.ofNat 64 k).toNat = t.toNat + k := by
  obtain ⟨h1, h2, h3, h4⟩ := hlay
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hk' : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  rw [hk']
  exact Nat.mod_eq_of_lt (by omega)

theorem node_toNat (hlay : HtabLayout t v) {i o : Nat} (hi : i ≤ v.nc.toNat) (ho : o < 32) :
    (nodeField v i o).toNat = v.nodes.toNat + (i * 32 + o) := by
  obtain ⟨h1, h2, h3, h4⟩ := hlay
  unfold nodeField
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hk' : (i * 32 + o) % 2 ^ 64 = i * 32 + o := Nat.mod_eq_of_lt (by omega)
  rw [hk']
  exact Nat.mod_eq_of_lt (by omega)

theorem ord_toNat (hlay : HtabLayout t v) {p : Nat} (hp : p ≤ v.nc.toNat) :
    (orderSlot v p).toNat = v.order.toNat + p * 8 := by
  obtain ⟨h1, h2, h3, h4⟩ := hlay
  unfold orderSlot
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hk' : (p * 8) % 2 ^ 64 = p * 8 := Nat.mod_eq_of_lt (by omega)
  rw [hk']
  exact Nat.mod_eq_of_lt (by omega)

theorem node_eq_node (hlay : HtabLayout t v) {i i' o o' : Nat} (hi : i ≤ v.nc.toNat)
    (hi' : i' ≤ v.nc.toNat) (ho : o < 32) (ho' : o' < 32) (h8 : o % 8 = 0) (h8' : o' % 8 = 0) :
    nodeField v i o = nodeField v i' o' ↔ i = i' ∧ o = o' := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [node_toNat hlay hi ho, node_toNat hlay hi' ho'] at this
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

theorem node_ne_hdr (hlay : HtabLayout t v) {i o k : Nat} (hi : i ≤ v.nc.toNat) (ho : o < 32)
    (hk : k < 88) : nodeField v i o = t + BitVec.ofNat 64 k ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  have := congrArg BitVec.toNat h
  rw [node_toNat hlay hi ho, hdr_toNat hlay hk] at this
  obtain ⟨h1, h2, h3, h4⟩ := hlay
  omega

theorem hdr_ne_node (hlay : HtabLayout t v) {i o k : Nat} (hi : i ≤ v.nc.toNat) (ho : o < 32)
    (hk : k < 88) : t + BitVec.ofNat 64 k = nodeField v i o ↔ False := by
  rw [eq_comm]
  exact node_ne_hdr hlay hi ho hk

theorem node_ne_ord (hlay : HtabLayout t v) {i o p : Nat} (hi : i ≤ v.nc.toNat) (ho : o < 32)
    (hp : p ≤ v.nc.toNat) : nodeField v i o = orderSlot v p ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  have := congrArg BitVec.toNat h
  rw [node_toNat hlay hi ho, ord_toNat hlay hp] at this
  obtain ⟨h1, h2, h3, h4⟩ := hlay
  omega

theorem ord_ne_node (hlay : HtabLayout t v) {i o p : Nat} (hi : i ≤ v.nc.toNat) (ho : o < 32)
    (hp : p ≤ v.nc.toNat) : orderSlot v p = nodeField v i o ↔ False := by
  rw [eq_comm]
  exact node_ne_ord hlay hi ho hp

theorem ord_ne_hdr (hlay : HtabLayout t v) {p k : Nat} (hp : p ≤ v.nc.toNat) (hk : k < 88) :
    orderSlot v p = t + BitVec.ofNat 64 k ↔ False := by
  refine ⟨fun h => ?_, False.elim⟩
  have := congrArg BitVec.toNat h
  rw [ord_toNat hlay hp, hdr_toNat hlay hk] at this
  obtain ⟨h1, h2, h3, h4⟩ := hlay
  omega

theorem hdr_ne_ord (hlay : HtabLayout t v) {p k : Nat} (hp : p ≤ v.nc.toNat) (hk : k < 88) :
    t + BitVec.ofNat 64 k = orderSlot v p ↔ False := by
  rw [eq_comm]
  exact ord_ne_hdr hlay hp hk

theorem ord_eq_ord (hlay : HtabLayout t v) {p p' : Nat} (hp : p ≤ v.nc.toNat)
    (hp' : p' ≤ v.nc.toNat) : orderSlot v p = orderSlot v p' ↔ p = p' := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [ord_toNat hlay hp, ord_toNat hlay hp'] at this
    omega
  · rintro rfl
    rfl

theorem hdr_eq_hdr (hlay : HtabLayout t v) {k k' : Nat} (hk : k < 88) (hk' : k' < 88) :
    t + BitVec.ofNat 64 k = t + BitVec.ofNat 64 k' ↔ k = k' := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [hdr_toNat hlay hk, hdr_toNat hlay hk'] at this
    omega
  · rintro rfl
    rfl

theorem align8_toNat (x : Word) : (RiscV.panRiscVByteAlign 8#64 x).toNat = x.toNat / 8 * 8 := by
  have h8 : (8#64 : Word).toNat = 8 := by decide
  unfold RiscV.panRiscVByteAlign
  simp only [h8]
  rw [if_neg (by decide)]
  simp only [RiscV.panRiscV_log2_eight]
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have := x.isLt
  omega

/-- A key bit only depends on the cells of an aligned range holding the key. -/
theorem KeyBitIs.frame {m m' : Word → Option (PanValue Word)} {kp j : Word} {bit : Bool}
    {lo hi : Nat} (hlo8 : lo % 8 = 0) (hkp : lo ≤ kp.toNat)
    (hhi : kp.toNat + j.toNat / 8 < hi) (hhi64 : hi ≤ 2 ^ 64)
    (hframe : ∀ a : Word, lo ≤ a.toNat → a.toNat < hi → m' a = m a)
    (h : KeyBitIs 8#64 m kp j bit) : KeyBitIs 8#64 m' kp j bit := by
  intro a cell y hs hcell hy
  refine h a cell y hs ?_ hy
  have ha : a.toNat = j.toNat / 8 := by
    unfold RiscV.panRiscVShift at hs
    split at hs
    · simp only [Option.some.injEq] at hs
      subst hs
      have h3 : (3#64 : Word).toNat = 3 := by decide
      rw [h3, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    · cases hs
  have hsum : (kp + a).toNat = kp.toNat + a.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  rw [← hframe _ (by rw [align8_toNat, hsum]; omega) (by rw [align8_toNat, hsum]; omega)]
  exact hcell

end InitECandidate.Solver.GuestBound
