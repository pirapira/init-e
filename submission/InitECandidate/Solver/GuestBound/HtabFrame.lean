import InitECandidate.Solver.GuestBound.HtabNode

/-!
# The table invariant is local to the table's footprint

`TabFoot t v`: the header `[t, t + 88)` and the three blocks
`[keys, order + 8·(nc + 1))`. `HtabOK` only reads these cells, so it survives
any change elsewhere (`HtabOK.frame`). This is what lets several tables, the
journal and other heap structures be kept side by side.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m m' : Word → Option (PanValue Word)} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
  {rep : KeyRep}

/-- The cells of a table: header and blocks. -/
def TabFoot (t : Word) (v : HtabV) (a : Word) : Prop :=
  (t.toNat ≤ a.toNat ∧ a.toNat < t.toNat + 88) ∨
    (v.keys.toNat ≤ a.toNat ∧ a.toNat < v.order.toNat + (v.nc.toNat + 1) * 8)

/-- The table invariant only depends on the table's footprint. -/
theorem HtabOK.frame (hok : HtabOK m t v kind rep) (h : ∀ a, TabFoot t v a → m' a = m a) :
    HtabOK m' t v kind rep := by
  have hlay := hok.wf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  have hkn : v.keys.toNat ≤ v.nodes.toNat := Nat.le_trans (Nat.le_add_right _ _) l2
  have hH : ∀ (k : Nat) (w : Word), k < 88 → Rd m (t + BitVec.ofNat 64 k) w →
      Rd m' (t + BitVec.ofNat 64 k) w := by
    intro k w hk hr
    unfold Rd at hr ⊢
    rw [h _ (Or.inl (by rw [hdr_toNat hlay hk]; omega))]
    exact hr
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hok.wf.hdr
  have hhdr : HtabHdr m' t v :=
    ⟨hH 0 _ (by omega) h0, hH 8 _ (by omega) h1, hH 16 _ (by omega) h2, hH 24 _ (by omega) h3,
      hH 32 _ (by omega) h4, hH 40 _ (by omega) h5, hH 48 _ (by omega) h6, hH 56 _ (by omega) h7,
      hH 64 _ (by omega) h8, hH 72 _ (by omega) h9, hH 80 _ (by omega) h10⟩
  have key := (hok.toDet.transport (m' := m') (cp' := v.cp) (nc' := v.nc) (K := v.keys)
    (N := v.nodes) (O := v.order) (Nat.le_refl _) hlay hhdr hok.keys8 hok.nodes8 hok.order8
    (fun i o w hi ho _ => by
      show Rd m' (nodeField v i o) w ↔ Rd m (nodeField v i o) w
      unfold Rd
      rw [h _ (Or.inr (by rw [node_toNat hlay hi ho]; constructor <;> omega))])
    (fun p w hp => by
      show Rd m' (orderSlot v p) w ↔ Rd m (orderSlot v p) w
      unfold Rd
      rw [h _ (Or.inr (by rw [ord_toNat hlay hp]; constructor <;> omega))])
    (fun i hi j bit hj hb => keybit_frame hlay hok.keys8 hok.kl_st hok.kl8
      (fun a ha1 ha2 => h a (Or.inr ⟨ha1, by omega⟩)) hi hj hb)).toOK
  exact key

end InitECandidate.Solver.GuestBound
