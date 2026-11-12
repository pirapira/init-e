import InitECandidate.Solver.GuestBound.HtabDelInv

/-!
# Hash tables with detached nodes

While `htab_set` runs, the new leaf and the new internal node exist but are not
linked into the trie yet. `HtabOKd … det` is the table invariant with the
nodes in `det` exempt from the parent and child conditions; with no detached
node it is `HtabOK`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- `ParentOk`, with a parent that is not detached. -/
def ParentOkd (m : Word → Option (PanValue Word)) (v : HtabV) (kind : Nat → NodeKind)
    (det : Nat → Prop) (i : Nat) (p : Word) : Prop :=
  ParentOk m v kind i p ∧ (p ≠ 0 → ¬ det p.toNat)

/-- `HtabWF` with the nodes in `det` exempt from the link conditions. -/
structure HtabWFd (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV)
    (kind : Nat → NodeKind) (det : Nat → Prop) : Prop where
  hdr : HtabHdr m t v
  layout : HtabLayout t v
  next_pos : 1 ≤ v.next.toNat
  next_le : v.next.toNat ≤ v.nc.toNat + 1
  cnt_le : v.cnt.toNat ≤ v.nc.toNat
  root_ok : v.root = 0 ∨ (1 ≤ v.root.toNat ∧ v.root.toNat < v.next.toNat ∧
    kind v.root.toNat ≠ .free ∧ ¬ det v.root.toNat ∧ Rd m (nodeField v v.root.toNat 0) 0)
  free_chain : ∃ fl : List Nat, FreeChain m v kind v.free fl
  internal_ok : ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .internal →
    ∃ p l r b : Word, Rd m (nodeField v i 0) p ∧ Rd m (nodeField v i 8) l ∧
      Rd m (nodeField v i 16) r ∧ Rd m (nodeField v i 24) b ∧ b ≠ v.kl * 8#64 ∧
      (¬ det i → ParentOkd m v kind det i p ∧ ChildOk m v kind i l ∧ ChildOk m v kind i r ∧
        ¬ det l.toNat ∧ ¬ det r.toNat ∧ l ≠ r)
  leaf_ok : ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .leaf →
    ∃ p value pos : Word, Rd m (nodeField v i 0) p ∧ Rd m (nodeField v i 8) value ∧
      Rd m (nodeField v i 16) pos ∧ Rd m (nodeField v i 24) (v.kl * 8#64) ∧
      (¬ det i → ParentOkd m v kind det i p) ∧ pos.toNat < v.cnt.toNat ∧
      Rd m (orderSlot v pos.toNat) (BitVec.ofNat 64 i)
  order_ok : ∀ pos, pos < v.cnt.toNat →
    ∃ i : Word, Rd m (orderSlot v pos) i ∧ 1 ≤ i.toNat ∧ i.toNat < v.next.toNat ∧
      kind i.toNat = .leaf ∧ Rd m (nodeField v i.toNat 16) (BitVec.ofNat 64 pos)

/-- `HtabOK` with detached nodes. -/
structure HtabOKd (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV)
    (kind : Nat → NodeKind) (rep : KeyRep) (det : Nat → Prop) : Prop where
  wf : HtabWFd m t v kind det
  bits : ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .internal → ¬ det i →
    ∀ b l r : Word, Rd m (nodeField v i 24) b → Rd m (nodeField v i 8) l →
      Rd m (nodeField v i 16) r →
      b.toNat < (v.kl * 8#64).toNat ∧ rep l.toNat b = false ∧ rep r.toNat b = true ∧
      (∀ j : Word, j.toNat < b.toNat → rep l.toNat j = rep i j ∧ rep r.toNat j = rep i j) ∧
      (∀ bl, Rd m (nodeField v l.toNat 24) bl → b.toNat < bl.toNat) ∧
      (∀ br, Rd m (nodeField v r.toNat 24) br → b.toNat < br.toNat)
  keys8 : v.keys.toNat % 8 = 0
  nodes8 : v.nodes.toNat % 8 = 0
  order8 : v.order.toNat % 8 = 0
  nc_pos : 1 ≤ v.nc.toNat
  kl_st : v.kl.toNat ≤ v.st.toNat
  kl8 : v.kl.toNat * 8 < 2 ^ 64
  leaf_key : ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .leaf →
    ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs 8#64 m (v.keys + BitVec.ofNat 64 i * v.st) j (rep i j)

variable {m : Word → Option (PanValue Word)} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
  {rep : KeyRep}

/-- A table without detached nodes. -/
theorem HtabOK.toDet (h : HtabOK m t v kind rep) : HtabOKd m t v kind rep (fun _ => False) where
  wf :=
    { hdr := h.wf.hdr
      layout := h.wf.layout
      next_pos := h.wf.next_pos
      next_le := h.wf.next_le
      cnt_le := h.wf.cnt_le
      root_ok := h.wf.root_ok.imp id (fun ⟨a, b, c, d⟩ => ⟨a, b, c, fun x => x, d⟩)
      free_chain := h.wf.free_chain
      internal_ok := by
        intro i h1 h2 hk
        obtain ⟨p, l, r, b, hp, hl, hr, hb, hbne, hpar, hcl, hcr, hlr⟩ := h.wf.internal_ok i h1 h2 hk
        exact ⟨p, l, r, b, hp, hl, hr, hb, hbne,
          fun _ => ⟨⟨hpar, fun _ x => x⟩, hcl, hcr, fun x => x, fun x => x, hlr⟩⟩
      leaf_ok := by
        intro i h1 h2 hk
        obtain ⟨p, val, pos, hp, hv, hpos, hb, hpar, hlt, hord⟩ := h.wf.leaf_ok i h1 h2 hk
        exact ⟨p, val, pos, hp, hv, hpos, hb, fun _ => ⟨hpar, fun _ x => x⟩, hlt, hord⟩
      order_ok := h.wf.order_ok }
  bits := fun i h1 h2 hk _ => h.keys.internal_bits i h1 h2 hk
  keys8 := h.keys8
  nodes8 := h.nodes8
  order8 := h.order8
  nc_pos := h.nc_pos
  kl_st := h.kl_st
  kl8 := h.kl8
  leaf_key := h.leaf_key

/-- With no detached node the invariant is `HtabOK`. -/
theorem HtabOKd.toOK (h : HtabOKd m t v kind rep (fun _ => False)) : HtabOK m t v kind rep where
  wf :=
    { hdr := h.wf.hdr
      layout := h.wf.layout
      next_pos := h.wf.next_pos
      next_le := h.wf.next_le
      cnt_le := h.wf.cnt_le
      root_ok := h.wf.root_ok.imp id (fun ⟨a, b, c, _, d⟩ => ⟨a, b, c, d⟩)
      free_chain := h.wf.free_chain
      internal_ok := by
        intro i h1 h2 hk
        obtain ⟨p, l, r, b, hp, hl, hr, hb, hbne, hrest⟩ := h.wf.internal_ok i h1 h2 hk
        obtain ⟨hpar, hcl, hcr, -, -, hlr⟩ := hrest (fun x => x)
        exact ⟨p, l, r, b, hp, hl, hr, hb, hbne, hpar.1, hcl, hcr, hlr⟩
      leaf_ok := by
        intro i h1 h2 hk
        obtain ⟨p, val, pos, hp, hv, hpos, hb, hpar, hlt, hord⟩ := h.wf.leaf_ok i h1 h2 hk
        exact ⟨p, val, pos, hp, hv, hpos, hb, (hpar (fun x => x)).1, hlt, hord⟩
      order_ok := h.wf.order_ok }
  keys := ⟨fun i h1 h2 hk => h.bits i h1 h2 hk (fun x => x)⟩
  keys8 := h.keys8
  nodes8 := h.nodes8
  order8 := h.order8
  nc_pos := h.nc_pos
  kl_st := h.kl_st
  kl8 := h.kl8
  leaf_key := h.leaf_key

end InitECandidate.Solver.GuestBound
