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

set_option maxHeartbeats 4000000 in
/-- Deleting the root leaf keeps the invariant. -/
theorem del_ok_root (hok : HtabOK m t v kind rep) {Lw pos moved : Word}
    (hL : LiveN v kind Lw.toNat) (hLk : kind Lw.toNat = .leaf) (hr : v.root = Lw)
    (hpos : Rd m (nodeField v Lw.toNat 16) pos)
    (hmoved : Rd m (orderSlot v (v.cnt.toNat - 1)) moved) :
    HtabOK (setCell (setCell (setCell (delA m t v pos moved) (t + 56#64) 0#64)
        (nodeField v Lw.toNat 0) v.free) (t + 72#64) Lw) t
      ⟨v.kl, v.st, v.cp, v.nc, v.cnt - 1#64, v.keys, v.nodes, v.order, 0#64, v.next, Lw⟩
      (fun i => if i = Lw.toNat then .free else kind i) rep := by
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨hL1, hL2, hL3⟩ := hL
  have hnl := hwf.next_le
  have hcl := hwf.cnt_le
  have hn64 := v.next.isLt
  obtain ⟨p, value, pos', hp, hval, hpos', hbitL, hpar, hposlt, hordL⟩ :=
    hwf.leaf_ok _ hL1 hL2 hLk
  have := Rd.inj hpos' hpos
  subst this
  have h1 : (1#64 : Word).toNat = 1 := by decide
  have hc1 : (v.cnt - 1#64).toNat = v.cnt.toNat - 1 := by
    rw [BitVec.toNat_sub, h1]
    have := v.cnt.isLt
    omega
  obtain ⟨moved', hmoved', hm1, hm2, hmk, hm16⟩ := hwf.order_ok (v.cnt.toNat - 1) (by omega)
  have := Rd.inj hmoved' hmoved
  subst this
  have hLnc : Lw.toNat ≤ v.nc.toNat := by omega
  have hpnc : pos'.toNat ≤ v.nc.toNat := by omega
  have hmnc : moved'.toNat ≤ v.nc.toNat := by omega
  have hp0 : Rd m (nodeField v Lw.toNat 0) 0#64 := by
    rcases hwf.root_ok with h0 | ⟨-, -, -, h⟩
    · rw [hr] at h0
      rw [h0] at hL1
      exact absurd hL1 (by decide)
    · rw [hr] at h
      exact h
  -- `moved` is the leaf itself exactly when it sits at the last position
  have hmL : moved'.toNat = Lw.toNat → pos'.toNat = v.cnt.toNat - 1 := by
    intro h
    rw [h] at hm16
    exact toNat_of_eq_ofNat (by have := v.cnt.isLt; omega) (Rd.inj hpos hm16)
  have hLm : pos'.toNat = v.cnt.toNat - 1 → moved'.toNat = Lw.toNat := by
    intro h
    rw [h] at hordL
    exact toNat_of_eq_ofNat (by omega) (Rd.inj hmoved hordL)
  generalize hm' : setCell (setCell (setCell (delA m t v pos' moved') (t + 56#64) 0#64)
    (nodeField v Lw.toNat 0) v.free) (t + 72#64) Lw = m'
  have hN : ∀ (i o : Nat) (w : Word), i ≤ v.nc.toNat → o < 32 → o % 8 = 0 →
      ¬(i = Lw.toNat ∧ o = 0) → ¬(i = moved'.toNat ∧ o = 16) →
      (Rd m' (nodeField v i o) w ↔ Rd m (nodeField v i o) w) := by
    intro i o w hi ho ho8 hn1 hn2
    subst hm'
    simp (disch := omega) [delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay,
      node_ne_ord hlay, hn1, hn2]
  have hO : ∀ (q : Nat) (w : Word), q ≤ v.nc.toNat → q ≠ pos'.toNat →
      (Rd m' (orderSlot v q) w ↔ Rd m (orderSlot v q) w) := by
    intro q w hq hne
    subst hm'
    simp (disch := omega) [delA, rd_setCell, ord_ne_hdr hlay, ord_ne_node hlay,
      ord_eq_ord hlay, hne]
  have hH : ∀ (k : Nat) (w : Word), k < 88 → k ≠ 24 → k ≠ 56 → k ≠ 72 →
      (Rd m' (t + BitVec.ofNat 64 k) w ↔ Rd m (t + BitVec.ofNat 64 k) w) := by
    intro k w hk h24 h56 h72
    subst hm'
    simp (disch := omega) [delA, rd_setCell, hdr_ne_ord hlay, hdr_ne_node hlay,
      hdr_eq_hdr hlay, h24, h56, h72]
  have hOpos : Rd m' (orderSlot v pos'.toNat) moved' := by
    subst hm'
    simp (disch := omega) [delA, rd_setCell, ord_ne_hdr hlay, ord_ne_node hlay, ord_eq_ord hlay]
  have hM16 : Rd m' (nodeField v moved'.toNat 16) pos' := by
    subst hm'
    simp (disch := omega) [delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay,
      node_ne_ord hlay]
  have hL0 : Rd m' (nodeField v Lw.toNat 0) v.free := by
    subst hm'
    simp (disch := omega) [delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay,
      node_ne_ord hlay]
  have hC : Rd m' (t + 24#64) (v.cnt - 1#64) := by
    subst hm'
    simp (disch := omega) [delA, rd_setCell, hdr_ne_ord hlay, hdr_ne_node hlay, hdr_eq_hdr hlay]
  have hR : Rd m' (t + 56#64) 0#64 := by
    subst hm'
    simp (disch := omega) [delA, rd_setCell, hdr_ne_ord hlay, hdr_ne_node hlay, hdr_eq_hdr hlay]
  have hF : Rd m' (t + 72#64) Lw := by
    subst hm'
    simp (disch := omega) [delA, rd_setCell, hdr_ne_ord hlay, hdr_ne_node hlay, hdr_eq_hdr hlay]
  have hK : ∀ a : Word, v.keys.toNat ≤ a.toNat → a.toNat < v.nodes.toNat → m' a = m a := by
    intro a ha ha'
    subst hm'
    simp (disch := omega) only [delA, setCell_key_hdr hlay, setCell_key_node hlay,
      setCell_key_ord hlay]
  clear hm'
  have hkindL : ∀ i, i ≠ Lw.toNat → (if i = Lw.toNat then NodeKind.free else kind i) = kind i :=
    fun i h => if_neg h
  have hkfree : ∀ i, kind i = .free → (if i = Lw.toNat then NodeKind.free else kind i) = .free := by
    intro i h
    split
    · rfl
    · exact h
  -- parent and child links carry over
  have hParent : ∀ (i : Nat) (pi : Word), i ≠ Lw.toNat → ParentOk m v kind i pi →
      ParentOk m' ⟨v.kl, v.st, v.cp, v.nc, v.cnt - 1#64, v.keys, v.nodes, v.order, 0#64, v.next,
        Lw⟩ (fun i => if i = Lw.toNat then .free else kind i) i pi := by
    intro i pi hiL hpari
    rcases hpari with ⟨-, hroot⟩ | ⟨a1, a2, a3, a4⟩
    · rw [hr] at hroot
      exact absurd hroot.symm hiL
    · have hpiL : pi.toNat ≠ Lw.toNat := by
        intro h
        rw [h, hLk] at a3
        cases a3
      have hpim : pi.toNat ≠ moved'.toNat := by
        intro h
        rw [h, hmk] at a3
        cases a3
      refine Or.inr ⟨a1, a2, (hkindL _ hpiL).trans a3, ?_⟩
      rcases a4 with h | h
      · exact Or.inl ((hN _ 8 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mpr h)
      · exact Or.inr ((hN _ 16 _ (by omega) (by omega) (by omega) (by omega)
          (fun hh => hpim hh.1)).mpr h)
  have hChild : ∀ (i : Nat) (c : Word), 1 ≤ i → i < v.next.toNat → ChildOk m v kind i c →
      ChildOk m' ⟨v.kl, v.st, v.cp, v.nc, v.cnt - 1#64, v.keys, v.nodes, v.order, 0#64, v.next,
        Lw⟩ (fun i => if i = Lw.toNat then .free else kind i) i c := by
    intro i c hi1 hi2 ⟨c1, c2, c3, c4⟩
    have hcL : c.toNat ≠ Lw.toNat := by
      intro h
      rw [h] at c4
      have := toNat_of_eq_ofNat (x := 0#64) (n := i) (by omega) (Rd.inj hp0 c4)
      have h0 : (0#64 : Word).toNat = 0 := by decide
      omega
    exact ⟨c1, c2, by
        show (if c.toNat = Lw.toNat then NodeKind.free else kind c.toNat) ≠ NodeKind.free
        rw [hkindL _ hcL]
        exact c3,
      (hN _ 0 _ (by omega) (by omega) (by omega) (fun hh => hcL hh.1) (by omega)).mpr c4⟩
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  refine ⟨⟨?hdr, hlay, hwf.next_pos, hwf.next_le, ?cnt, Or.inl rfl, ?free, ?fnext, ?int, ?leaf,
    ?order⟩, ⟨?bits⟩, hok.keys8, hok.kl_st, hok.kl8, ?lkey⟩
  case hdr =>
    exact ⟨(hH 0 _ (by omega) (by omega) (by omega) (by omega)).mpr hkl,
      (hH 8 _ (by omega) (by omega) (by omega) (by omega)).mpr hst,
      (hH 16 _ (by omega) (by omega) (by omega) (by omega)).mpr hcp, hC,
      (hH 32 _ (by omega) (by omega) (by omega) (by omega)).mpr hkeys,
      (hH 40 _ (by omega) (by omega) (by omega) (by omega)).mpr hnd,
      (hH 48 _ (by omega) (by omega) (by omega) (by omega)).mpr hord, hR,
      (hH 64 _ (by omega) (by omega) (by omega) (by omega)).mpr hnext, hF,
      (hH 80 _ (by omega) (by omega) (by omega) (by omega)).mpr hnc⟩
  case cnt =>
    show (v.cnt - 1#64).toNat ≤ v.nc.toNat
    omega
  case free =>
    exact Or.inr ⟨hL1, hL2, if_pos rfl⟩
  case fnext =>
    intro i hi1 hi2 hki
    have hi2 : i < v.next.toNat := hi2
    have hold : ∀ f : Word, (f = 0 ∨ (1 ≤ f.toNat ∧ f.toNat < v.next.toNat ∧
        kind f.toNat = .free)) → (f = 0 ∨ (1 ≤ f.toNat ∧ f.toNat < v.next.toNat ∧
        (if f.toNat = Lw.toNat then NodeKind.free else kind f.toNat) = .free)) := by
      rintro f (h | ⟨a, b, c⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, b, hkfree _ c⟩
    by_cases hiL : i = Lw.toNat
    · subst hiL
      exact ⟨v.free, hL0, hold _ hwf.free_ok⟩
    · have hki' : kind i = .free := by rw [← hkindL _ hiL]; exact hki
      obtain ⟨f, hf, hcond⟩ := hwf.free_next i hi1 hi2 hki'
      have him : i ≠ moved'.toNat := by
        intro h
        rw [h, hmk] at hki'
        cases hki'
      exact ⟨f, (hN _ 0 _ (by omega) (by omega) (by omega) (fun hh => hiL hh.1)
        (by omega)).mpr hf, hold _ hcond⟩
  case int =>
    intro i hi1 hi2 hki
    have hi2 : i < v.next.toNat := hi2
    have hiL : i ≠ Lw.toNat := by
      intro h
      rw [h, if_pos rfl] at hki
      cases hki
    have hki' : kind i = .internal := by rw [← hkindL _ hiL]; exact hki
    have him : i ≠ moved'.toNat := by
      intro h
      rw [h, hmk] at hki'
      cases hki'
    obtain ⟨pi, l, r, b, hpi, hl, hrr, hb, hbne, hpari, hcl', hcr', hlr⟩ :=
      hwf.internal_ok i hi1 hi2 hki'
    exact ⟨pi, l, r, b,
      (hN _ 0 _ (by omega) (by omega) (by omega) (fun hh => hiL hh.1) (by omega)).mpr hpi,
      (hN _ 8 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mpr hl,
      (hN _ 16 _ (by omega) (by omega) (by omega) (by omega) (fun hh => him hh.1)).mpr hrr,
      (hN _ 24 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mpr hb, hbne,
      hParent i pi hiL hpari, hChild i l hi1 hi2 hcl', hChild i r hi1 hi2 hcr', hlr⟩
  case leaf =>
    intro i hi1 hi2 hki
    have hi2 : i < v.next.toNat := hi2
    have hiL : i ≠ Lw.toNat := by
      intro h
      rw [h, if_pos rfl] at hki
      cases hki
    have hki' : kind i = .leaf := by rw [← hkindL _ hiL]; exact hki
    obtain ⟨pi, val, posi, h0, h8, h16, h24, hpari, hposi, hordi⟩ :=
      hwf.leaf_ok i hi1 hi2 hki'
    have hi64 : i < 2 ^ 64 := by omega
    by_cases him : i = moved'.toNat
    · subst him
      have hne : pos'.toNat ≠ v.cnt.toNat - 1 := fun h => hiL (hLm h)
      refine ⟨pi, val, pos',
        (hN _ 0 _ (by omega) (by omega) (by omega) (fun hh => hiL hh.1) (by omega)).mpr h0,
        (hN _ 8 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mpr h8, hM16,
        (hN _ 24 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mpr h24,
        hParent _ pi hiL hpari, ?_, ?_⟩
      · show pos'.toNat < (v.cnt - 1#64).toNat
        omega
      · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact hOpos
    · have hne1 : posi.toNat ≠ v.cnt.toNat - 1 := by
        intro h
        rw [h] at hordi
        exact him (toNat_of_eq_ofNat hi64 (Rd.inj hmoved hordi)).symm
      have hne2 : posi.toNat ≠ pos'.toNat := by
        intro h
        rw [h] at hordi
        have e := Rd.inj hordi hordL
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64,
          Nat.mod_eq_of_lt (by omega)] at this
        exact hiL this
      refine ⟨pi, val, posi,
        (hN _ 0 _ (by omega) (by omega) (by omega) (fun hh => hiL hh.1) (by omega)).mpr h0,
        (hN _ 8 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mpr h8,
        (hN _ 16 _ (by omega) (by omega) (by omega) (by omega) (fun hh => him hh.1)).mpr h16,
        (hN _ 24 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mpr h24,
        hParent _ pi hiL hpari, ?_, (hO _ _ (by omega) hne2).mpr hordi⟩
      show posi.toNat < (v.cnt - 1#64).toNat
      omega
  case order =>
    intro q hq
    have hq' : q < v.cnt.toNat - 1 := by rw [← hc1]; exact hq
    by_cases hqp : q = pos'.toNat
    · have hmL' : moved'.toNat ≠ Lw.toNat := fun h => by have := hmL h; omega
      refine ⟨moved', by rw [hqp]; exact hOpos, hm1, hm2, (hkindL _ hmL').trans hmk, ?_⟩
      rw [hqp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact hM16
    · obtain ⟨i, hrd, i1, i2, ik, i16⟩ := hwf.order_ok q (by omega)
      have hq64 : q < 2 ^ 64 := by have := v.cnt.isLt; omega
      have hiL : i.toNat ≠ Lw.toNat := by
        intro h
        rw [h] at i16
        exact hqp (toNat_of_eq_ofNat hq64 (Rd.inj hpos i16)).symm
      have him : i.toNat ≠ moved'.toNat := by
        intro h
        rw [h] at i16
        have e := Rd.inj i16 hm16
        have := congrArg BitVec.toNat e
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq64,
          Nat.mod_eq_of_lt (by have := v.cnt.isLt; omega)] at this
        omega
      exact ⟨i, (hO _ _ (by omega) hqp).mpr hrd, i1, i2, (hkindL _ hiL).trans ik,
        (hN _ 16 _ (by omega) (by omega) (by omega) (by omega) (fun hh => him hh.1)).mpr i16⟩
  case bits =>
    intro i hi1 hi2 hki b l r hb hl hrr
    have hi2 : i < v.next.toNat := hi2
    have hiL : i ≠ Lw.toNat := by
      intro h
      rw [h, if_pos rfl] at hki
      cases hki
    have hki' : kind i = .internal := by rw [← hkindL _ hiL]; exact hki
    have him : i ≠ moved'.toNat := by
      intro h
      rw [h, hmk] at hki'
      cases hki'
    have hb' := (hN _ 24 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mp hb
    have hl' := (hN _ 8 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mp hl
    have hr' := (hN _ 16 _ (by omega) (by omega) (by omega) (by omega)
      (fun hh => him hh.1)).mp hrr
    obtain ⟨_, l0, r0, _, -, hl0, hr0, -, -, -, hcl', hcr', -⟩ := hwf.internal_ok i hi1 hi2 hki'
    have el := Rd.inj hl0 hl'
    have er := Rd.inj hr0 hr'
    subst el er
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hok.keys.internal_bits i hi1 hi2 hki' b l0 r0 hb' hl' hr'
    have := hcl'.2.1
    have := hcr'.2.1
    exact ⟨x1, x2, x3, x4,
      fun bl h => x5 bl ((hN _ 24 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mp h),
      fun br h => x6 br ((hN _ 24 _ (by omega) (by omega) (by omega) (by omega) (by omega)).mp h)⟩
  case lkey =>
    intro i hi1 hi2 hki j hj
    have hi2 : i < v.next.toNat := hi2
    have hiL : i ≠ Lw.toNat := by
      intro h
      rw [h, if_pos rfl] at hki
      cases hki
    exact leaf_key_frame hok hK i hi1 hi2 (by rw [← hkindL _ hiL]; exact hki) j hj

end InitECandidate.Solver.GuestBound
