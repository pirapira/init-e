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

/-- Facts about the parent `p`, sibling `sb` and grandparent `g` of a leaf `Lw`
below the root. -/
structure SpliceFacts (m : Word → Option (PanValue Word)) (v : HtabV) (kind : Nat → NodeKind)
    (rep : KeyRep) (Lw p g gl sb bP : Word) : Prop where
  P1 : 1 ≤ p.toNat
  P2 : p.toNat < v.next.toNat
  Pk : kind p.toNat = .internal
  Pbit : Rd m (nodeField v p.toNat 24) bP
  S1 : 1 ≤ sb.toNat
  S2 : sb.toNat < v.next.toNat
  Sk : kind sb.toNat ≠ .free
  S0 : Rd m (nodeField v sb.toNat 0) p
  SL : sb.toNat ≠ Lw.toNat
  SP : sb.toNat ≠ p.toNat
  PL : p.toNat ≠ Lw.toNat
  Srep : ∀ j : Word, j.toNat < bP.toNat → rep sb.toNat j = rep p.toNat j
  Sbit : ∀ bs, Rd m (nodeField v sb.toNat 24) bs → bP.toNat < bs.toNat
  kids : ∀ c : Word, (Rd m (nodeField v p.toNat 8) c ∨ Rd m (nodeField v p.toNat 16) c) →
    c = Lw ∨ c = sb
  G0 : g = 0#64 → v.root.toNat = p.toNat
  Gn : g ≠ 0#64 → 1 ≤ g.toNat ∧ g.toNat < v.next.toNat ∧ kind g.toNat = .internal ∧
    Rd m (nodeField v g.toNat 8) gl ∧ (gl ≠ p → Rd m (nodeField v g.toNat 16) p)
  GL : g.toNat ≠ Lw.toNat
  GP : g.toNat ≠ p.toNat
  GS : g.toNat ≠ sb.toNat

theorem splice_facts (hok : HtabOK m t v kind rep) {Lw p g lc rc gl : Word}
    (hL : LiveN v kind Lw.toNat) (hLk : kind Lw.toNat = .leaf) (hr : v.root ≠ Lw)
    (hp : Rd m (nodeField v Lw.toNat 0) p) (hg : Rd m (nodeField v p.toNat 0) g)
    (hlc : Rd m (nodeField v p.toNat 8) lc) (hrc : Rd m (nodeField v p.toNat 16) rc)
    (hgl : g ≠ 0#64 → Rd m (nodeField v g.toNat 8) gl) :
    ∃ bP, SpliceFacts m v kind rep Lw p g gl (if lc = Lw then rc else lc) bP := by
  have hwf := hok.wf
  obtain ⟨hL1, hL2, hL3⟩ := hL
  have hn64 := v.next.isLt
  obtain ⟨p', _, _, hp', -, -, -, hpar, -⟩ := hwf.leaf_ok _ hL1 hL2 hLk
  have := Rd.inj hp' hp
  subst this
  rcases hpar with ⟨-, hroot'⟩ | ⟨hP1, hP2, hPk, hlink⟩
  · exact absurd (BitVec.eq_of_toNat_eq hroot') hr
  obtain ⟨g', lc', rc', bP, hg', hlc', hrc', hbP, -, hgpar, hclc, hcrc, hlcrc⟩ :=
    hwf.internal_ok _ hP1 hP2 hPk
  have e1 := Rd.inj hg' hg
  have e2 := Rd.inj hlc' hlc
  have e3 := Rd.inj hrc' hrc
  subst e1 e2 e3
  obtain ⟨-, z2, z3, z4, z5, z6⟩ := hok.keys.internal_bits _ hP1 hP2 hPk bP lc' rc' hbP hlc hrc
  have hLw : BitVec.ofNat 64 Lw.toNat = Lw := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hLw] at hlink
  have hside : lc' = Lw ∨ rc' = Lw := by
    rcases hlink with h | h
    · exact Or.inl (Rd.inj hlc h)
    · exact Or.inr (Rd.inj hrc h)
  have hPL : p'.toNat ≠ Lw.toNat := by
    intro h
    rw [h, hLk] at hPk
    cases hPk
  -- the sibling
  have hS : ∃ sb, sb = (if lc' = Lw then rc' else lc') ∧ ChildOk m v kind p'.toNat sb ∧
      sb ≠ Lw ∧ (∀ j : Word, j.toNat < bP.toNat → rep sb.toNat j = rep p'.toNat j) ∧
      (∀ bs, Rd m (nodeField v sb.toNat 24) bs → bP.toNat < bs.toNat) ∧
      (∀ c : Word, (Rd m (nodeField v p'.toNat 8) c ∨ Rd m (nodeField v p'.toNat 16) c) →
        c = Lw ∨ c = sb) := by
    by_cases hlL : lc' = Lw
    · refine ⟨rc', by rw [if_pos hlL], hcrc, fun h => hlcrc (hlL.trans h.symm),
        fun j hj => (z4 j hj).2, z6, ?_⟩
      rintro c (h | h)
      · exact Or.inl ((Rd.inj h hlc).trans hlL)
      · exact Or.inr (Rd.inj h hrc)
    · have hrL : rc' = Lw := hside.resolve_left hlL
      refine ⟨lc', by rw [if_neg hlL], hclc, hlL, fun j hj => (z4 j hj).1, z5, ?_⟩
      rintro c (h | h)
      · exact Or.inr (Rd.inj h hlc)
      · exact Or.inl ((Rd.inj h hrc).trans hrL)
  obtain ⟨sb, hsbdef, ⟨hS1, hS2, hSk, hS0⟩, hSne, hSrep, hSbit, hkids⟩ := hS
  rw [← hsbdef]
  have hp64 : BitVec.ofNat 64 p'.toNat = p' := by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hp64] at hS0
  have hSL : sb.toNat ≠ Lw.toNat := fun h => hSne (BitVec.eq_of_toNat_eq h)
  obtain ⟨bS, hbS⟩ := live_bit hwf (i := sb.toNat) ⟨hS1, hS2, hSk⟩
  have hSP : sb.toNat ≠ p'.toNat := by
    intro h
    rw [h] at hbS
    have := hSbit bP (by rw [h]; exact hbP)
    omega
  have hbSP := hSbit bS hbS
  have h0 : (0#64 : Word).toNat = 0 := by decide
  by_cases hg0 : g' = 0#64
  · refine ⟨bP, hP1, hP2, hPk, hbP, hS1, hS2, hSk, hS0, hSL, hSP, hPL, hSrep, hSbit, hkids, ?_,
      fun h => absurd hg0 h, ?_, ?_, ?_⟩
    · intro _
      rcases hgpar with ⟨-, hroot'⟩ | ⟨hg1, -⟩
      · exact hroot'
      · rw [hg0, h0] at hg1
        omega
    all_goals rw [hg0, h0]; omega
  · obtain ⟨⟨hG1, hG2, -⟩, hGk, bG, gl', gr', hbG, hgl', hgr', hGside, -, -, -, hGbit⟩ :=
      parent_internal hwf hok.keys hP2 hgpar hg0
    have := Rd.inj hgl' (hgl hg0)
    subst this
    have hbGP := hGbit bP hbP
    refine ⟨bP, hP1, hP2, hPk, hbP, hS1, hS2, hSk, hS0, hSL, hSP, hPL, hSrep, hSbit, hkids,
      fun h => absurd h hg0, fun _ => ⟨hG1, hG2, hGk, hgl', ?_⟩, ?_, ?_, ?_⟩
    · intro hne
      rcases hGside with h | h
      · exact absurd (BitVec.eq_of_toNat_eq h) hne
      · rw [← BitVec.eq_of_toNat_eq h]
        exact hgr'
    · intro h
      rw [h, hLk] at hGk
      cases hGk
    · intro h
      rw [h] at hbG
      have := Rd.inj hbG hbP
      rw [this] at hbGP
      omega
    · intro h
      rw [h] at hbG
      have := Rd.inj hbG hbS
      rw [this] at hbGP
      omega

set_option maxHeartbeats 8000000 in
/-- Deleting a leaf below the root keeps the invariant. -/
theorem del_ok_splice (hok : HtabOK m t v kind rep) {Lw pos moved p g gl sb bP : Word}
    (hL : LiveN v kind Lw.toNat) (hLk : kind Lw.toNat = .leaf) (hr : v.root ≠ Lw)
    (hpos : Rd m (nodeField v Lw.toNat 16) pos)
    (hmoved : Rd m (orderSlot v (v.cnt.toNat - 1)) moved)
    (hp : Rd m (nodeField v Lw.toNat 0) p) (hg : Rd m (nodeField v p.toNat 0) g)
    (F : SpliceFacts m v kind rep Lw p g gl sb bP) :
    HtabOK (setCell (setCell (setCell (setCell (setCell (setCell (delA m t v pos moved)
        (nodeField v sb.toNat 0) g) (delX t v g gl p) sb) (nodeField v p.toNat 0) v.free)
        (t + 72#64) p) (nodeField v Lw.toNat 0) p) (t + 72#64) Lw) t
      ⟨v.kl, v.st, v.cp, v.nc, v.cnt - 1#64, v.keys, v.nodes, v.order,
        if g = 0#64 then sb else v.root, v.next, Lw⟩
      (fun i => if i = Lw.toNat ∨ i = p.toNat then .free else kind i) rep := by
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨hL1, hL2, hL3⟩ := hL
  have hnl := hwf.next_le
  have hcl := hwf.cnt_le
  have hn64 := v.next.isLt
  obtain ⟨_, value, pos', _, hval, hpos', hbitL, -, hposlt, hordL⟩ :=
    hwf.leaf_ok _ hL1 hL2 hLk
  have := Rd.inj hpos' hpos
  subst this
  have h1 : (1#64 : Word).toNat = 1 := by decide
  have h0 : (0#64 : Word).toNat = 0 := by decide
  have hc1 : (v.cnt - 1#64).toNat = v.cnt.toNat - 1 := by
    rw [BitVec.toNat_sub, h1]
    have := v.cnt.isLt
    omega
  obtain ⟨moved', hmoved', hm1, hm2, hmk, hm16⟩ := hwf.order_ok (v.cnt.toNat - 1) (by omega)
  have := Rd.inj hmoved' hmoved
  subst this
  have hP1 := F.P1
  have hP2 := F.P2
  have hS1 := F.S1
  have hS2 := F.S2
  have hSL := F.SL
  have hSP := F.SP
  have hPL := F.PL
  have hGL := F.GL
  have hGP := F.GP
  have hGS := F.GS
  have hLnc : Lw.toNat ≤ v.nc.toNat := by omega
  have hpnc : pos'.toNat ≤ v.nc.toNat := by omega
  have hmnc : moved'.toNat ≤ v.nc.toNat := by omega
  have hPnc : p.toNat ≤ v.nc.toNat := by omega
  have hSnc : sb.toNat ≤ v.nc.toNat := by omega
  have hGnc : g.toNat ≤ v.nc.toNat := by
    by_cases hg0 : g = 0#64
    · rw [hg0, h0]; omega
    · have := (F.Gn hg0).2.1; omega
  have hmP : moved'.toNat ≠ p.toNat := by
    intro h
    have := F.Pk
    rw [← h, hmk] at this
    cases this
  have hmG : moved'.toNat ≠ g.toNat := by
    intro h
    by_cases hg0 : g = 0#64
    · rw [hg0, h0] at h; omega
    · have := (F.Gn hg0).2.2.1
      rw [← h, hmk] at this
      cases this
  have hp0 : p ≠ 0#64 := by
    intro h
    rw [h, h0] at hP1
    omega
  have hmL : moved'.toNat = Lw.toNat → pos'.toNat = v.cnt.toNat - 1 := by
    intro h
    rw [h] at hm16
    exact toNat_of_eq_ofNat (by have := v.cnt.isLt; omega) (Rd.inj hpos hm16)
  have hLm : pos'.toNat = v.cnt.toNat - 1 → moved'.toNat = Lw.toNat := by
    intro h
    rw [h] at hordL
    exact toNat_of_eq_ofNat (by omega) (Rd.inj hmoved hordL)
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  generalize hm' : setCell (setCell (setCell (setCell (setCell (setCell (delA m t v pos' moved')
      (nodeField v sb.toNat 0) g) (delX t v g gl p) sb) (nodeField v p.toNat 0) v.free)
      (t + 72#64) p) (nodeField v Lw.toNat 0) p) (t + 72#64) Lw = m'
  have hN0 : ∀ (i : Nat) (w : Word), i ≤ v.nc.toNat → i ≠ Lw.toNat → i ≠ p.toNat →
      i ≠ sb.toNat → (Rd m' (nodeField v i 0) w ↔ Rd m (nodeField v i 0) w) := by
    intro i w hi hn1 hn2 hn3
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp, hn1, hn2, hn3]
  have hN24 : ∀ (i : Nat) (w : Word), i ≤ v.nc.toNat →
      (Rd m' (nodeField v i 24) w ↔ Rd m (nodeField v i 24) w) := by
    intro i w hi
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp]
  have hN8 : ∀ (i : Nat) (w : Word), i ≤ v.nc.toNat → (g ≠ 0#64 → gl = p → i ≠ g.toNat) →
      (Rd m' (nodeField v i 8) w ↔ Rd m (nodeField v i 8) w) := by
    intro i w hi hx
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p
    · simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp]
    · simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp]
    · have := hx hg0 hglp
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp, this]
    · simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp]
  have hN16 : ∀ (i : Nat) (w : Word), i ≤ v.nc.toNat → i ≠ moved'.toNat →
      (g ≠ 0#64 → gl ≠ p → i ≠ g.toNat) →
      (Rd m' (nodeField v i 16) w ↔ Rd m (nodeField v i 16) w) := by
    intro i w hi hn1 hx
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p
    · simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp, hn1]
    · simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp, hn1]
    · simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp, hn1]
    · have := hx hg0 hglp
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp, hn1, this]
  have hX8 : g ≠ 0#64 → gl = p → Rd m' (nodeField v g.toNat 8) sb := by
    intro hg0 hglp
    subst hm'
    simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp]
  have hX16 : g ≠ 0#64 → gl ≠ p → Rd m' (nodeField v g.toNat 16) sb := by
    intro hg0 hglp
    subst hm'
    simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp]
  have hS0 : Rd m' (nodeField v sb.toNat 0) g := by
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp, hSL, hSP]
  have hP0 : Rd m' (nodeField v p.toNat 0) v.free := by
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp, hPL]
  have hL0 : Rd m' (nodeField v Lw.toNat 0) p := by
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp]
  have hM16 : Rd m' (nodeField v moved'.toNat 16) pos' := by
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, node_ne_hdr hlay, node_eq_node hlay, node_ne_ord hlay, hg0, hglp, hmG]
  have hO : ∀ (q : Nat) (w : Word), q ≤ v.nc.toNat → q ≠ pos'.toNat →
      (Rd m' (orderSlot v q) w ↔ Rd m (orderSlot v q) w) := by
    intro q w hq hne
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, ord_ne_hdr hlay, ord_ne_node hlay, ord_eq_ord hlay, hg0, hglp, hne]
  have hOpos : Rd m' (orderSlot v pos'.toNat) moved' := by
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, ord_ne_hdr hlay, ord_ne_node hlay, ord_eq_ord hlay, hg0, hglp]
  have hH : ∀ (k : Nat) (w : Word), k < 88 → k ≠ 24 → k ≠ 56 → k ≠ 72 →
      (Rd m' (t + BitVec.ofNat 64 k) w ↔ Rd m (t + BitVec.ofNat 64 k) w) := by
    intro k w hk h24 h56 h72
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, hdr_ne_ord hlay, hdr_ne_node hlay, hdr_eq_hdr hlay, hg0, hglp, h24, h56, h72]
  have hC : Rd m' (t + 24#64) (v.cnt - 1#64) := by
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, hdr_ne_ord hlay, hdr_ne_node hlay, hdr_eq_hdr hlay, hg0, hglp]
  have hF : Rd m' (t + 72#64) Lw := by
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, hdr_ne_ord hlay, hdr_ne_node hlay, hdr_eq_hdr hlay, hg0, hglp]
  have hR : Rd m' (t + 56#64) (if g = 0#64 then sb else v.root) := by
    subst hm'
    by_cases hg0 : g = 0#64 <;> by_cases hglp : gl = p <;>
      simp (disch := first | omega | assumption) [delX, delA, rd_setCell, hdr_ne_ord hlay, hdr_ne_node hlay, hdr_eq_hdr hlay, hg0, hglp, hroot]
  have hK : ∀ a : Word, v.keys.toNat ≤ a.toNat → a.toNat < v.nodes.toNat → m' a = m a := by
    intro a ha ha'
    subst hm'
    unfold delX
    split_ifs <;>
      simp (disch := omega) only [delA, setCell_key_hdr hlay, setCell_key_node hlay,
        setCell_key_ord hlay]
  clear hm'
  have hkO : ∀ i, i ≠ Lw.toNat → i ≠ p.toNat →
      (if i = Lw.toNat ∨ i = p.toNat then NodeKind.free else kind i) = kind i :=
    fun i a b => if_neg (fun h => h.elim a b)
  have hkfree : ∀ i, kind i = .free →
      (if i = Lw.toNat ∨ i = p.toNat then NodeKind.free else kind i) = .free := by
    intro i h
    split
    · rfl
    · exact h
  have hold : ∀ f : Word, (f = 0 ∨ (1 ≤ f.toNat ∧ f.toNat < v.next.toNat ∧
      kind f.toNat = .free)) → (f = 0 ∨ (1 ≤ f.toNat ∧ f.toNat < v.next.toNat ∧
      (if f.toNat = Lw.toNat ∨ f.toNat = p.toNat then NodeKind.free else kind f.toNat) =
        .free)) := by
    rintro f (h | ⟨a, b, c⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, b, hkfree _ c⟩
  have hSk' : (if sb.toNat = Lw.toNat ∨ sb.toNat = p.toNat then NodeKind.free
      else kind sb.toNat) ≠ .free := by
    rw [hkO _ hSL hSP]
    exact F.Sk
  have hof : ∀ x : Word, BitVec.ofNat 64 x.toNat = x := fun x => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  -- a node other than the sibling keeps its parent link
  have hParent : ∀ (i : Nat) (pi : Word), i < v.next.toNat → i ≠ Lw.toNat → i ≠ p.toNat →
      i ≠ sb.toNat → ParentOk m v kind i pi →
      ParentOk m' ⟨v.kl, v.st, v.cp, v.nc, v.cnt - 1#64, v.keys, v.nodes, v.order,
        if g = 0#64 then sb else v.root, v.next, Lw⟩
        (fun i => if i = Lw.toNat ∨ i = p.toNat then .free else kind i) i pi := by
    intro i pi hi2 hiL hiP hiS hpari
    have hi64 : i < 2 ^ 64 := by omega
    rcases hpari with ⟨hpi0, hroot'⟩ | ⟨a1, a2, a3, a4⟩
    · refine Or.inl ⟨hpi0, ?_⟩
      by_cases hg0 : g = 0#64
      · exact absurd ((F.G0 hg0).symm.trans hroot').symm hiP
      · show (if g = 0#64 then sb else v.root).toNat = i
        rw [if_neg hg0]
        exact hroot'
    · have hpiL : pi.toNat ≠ Lw.toNat := by
        intro h
        rw [h, hLk] at a3
        cases a3
      have hpiP : pi.toNat ≠ p.toNat := by
        intro h
        rw [h] at a4
        rcases F.kids _ a4 with e | e
        · exact hiL (toNat_of_eq_ofNat hi64 e.symm).symm
        · exact hiS (toNat_of_eq_ofNat hi64 e.symm).symm
      have hpim : pi.toNat ≠ moved'.toNat := by
        intro h
        rw [h, hmk] at a3
        cases a3
      refine Or.inr ⟨a1, a2, (hkO _ hpiL hpiP).trans a3, ?_⟩
      rcases a4 with h | h
      · refine Or.inl ((hN8 _ _ (by omega) ?_).mpr h)
        intro hg0 hglp hpiG
        rw [hpiG] at h
        have e := Rd.inj h (F.Gn hg0).2.2.2.1
        rw [hglp] at e
        exact hiP (toNat_of_eq_ofNat hi64 e.symm).symm
      · refine Or.inr ((hN16 _ _ (by omega) hpim ?_).mpr h)
        intro hg0 hglp hpiG
        rw [hpiG] at h
        have e := Rd.inj h ((F.Gn hg0).2.2.2.2 hglp)
        exact hiP (toNat_of_eq_ofNat hi64 e.symm).symm
  have hParentS : ParentOk m' ⟨v.kl, v.st, v.cp, v.nc, v.cnt - 1#64, v.keys, v.nodes, v.order,
        if g = 0#64 then sb else v.root, v.next, Lw⟩
      (fun i => if i = Lw.toNat ∨ i = p.toNat then .free else kind i) sb.toNat g := by
    by_cases hg0 : g = 0#64
    · refine Or.inl ⟨hg0, ?_⟩
      show (if g = 0#64 then sb else v.root).toNat = sb.toNat
      rw [if_pos hg0]
    · obtain ⟨g1, g2, g3, -, -⟩ := F.Gn hg0
      refine Or.inr ⟨g1, g2, (hkO _ hGL hGP).trans g3, ?_⟩
      rw [hof]
      by_cases hglp : gl = p
      · exact Or.inl (hX8 hg0 hglp)
      · exact Or.inr (hX16 hg0 hglp)
  have hChild : ∀ (i : Nat) (c : Word), 1 ≤ i → i < v.next.toNat → i ≠ p.toNat →
      c.toNat ≠ p.toNat → ChildOk m v kind i c →
      ChildOk m' ⟨v.kl, v.st, v.cp, v.nc, v.cnt - 1#64, v.keys, v.nodes, v.order,
        if g = 0#64 then sb else v.root, v.next, Lw⟩
        (fun i => if i = Lw.toNat ∨ i = p.toNat then .free else kind i) i c := by
    intro i c hi1 hi2 hiP hcP ⟨c1, c2, c3, c4⟩
    have hi64 : i < 2 ^ 64 := by omega
    have hcL : c.toNat ≠ Lw.toNat := by
      intro h
      rw [h] at c4
      exact hiP (toNat_of_eq_ofNat hi64 (Rd.inj hp c4)).symm
    have hcS : c.toNat ≠ sb.toNat := by
      intro h
      rw [h] at c4
      exact hiP (toNat_of_eq_ofNat hi64 (Rd.inj F.S0 c4)).symm
    exact ⟨c1, c2, by
        show (if c.toNat = Lw.toNat ∨ c.toNat = p.toNat then NodeKind.free else kind c.toNat) ≠
          NodeKind.free
        rw [hkO _ hcL hcP]
        exact c3,
      (hN0 _ _ (by omega) hcL hcP hcS).mpr c4⟩
  have hChildS : ChildOk m' ⟨v.kl, v.st, v.cp, v.nc, v.cnt - 1#64, v.keys, v.nodes, v.order,
        if g = 0#64 then sb else v.root, v.next, Lw⟩
      (fun i => if i = Lw.toNat ∨ i = p.toNat then .free else kind i) g.toNat sb := ⟨hS1, hS2, hSk', by rw [hof]; exact hS0⟩
  -- a child other than `p` of a node other than `g`
  have hnotP : ∀ (i : Nat) (c : Word), 1 ≤ i → i < v.next.toNat → ChildOk m v kind i c →
      c.toNat = p.toNat → g ≠ 0#64 ∧ i = g.toNat := by
    intro i c hi1 hi2 ⟨_, _, _, c4⟩ h
    rw [h] at c4
    have e := toNat_of_eq_ofNat (by omega) (Rd.inj hg c4)
    refine ⟨?_, e.symm⟩
    intro hg0
    rw [hg0, h0] at e
    omega
  refine ⟨⟨?hdr, hlay, hwf.next_pos, hwf.next_le, ?cnt, ?root, ?free, ?fnext, ?int, ?leaf,
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
  case root =>
    by_cases hg0 : g = 0#64
    · refine Or.inr ?_
      show 1 ≤ (if g = 0#64 then sb else v.root).toNat ∧ _
      rw [if_pos hg0]
      exact ⟨hS1, hS2, hSk', by
        show Rd m' (nodeField v sb.toNat 0) 0
        have := hS0
        rw [hg0] at this
        exact this⟩
    · show (if g = 0#64 then sb else v.root) = 0 ∨ _
      rw [if_neg hg0]
      rcases hwf.root_ok with hz | ⟨r1, r2, r3, r4⟩
      · exact Or.inl hz
      · have hRL : v.root.toNat ≠ Lw.toNat := fun h => hr (BitVec.eq_of_toNat_eq h)
        have hRP : v.root.toNat ≠ p.toNat := by
          intro h
          rw [h] at r4
          exact hg0 (Rd.inj hg r4)
        have hRS : v.root.toNat ≠ sb.toNat := by
          intro h
          rw [h] at r4
          exact hp0 (Rd.inj F.S0 r4)
        exact Or.inr ⟨r1, r2, by
            show (if v.root.toNat = Lw.toNat ∨ v.root.toNat = p.toNat then NodeKind.free
              else kind v.root.toNat) ≠ NodeKind.free
            rw [hkO _ hRL hRP]
            exact r3,
          (hN0 _ _ (by omega) hRL hRP hRS).mpr r4⟩
  case free =>
    exact Or.inr ⟨hL1, hL2, if_pos (Or.inl rfl)⟩
  case fnext =>
    intro i hi1 hi2 hki
    have hi2 : i < v.next.toNat := hi2
    by_cases hiL : i = Lw.toNat
    · subst hiL
      exact ⟨p, hL0, Or.inr ⟨hP1, hP2, if_pos (Or.inr rfl)⟩⟩
    by_cases hiP : i = p.toNat
    · subst hiP
      exact ⟨v.free, hP0, hold _ hwf.free_ok⟩
    have hki' : kind i = .free := by rw [← hkO _ hiL hiP]; exact hki
    obtain ⟨f, hf, hcond⟩ := hwf.free_next i hi1 hi2 hki'
    have hiS : i ≠ sb.toNat := by
      intro h
      rw [h] at hki'
      exact F.Sk hki'
    exact ⟨f, (hN0 _ _ (by omega) hiL hiP hiS).mpr hf, hold _ hcond⟩
  case int =>
    intro i hi1 hi2 hki
    have hi2 : i < v.next.toNat := hi2
    have hiL : i ≠ Lw.toNat := by
      intro h
      rw [h, if_pos (Or.inl rfl)] at hki
      cases hki
    have hiP : i ≠ p.toNat := by
      intro h
      rw [h, if_pos (Or.inr rfl)] at hki
      cases hki
    have hki' : kind i = .internal := by rw [← hkO _ hiL hiP]; exact hki
    have him : i ≠ moved'.toNat := by
      intro h
      rw [h, hmk] at hki'
      cases hki'
    obtain ⟨pi, l, r, b, hpi, hl, hrr, hb, hbne, hpari, hcl', hcr', hlr⟩ :=
      hwf.internal_ok i hi1 hi2 hki'
    -- parent field and link
    have hpar' : ∃ pi', Rd m' (nodeField v i 0) pi' ∧
        ParentOk m' ⟨v.kl, v.st, v.cp, v.nc, v.cnt - 1#64, v.keys, v.nodes, v.order,
        if g = 0#64 then sb else v.root, v.next, Lw⟩
          (fun i => if i = Lw.toNat ∨ i = p.toNat then .free else kind i) i pi' := by
      by_cases hiS : i = sb.toNat
      · subst hiS
        exact ⟨g, hS0, hParentS⟩
      · exact ⟨pi, (hN0 _ _ (by omega) hiL hiP hiS).mpr hpi, hParent i pi hi2 hiL hiP hiS hpari⟩
    obtain ⟨pi', hpi', hpar''⟩ := hpar'
    have hb' := (hN24 i b (by omega)).mpr hb
    by_cases hiG : g ≠ 0#64 ∧ i = g.toNat
    · obtain ⟨hg0, rfl⟩ := hiG
      obtain ⟨-, -, -, hgl', hg16⟩ := F.Gn hg0
      have := Rd.inj hl hgl'
      subst this
      by_cases hglp : l = p
      · have hrP : r.toNat ≠ p.toNat := fun h => hlr (hglp.trans (BitVec.eq_of_toNat_eq h).symm)
        refine ⟨pi', sb, r, b, hpi', hX8 hg0 hglp,
          (hN16 _ _ (by omega) him (fun _ h _ => h hglp)).mpr hrr, hb', hbne, hpar'', hChildS,
          hChild _ r hi1 hi2 hGP hrP hcr', ?_⟩
        intro h
        rw [← h] at hcr'
        exact hGP (toNat_of_eq_ofNat (by omega) (Rd.inj F.S0 hcr'.2.2.2)).symm
      · have hlP : l.toNat ≠ p.toNat := fun h => hglp (BitVec.eq_of_toNat_eq h)
        refine ⟨pi', l, sb, b, hpi', (hN8 _ _ (by omega) (fun _ h _ => hglp h)).mpr hl,
          hX16 hg0 hglp, hb', hbne, hpar'', hChild _ l hi1 hi2 hGP hlP hcl', hChildS, ?_⟩
        intro h
        rw [h] at hcl'
        exact hGP (toNat_of_eq_ofNat (by omega) (Rd.inj F.S0 hcl'.2.2.2)).symm
    · have hlP : l.toNat ≠ p.toNat := fun h => hiG (hnotP i l hi1 hi2 hcl' h)
      have hrP : r.toNat ≠ p.toNat := fun h => hiG (hnotP i r hi1 hi2 hcr' h)
      exact ⟨pi', l, r, b, hpi',
        (hN8 _ _ (by omega) (fun hg0 _ h => hiG ⟨hg0, h⟩)).mpr hl,
        (hN16 _ _ (by omega) him (fun hg0 _ h => hiG ⟨hg0, h⟩)).mpr hrr, hb', hbne, hpar'',
        hChild _ l hi1 hi2 hiP hlP hcl', hChild _ r hi1 hi2 hiP hrP hcr', hlr⟩
  case leaf =>
    intro i hi1 hi2 hki
    have hi2 : i < v.next.toNat := hi2
    have hiL : i ≠ Lw.toNat := by
      intro h
      rw [h, if_pos (Or.inl rfl)] at hki
      cases hki
    have hiP : i ≠ p.toNat := by
      intro h
      rw [h, if_pos (Or.inr rfl)] at hki
      cases hki
    have hki' : kind i = .leaf := by rw [← hkO _ hiL hiP]; exact hki
    have hiG : ∀ hg0 : g ≠ 0#64, i ≠ g.toNat := by
      intro hg0 h
      have := (F.Gn hg0).2.2.1
      rw [← h, hki'] at this
      cases this
    obtain ⟨pi, val, posi, hpi, h8, h16, h24, hpari, hposi, hordi⟩ :=
      hwf.leaf_ok i hi1 hi2 hki'
    have hi64 : i < 2 ^ 64 := by omega
    have hpar' : ∃ pi', Rd m' (nodeField v i 0) pi' ∧
        ParentOk m' ⟨v.kl, v.st, v.cp, v.nc, v.cnt - 1#64, v.keys, v.nodes, v.order,
        if g = 0#64 then sb else v.root, v.next, Lw⟩
          (fun i => if i = Lw.toNat ∨ i = p.toNat then .free else kind i) i pi' := by
      by_cases hiS : i = sb.toNat
      · subst hiS
        exact ⟨g, hS0, hParentS⟩
      · exact ⟨pi, (hN0 _ _ (by omega) hiL hiP hiS).mpr hpi, hParent i pi hi2 hiL hiP hiS hpari⟩
    obtain ⟨pi', hpi', hpar''⟩ := hpar'
    have h8' := (hN8 i val (by omega) (fun hg0 _ => hiG hg0)).mpr h8
    have h24' := (hN24 i _ (by omega)).mpr h24
    by_cases him : i = moved'.toNat
    · subst him
      have hne : pos'.toNat ≠ v.cnt.toNat - 1 := fun h => hiL (hLm h)
      refine ⟨pi', val, pos', hpi', h8', hM16, h24', hpar'', ?_, ?_⟩
      · show pos'.toNat < (v.cnt - 1#64).toNat
        omega
      · rw [hof]
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
      refine ⟨pi', val, posi, hpi', h8',
        (hN16 _ _ (by omega) him (fun hg0 _ => hiG hg0)).mpr h16, h24', hpar'', ?_,
        (hO _ _ (by omega) hne2).mpr hordi⟩
      show posi.toNat < (v.cnt - 1#64).toNat
      omega
  case order =>
    intro q hq
    have hq' : q < v.cnt.toNat - 1 := by rw [← hc1]; exact hq
    have hleafG : ∀ i : Nat, kind i = .leaf → ∀ hg0 : g ≠ 0#64, i ≠ g.toNat := by
      intro i hk hg0 h
      have := (F.Gn hg0).2.2.1
      rw [← h, hk] at this
      cases this
    have hleafP : ∀ i : Nat, kind i = .leaf → i ≠ p.toNat := by
      intro i hk h
      have := F.Pk
      rw [← h, hk] at this
      cases this
    by_cases hqp : q = pos'.toNat
    · have hmL' : moved'.toNat ≠ Lw.toNat := fun h => by have := hmL h; omega
      refine ⟨moved', by rw [hqp]; exact hOpos, hm1, hm2,
        (hkO _ hmL' (hleafP _ hmk)).trans hmk, ?_⟩
      rw [hqp, hof]
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
      exact ⟨i, (hO _ _ (by omega) hqp).mpr hrd, i1, i2, (hkO _ hiL (hleafP _ ik)).trans ik,
        (hN16 _ _ (by omega) him (fun hg0 _ => hleafG _ ik hg0)).mpr i16⟩
  case bits =>
    intro i hi1 hi2 hki b l r hb hl hrr
    have hi2 : i < v.next.toNat := hi2
    have hiL : i ≠ Lw.toNat := by
      intro h
      rw [h, if_pos (Or.inl rfl)] at hki
      cases hki
    have hiP : i ≠ p.toNat := by
      intro h
      rw [h, if_pos (Or.inr rfl)] at hki
      cases hki
    have hki' : kind i = .internal := by rw [← hkO _ hiL hiP]; exact hki
    have him : i ≠ moved'.toNat := by
      intro h
      rw [h, hmk] at hki'
      cases hki'
    have hb' := (hN24 i b (by omega)).mp hb
    obtain ⟨_, l0, r0, _, -, hl0, hr0, -, -, -, hcl', hcr', -⟩ := hwf.internal_ok i hi1 hi2 hki'
    have hl0n := hcl'.2.1
    have hr0n := hcr'.2.1
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hok.keys.internal_bits i hi1 hi2 hki' b l0 r0 hb' hl0 hr0
    have hSbits : b.toNat < bP.toNat → rep sb.toNat b = rep p.toNat b ∧
        (∀ j : Word, j.toNat < b.toNat → rep sb.toNat j = rep p.toNat j) ∧
        (∀ bl, Rd m' (nodeField v sb.toNat 24) bl → b.toNat < bl.toNat) := by
      intro hlt
      refine ⟨F.Srep b hlt, fun j hj => F.Srep j (by omega), fun bl h => ?_⟩
      have := F.Sbit bl ((hN24 _ _ (by omega)).mp h)
      omega
    by_cases hiG : g ≠ 0#64 ∧ i = g.toNat
    · obtain ⟨hg0, rfl⟩ := hiG
      obtain ⟨-, -, -, hgl', hg16⟩ := F.Gn hg0
      have := Rd.inj hl0 hgl'
      subst this
      by_cases hglp : l0 = p
      · have el := Rd.inj hl (hX8 hg0 hglp)
        have er := Rd.inj hr0 ((hN16 _ _ (by omega) him (fun _ h _ => h hglp)).mp hrr)
        subst el er
        rw [hglp] at x2 x4 x5
        obtain ⟨s1, s2, s3⟩ := hSbits (x5 bP F.Pbit)
        exact ⟨x1, s1.trans x2, x3, fun j hj => ⟨(s2 j hj).trans (x4 j hj).1, (x4 j hj).2⟩, s3,
          fun br h => x6 br ((hN24 _ _ (by omega)).mp h)⟩
      · have el := Rd.inj hl0 ((hN8 _ _ (by omega) (fun _ h _ => hglp h)).mp hl)
        have er := Rd.inj hrr (hX16 hg0 hglp)
        have e16 := Rd.inj hr0 (hg16 hglp)
        subst el er e16
        obtain ⟨s1, s2, s3⟩ := hSbits (x6 bP F.Pbit)
        exact ⟨x1, x2, s1.trans x3, fun j hj => ⟨(x4 j hj).1, (s2 j hj).trans (x4 j hj).2⟩,
          fun bl h => x5 bl ((hN24 _ _ (by omega)).mp h), s3⟩
    · have el := Rd.inj hl0 ((hN8 _ _ (by omega) (fun hg0 _ h => hiG ⟨hg0, h⟩)).mp hl)
      have er := Rd.inj hr0 ((hN16 _ _ (by omega) him (fun hg0 _ h => hiG ⟨hg0, h⟩)).mp hrr)
      subst el er
      exact ⟨x1, x2, x3, x4, fun bl h => x5 bl ((hN24 _ _ (by omega)).mp h),
        fun br h => x6 br ((hN24 _ _ (by omega)).mp h)⟩
  case lkey =>
    intro i hi1 hi2 hki j hj
    have hi2 : i < v.next.toNat := hi2
    have hiL : i ≠ Lw.toNat := by
      intro h
      rw [h, if_pos (Or.inl rfl)] at hki
      cases hki
    have hiP : i ≠ p.toNat := by
      intro h
      rw [h, if_pos (Or.inr rfl)] at hki
      cases hki
    exact leaf_key_frame hok hK i hi1 hi2 (by rw [← hkO _ hiL hiP]; exact hki) j hj

/-- The header after a delete: same blocks and capacity, one entry fewer. -/
def SameTable (v v' : HtabV) : Prop :=
  v'.kl = v.kl ∧ v'.st = v.st ∧ v'.cp = v.cp ∧ v'.nc = v.nc ∧ v'.keys = v.keys ∧
    v'.nodes = v.nodes ∧ v'.order = v.order ∧ v'.next = v.next ∧ v'.cnt = v.cnt - 1#64

/-- `htab_del` of a stored key keeps the table invariant and removes one entry. -/
theorem htab_del_ok (hok : HtabOK m t v kind rep) {Lw : Word} (hL : LiveN v kind Lw.toNat)
    (hLk : kind Lw.toNat = .leaf) {m' : Word → Option (PanValue Word)}
    (hrel : DelRel m t v Lw m') :
    ∃ v' kind', HtabOK m' t v' kind' rep ∧ SameTable v v' := by
  obtain ⟨pos, moved, p, g, lc, rc, gl, hpos, hmoved, hsp, rfl⟩ := hrel
  unfold delFinal delB
  by_cases hr : v.root = Lw
  · simp only [if_pos hr]
    exact ⟨_, _, del_ok_root hok hL hLk hr hpos hmoved, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [if_neg hr]
    obtain ⟨hp, hg, hlc, hrc, hgl⟩ := hsp hr
    obtain ⟨bP, F⟩ := splice_facts hok hL hLk hr hp hg hlc hrc hgl
    exact ⟨_, _, del_ok_splice hok hL hLk hr hpos hmoved hp hg F, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl⟩

end InitECandidate.Solver.GuestBound
