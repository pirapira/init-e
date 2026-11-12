import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import InitECandidate.Solver.GuestBound.HtabLeaf
import InitECandidate.Solver.GuestBound.HtabDiff

/-!
# Hash tables: the table after `htab_new_leaf`

The new leaf is detached: it has its key, value and insertion-order position,
but no parent yet.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- `c` values mapped injectively into `[1, nx)` minus one point. -/
theorem inj_card (c nx x : Nat) (f : Nat → Nat)
    (hf : ∀ p, p < c → 1 ≤ f p ∧ f p < nx ∧ f p ≠ x)
    (hinj : ∀ p q, p < c → q < c → f p = f q → p = q) (hx : 1 ≤ x ∧ x < nx) : c + 2 ≤ nx := by
  have h1 : (Finset.image f (Finset.range c)).card = c := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro p hp q hq h
    exact hinj p q (by simpa using hp) (by simpa using hq) h
  have h2 : Finset.image f (Finset.range c) ⊆ (Finset.Ico 1 nx).erase x := by
    intro y hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    have := hf p hp
    simp only [Finset.mem_erase, Finset.mem_Ico]
    exact ⟨this.2.2, this.1, this.2.1⟩
  have h3 := Finset.card_le_card h2
  rw [h1, Finset.card_erase_of_mem (by simp only [Finset.mem_Ico]; omega), Nat.card_Ico] at h3
  omega

/-- Bit `j` of the key at `keyp`, most significant bit of each byte first. -/
def srcBit (m : Word → Option (PanValue Word)) (keyp j : Word) : Bool :=
  match byteAt m (keyp + (j >>> (3 : Nat))) with
  | some x => bitOf x (j.toNat % 8)
  | none => false

theorem and7_toNat (j : Word) : (j &&& 7#64).toNat = j.toNat % 8 := by
  have h7 : (7#64 : Word).toNat = 2 ^ 3 - 1 := by decide
  rw [BitVec.toNat_and, h7, Nat.and_two_pow_sub_one_eq_mod]

/-- A key bit read through a known byte. -/
theorem KeyBitIs.of_byte {M : Word → Option (PanValue Word)} {kp j : Word} {bit : Bool}
    (h : ∀ x, byteAt M (kp + (j >>> (3 : Nat))) = some x → bit = bitOf x (j.toNat % 8)) :
    KeyBitIs 8#64 M kp j bit := by
  intro a cell y hs hcell hy
  have ha : a = j >>> (3 : Nat) := by
    unfold RiscV.panRiscVShift at hs
    split at hs
    · simp only [Option.some.injEq] at hs
      rw [← hs]
      rfl
    · cases hs
  subst ha
  have hb : byteAt M (kp + (j >>> (3 : Nat))) = some (gb (kp + (j >>> (3 : Nat))) cell) := by
    unfold byteAt
    rw [hcell]
  have hbit := h _ hb
  have hsh : (7#64 - (j &&& 7#64)).toNat = 7 - j.toNat % 8 := by
    have h7 : (7#64 : Word).toNat = 7 := by decide
    rw [BitVec.toNat_sub, h7, and7_toNat]
    omega
  unfold RiscV.panRiscVShift at hy
  split at hy
  · simp only [Option.some.injEq] at hy
    rw [hsh] at hy
    rw [← hy, hbit]
    unfold bitOf
    by_cases hb1 : (gb (kp + (j >>> (3 : Nat))) cell).getLsbD (7 - j.toNat % 8) = true
    · have := (and_one_ne_zero _ _).mpr hb1
      simp [hb1, this]
    · have hz : (gb (kp + (j >>> (3 : Nat))) cell >>> (7 - j.toNat % 8)) &&& 1#64 = 0#64 := by
        by_contra hne
        exact hb1 ((and_one_ne_zero _ _).mp hne)
      have hf : (gb (kp + (j >>> (3 : Nat))) cell).getLsbD (7 - j.toNat % 8) = false := by
        simpa using hb1
      show (((gb (kp + (j >>> (3 : Nat))) cell) >>> (7 - j.toNat % 8)) &&& 1#64 == 0#64) = _
      rw [hz, hf]
      rfl
  · cases hy

variable {m0 mc : Word → Option (PanValue Word)} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
  {rep : KeyRep}

set_option maxHeartbeats 8000000 in
/-- The table after `htab_new_leaf`: node `n` is a detached leaf holding the
copied key, at the next insertion-order position. -/
theorem leaf_ok {det : Nat → Prop} (hok : HtabOKd m0 t v kind rep det) {n keyp val : Word}
    (hn1 : 1 ≤ n.toNat) (hn2 : n.toNat < v.next.toNat) (hfree : kind n.toNat = .free)
    (hfl : ∃ fl, FreeChain m0 v kind v.free fl ∧ n.toNat ∉ fl)
    (c : CopyInv m0 (v.keys + n * v.st) keyp v.kl.toNat mc)
    (hslot : (v.keys + n * v.st).toNat = v.keys.toNat + n.toNat * v.st.toNat)
    {kind' : Nat → NodeKind} {rep' : KeyRep} {det' : Nat → Prop}
    (hkn : kind' n.toNat = .leaf) (hko : ∀ i, i ≠ n.toNat → kind' i = kind i)
    (hrn : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat → rep' n.toNat j = srcBit m0 keyp j)
    (hro : ∀ i, i ≠ n.toNat → rep' i = rep i)
    (hdet : ∀ i, det' i ↔ (i = n.toNat ∨ det i)) :
    HtabOKd (leafMem mc t v n val) t
      ⟨v.kl, v.st, v.cp, v.nc, v.cnt + 1#64, v.keys, v.nodes, v.order, v.root, v.next, v.free⟩
      kind' rep' det' := by
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  have hnl := hwf.next_le
  have hcl := hwf.cnt_le
  have hnle : n.toNat ≤ v.nc.toNat := by omega
  have hks := hok.kl_st
  have hmulS : n.toNat * v.st.toNat + v.st.toNat ≤ (v.nc.toNat + 1) * v.st.toNat := by
    have := Nat.mul_le_mul_right v.st.toNat (show n.toNat + 1 ≤ v.nc.toNat + 1 by omega)
    have e : (n.toNat + 1) * v.st.toNat = n.toNat * v.st.toNat + v.st.toNat := by ring
    omega
  have hT : ∀ k, k < 88 → (t + BitVec.ofNat 64 k).toNat = t.toNat + k :=
    fun k hk => hdr_toNat hlay hk
  have hNf : ∀ i o, i ≤ v.nc.toNat → o < 32 →
      (nodeField v i o).toNat = v.nodes.toNat + (i * 32 + o) := fun i o hi ho => node_toNat hlay hi ho
  have hOs : ∀ p, p ≤ v.nc.toNat → (orderSlot v p).toNat = v.order.toNat + p * 8 :=
    fun p hp => ord_toNat hlay hp
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  -- cells the leaf stores do not touch
  have hoth : ∀ a : Word, a.toNat ≠ t.toNat + 24 → a.toNat ≠ v.order.toNat + v.cnt.toNat * 8 →
      (∀ o, o < 32 → a.toNat ≠ v.nodes.toNat + (n.toNat * 32 + o)) →
      leafMem mc t v n val a = mc a := by
    intro a h1 h2 h3
    unfold leafMem
    rw [setCell_ne' _ (NE (by rw [hT 24 (by omega)]; exact h1)),
      setCell_ne' _ (NE (by rw [hOs _ hcl]; exact h2)),
      setCell_ne' _ (NE (by rw [hNf _ 24 hnle (by omega)]; exact h3 24 (by omega))),
      setCell_ne' _ (NE (by rw [hNf _ 16 hnle (by omega)]; exact h3 16 (by omega))),
      setCell_ne' _ (NE (by rw [hNf _ 8 hnle (by omega)]; exact h3 8 (by omega))),
      setCell_ne' _ (NE (by rw [hNf _ 0 hnle (by omega)]; exact h3 0 (by omega)))]
  have hmcHi : ∀ A : Word, v.nodes.toNat ≤ A.toNat → mc A = m0 A :=
    fun A hA => c.cells A (Or.inr (Or.inl (by rw [hslot]; omega)))
  have hmcLo : ∀ A : Word, A.toNat + 8 ≤ v.keys.toNat → mc A = m0 A :=
    fun A hA => c.cells A (Or.inl (by rw [hslot]; omega))
  have hNode : ∀ (i o : Nat) (w : Word), i ≤ v.nc.toNat → i ≠ n.toNat → o < 32 →
      (Rd (leafMem mc t v n val) (nodeField v i o) w ↔ Rd m0 (nodeField v i o) w) := by
    intro i o w hi hin ho
    unfold Rd
    rw [hoth _ (by rw [hNf i o hi ho]; omega) (by rw [hNf i o hi ho]; omega)
      (fun o' ho' => by rw [hNf i o hi ho]; omega), hmcHi _ (by rw [hNf i o hi ho]; omega)]
  have hOrd : ∀ (p : Nat) (w : Word), p ≤ v.nc.toNat → p ≠ v.cnt.toNat →
      (Rd (leafMem mc t v n val) (orderSlot v p) w ↔ Rd m0 (orderSlot v p) w) := by
    intro p w hp hpc
    unfold Rd
    rw [hoth _ (by rw [hOs p hp]; omega) (by rw [hOs p hp]; omega)
      (fun o' ho' => by rw [hOs p hp]; omega), hmcHi _ (by rw [hOs p hp]; omega)]
  have hH : ∀ (k : Nat) (w : Word), k ≤ 80 → k ≠ 24 → Rd m0 (t + BitVec.ofNat 64 k) w →
      Rd (leafMem mc t v n val) (t + BitVec.ofNat 64 k) w := by
    intro k w hk hk24 h
    unfold Rd
    rw [hoth _ (by rw [hT k (by omega)]; omega) (by rw [hT k (by omega)]; omega)
      (fun o' ho' => by rw [hT k (by omega)]; omega), hmcLo _ (by rw [hT k (by omega)]; omega)]
    exact h
  have hne : ∀ o o', o < 32 → o' < 32 → o ≠ o' → nodeField v n.toNat o ≠ nodeField v n.toNat o' :=
    fun o o' ho ho' h => NE (by rw [hNf _ o hnle ho, hNf _ o' hnle ho']; omega)
  have hnO : ∀ o, o < 32 → nodeField v n.toNat o ≠ orderSlot v v.cnt.toNat :=
    fun o ho => NE (by rw [hNf _ o hnle ho, hOs _ hcl]; omega)
  have hnH : ∀ o, o < 32 → nodeField v n.toNat o ≠ t + 24#64 :=
    fun o ho => NE (by rw [hNf _ o hnle ho, hT 24 (by omega)]; omega)
  have hN0 : Rd (leafMem mc t v n val) (nodeField v n.toNat 0) 0#64 :=
    (((((Rd.here _ _ _).frame _ (hne 0 8 (by omega) (by omega) (by omega))).frame _
      (hne 0 16 (by omega) (by omega) (by omega))).frame _
      (hne 0 24 (by omega) (by omega) (by omega))).frame _ (hnO 0 (by omega))).frame _
      (hnH 0 (by omega))
  have hN8 : Rd (leafMem mc t v n val) (nodeField v n.toNat 8) val :=
    ((((Rd.here _ _ _).frame _ (hne 8 16 (by omega) (by omega) (by omega))).frame _
      (hne 8 24 (by omega) (by omega) (by omega))).frame _ (hnO 8 (by omega))).frame _
      (hnH 8 (by omega))
  have hN16 : Rd (leafMem mc t v n val) (nodeField v n.toNat 16) v.cnt :=
    (((Rd.here _ _ _).frame _ (hne 16 24 (by omega) (by omega) (by omega))).frame _
      (hnO 16 (by omega))).frame _ (hnH 16 (by omega))
  have hN24 : Rd (leafMem mc t v n val) (nodeField v n.toNat 24) (v.kl * 8#64) :=
    ((Rd.here _ _ _).frame _ (hnO 24 (by omega))).frame _ (hnH 24 (by omega))
  have hOc : Rd (leafMem mc t v n val) (orderSlot v v.cnt.toNat) n :=
    (Rd.here _ _ _).frame _ (NE (by rw [hOs _ hcl, hT 24 (by omega)]; omega))
  have hHc : Rd (leafMem mc t v n val) (t + 24#64) (v.cnt + 1#64) := Rd.here _ _ _
  -- room for one more leaf
  have hcard : v.cnt.toNat + 2 ≤ v.next.toNat := by
    classical
    let f : Nat → Nat := fun p =>
      if h : p < v.cnt.toNat then (Classical.choose (hwf.order_ok p h)).toNat else 0
    have hf : ∀ p, p < v.cnt.toNat → ∃ i : Word, f p = i.toNat ∧ 1 ≤ i.toNat ∧
        i.toNat < v.next.toNat ∧ kind i.toNat = .leaf ∧
        Rd m0 (nodeField v i.toNat 16) (BitVec.ofNat 64 p) := by
      intro p h
      have hs := Classical.choose_spec (hwf.order_ok p h)
      exact ⟨Classical.choose (hwf.order_ok p h), by simp only [f, dif_pos h], hs.2.1, hs.2.2.1,
        hs.2.2.2.1, hs.2.2.2.2⟩
    refine inj_card _ _ n.toNat f (fun p hp => ?_) (fun p q hp hq e => ?_) ⟨hn1, hn2⟩
    · obtain ⟨i, e, a, b, k, -⟩ := hf p hp
      rw [e]
      exact ⟨a, b, fun h => by rw [h, hfree] at k; cases k⟩
    · obtain ⟨i, ei, -, -, -, ri⟩ := hf p hp
      obtain ⟨i', ei', -, -, -, ri'⟩ := hf q hq
      rw [ei, ei'] at e
      rw [e] at ri
      have h := congrArg BitVec.toNat (Rd.inj ri ri')
      simp only [BitVec.toNat_ofNat] at h
      have := v.cnt.isLt
      omega
  have h1 : (1#64 : Word).toNat = 1 := by decide
  have hc1 : (v.cnt + 1#64).toNat = v.cnt.toNat + 1 := by
    rw [BitVec.toNat_add, h1]
    exact Nat.mod_eq_of_lt (by have := v.nc.isLt; omega)
  have hnn : BitVec.ofNat 64 n.toNat = n := by simp
  have hcc : BitVec.ofNat 64 v.cnt.toNat = v.cnt := by simp
  have hnk : ∀ i, kind i ≠ .free → i ≠ n.toNat := fun i h e => h (e ▸ hfree)
  -- parents carry over
  have hPar : ∀ i p, i ≠ n.toNat → ParentOkd m0 v kind det i p →
      ParentOkd (leafMem mc t v n val)
        ⟨v.kl, v.st, v.cp, v.nc, v.cnt + 1#64, v.keys, v.nodes, v.order, v.root, v.next, v.free⟩
        kind' det' i p := by
    rintro i p hin ⟨hp, hpd⟩
    refine ⟨?_, fun hp0 hd => ?_⟩
    · rcases hp with hr | ⟨a, b, k, hrd⟩
      · exact Or.inl hr
      · have hpn : p.toNat ≠ n.toNat := hnk _ (by rw [k]; exact NodeKind.noConfusion)
        exact Or.inr ⟨a, b, by rw [hko _ hpn]; exact k,
          hrd.imp (hNode _ 8 _ (by omega) hpn (by omega)).mpr
            (hNode _ 16 _ (by omega) hpn (by omega)).mpr⟩
    · rcases (hdet _).mp hd with e | hd
      · rcases hp with ⟨hr, -⟩ | ⟨-, -, k, -⟩
        · exact hp0 hr
        · exact hnk _ (by rw [k]; exact NodeKind.noConfusion) e
      · exact hpd hp0 hd
  have hChild : ∀ i cw, ChildOk m0 v kind i cw →
      ChildOk (leafMem mc t v n val)
        ⟨v.kl, v.st, v.cp, v.nc, v.cnt + 1#64, v.keys, v.nodes, v.order, v.root, v.next, v.free⟩
        kind' i cw ∧ cw.toNat ≠ n.toNat := by
    rintro i cw ⟨a, b, k, hrd⟩
    have hcn := hnk _ k
    exact ⟨⟨a, b, by rw [hko _ hcn]; exact k, (hNode _ 0 _ (by omega) hcn (by omega)).mpr hrd⟩, hcn⟩
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfreeh, hnc⟩ := hwf.hdr
  obtain ⟨fl, hflc, hnfl⟩ := hfl
  have hmem := FreeChain.kind_mem fl _ hflc
  -- bytes of the key block
  have hkl8 : (v.kl * 8#64).toNat = v.kl.toNat * 8 := by
    have h8 : (8#64 : Word).toNat = 8 := by decide
    rw [BitVec.toNat_mul, h8]
    exact Nat.mod_eq_of_lt hok.kl8
  have hKb : ∀ a : Word, v.keys.toNat ≤ a.toNat → a.toNat < v.nodes.toNat →
      byteAt (leafMem mc t v n val) a = byteAt mc a := by
    intro a ha1 ha2
    have hal : (al8 a).toNat = a.toNat / 8 * 8 := align8_toNat a
    have := hok.keys8
    have := hok.nodes8
    exact byteAt_congr (hoth _ (by omega) (by omega) (fun o' ho' => by omega))
  refine
    { wf :=
        { hdr := ⟨hH 0 _ (by omega) (by omega) hkl, hH 8 _ (by omega) (by omega) hst,
            hH 16 _ (by omega) (by omega) hcp, hHc, hH 32 _ (by omega) (by omega) hkeys,
            hH 40 _ (by omega) (by omega) hnd, hH 48 _ (by omega) (by omega) hord,
            hH 56 _ (by omega) (by omega) hroot, hH 64 _ (by omega) (by omega) hnext,
            hH 72 _ (by omega) (by omega) hfreeh, hH 80 _ (by omega) (by omega) hnc⟩
          layout := hlay
          next_pos := hwf.next_pos
          next_le := hnl
          cnt_le := by show (v.cnt + 1#64).toNat ≤ v.nc.toNat; omega
          root_ok := ?_
          free_chain := ⟨fl, FreeChain.congr (v := v) (kind := kind)
            (v' := ⟨v.kl, v.st, v.cp, v.nc, v.cnt + 1#64, v.keys, v.nodes, v.order, v.root, v.next,
              v.free⟩) (Nat.le_refl _) fl _ hflc (fun i hi => by
              have hin : i ≠ n.toNat := fun e => hnfl (e ▸ hi)
              have := hmem i hi
              exact ⟨by rw [hko _ hin]; exact this.1,
                fun w hw => (hNode i 0 w (by omega) hin (by omega)).mpr hw⟩)⟩
          internal_ok := ?_
          leaf_ok := ?_
          order_ok := ?_ }
      bits := ?_
      keys8 := hok.keys8
      nodes8 := hok.nodes8
      order8 := hok.order8
      nc_pos := hok.nc_pos
      kl_st := hok.kl_st
      kl8 := hok.kl8
      leaf_key := ?_ }
  · rcases hwf.root_ok with h | ⟨a, b, k, d, hrd⟩
    · exact Or.inl h
    · have hrn' := hnk _ k
      exact Or.inr ⟨a, b, by rw [hko _ hrn']; exact k,
        fun hd => ((hdet _).mp hd).elim hrn' d, (hNode _ 0 _ (by omega) hrn' (by omega)).mpr hrd⟩
  · intro i hi1 hi2 hk
    have hi2 : i < v.next.toNat := hi2
    have hin : i ≠ n.toNat := fun e => by rw [e, hkn] at hk; cases hk
    rw [hko _ hin] at hk
    obtain ⟨p, l, r, b, hp, hl, hr, hb, hbne, hrest⟩ := hwf.internal_ok i hi1 hi2 hk
    refine ⟨p, l, r, b, (hNode i 0 _ (by omega) hin (by omega)).mpr hp,
      (hNode i 8 _ (by omega) hin (by omega)).mpr hl,
      (hNode i 16 _ (by omega) hin (by omega)).mpr hr,
      (hNode i 24 _ (by omega) hin (by omega)).mpr hb, hbne, fun hd => ?_⟩
    obtain ⟨hpar, hcl', hcr', -, -, hlr⟩ := hrest (fun d => hd ((hdet _).mpr (Or.inr d)))
    have hL := hChild i l hcl'
    have hR := hChild i r hcr'
    have hdl : ¬ det l.toNat := (hrest (fun d => hd ((hdet _).mpr (Or.inr d)))).2.2.2.1
    have hdr : ¬ det r.toNat := (hrest (fun d => hd ((hdet _).mpr (Or.inr d)))).2.2.2.2.1
    exact ⟨hPar i p hin hpar, hL.1, hR.1, fun d => ((hdet _).mp d).elim hL.2 hdl,
      fun d => ((hdet _).mp d).elim hR.2 hdr, hlr⟩
  · intro i hi1 hi2 hk
    have hi2 : i < v.next.toNat := hi2
    by_cases hin : i = n.toNat
    · subst hin
      refine ⟨0#64, val, v.cnt, hN0, hN8, hN16, hN24, fun hd => absurd ((hdet _).mpr (Or.inl rfl)) hd,
        by show v.cnt.toNat < (v.cnt + 1#64).toNat; omega, ?_⟩
      rw [hnn]
      exact hOc
    · rw [hko _ hin] at hk
      obtain ⟨p, value, pos, hp, hv, hpos, hb, hpar, hlt, hord'⟩ := hwf.leaf_ok i hi1 hi2 hk
      exact ⟨p, value, pos, (hNode i 0 _ (by omega) hin (by omega)).mpr hp,
        (hNode i 8 _ (by omega) hin (by omega)).mpr hv,
        (hNode i 16 _ (by omega) hin (by omega)).mpr hpos,
        (hNode i 24 _ (by omega) hin (by omega)).mpr hb,
        fun hd => hPar i p hin (hpar (fun d => hd ((hdet _).mpr (Or.inr d)))),
        by show pos.toNat < (v.cnt + 1#64).toNat; omega,
        (hOrd _ _ (by omega) (by omega)).mpr hord'⟩
  · intro pos hpos
    have hpos' : pos < v.cnt.toNat + 1 := by rw [← hc1]; exact hpos
    by_cases hpc : pos = v.cnt.toNat
    · subst hpc
      refine ⟨n, hOc, hn1, hn2, hkn, ?_⟩
      rw [hcc]
      exact hN16
    · obtain ⟨i, hi, a, b, k, hrd⟩ := hwf.order_ok pos (by omega)
      have hin := hnk i.toNat (by rw [k]; exact NodeKind.noConfusion)
      exact ⟨i, (hOrd _ _ (by omega) hpc).mpr hi, a, b, by rw [hko _ hin]; exact k,
        (hNode _ 16 _ (by omega) hin (by omega)).mpr hrd⟩
  · intro i hi1 hi2 hk hd b l r hb hl hr
    have hi2 : i < v.next.toNat := hi2
    have hin : i ≠ n.toNat := fun e => by rw [e, hkn] at hk; cases hk
    rw [hko _ hin] at hk
    have hd0 : ¬ det i := fun d => hd ((hdet _).mpr (Or.inr d))
    have hb0 := (hNode i 24 _ (by omega) hin (by omega)).mp hb
    have hl0 := (hNode i 8 _ (by omega) hin (by omega)).mp hl
    have hr0 := (hNode i 16 _ (by omega) hin (by omega)).mp hr
    obtain ⟨p', l', r', b', -, hl', hr', -, -, hrest⟩ := hwf.internal_ok i hi1 hi2 hk
    obtain ⟨-, hcl', hcr', -⟩ := hrest hd0
    have el := Rd.inj hl' hl0
    have er := Rd.inj hr' hr0
    subst el
    subst er
    have hln := hnk _ hcl'.2.2.1
    have hrn' := hnk _ hcr'.2.2.1
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hok.bits i hi1 hi2 hk hd0 b l' r' hb0 hl0 hr0
    rw [hro _ hln, hro _ hrn', hro _ hin]
    exact ⟨g1, g2, g3, g4,
      fun bl hbl => g5 bl ((hNode _ 24 _ (by have := hcl'.2.1; omega) hln (by omega)).mp hbl),
      fun br hbr => g6 br ((hNode _ 24 _ (by have := hcr'.2.1; omega) hrn' (by omega)).mp hbr)⟩
  · intro i hi1 hi2 hk j hj
    have hi2 : i < v.next.toNat := hi2
    have hj : j.toNat < (v.kl * 8#64).toNat := hj
    have hj' : j.toNat / 8 < v.kl.toNat := by
      have : j.toNat < v.kl.toNat * 8 := by rw [← hkl8]; exact hj
      omega
    obtain ⟨hkp, hkp'⟩ := keyptr_bounds hlay (i := i) (by omega)
    have hadd : ∀ a : Word, a.toNat = j.toNat / 8 →
        (v.keys + BitVec.ofNat 64 i * v.st + a).toNat =
          v.keys.toNat + i * v.st.toNat + j.toNat / 8 := by
      intro a ha
      rw [BitVec.toNat_add, hkp, ha]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hin : i = n.toNat
    · subst hin
      rw [hrn j hj]
      refine KeyBitIs.of_byte (fun x hx => ?_)
      have ha : j >>> (3 : Nat) = BitVec.ofNat 64 (j.toNat / 8) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
        exact (Nat.mod_eq_of_lt (by have := j.isLt; omega)).symm
      have hat : (j >>> (3 : Nat)).toNat = j.toNat / 8 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      rw [hnn] at hx hadd
      rw [hKb _ (by rw [hadd _ hat]; omega) (by rw [hadd _ hat]; omega), ha] at hx
      have hcp := c.copied (j.toNat / 8) hj'
      unfold off at hcp
      rw [hcp] at hx
      unfold srcBit
      rw [ha, hx]
    · rw [hko _ hin] at hk
      rw [hro _ hin]
      refine KeyBitIs.of_bytes (fun a ha => ?_) (hok.leaf_key i hi1 hi2 hk j hj)
      rw [hKb _ (by rw [hadd a ha]; omega) (by rw [hadd a ha]; omega)]
      refine c.rest _ ?_
      rw [hadd a ha, hslot]
      rcases Nat.lt_or_ge i n.toNat with h | h
      · left
        have := Nat.mul_le_mul_right v.st.toNat (show i + 1 ≤ n.toNat by omega)
        have e : (i + 1) * v.st.toNat = i * v.st.toNat + v.st.toNat := by ring
        omega
      · right
        have := Nat.mul_le_mul_right v.st.toNat (show n.toNat + 1 ≤ i by omega)
        have e : (n.toNat + 1) * v.st.toNat = n.toNat * v.st.toNat + v.st.toNat := by ring
        omega

/-- The leaf stores and the key copy change nothing outside the table. -/
theorem leafMem_frame (hlay : HtabLayout t v) {n keyp val : Word} (hnle : n.toNat ≤ v.nc.toNat)
    (hcl : v.cnt.toNat ≤ v.nc.toNat) (hks : v.kl.toNat ≤ v.st.toNat)
    (c : CopyInv m0 (v.keys + n * v.st) keyp v.kl.toNat mc)
    (hslot : (v.keys + n * v.st).toNat = v.keys.toNat + n.toNat * v.st.toNat) (A : Word)
    (hT : A.toNat + 8 ≤ t.toNat ∨ t.toNat + 88 ≤ A.toNat)
    (hB : A.toNat + 8 ≤ v.keys.toNat ∨ v.order.toNat + (v.nc.toNat + 1) * 8 ≤ A.toNat) :
    leafMem mc t v n val A = m0 A := by
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  have hmulS : n.toNat * v.st.toNat + v.st.toNat ≤ (v.nc.toNat + 1) * v.st.toNat := by
    have := Nat.mul_le_mul_right v.st.toNat (show n.toNat + 1 ≤ v.nc.toNat + 1 by omega)
    have e : (n.toNat + 1) * v.st.toNat = n.toNat * v.st.toNat + v.st.toNat := by ring
    omega
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have h24 := hdr_toNat hlay (k := 24) (by omega)
  unfold leafMem
  rw [setCell_ne' _ (NE (by rw [h24]; omega)),
    setCell_ne' _ (NE (by rw [ord_toNat hlay hcl]; omega)),
    setCell_ne' _ (NE (by rw [node_toNat hlay hnle (o := 24) (by omega)]; omega)),
    setCell_ne' _ (NE (by rw [node_toNat hlay hnle (o := 16) (by omega)]; omega)),
    setCell_ne' _ (NE (by rw [node_toNat hlay hnle (o := 8) (by omega)]; omega)),
    setCell_ne' _ (NE (by rw [node_toNat hlay hnle (o := 0) (by omega)]; omega))]
  exact c.cells A (by rw [hslot]; omega)

/-- `htab_new_node` changes only the header and fresh heap memory. -/
theorem new_node_frame {det : Nat → Prop} {m m' : Word → Option (PanValue Word)}
    (hok : HtabOKd m t v kind rep det) {g g' : VarName → Option (PanValue Word)} {pv n : Word}
    (hrel : NewNodeRel m t v kind rep det g pv m' g' n) (A : Word)
    (hT : A.toNat + 8 ≤ t.toNat ∨ t.toNat + 88 ≤ A.toNat)
    (hP : A.toNat + 8 ≤ pv.toNat ∨ 2952790016 ≤ A.toNat) : m' A = m A := by
  have hlay := hok.wf.layout
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hH : ∀ k, k < 88 → (t + BitVec.ofNat 64 k).toNat = t.toNat + k :=
    fun k hk => hdr_toNat hlay hk
  rcases hrel with ⟨-, -, -, nf, -, rfl⟩ | ⟨-, -, m1, v1, ⟨-, -, -, -, -, -, -, -, hcase⟩, rfl⟩
  · exact setCell_ne' _ (NE (by rw [hH 72 (by omega)]; omega))
  · rw [setCell_ne' _ (NE (by rw [hH 64 (by omega)]; omega))]
    rcases hcase with ⟨rfl, -, -⟩ | ⟨N, O, q, hR, -, -⟩
    · rfl
    · obtain ⟨m1', m2, m3, c1, c2, c3, rfl⟩ := hR.mem
      have hmul : (v.nc.toNat + 1) * v.st.toNat ≤ (v.nc.toNat * 2 + 1) * v.st.toNat :=
        Nat.mul_le_mul_right _ (by omega)
      have := hR.hN
      have := hR.hO
      have := hR.hq
      obtain ⟨hNle, -⟩ := hR.inN
      obtain ⟨hOle, -⟩ := hR.inO
      obtain ⟨hqle, -⟩ := hR.inq
      rw [setCell_ne' _ (NE (by rw [hH 80 (by omega)]; omega)),
        setCell_ne' _ (NE (by rw [hH 16 (by omega)]; omega)),
        setCell_ne' _ (NE (by rw [hH 48 (by omega)]; omega)),
        c3.cells A (by omega), setCell_ne' _ (NE (by rw [hH 40 (by omega)]; omega)),
        c2.cells A (by omega), setCell_ne' _ (NE (by rw [hH 32 (by omega)]; omega)),
        c1.cells A (by omega)]

end InitECandidate.Solver.GuestBound
