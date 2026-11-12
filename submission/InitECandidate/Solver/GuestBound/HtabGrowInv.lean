import InitECandidate.Solver.GuestBound.MemEqGen
import InitECandidate.Solver.GuestBound.HtabGrow
import InitECandidate.Solver.GuestBound.HtabDelInv

/-!
# Hash tables: moving a table

`HtabOK.transport`: a table whose node cells, order slots and key bits read
the same at new block addresses, with a header pointing there, is well formed
again. `htab_grow` is an instance.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m m' : Word → Option (PanValue Word)} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
  {rep : KeyRep}

set_option maxHeartbeats 2000000 in
/-- The table invariant at new block addresses. -/
theorem HtabOK.transport (hok : HtabOK m t v kind rep) {cp' nc' K N O : Word}
    (hnc : v.nc.toNat ≤ nc'.toNat)
    (hlay : HtabLayout t ⟨v.kl, v.st, cp', nc', v.cnt, K, N, O, v.root, v.next, v.free⟩)
    (hhdr : HtabHdr m' t ⟨v.kl, v.st, cp', nc', v.cnt, K, N, O, v.root, v.next, v.free⟩)
    (hK8 : K.toNat % 8 = 0) (hN8 : N.toNat % 8 = 0) (hO8 : O.toNat % 8 = 0)
    (hN : ∀ (i o : Nat) (w : Word), i ≤ v.nc.toNat → o < 32 → o % 8 = 0 →
      (Rd m' (N + BitVec.ofNat 64 (i * 32 + o)) w ↔ Rd m (nodeField v i o) w))
    (hO : ∀ (p : Nat) (w : Word), p ≤ v.nc.toNat →
      (Rd m' (O + BitVec.ofNat 64 (p * 8)) w ↔ Rd m (orderSlot v p) w))
    (hKey : ∀ i, i ≤ v.nc.toNat → ∀ (j : Word) (bit : Bool), j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs 8#64 m (v.keys + BitVec.ofNat 64 i * v.st) j bit →
      KeyBitIs 8#64 m' (K + BitVec.ofNat 64 i * v.st) j bit) :
    HtabOK m' t ⟨v.kl, v.st, cp', nc', v.cnt, K, N, O, v.root, v.next, v.free⟩ kind rep := by
  have hwf := hok.wf
  have hnl := hwf.next_le
  have hcl := hwf.cnt_le
  have hPar : ∀ (i : Nat) (p : Word), ParentOk m v kind i p →
      ParentOk m' ⟨v.kl, v.st, cp', nc', v.cnt, K, N, O, v.root, v.next, v.free⟩ kind i p := by
    rintro i p (h | ⟨a1, a2, a3, a4⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a1, a2, a3, a4.imp (fun h => (hN _ 8 _ (by omega) (by omega) (by omega)).mpr h)
        (fun h => (hN _ 16 _ (by omega) (by omega) (by omega)).mpr h)⟩
  have hCh : ∀ (i : Nat) (c : Word), ChildOk m v kind i c →
      ChildOk m' ⟨v.kl, v.st, cp', nc', v.cnt, K, N, O, v.root, v.next, v.free⟩ kind i c := by
    rintro i c ⟨c1, c2, c3, c4⟩
    exact ⟨c1, c2, c3, (hN _ 0 _ (by omega) (by omega) (by omega)).mpr c4⟩
  refine ⟨⟨hhdr, hlay, hwf.next_pos, ?_, ?_, ?_, hwf.free_ok, ?_, ?_, ?_, ?_⟩, ⟨?_⟩, hK8, hN8, hO8,
    hok.kl_st, hok.kl8, ?_⟩
  · show v.next.toNat ≤ nc'.toNat + 1
    omega
  · show v.cnt.toNat ≤ nc'.toNat
    omega
  · rcases hwf.root_ok with h | ⟨r1, r2, r3, r4⟩
    · exact Or.inl h
    · exact Or.inr ⟨r1, r2, r3, (hN v.root.toNat 0 _ (by omega) (by omega) (by omega)).mpr r4⟩
  · intro i hi1 hi2 hk
    have hi2 : i < v.next.toNat := hi2
    obtain ⟨f, hf, hc⟩ := hwf.free_next i hi1 hi2 hk
    exact ⟨f, (hN _ 0 _ (by omega) (by omega) (by omega)).mpr hf, hc⟩
  · intro i hi1 hi2 hk
    have hi2 : i < v.next.toNat := hi2
    obtain ⟨p, l, r, b, hp, hl, hr, hb, hbne, hpar, hcl', hcr', hlr⟩ :=
      hwf.internal_ok i hi1 hi2 hk
    exact ⟨p, l, r, b, (hN _ 0 _ (by omega) (by omega) (by omega)).mpr hp,
      (hN _ 8 _ (by omega) (by omega) (by omega)).mpr hl,
      (hN _ 16 _ (by omega) (by omega) (by omega)).mpr hr,
      (hN _ 24 _ (by omega) (by omega) (by omega)).mpr hb, hbne, hPar i p hpar, hCh i l hcl',
      hCh i r hcr', hlr⟩
  · intro i hi1 hi2 hk
    have hi2 : i < v.next.toNat := hi2
    obtain ⟨p, val, pos, hp, hv, hpos, hb, hpar, hlt, hord⟩ := hwf.leaf_ok i hi1 hi2 hk
    exact ⟨p, val, pos, (hN _ 0 _ (by omega) (by omega) (by omega)).mpr hp,
      (hN _ 8 _ (by omega) (by omega) (by omega)).mpr hv,
      (hN _ 16 _ (by omega) (by omega) (by omega)).mpr hpos,
      (hN _ 24 _ (by omega) (by omega) (by omega)).mpr hb, hPar i p hpar, hlt,
      (hO _ _ (by omega)).mpr hord⟩
  · intro pos hpos
    have hpos : pos < v.cnt.toNat := hpos
    obtain ⟨i, hrd, i1, i2, ik, i16⟩ := hwf.order_ok pos hpos
    exact ⟨i, (hO _ _ (by omega)).mpr hrd, i1, i2, ik,
      (hN _ 16 _ (by omega) (by omega) (by omega)).mpr i16⟩
  · intro i hi1 hi2 hk b l r hb hl hr
    have hi2 : i < v.next.toNat := hi2
    have hb' := (hN _ 24 _ (by omega) (by omega) (by omega)).mp hb
    have hl' := (hN _ 8 _ (by omega) (by omega) (by omega)).mp hl
    have hr' := (hN _ 16 _ (by omega) (by omega) (by omega)).mp hr
    obtain ⟨_, l0, r0, _, -, hl0, hr0, -, -, -, hcl', hcr', -⟩ := hwf.internal_ok i hi1 hi2 hk
    have el := Rd.inj hl0 hl'
    have er := Rd.inj hr0 hr'
    subst el er
    have := hcl'.2.1
    have := hcr'.2.1
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hok.keys.internal_bits i hi1 hi2 hk b l0 r0 hb' hl' hr'
    exact ⟨x1, x2, x3, x4,
      fun bl h => x5 bl ((hN _ 24 _ (by omega) (by omega) (by omega)).mp h),
      fun br h => x6 br ((hN _ 24 _ (by omega) (by omega) (by omega)).mp h)⟩
  · intro i hi1 hi2 hk j hj
    have hi2 : i < v.next.toNat := hi2
    exact hKey i (by omega) j _ hj (hok.leaf_key i hi1 hi2 hk j hj)

theorem byteAt_aligned {M : Word → Option (PanValue Word)} {X : Word} {k : Nat}
    (hX8 : X.toNat % 8 = 0) (hX64 : X.toNat + 8 ≤ 2 ^ 64) (hk : k < 8) :
    byteAt M (off X k) = match M X with
      | some (.word c) => some (gb (off X k) c)
      | _ => none := by
  have hal : al8 (off X k) = X := by
    apply BitVec.eq_of_toNat_eq
    rw [align8_toNat, off_toNat (by omega)]
    omega
  unfold byteAt
  rw [hal]
  rfl

/-- An aligned cell holds `w` when its bytes are those of a cell holding `w`. -/
theorem rd_of_bytes {M M' : Word → Option (PanValue Word)} {X Y w : Word}
    (hX8 : X.toNat % 8 = 0) (hY8 : Y.toNat % 8 = 0) (hX64 : X.toNat + 8 ≤ 2 ^ 64)
    (hY64 : Y.toNat + 8 ≤ 2 ^ 64)
    (h : ∀ k, k < 8 → byteAt M (off X k) = byteAt M' (off Y k)) (hw : Rd M' Y w) : Rd M X w := by
  unfold Rd at hw ⊢
  have h0 := h 0 (by omega)
  rw [byteAt_aligned hX8 hX64 (by omega), byteAt_aligned hY8 hY64 (by omega), hw] at h0
  cases hM : M X with
  | none => rw [hM] at h0; cases h0
  | some x =>
    cases x with
    | word c =>
      have hc : c = w := by
        refine word_ext hX8 hY8 hX64 hY64 (fun k hk => ?_)
        have hk' := h k hk
        rw [byteAt_aligned hX8 hX64 hk, byteAt_aligned hY8 hY64 hk, hw, hM] at hk'
        exact Option.some.inj hk'
      rw [hc]
    | _ => rw [hM] at h0; cases h0

theorem rd_iff_bytes {M M' : Word → Option (PanValue Word)} {X Y : Word} (w : Word)
    (hX8 : X.toNat % 8 = 0) (hY8 : Y.toNat % 8 = 0) (hX64 : X.toNat + 8 ≤ 2 ^ 64)
    (hY64 : Y.toNat + 8 ≤ 2 ^ 64)
    (h : ∀ k, k < 8 → byteAt M (off X k) = byteAt M' (off Y k)) : Rd M X w ↔ Rd M' Y w :=
  ⟨rd_of_bytes hY8 hX8 hY64 hX64 (fun k hk => (h k hk).symm),
    rd_of_bytes hX8 hY8 hX64 hY64 h⟩

/-- A key bit read through bytes that agree with another key's bytes. -/
theorem KeyBitIs.of_bytes {kp kp' j : Word} {bit : Bool}
    (h : ∀ a : Word, a.toNat = j.toNat / 8 → byteAt m' (kp' + a) = byteAt m (kp + a))
    (hold : KeyBitIs 8#64 m kp j bit) : KeyBitIs 8#64 m' kp' j bit := by
  intro a cell y hs hcell hy
  have ha : a.toNat = j.toNat / 8 := by
    unfold RiscV.panRiscVShift at hs
    split at hs
    · simp only [Option.some.injEq] at hs
      subst hs
      have h3 : (3#64 : Word).toNat = 3 := by decide
      rw [h3, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    · cases hs
  have hb := h a ha
  unfold byteAt at hb
  rw [hcell] at hb
  cases hm : m (al8 (kp + a)) with
  | none => rw [hm] at hb; cases hb
  | some x =>
    cases x with
    | word c0 =>
      rw [hm] at hb
      simp only [Option.some.injEq] at hb
      have hb' : RiscV.panRiscVGetByte 8#64 (kp' + a) cell =
          RiscV.panRiscVGetByte 8#64 (kp + a) c0 := hb
      exact hold a c0 y hs hm (by rw [← hb']; exact hy)
    | _ => rw [hm] at hb; cases hb

theorem byteAt_congr {M M' : Word → Option (PanValue Word)} {X : Word}
    (h : M (al8 X) = M' (al8 X)) : byteAt M X = byteAt M' X := by
  unfold byteAt
  rw [h]

set_option maxHeartbeats 4000000 in
/-- After `htab_grow` the table is well formed at its new blocks, with twice the capacity. -/
theorem htab_grow_ok (hok : HtabOK m t v kind rep) {pv N O q : Word}
    {mF : Word → Option (PanValue Word)} (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (R : GrowRel m t v pv N O q mF) :
    HtabOK mF t ⟨v.kl, v.st, v.cp * 2#64, v.nc * 2#64, v.cnt, pv, N, O, v.root, v.next, v.free⟩
      kind rep := by
  obtain ⟨hN, inN, hO, inO, hq, inq, m1, m2, m3, c1, c2, c3, rfl⟩ := R
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  obtain ⟨hple, hp8⟩ := hpH
  obtain ⟨hNle, hN8⟩ := inN
  obtain ⟨hOle, hO8⟩ := inO
  obtain ⟨hqle, hq8⟩ := inq
  have h2 : (2#64 : Word).toNat = 2 := by decide
  have hncs : v.nc.toNat < 2 ^ 27 := by omega
  have hnc2 : (v.nc * 2#64).toNat = v.nc.toNat * 2 := by
    rw [BitVec.toNat_mul, h2]
    exact Nat.mod_eq_of_lt (by omega)
  have hbig : (v.nc.toNat + 1) * v.st.toNat ≤ (v.nc.toNat * 2 + 1) * v.st.toNat :=
    Nat.mul_le_mul_right _ (by omega)
  have hT : ∀ k, k < 88 → (t + BitVec.ofNat 64 k).toNat = t.toNat + k :=
    fun k hk => hdr_toNat hlay hk
  have E1 : ∀ A : Word, A.toNat + 8 ≤ pv.toNat → m1 A = m A := fun A hA => c1.cells A (Or.inl hA)
  have E2 : ∀ A : Word, A.toNat + 8 ≤ N.toNat → m2 A = setCell m1 (t + 32#64) pv A :=
    fun A hA => c2.cells A (Or.inl hA)
  have E3 : ∀ A : Word, A.toNat + 8 ≤ O.toNat → m3 A = setCell m2 (t + 40#64) N A :=
    fun A hA => c3.cells A (Or.inl hA)
  have hneT : ∀ (A : Word) (k : Nat), k < 88 → t.toNat + k ≠ A.toNat → A ≠ t + BitVec.ofNat 64 k := by
    intro A k hk hne h
    rw [h, hT k hk] at hne
    exact hne rfl
  -- cells from the heap pointer on are untouched by the header stores
  have hF : ∀ A : Word, pv.toNat ≤ A.toNat →
      setCell (setCell (setCell m3 (t + 48#64) O) (t + 16#64) (v.cp * 2#64)) (t + 80#64)
        (v.nc * 2#64) A = m3 A := by
    intro A hA
    rw [setCell_ne' _ (hneT A 80 (by omega) (by omega)),
      setCell_ne' _ (hneT A 16 (by omega) (by omega)),
      setCell_ne' _ (hneT A 48 (by omega) (by omega))]
  have hH : ∀ k, k < 88 → k ≠ 16 → k ≠ 32 → k ≠ 40 → k ≠ 48 → k ≠ 80 →
      setCell (setCell (setCell m3 (t + 48#64) O) (t + 16#64) (v.cp * 2#64)) (t + 80#64)
        (v.nc * 2#64) (t + BitVec.ofNat 64 k) = m (t + BitVec.ofNat 64 k) := by
    intro k hk k16 k32 k40 k48 k80
    have hk8 : (t + BitVec.ofNat 64 k).toNat = t.toNat + k := hT k hk
    rw [setCell_ne' _ (hneT _ 80 (by omega) (by omega)),
      setCell_ne' _ (hneT _ 16 (by omega) (by omega)),
      setCell_ne' _ (hneT _ 48 (by omega) (by omega)), E3 _ (by omega),
      setCell_ne' _ (hneT _ 40 (by omega) (by omega)), E2 _ (by omega),
      setCell_ne' _ (hneT _ 32 (by omega) (by omega)), E1 _ (by omega)]
  refine HtabOK.transport hok (by rw [hnc2]; omega) ?_ ?_ hp8 hN8 hO8 ?_ ?_ ?_
  · -- layout
    refine ⟨by show t.toNat + 88 ≤ pv.toNat; omega, ?_, ?_, ?_⟩
    · show pv.toNat + ((v.nc * 2#64).toNat + 1) * v.st.toNat ≤ N.toNat
      rw [hnc2]
      exact hN
    · show N.toNat + ((v.nc * 2#64).toNat + 1) * 32 ≤ O.toNat
      rw [hnc2]
      exact hO
    · show O.toNat + ((v.nc * 2#64).toNat + 1) * 8 ≤ 2952790016
      rw [hnc2]
      omega
  · -- header
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · unfold Rd; rw [hH 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hkl
    · unfold Rd; rw [hH 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hst
    · unfold Rd
      rw [setCell_ne' _ (hneT _ 80 (by omega) (by rw [hT 16 (by omega)]; omega))]
      exact Rd.here _ _ _
    · unfold Rd; rw [hH 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hcnt
    · unfold Rd
      rw [setCell_ne' _ (hneT _ 80 (by omega) (by rw [hT 32 (by omega)]; omega)),
        setCell_ne' _ (hneT _ 16 (by omega) (by rw [hT 32 (by omega)]; omega)),
        setCell_ne' _ (hneT _ 48 (by omega) (by rw [hT 32 (by omega)]; omega)),
        E3 _ (by rw [hT 32 (by omega)]; omega),
        setCell_ne' _ (hneT _ 40 (by omega) (by rw [hT 32 (by omega)]; omega)),
        E2 _ (by rw [hT 32 (by omega)]; omega)]
      exact Rd.here _ _ _
    · unfold Rd
      rw [setCell_ne' _ (hneT _ 80 (by omega) (by rw [hT 40 (by omega)]; omega)),
        setCell_ne' _ (hneT _ 16 (by omega) (by rw [hT 40 (by omega)]; omega)),
        setCell_ne' _ (hneT _ 48 (by omega) (by rw [hT 40 (by omega)]; omega)),
        E3 _ (by rw [hT 40 (by omega)]; omega)]
      exact Rd.here _ _ _
    · unfold Rd
      rw [setCell_ne' _ (hneT _ 80 (by omega) (by rw [hT 48 (by omega)]; omega)),
        setCell_ne' _ (hneT _ 16 (by omega) (by rw [hT 48 (by omega)]; omega))]
      exact Rd.here _ _ _
    · unfold Rd; rw [hH 56 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hroot
    · unfold Rd; rw [hH 64 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hnext
    · unfold Rd; rw [hH 72 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hfree
    · exact Rd.here _ _ _
  · -- node cells
    intro i o w hi ho ho8
    have hX : (off N (i * 32 + o)).toNat = N.toNat + (i * 32 + o) := off_toNat (by omega)
    have hY : (off v.nodes (i * 32 + o)).toNat = v.nodes.toNat + (i * 32 + o) :=
      off_toNat (by omega)
    show Rd _ (off N (i * 32 + o)) w ↔ Rd m (off v.nodes (i * 32 + o)) w
    have e1 : setCell (setCell (setCell m3 (t + 48#64) O) (t + 16#64) (v.cp * 2#64)) (t + 80#64)
        (v.nc * 2#64) (off N (i * 32 + o)) = m2 (off N (i * 32 + o)) := by
      rw [hF _ (by omega), E3 _ (by omega), setCell_ne' _ (hneT _ 40 (by omega) (by omega))]
    have e2 : setCell m1 (t + 32#64) pv (off v.nodes (i * 32 + o)) =
        m (off v.nodes (i * 32 + o)) := by
      rw [setCell_ne' _ (hneT _ 32 (by omega) (by omega)), E1 _ (by omega)]
    unfold Rd
    rw [e1, ← e2]
    exact rd_iff_bytes w (by omega) (by have := hok.nodes8; omega) (by omega) (by omega)
      (fun k hk => by rw [off_off, off_off]; exact c2.copied _ (by omega))
  · -- order slots
    intro p w hp
    have hX : (off O (p * 8)).toNat = O.toNat + p * 8 := off_toNat (by omega)
    have hY : (off v.order (p * 8)).toNat = v.order.toNat + p * 8 := off_toNat (by omega)
    show Rd _ (off O (p * 8)) w ↔ Rd m (off v.order (p * 8)) w
    have e1 : setCell (setCell (setCell m3 (t + 48#64) O) (t + 16#64) (v.cp * 2#64)) (t + 80#64)
        (v.nc * 2#64) (off O (p * 8)) = m3 (off O (p * 8)) := hF _ (by omega)
    have e2 : setCell m2 (t + 40#64) N (off v.order (p * 8)) = m (off v.order (p * 8)) := by
      rw [setCell_ne' _ (hneT _ 40 (by omega) (by omega)), E2 _ (by omega),
        setCell_ne' _ (hneT _ 32 (by omega) (by omega)), E1 _ (by omega)]
    unfold Rd
    rw [e1, ← e2]
    exact rd_iff_bytes w (by omega) (by have := hok.order8; omega) (by omega) (by omega)
      (fun k hk => by rw [off_off, off_off]; exact c3.copied _ (by omega))
  · -- key bits
    intro i hi j bit hj hold
    refine KeyBitIs.of_bytes ?_ hold
    intro a ha
    have h8 : (8#64 : Word).toNat = 8 := by decide
    have hkl8 : (v.kl * 8#64).toNat = v.kl.toNat * 8 := by
      rw [BitVec.toNat_mul, h8]
      exact Nat.mod_eq_of_lt hok.kl8
    have hklst := hok.kl_st
    have hle : i * v.st.toNat + v.st.toNat ≤ (v.nc.toNat + 1) * v.st.toNat := by
      have : (i + 1) * v.st.toNat ≤ (v.nc.toNat + 1) * v.st.toNat :=
        Nat.mul_le_mul_right _ (by omega)
      have e : (i + 1) * v.st.toNat = i * v.st.toNat + v.st.toNat := by ring
      omega
    have hmul : (BitVec.ofNat 64 i * v.st).toNat = i * v.st.toNat := by
      have hi64 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat, hi64]
      exact Nat.mod_eq_of_lt (by omega)
    have eK : pv + BitVec.ofNat 64 i * v.st + a = off pv (i * v.st.toNat + a.toNat) := by
      apply BitVec.eq_of_toNat_eq
      rw [off_toNat (by omega), BitVec.toNat_add, BitVec.toNat_add, hmul]
      omega
    have eS : v.keys + BitVec.ofNat 64 i * v.st + a = off v.keys (i * v.st.toNat + a.toNat) := by
      apply BitVec.eq_of_toNat_eq
      rw [off_toNat (by omega), BitVec.toNat_add, BitVec.toNat_add, hmul]
      omega
    rw [eK, eS, ← c1.copied _ (by omega)]
    apply byteAt_congr
    have hX : (off pv (i * v.st.toNat + a.toNat)).toNat = pv.toNat + (i * v.st.toNat + a.toNat) :=
      off_toNat (by omega)
    have hC : (al8 (off pv (i * v.st.toNat + a.toNat))).toNat =
        (pv.toNat + (i * v.st.toNat + a.toNat)) / 8 * 8 := by rw [align8_toNat, hX]
    rw [hF _ (by omega), E3 _ (by omega), setCell_ne' _ (hneT _ 40 (by omega) (by omega)),
      E2 _ (by omega), setCell_ne' _ (hneT _ 32 (by omega) (by omega))]

end InitECandidate.Solver.GuestBound
