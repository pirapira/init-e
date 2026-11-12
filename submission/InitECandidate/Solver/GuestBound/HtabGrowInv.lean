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

end InitECandidate.Solver.GuestBound
