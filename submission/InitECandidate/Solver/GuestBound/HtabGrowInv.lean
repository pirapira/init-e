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
    (hKey : ∀ i, i ≤ v.nc.toNat → ∀ (j : Word) (bit : Bool),
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
    exact hKey i (by omega) j _ (hok.leaf_key i hi1 hi2 hk j hj)

end InitECandidate.Solver.GuestBound
