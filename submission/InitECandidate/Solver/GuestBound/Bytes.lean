import Mathlib.Tactic.IntervalCases
import InitECandidate.Solver.GuestBound.HtabCells

/-!
# Bytes of memory

Memory holds word cells; a byte access reads or patches one byte of the
aligned cell. `byteAt m a` is the byte at address `a`, if its cell holds a word.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- The aligned cell of an address. -/
abbrev al8 (a : Word) : Word := RiscV.panRiscVByteAlign 8#64 a

/-- Byte of the cell value `c` selected by address `a`. -/
abbrev gb (a c : Word) : Word := RiscV.panRiscVGetByte 8#64 a c

/-- Cell value `c` with the byte selected by `a` replaced by `b`. -/
abbrev sb (a b c : Word) : Word := RiscV.panRiscVSetByte 8#64 a b c

theorem setCell_ne' {m : Word → Option (PanValue Word)} {a a' : Word} (x : Word) (h : a ≠ a') :
    setCell m a' x a = m a := by
  unfold setCell
  have : (a == a') = false := by simpa using h
  rw [this]
  rfl

/-- The byte at address `a`. -/
def byteAt (m : Word → Option (PanValue Word)) (a : Word) : Option Word :=
  match m (al8 a) with
  | some (.word c) => some (gb a c)
  | _ => none

theorem gb_toNat (a c : Word) : (gb a c).toNat = c.toNat / 256 ^ (a.toNat % 8) % 256 := by
  have h8 : (8#64 : Word).toNat = 8 := by decide
  unfold gb RiscV.panRiscVGetByte RiscV.panRiscVByteIndex
  simp only [h8]
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem getset_nat (c b i i' : Nat) (hc : c < 2 ^ 64) (hi : i < 8) (hi' : i' < 8) :
    ((c % 256 ^ i' + (b % 256) * 256 ^ i' + c / (256 ^ i' * 256) * (256 ^ i' * 256)) % 2 ^ 64 /
      256 ^ i) % 256 = if i = i' then b % 256 else (c / 256 ^ i) % 256 := by
  have hb : b % 256 < 256 := Nat.mod_lt _ (by decide)
  generalize b % 256 = B at hb
  interval_cases i <;> interval_cases i' <;> simp <;> omega

theorem gb_sb (a a' b c : Word) :
    gb a (sb a' b c) =
      if a.toNat % 8 = a'.toNat % 8 then BitVec.ofNat 64 (b.toNat % 256) else gb a c := by
  apply BitVec.eq_of_toNat_eq
  rw [gb_toNat]
  have h8 : (8#64 : Word).toNat = 8 := by decide
  have hset : (sb a' b c).toNat = (c.toNat % 256 ^ (a'.toNat % 8) +
      (b.toNat % 256) * 256 ^ (a'.toNat % 8) +
      c.toNat / (256 ^ (a'.toNat % 8) * 256) * (256 ^ (a'.toNat % 8) * 256)) % 2 ^ 64 := by
    unfold sb RiscV.panRiscVSetByte RiscV.panRiscVByteIndex
    simp only [h8]
    rw [BitVec.toNat_ofNat]
  rw [hset, getset_nat _ _ _ _ c.isLt (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))]
  split
  · rw [BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · rw [gb_toNat]

theorem al8_eq_iff (a a' : Word) :
    a = a' ↔ al8 a = al8 a' ∧ a.toNat % 8 = a'.toNat % 8 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h1
    rw [align8_toNat, align8_toNat] at this
    omega

/-- Bytes after a byte store. -/
theorem byteAt_storeByte (m : Word → Option (PanValue Word)) (a' b c : Word)
    (hc : m (al8 a') = some (.word c)) (a : Word) :
    byteAt (setCell m (al8 a') (sb a' b c)) a =
      if a = a' then some (BitVec.ofNat 64 (b.toNat % 256)) else byteAt m a := by
  unfold byteAt setCell
  by_cases hcell : al8 a = al8 a'
  · have hbeq : (al8 a == al8 a') = true := by simpa using hcell
    simp only [hbeq, if_true]
    rw [gb_sb]
    by_cases hmod : a.toNat % 8 = a'.toNat % 8
    · rw [if_pos hmod, if_pos ((al8_eq_iff a a').mpr ⟨hcell, hmod⟩)]
    · rw [if_neg hmod, if_neg (fun h => hmod ((al8_eq_iff a a').mp h).2), hcell, hc]
  · have hbeq : (al8 a == al8 a') = false := by simpa using hcell
    simp only [hbeq]
    rw [if_neg (fun h => hcell ((al8_eq_iff a a').mp h).1)]
    rfl

/-- Bytes after a word store into an aligned cell. -/
theorem byteAt_setCell (m : Word → Option (PanValue Word)) (A w a : Word) :
    byteAt (setCell m A w) a = if al8 a = A then some (gb a w) else byteAt m a := by
  unfold byteAt setCell
  by_cases h : al8 a = A
  · have hbeq : (al8 a == A) = true := by simpa using h
    simp only [hbeq, if_true, if_pos h]
  · have hbeq : (al8 a == A) = false := by simpa using h
    simp only [hbeq, if_neg h]
    rfl

/-- Address `a + k`. -/
def off (a : Word) (k : Nat) : Word := a + BitVec.ofNat 64 k

theorem off_toNat {a : Word} {k : Nat} (h : a.toNat + k < 2 ^ 64) :
    (off a k).toNat = a.toNat + k := by
  unfold off
  have hk : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, hk]
  exact Nat.mod_eq_of_lt h

theorem gb_congr {a a' : Word} (c : Word) (h : a.toNat % 8 = a'.toNat % 8) : gb a c = gb a' c := by
  apply BitVec.eq_of_toNat_eq
  rw [gb_toNat, gb_toNat, h]

theorem gb_lt (a c : Word) : (gb a c).toNat < 256 := by
  rw [gb_toNat]
  exact Nat.mod_lt _ (by decide)

/-- After copying `j` bytes from `src` to `dst`, starting from memory `m0`. -/
structure CopyInv (m0 : Word → Option (PanValue Word)) (dst src : Word) (j : Nat)
    (m : Word → Option (PanValue Word)) : Prop where
  copied : ∀ k, k < j → byteAt m (off dst k) = byteAt m0 (off src k)
  rest : ∀ a : Word, (a.toNat < dst.toNat ∨ dst.toNat + j ≤ a.toNat) → byteAt m a = byteAt m0 a
  cells : ∀ A : Word, (A.toNat + 8 ≤ dst.toNat ∨ dst.toNat + j ≤ A.toNat ∨ A.toNat % 8 ≠ 0) →
    m A = m0 A

theorem CopyInv.start (m0 : Word → Option (PanValue Word)) (dst src : Word) :
    CopyInv m0 dst src 0 m0 :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ => rfl⟩

variable {m0 m : Word → Option (PanValue Word)} {dst src : Word} {j n : Nat}

/-- One more byte copied. -/
theorem CopyInv.byte (h : CopyInv m0 dst src j m) (hj : j < n) (hd : dst.toNat + n < 2 ^ 64)
    (hs : src.toNat + n < 2 ^ 64)
    (hdisj : src.toNat + n ≤ dst.toNat ∨ dst.toNat + n ≤ src.toNat) {c b : Word}
    (hc : m (al8 (off dst j)) = some (.word c)) (hb : byteAt m (off src j) = some b) :
    CopyInv m0 dst src (j + 1) (setCell m (al8 (off dst j)) (sb (off dst j) b c)) := by
  have hdj : (off dst j).toNat = dst.toNat + j := off_toNat (by omega)
  have hsj : (off src j).toNat = src.toNat + j := off_toNat (by omega)
  have hsrc : byteAt m (off src j) = byteAt m0 (off src j) := h.rest _ (by omega)
  have hbb : BitVec.ofNat 64 (b.toNat % 256) = b := by
    unfold byteAt at hb
    split at hb
    · simp only [Option.some.injEq] at hb
      rw [← hb]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (gb_lt _ _)]
      exact Nat.mod_eq_of_lt (by have := gb_lt (off src j) ‹Word›; omega)
    · cases hb
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [byteAt_storeByte m _ b c hc]
    by_cases hkj : k = j
    · subst hkj
      rw [if_pos rfl, hbb, ← hb, hsrc]
    · have hne : off dst k ≠ off dst j := by
        intro heq
        have := congrArg BitVec.toNat heq
        rw [off_toNat (by omega), hdj] at this
        omega
      rw [if_neg hne]
      exact h.copied k (by omega)
  · intro a ha
    rw [byteAt_storeByte m _ b c hc]
    have hne : a ≠ off dst j := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [hdj] at this
      omega
    rw [if_neg hne]
    exact h.rest a (by omega)
  · intro A hA
    have hne : A ≠ al8 (off dst j) := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [align8_toNat, hdj] at this
      omega
    rw [setCell_ne' _ hne]
    exact h.cells A (by omega)

/-- One more aligned word copied. -/
theorem CopyInv.word (h : CopyInv m0 dst src j m) (hj : j + 8 ≤ n) (hd : dst.toNat + n < 2 ^ 64)
    (hs : src.toNat + n < 2 ^ 64)
    (hdisj : src.toNat + n ≤ dst.toNat ∨ dst.toNat + n ≤ src.toNat)
    (hd8 : (dst.toNat + j) % 8 = 0) (hs8 : (src.toNat + j) % 8 = 0) {w : Word}
    (hw : m (off src j) = some (.word w)) :
    CopyInv m0 dst src (j + 8) (setCell m (off dst j) w) := by
  have hdj : (off dst j).toNat = dst.toNat + j := off_toNat (by omega)
  have hsj : (off src j).toNat = src.toNat + j := off_toNat (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have hdk : (off dst k).toNat = dst.toNat + k := off_toNat (by omega)
    have hsk : (off src k).toNat = src.toNat + k := off_toNat (by omega)
    rw [byteAt_setCell]
    by_cases hkj : j ≤ k
    · have hal : al8 (off dst k) = off dst j := by
        apply BitVec.eq_of_toNat_eq
        rw [align8_toNat, hdk, hdj]
        omega
      rw [if_pos hal, ← h.rest (off src k) (by omega)]
      have hals : al8 (off src k) = off src j := by
        apply BitVec.eq_of_toNat_eq
        rw [align8_toNat, hsk, hsj]
        omega
      unfold byteAt
      rw [hals, hw]
      simp only [Option.some.injEq]
      exact gb_congr w (by rw [hdk, hsk]; omega)
    · have hal : al8 (off dst k) ≠ off dst j := by
        intro heq
        have := congrArg BitVec.toNat heq
        rw [align8_toNat, hdk, hdj] at this
        omega
      rw [if_neg hal]
      exact h.copied k (by omega)
  · intro a ha
    rw [byteAt_setCell]
    have hal : al8 a ≠ off dst j := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [align8_toNat, hdj] at this
      omega
    rw [if_neg hal]
    exact h.rest a (by omega)
  · intro A hA
    have hne : A ≠ off dst j := by
      intro heq
      have := congrArg BitVec.toNat heq
      rw [hdj] at this
      omega
    rw [setCell_ne' _ hne]
    exact h.cells A (by omega)

/-- A 64-bit value is determined by its eight bytes. -/
theorem nat_bytes_ext (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h0 : a / 256 ^ 0 % 256 = b / 256 ^ 0 % 256) (h1 : a / 256 ^ 1 % 256 = b / 256 ^ 1 % 256)
    (h2 : a / 256 ^ 2 % 256 = b / 256 ^ 2 % 256) (h3 : a / 256 ^ 3 % 256 = b / 256 ^ 3 % 256)
    (h4 : a / 256 ^ 4 % 256 = b / 256 ^ 4 % 256) (h5 : a / 256 ^ 5 % 256 = b / 256 ^ 5 % 256)
    (h6 : a / 256 ^ 6 % 256 = b / 256 ^ 6 % 256) (h7 : a / 256 ^ 7 % 256 = b / 256 ^ 7 % 256) :
    a = b := by
  omega

/-- Two cell values with the same bytes, read through aligned cells, are equal. -/
theorem word_ext {A B w1 w2 : Word} (hA : A.toNat % 8 = 0) (hB : B.toNat % 8 = 0)
    (hA64 : A.toNat + 8 ≤ 2 ^ 64) (hB64 : B.toNat + 8 ≤ 2 ^ 64)
    (h : ∀ k, k < 8 → gb (off A k) w1 = gb (off B k) w2) : w1 = w2 := by
  apply BitVec.eq_of_toNat_eq
  have key : ∀ k, k < 8 → w1.toNat / 256 ^ k % 256 = w2.toNat / 256 ^ k % 256 := by
    intro k hk
    have := congrArg BitVec.toNat (h k hk)
    rw [gb_toNat, gb_toNat, off_toNat (by omega), off_toNat (by omega)] at this
    have e1 : (A.toNat + k) % 8 = k := by omega
    have e2 : (B.toNat + k) % 8 = k := by omega
    rw [e1, e2] at this
    exact this
  exact nat_bytes_ext _ _ w1.isLt w2.isLt (key 0 (by omega)) (key 1 (by omega))
    (key 2 (by omega)) (key 3 (by omega)) (key 4 (by omega)) (key 5 (by omega))
    (key 6 (by omega)) (key 7 (by omega))

end InitECandidate.Solver.GuestBound
