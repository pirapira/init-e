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

end InitECandidate.Solver.GuestBound
