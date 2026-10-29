import InitE.SourceReduction
import Mathlib.Data.Nat.Bits

/-! A proof-free memory representation. Lookup correctness is unconditional:
there is no bundled tree invariant to grow with the execution proof. -/
namespace InitE.SourceWordTrie
open Flapjack

inductive Words where
  | empty
  | node (value : Option (HolWordLab 64)) (left right : Words)

instance : EmptyCollection Words := ⟨.empty⟩

def root : Words → Option (HolWordLab 64)
  | .empty => none
  | .node value _ _ => value

def left : Words → Words
  | .empty => .empty
  | .node _ l _ => l

def right : Words → Words
  | .empty => .empty
  | .node _ _ r => r

def getBits : Words → List Bool → Option (HolWordLab 64)
  | words, [] => root words
  | words, false :: bits => getBits (left words) bits
  | words, true :: bits => getBits (right words) bits

def putBits (words : Words) : List Bool → HolWordLab 64 → Words
  | [], value => .node (some value) (left words) (right words)
  | false :: bits, value => .node (root words) (putBits (left words) bits value) (right words)
  | true :: bits, value => .node (root words) (left words) (putBits (right words) bits value)

theorem getBits_putBits (words : Words) (key other : List Bool) (value : HolWordLab 64) :
    getBits (putBits words key value) other =
      if other = key then some value else getBits words other := by
  induction key generalizing words other with
  | nil =>
    cases other with
    | nil => rfl
    | cons b bs => cases b <;> simp [putBits, getBits, left, right]
  | cons b bs ih =>
    cases other with
    | nil => cases b <;> simp [putBits, getBits, root, left, right]
    | cons c cs => cases b <;> cases c <;>
        simp [putBits, getBits, root, left, right, ih]

def decodeBits : List Bool → Nat := List.foldr Nat.bit 0

theorem decodeBits_bits (key : Nat) : decodeBits key.bits = key := by
  induction key using Nat.binaryRec with
  | zero => simp [decodeBits]
  | bit b n ih =>
    by_cases zero : n = 0
    · subst n
      cases b <;> simp [decodeBits, Nat.bit, Nat.one_bits]
    · rw [Nat.bits_append_bit n b (by intro equal; exact False.elim (zero equal))]
      change Nat.bit b (decodeBits n.bits) = Nat.bit b n
      rw [ih]

theorem bits_injective : Function.Injective Nat.bits := by
  intro a b equal
  simpa only [decodeBits_bits] using congrArg decodeBits equal

def Words.lookup (words : Words) (key : Nat) := getBits words key.bits

def Words.insert (words : Words) (key : Nat) (value : HolWordLab 64) :=
  putBits words key.bits value

@[simp] theorem lookup_empty (key : Nat) : (∅ : Words).lookup key = none := by
  change getBits Words.empty key.bits = none
  generalize key.bits = bits
  induction bits with
  | nil => rfl
  | cons b bs ih => cases b <;> simpa [getBits, left, right] using ih

theorem lookup_insert (words : Words) (key other : Nat) (value : HolWordLab 64) :
    (words.insert key value).lookup other =
      if other = key then some value else words.lookup other := by
  simp only [Words.lookup, Words.insert, getBits_putBits, bits_injective.eq_iff]

end InitE.SourceWordTrie
