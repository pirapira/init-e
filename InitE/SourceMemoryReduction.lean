import InitE.SourceReduction
import InitE.SourceWordTrie

namespace InitE.SourceMemoryReduction
open Flapjack Lean Meta Sym Meta.Tactic.Cbv

abbrev Words := SourceWordTrie.Words

def overlay (base : BitVec 64 → HolWordLab 64) (words : Words) (address : BitVec 64) :
    HolWordLab 64 := (words.lookup address.toNat).getD (base address)

scoped cbv_simproc holdOverlay (overlay _ _) :=
  fun e => return .rfl (done := e.getAppNumArgs == 2)

theorem overlay_update (base : BitVec 64 → HolWordLab 64) (words : Words)
    (address : BitVec 64) (value : HolWordLab 64) :
    (fun current => if current = address then value else overlay base words current) =
      overlay base (words.insert address.toNat value) := by
  funext current
  by_cases equal : current = address
  · subst current
    simp [overlay, SourceWordTrie.lookup_insert]
  · simp [overlay, SourceWordTrie.lookup_insert, equal, BitVec.toNat_inj]

theorem store_overlay (base : BitVec 64 → HolWordLab 64) (words : Words)
    (domain : BitVec 64 → Prop) [DecidablePred domain]
    (address : BitVec 64) (value : HolWordLab 64) :
    panMemStoreHOL address value domain (overlay base words) =
      if domain address then some (overlay base (words.insert address.toNat value)) else none := by
  unfold panMemStoreHOL
  split
  · rw [overlay_update]
  · rfl

attribute [scoped cbv_eval] store_overlay

theorem store_byte_overlay (base : BitVec 64 → HolWordLab 64) (words : Words)
    (domain : BitVec 64 → Prop) [DecidablePred domain] (be : Bool)
    (address : BitVec 64) (byte : BitVec 8) :
    panMemStoreByteWord8HOL (overlay base words) domain be address byte =
      (match overlay base words (panByteAlignHOL address) with
      | .word cell =>
        if domain (panByteAlignHOL address) then
          some (overlay base (words.insert (panByteAlignHOL address).toNat
            (.word (panSetByteHOL address (BitVec.ofNat 64 byte.toNat) cell be))))
        else none) := by
  unfold panMemStoreByteWord8HOL
  cases cell : overlay base words (panByteAlignHOL address)
  dsimp only
  split
  · rw [overlay_update]
    simp only [cell]
  · rfl

attribute [scoped cbv_eval] store_byte_overlay

theorem source_memory_overlay :
    sourceMemory = overlay (fun address => .word
      (if sourceBase ≤ address.toNat ∧ address.toNat < sourceBase + 40 then
        Guest.startupHeaders[(address.toNat - sourceBase) / 8]?.getD 0 else 0))
      (∅ : Words) := by
  funext address
  simp [overlay, sourceMemory]

attribute [scoped cbv_eval] source_memory_overlay

end InitE.SourceMemoryReduction
