import InitECandidate.Solver.GuestBound.WorldNode

/-!
# Nibble segments of trie nodes

Branch slots are addressed by bytes read from nibble arrays, so memory safety
of the trie code needs those bytes to be below 16. `NibSeg m p n` says so for
`[p, p + n)`. Leaves and extensions store a segment pointer at `+32` and its
length at `+40`; `SegsOK Im m N` says every such segment is empty or lies in
an immutable block of `Im` and is a nibble array. `SegsOK.frame`: the property
survives any step that changes neither those two cells of a node nor a cell
of an immutable block.

This file only has the definitions and the frame lemma; `SegsOK` is not yet
part of `WorldTJ` (see the note on pirapira/init-e#21).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m m' : Word → Option (PanValue Word)} {N : Word → Option Word}
  {Im : Word → Word → Prop}

/-- The bytes of `[p, p + n)` are defined and below 16. -/
def NibSeg (m : Word → Option (PanValue Word)) (p n : Word) : Prop :=
  ∀ i : Nat, i < n.toNat → ∃ b : Word, byteAt m (off p i) = some b ∧ b.toNat < 16

/-- A nibble array inside an aligned range whose cells did not change. -/
theorem NibSeg.frame {p n lo hi : Word} (h : NibSeg m p n) (hlo8 : lo.toNat % 8 = 0)
    (hlo : lo.toNat ≤ p.toNat) (hhi : p.toNat + n.toNat ≤ hi.toNat)
    (hm : ∀ x : Word, x.toNat % 8 = 0 → lo.toNat ≤ x.toNat → x.toNat < hi.toNat → m' x = m x) :
    NibSeg m' p n := by
  intro i hi'
  obtain ⟨b, hb, hb16⟩ := h i hi'
  have hhi64 := hi.isLt
  have ho : (off p i).toNat = p.toNat + i := off_toNat (by omega)
  refine ⟨b, ?_, hb16⟩
  rw [byteAt_congr (hm _ (by rw [align8_toNat]; omega) (by rw [align8_toNat, ho]; omega)
    (by rw [align8_toNat, ho]; omega))]
  exact hb

/-- The segments of leaves and extensions: empty, or nibble arrays inside an
immutable block. -/
def SegsOK (Im : Word → Word → Prop) (m : Word → Option (PanValue Word))
    (N : Word → Option Word) : Prop :=
  ∀ a k, N a = some k → (k = 1#64 ∨ k = 2#64) → ∃ sp nl : Word,
    Rd m (a + 32#64) sp ∧ Rd m (a + 40#64) nl ∧
      (nl = 0#64 ∨ ∃ lo hi, Im lo hi ∧ lo.toNat % 8 = 0 ∧ lo.toNat ≤ sp.toNat ∧
        sp.toNat + nl.toNat ≤ hi.toNat ∧ NibSeg m sp nl)

/-- The cells `SegsOK` depends on. -/
def SegCell (Im : Word → Word → Prop) (N : Word → Option Word) (x : Word) : Prop :=
  (∃ a k, N a = some k ∧ (x = a + 32#64 ∨ x = a + 40#64)) ∨
    (x.toNat % 8 = 0 ∧ ∃ lo hi, Im lo hi ∧ lo.toNat ≤ x.toNat ∧ x.toNat < hi.toNat)

theorem SegsOK.frame (h : SegsOK Im m N) (hm : ∀ x, SegCell Im N x → m' x = m x) :
    SegsOK Im m' N := by
  intro a k hN hk
  obtain ⟨sp, nl, r1, r2, hcase⟩ := h a k hN hk
  have rd : ∀ x w, (x = a + 32#64 ∨ x = a + 40#64) → Rd m x w → Rd m' x w := by
    intro x w hx hr
    unfold Rd at hr ⊢
    rw [hm x (Or.inl ⟨a, k, hN, hx⟩)]
    exact hr
  refine ⟨sp, nl, rd _ _ (Or.inl rfl) r1, rd _ _ (Or.inr rfl) r2, ?_⟩
  rcases hcase with h0 | ⟨lo, hi, hI, hlo8, h1, h2, hn⟩
  · exact Or.inl h0
  · exact Or.inr ⟨lo, hi, hI, hlo8, h1, h2, hn.frame hlo8 h1 h2
      (fun x hx8 hx1 hx2 => hm x (Or.inr ⟨hx8, lo, hi, hI, hx1, hx2⟩))⟩

/-- More immutable blocks. -/
theorem SegsOK.mono {Im' : Word → Word → Prop} (h : SegsOK Im m N)
    (hI : ∀ lo hi, Im lo hi → Im' lo hi) : SegsOK Im' m N := by
  intro a k hN hk
  obtain ⟨sp, nl, r1, r2, hcase⟩ := h a k hN hk
  refine ⟨sp, nl, r1, r2, ?_⟩
  rcases hcase with h0 | ⟨lo, hi, hIm, rest⟩
  · exact Or.inl h0
  · exact Or.inr ⟨lo, hi, hI lo hi hIm, rest⟩

end InitECandidate.Solver.GuestBound
