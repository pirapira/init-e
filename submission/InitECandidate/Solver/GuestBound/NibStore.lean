import InitECandidate.Solver.GuestBound.KeyNibbles
import InitECandidate.Solver.GuestBound.TrieSeg

/-!
# Byte stores of nibbles

`WPs.seq_storeByte_nib`: `st8 a, v; rest` when `v` evaluates to a word whose
low byte is below 16 — besides the cell frame of `WPs.seq_storeByte_fr`, the
continuation learns the bytes of the new memory. `nib_lsr4` / `nib_and15`: the
two value expressions `b >>> 4` and `b & 15` of a loaded byte. `Nibs.snoc`:
one more nibble at the end of a written prefix.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem Nibs.snoc {m m' : Word → Option (PanValue Word)} {o ad : Word} {c : Nat} {v : Word}
    (h : Nibs m o c) (hc : o.toNat + c < 2 ^ 64) (had : ad.toNat = o.toNat + c)
    (hv : v.toNat < 16)
    (hm : ∀ p, byteAt m' p = if p = ad then some v else byteAt m p) : Nibs m' o (c + 1) := by
  intro j hj
  rw [hm]
  by_cases e : off o j = ad
  · rw [if_pos e]
    exact ⟨v, rfl, hv⟩
  · rw [if_neg e]
    have : j ≠ c := by
      rintro rfl
      exact e (BitVec.eq_of_toNat_eq (by rw [off_toNat hc, had]))
    exact h j (by omega)

theorem Nibs.nibSeg {m : Word → Option (PanValue Word)} {o n : Word} (h : Nibs m o n.toNat) :
    NibSeg m o n := h

/-- `st8 a, v; rest` for a nibble value. -/
theorem WPs.seq_storeByte_nib (hE : GuestEnv E) {a v : Exp Word} {rest : Prog Word} {addr : Word}
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : ∀ y, E.eval s v = some y → ∃ b : Word, y = .word b ∧ b.toNat % 256 < 16)
    (h : ∀ m (w : Word), addr.toNat < 33806089704 + 8 →
      (∀ x : Word, x.toNat ≠ addr.toNat / 8 * 8 → m x = s.memory x) → w.toNat < 16 →
      (∀ p, byteAt m p = if p = addr then some w else byteAt s.memory p) →
      WPs E ⟨s.locals, s.globals, m, s.ffi⟩ rest Q) :
    WPs E s (.seq (.storeByte a v) rest) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  obtain ⟨fuel, n, hrun⟩ := h1
  rcases storeByte_inv' hE.mem hrun with herr | ⟨addr', val, cell, ha', hv', hcell, rfl, hdom⟩
  · cases r1 with
    | error l g m f => simp only at hrest; subst hrest; exact Or.inl trivial
    | _ => cases herr
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  obtain ⟨b, hb, hb16⟩ := hv _ hv'
  simp only [PanValue.word.injEq] at hb
  subst hb
  rw [hE.bytes] at hdom hrest hcell
  have hal : (al8 addr').toNat = addr'.toNat / 8 * 8 := align8_toNat addr'
  refine h _ (BitVec.ofNat 64 (val.toNat % 256)) (by rw [hal] at hdom; omega) (fun x hx => ?_)
    (by rw [BitVec.toNat_ofNat]; omega) (fun p => byteAt_storeByte _ _ _ _ hcell p) r hrest
  exact setCell_ne _ (by
    intro hh
    have := congrArg BitVec.toNat hh
    rw [hal] at this
    omega)

/-- A loaded byte is a word below 256. -/
theorem loadByte_lt (hE : GuestEnv E) {a : Exp Word} {x : PanValue Word}
    (h : E.eval s (.loadByte a) = some x) : ∃ b : Word, x = .word b ∧ b.toNat < 256 := by
  obtain ⟨addr, cell, -, -, rfl⟩ := eval_loadByte hE.mem h
  rw [hE.bytes]
  exact ⟨_, rfl, gb_lt _ _⟩

/-- `b >>> 4` of a byte is a nibble. -/
theorem nib_lsr4 (hE : GuestEnv E) {x : VarName} {b : Word} (hx : s.locals x = some (.word b))
    (hb : b.toNat < 256) :
    ∀ y, E.eval s (.shift .lsr (.var .local x) (.const 4#64)) = some y →
      ∃ w : Word, y = .word w ∧ w.toNat % 256 < 16 := by
  intro y hy
  rw [evalF_shift hE.word, evalF_local, hx, eval_const] at hy
  simp only [RiscV.panRiscVShift] at hy
  rw [if_pos (by decide)] at hy
  simp only [Option.map_some, Option.some.injEq] at hy
  subst hy
  refine ⟨_, rfl, ?_⟩
  rw [BitVec.toNat_ushiftRight, show (4#64 : Word).toNat = 4 by decide, Nat.shiftRight_eq_div_pow]
  omega

/-- `b & 15` is a nibble. -/
theorem nib_and15 (hE : GuestEnv E) {x : VarName} {b : Word} (hx : s.locals x = some (.word b)) :
    ∀ y, E.eval s (.op .and [.var .local x, .const 15#64]) = some y →
      ∃ w : Word, y = .word w ∧ w.toNat % 256 < 16 := by
  intro y hy
  simp (config := { decide := true }) [evalF_op hE.word, evalArgs_cons, evalArgs_nil,
    evalF_local, hx, wordsProj_cons, wordsProj_nil, wordOp] at hy
  subst hy
  refine ⟨_, rfl, ?_⟩
  have h15 : AndOp.and (15#64 : Word) 18446744073709551615#64 = 15#64 := by decide
  rw [h15]
  show (b &&& 15#64).toNat % 256 < 16
  rw [BitVec.toNat_and]
  have := Nat.and_two_pow_sub_one_eq_mod b.toNat 4
  have e : (15#64 : Word).toNat = 2 ^ 4 - 1 := by decide
  rw [e, this]
  omega

end InitECandidate.Solver.GuestBound
