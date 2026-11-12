import InitECandidate.Solver.GuestBound.MemCpy

/-!
# `memeq` on equal bytes

When the `n` bytes at `a` and at `b` are equal, no comparison in `memeq`
fails, so the function returns 1 if it returns.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The compared ranges do not wrap and hold the same bytes. -/
structure EqPre (m : Word → Option (PanValue Word)) (A B nW : Word) : Prop where
  hA : A.toNat + nW.toNat < 2 ^ 64
  hB : B.toNat + nW.toNat < 2 ^ 64
  hn : nW.toNat < 2 ^ 63
  bytes : ∀ k, k < nW.toNat → byteAt m (off A k) = byteAt m (off B k)

variable {m : Word → Option (PanValue Word)} {A B nW : Word}

theorem off_off (a : Word) (j k : Nat) : off (off a j) k = off a (j + k) := by
  unfold off
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The cell at an aligned offset holds the bytes of the range. -/
theorem byteAt_cell {a : Word} {j k : Nat} {w : Word} (h64 : a.toNat + j + 8 ≤ 2 ^ 64)
    (h8 : (a.toNat + j) % 8 = 0) (hk : k < 8) (hw : m (off a j) = some (.word w)) :
    byteAt m (off a (j + k)) = some (gb (off (off a j) k) w) := by
  have hal : al8 (off a (j + k)) = off a j := by
    apply BitVec.eq_of_toNat_eq
    rw [align8_toNat, off_toNat (by omega), off_toNat (by omega)]
    omega
  unfold byteAt
  rw [hal, hw, off_off]

/-- `if lds 1 ea != lds 1 eb { return 0; }` on equal aligned words. -/
theorem eq_wguard (hE : GuestEnv E) (P : EqPre m A B nW) (hm : s.memory = m)
    {ea eb : Exp Word} {rest : Prog Word} {j : Nat}
    (hea : E.eval s ea = some (.word (off A j))) (heb : E.eval s eb = some (.word (off B j)))
    (hj : j + 8 ≤ nW.toNat) (hA8 : (A.toNat + j) % 8 = 0) (hB8 : (B.toNat + j) % 8 = 0)
    (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual (.load .one ea) (.load .one eb))
      (.return (.const 0#64)) .skip) rest) Q := by
  have hPA := P.hA
  have hPB := P.hB
  refine WPs.guard0 ?_ h
  intro x hx
  rw [evalF_cmp hE.word] at hx
  cases h1 : E.eval s (.load .one ea) with
  | none => rw [h1] at hx; simp at hx
  | some y1 =>
    cases h2 : E.eval s (.load .one eb) with
    | none => rw [h1, h2] at hx; simp at hx
    | some y2 =>
      obtain ⟨a1, w1, ha1, rfl, hm1⟩ := eval_load_one hE.mem h1
      obtain ⟨a2, w2, ha2, rfl, hm2⟩ := eval_load_one hE.mem h2
      rw [hea] at ha1
      rw [heb] at ha2
      simp only [Option.some.injEq, PanValue.word.injEq] at ha1 ha2
      subst ha1 ha2
      rw [hm] at hm1 hm2
      have hw : w1 = w2 := by
        refine word_ext (A := off A j) (B := off B j) (by rw [off_toNat (by omega)]; exact hA8)
          (by rw [off_toNat (by omega)]; exact hB8) (by rw [off_toNat (by omega)]; omega)
          (by rw [off_toNat (by omega)]; omega) ?_
        intro k hk
        have hb := P.bytes (j + k) (by omega)
        rw [byteAt_cell (by omega) hA8 hk hm1, byteAt_cell (by omega) hB8 hk hm2] at hb
        exact Option.some.inj hb
      subst hw
      rw [h1, h2] at hx
      simp only [Option.some.injEq] at hx
      rw [← hx]
      simp [evalPanCmp]

/-- `if ld8 ea != ld8 eb { return 0; }` on equal bytes. -/
theorem eq_bguard (hE : GuestEnv E) (P : EqPre m A B nW) (hm : s.memory = m)
    {ea eb : Exp Word} {rest : Prog Word} {j : Nat}
    (hea : E.eval s ea = some (.word (off A j))) (heb : E.eval s eb = some (.word (off B j)))
    (hj : j < nW.toNat) (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual (.loadByte ea) (.loadByte eb))
      (.return (.const 0#64)) .skip) rest) Q := by
  refine WPs.guard0 ?_ h
  intro x hx
  rw [evalF_cmp hE.word] at hx
  cases h1 : E.eval s (.loadByte ea) with
  | none => rw [h1] at hx; simp at hx
  | some y1 =>
    cases h2 : E.eval s (.loadByte eb) with
    | none => rw [h1, h2] at hx; simp at hx
    | some y2 =>
      obtain ⟨a1, c1, ha1, hc1, rfl⟩ := eval_loadByte hE.mem h1
      obtain ⟨a2, c2, ha2, hc2, rfl⟩ := eval_loadByte hE.mem h2
      rw [hea] at ha1
      rw [heb] at ha2
      simp only [Option.some.injEq, PanValue.word.injEq] at ha1 ha2
      subst ha1 ha2
      rw [hE.bytes, hm] at hc1 hc2
      have hb := P.bytes j hj
      unfold byteAt at hb
      rw [hc1, hc2] at hb
      have hv := Option.some.inj hb
      rw [h1, h2] at hx
      simp only [Option.some.injEq] at hx
      rw [← hx, hE.bytes]
      show PanValue.word (evalPanCmp .notEqual (gb (off A j) c1) (gb (off B j) c2)) = _
      rw [hv]
      simp [evalPanCmp]

end InitECandidate.Solver.GuestBound
