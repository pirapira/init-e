import InitECandidate.Solver.GuestBound.FqAdd
import InitECandidate.Solver.GuestBound.HtabDel
import InitECandidate.Solver.GuestBound.U256Zero

/-!
# Montgomery multiplication in the bn254 base field: the column steps

`fq_mul` works on 32-bit digits. Each column adds products into a low sum `L`
and a high sum `H`; this file steps through one product.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {Q : Result σ → Prop}

theorem and32_toNat (w : Word) : (w &&& 4294967295#64).toNat = w.toNat % 2 ^ 32 := by
  have h : (4294967295#64 : Word).toNat = 2 ^ 32 - 1 := by decide
  rw [BitVec.toNat_and, h, Nat.and_two_pow_sub_one_eq_mod]

theorem shr32_toNat (w : Word) : (w >>> (32 : Nat)).toNat = w.toNat / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem shift32 (w : Word) : RiscV.panRiscVShift .lsr w 32#64 = some (w >>> (32 : Nat)) := by
  unfold RiscV.panRiscVShift
  rfl

theorem mul32_toNat {X Y : Word} (hX : X.toNat < 2 ^ 32) (hY : Y.toNat < 2 ^ 32) :
    (X * Y).toNat = X.toNat * Y.toNat := by
  rw [BitVec.toNat_mul]
  have : X.toNat * Y.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hX hY
  exact Nat.mod_eq_of_lt (by omega)

/-- `pr = x * y; L = L + (pr & M); H = H + (pr >>> 32); rest`. -/
def termStmts (x y : Exp Word) (rest : Prog Word) : Prog Word :=
  .seq (.assign .local "pr" (.panOp .mul [x, y]))
    (.seq (.assign .local "L" (.op .add [.var .local "L",
        .op .and [.var .local "pr", .const 4294967295#64]]))
      (.seq (.assign .local "H" (.op .add [.var .local "H",
        .shift .lsr (.var .local "pr") (.const 32#64)])) rest))

set_option maxHeartbeats 4000000 in
theorem term_wp (hE : GuestEnv E) {x y : Exp Word} {rest : Prog Word}
    {l g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {f : FfiState σ} {X Y Lw Hw pw : Word}
    (hx : E.eval ⟨l, g, m, f⟩ x = some (.word X)) (hy : E.eval ⟨l, g, m, f⟩ y = some (.word Y))
    (hpr : l "pr" = some (.word pw)) (hL : l "L" = some (.word Lw))
    (hH : l "H" = some (.word Hw)) (hXb : X.toNat < 2 ^ 32) (hYb : Y.toNat < 2 ^ 32)
    (hLb : Lw.toNat + 2 ^ 32 ≤ 2 ^ 64) (hHb : Hw.toNat + 2 ^ 32 ≤ 2 ^ 64)
    (h : ∀ l' Lw' Hw' pw', (∀ z, z ≠ "pr" → z ≠ "L" → z ≠ "H" → l' z = l z) →
      l' "pr" = some (.word pw') → l' "L" = some (.word Lw') → l' "H" = some (.word Hw') →
      Lw'.toNat = Lw.toNat + X.toNat * Y.toNat % 2 ^ 32 →
      Hw'.toNat = Hw.toNat + X.toNat * Y.toNat / 2 ^ 32 → WPs E ⟨l', g, m, f⟩ rest Q) :
    WPs E ⟨l, g, m, f⟩ (termStmts x y rest) Q := by
  unfold termStmts
  refine WPs.seq (fun a => a = ⟨updatePanValueMap l "pr" (.word (X * Y)), g, m, f⟩)
    (WPs.assign (old := pw) hpr (of_eval (w := X * Y) (by
      simp [evalF_panOp, evalArgs_cons, evalArgs_nil, hx, hy, evalPanOp])) ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨updatePanValueMap (updatePanValueMap l "pr" (.word (X * Y))) "L"
      (.word (Lw + ((X * Y) &&& 4294967295#64))), g, m, f⟩)
    (WPs.assign (old := Lw) (by lk [hL]) (of_eval (w := Lw + ((X * Y) &&& 4294967295#64)) (by
      ev [hL]; rfl)) ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap l "pr"
      (.word (X * Y))) "L" (.word (Lw + ((X * Y) &&& 4294967295#64)))) "H"
      (.word (Hw + ((X * Y) >>> (32 : Nat)))), g, m, f⟩)
    (WPs.assign (old := Hw) (by lk [hH]) (of_eval (w := Hw + ((X * Y) >>> (32 : Nat))) (by
      simp (config := { decide := true }) [evalF_op hE.word, evalF_shift hE.word, evalArgs_cons,
        evalArgs_nil, evalF_local, update_lookup, wordsProj_cons, wordsProj_nil, wordOp, hH,
        shift32])) ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  have hm := mul32_toNat hXb hYb
  refine h _ (Lw + ((X * Y) &&& 4294967295#64)) (Hw + ((X * Y) >>> (32 : Nat))) (X * Y) (fun z h1 h2 h3 => ?_) (by lk []) (by lk []) (by lk []) ?_ ?_
  · have e1 : (z == "pr") = false := by simpa using h1
    have e2 : (z == "L") = false := by simpa using h2
    have e3 : (z == "H") = false := by simpa using h3
    simp [update_lookup, e1, e2, e3]
  · rw [BitVec.toNat_add, and32_toNat, hm]
    exact Nat.mod_eq_of_lt (by have := Nat.mod_lt (X.toNat * Y.toNat) (show 0 < 2 ^ 32 by decide); omega)
  · rw [BitVec.toNat_add, shr32_toNat, hm]
    have : X.toNat * Y.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hXb hYb
    exact Nat.mod_eq_of_lt (by omega)

/-- Locals agree except for `pr`, `L` and `H`. -/
def PLH (l l' : VarName → Option (PanValue Word)) : Prop :=
  ∀ z, z ≠ "pr" → z ≠ "L" → z ≠ "H" → l' z = l z

theorem PLH.trans {l l' l'' : VarName → Option (PanValue Word)} (h : PLH l l') (h' : PLH l' l'') :
    PLH l l'' := fun z a b c => (h' z a b c).trans (h z a b c)

/-- The products of one column. -/
def termsProg : List (Exp Word × Exp Word) → Prog Word → Prog Word
  | [], rest => rest
  | (x, y) :: ts, rest => termStmts x y (termsProg ts rest)

/-- Operands of a product: 32-bit values, stable while `pr`, `L`, `H` change. -/
def TermVal (E : Env σ) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (f : FfiState σ)
    (l : VarName → Option (PanValue Word)) (t : Exp Word × Exp Word) (v : Word × Word) : Prop :=
  (∀ l', PLH l l' → E.eval ⟨l', g, m, f⟩ t.1 = some (.word v.1) ∧
    E.eval ⟨l', g, m, f⟩ t.2 = some (.word v.2)) ∧ v.1.toNat < 2 ^ 32 ∧ v.2.toNat < 2 ^ 32

theorem terms_wp (hE : GuestEnv E) {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {f : FfiState σ} {rest : Prog Word} :
    ∀ (ts : List (Exp Word × Exp Word)) (vals : List (Word × Word))
      (l : VarName → Option (PanValue Word)) (Lw Hw pw : Word),
      List.Forall₂ (TermVal E g m f l) ts vals → l "pr" = some (.word pw) →
      l "L" = some (.word Lw) → l "H" = some (.word Hw) →
      Lw.toNat + ts.length * 2 ^ 32 ≤ 2 ^ 64 → Hw.toNat + ts.length * 2 ^ 32 ≤ 2 ^ 64 →
      (∀ l' Lw' Hw' pw', PLH l l' → l' "pr" = some (.word pw') → l' "L" = some (.word Lw') →
        l' "H" = some (.word Hw') →
        Lw'.toNat = Lw.toNat + (vals.map fun v => v.1.toNat * v.2.toNat % 2 ^ 32).sum →
        Hw'.toNat = Hw.toNat + (vals.map fun v => v.1.toNat * v.2.toNat / 2 ^ 32).sum →
        Lw'.toNat ≤ Lw.toNat + ts.length * 2 ^ 32 → Hw'.toNat ≤ Hw.toNat + ts.length * 2 ^ 32 →
        WPs E ⟨l', g, m, f⟩ rest Q) →
      WPs E ⟨l, g, m, f⟩ (termsProg ts rest) Q
  | [], [], l, Lw, Hw, pw, _, hpr, hL, hH, _, _, h => by
    exact h l Lw Hw pw (fun _ _ _ _ => rfl) hpr hL hH (by simp) (by simp) (by simp) (by simp)
  | [], _ :: _, _, _, _, _, hF, _, _, _, _, _, _ => by cases hF
  | _ :: _, [], _, _, _, _, hF, _, _, _, _, _, _ => by cases hF
  | (x, y) :: ts, (X, Y) :: vals, l, Lw, Hw, pw, hF, hpr, hL, hH, hLb, hHb, h => by
    obtain ⟨⟨hev, hXb, hYb⟩, hF'⟩ := List.forall₂_cons.mp hF
    obtain ⟨hx, hy⟩ := hev l (fun _ _ _ _ => rfl)
    have hx : E.eval ⟨l, g, m, f⟩ x = some (.word X) := hx
    have hy : E.eval ⟨l, g, m, f⟩ y = some (.word Y) := hy
    have hXb : X.toNat < 2 ^ 32 := hXb
    have hYb : Y.toNat < 2 ^ 32 := hYb
    simp only [List.length_cons] at hLb hHb
    have hq : X.toNat * Y.toNat / 2 ^ 32 < 2 ^ 32 := by
      have : X.toNat * Y.toNat < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hXb hYb
      omega
    have hr : X.toNat * Y.toNat % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have e : (ts.length + 1) * 2 ^ 32 = ts.length * 2 ^ 32 + 2 ^ 32 := by ring
    show WPs E ⟨l, g, m, f⟩ (termStmts x y (termsProg ts rest)) Q
    refine term_wp hE hx hy hpr hL hH hXb hYb (by omega) (by omega)
      (fun l1 Lw1 Hw1 pw1 hfr hpr1 hL1 hH1 eL eH => ?_)
    refine terms_wp hE ts vals l1 Lw1 Hw1 pw1
      (hF'.imp (fun t v ⟨hv, b1, b2⟩ => ⟨fun l' hl' => hv l' (PLH.trans hfr hl'), b1, b2⟩)) hpr1
      hL1 hH1 (by omega) (by omega) (fun l' Lw' Hw' pw' hfr' hpr' hL' hH' eL' eH' bL' bH' => ?_)
    refine h l' Lw' Hw' pw' (PLH.trans hfr hfr') hpr' hL' hH' ?_ ?_ (by simp only [List.length_cons]; omega)
      (by simp only [List.length_cons]; omega)
    · simp only [List.map_cons, List.sum_cons]
      omega
    · simp only [List.map_cons, List.sum_cons]
      omega

theorem mont_digit (dg : Nat) :
    (dg + dg * 3834012553 % 2 ^ 32 * 3632069959 % 2 ^ 32) % 2 ^ 32 = 0 := by
  omega

set_option maxRecDepth 100000 in
theorem colEndA_num (Lw Hw cw : Word) (hLb : Lw.toNat < 2 ^ 37) (hHb : Hw.toNat < 2 ^ 37)
    (hcb : cw.toNat < 2 ^ 38) :
    ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64).toNat < 2 ^ 32 ∧
    (((Lw + cw) >>> (32 : Nat)) + (Hw + (((((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)) >>> (32 : Nat)) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) >>> (32 : Nat))))).toNat < 2 ^ 38 ∧
    2 ^ 32 * (((Lw + cw) >>> (32 : Nat)) + (Hw + (((((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)) >>> (32 : Nat)) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) >>> (32 : Nat))))).toNat =
      Lw.toNat + cw.toNat + 2 ^ 32 * Hw.toNat + ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64).toNat * 3632069959 := by
  have hcolN : (Lw + cw).toNat = Lw.toNat + cw.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  have hdgN : ((Lw + cw) &&& 4294967295#64).toNat = (Lw.toNat + cw.toNat) % 2 ^ 32 := by rw [and32_toNat, hcolN]
  have hk : (3834012553#64 : Word).toNat = 3834012553 := rfl
  have hmN : ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64).toNat = ((Lw + cw) &&& 4294967295#64).toNat * 3834012553 % 2 ^ 32 := by
    rw [and32_toNat, BitVec.toNat_mul, hk]
    omega
  have hmb : ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64).toNat < 2 ^ 32 := by
    rw [hmN]
    exact Nat.mod_lt _ (by norm_num)
  have hprN : (((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64).toNat = ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64).toNat * 3632069959 := mul32_toNat hmb (by
    rw [show (3632069959#64 : Word).toNat = 3632069959 from rfl]
    norm_num)
  generalize ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) = mv at hmN hmb hprN ⊢
  generalize ((Lw + cw) &&& 4294967295#64) = dg at hdgN hmN ⊢
  have hcol2N : (dg + ((mv * 3632069959#64) &&& 4294967295#64)).toNat =
      dg.toNat + (mv * 3632069959#64).toNat % 2 ^ 32 := by
    rw [BitVec.toNat_add, and32_toNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hcN : (((Lw + cw) >>> (32 : Nat)) + (Hw + (((dg + ((mv * 3632069959#64) &&& 4294967295#64)) >>> (32 : Nat)) +
      ((mv * 3632069959#64) >>> (32 : Nat))))).toNat = (Lw.toNat + cw.toNat) / 2 ^ 32 + Hw.toNat +
      (dg.toNat + (mv * 3632069959#64).toNat % 2 ^ 32) / 2 ^ 32 +
      (mv * 3632069959#64).toNat / 2 ^ 32 := by
    have hX := (mv * 3632069959#64).isLt
    have b1 : (Lw.toNat + cw.toNat) / 2 ^ 32 < 2 ^ 7 := by omega
    have b2 : (dg.toNat + (mv * 3632069959#64).toNat % 2 ^ 32) / 2 ^ 32 < 2 := by omega
    have b3 : (mv * 3632069959#64).toNat / 2 ^ 32 < 2 ^ 32 := by omega
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, shr32_toNat, shr32_toNat,
      shr32_toNat, hcolN, hcol2N]
    generalize (Lw.toNat + cw.toNat) / 2 ^ 32 = a at b1 ⊢
    generalize (dg.toNat + (mv * 3632069959#64).toNat % 2 ^ 32) / 2 ^ 32 = b at b2 ⊢
    generalize (mv * 3632069959#64).toNat / 2 ^ 32 = c at b3 ⊢
    omega
  rw [hcN]
  refine ⟨hmb, by omega, by omega⟩

/-- Locals agree outside the names in `S`. -/
def Keep (S : List VarName) (l l' : VarName → Option (PanValue Word)) : Prop :=
  ∀ z, z ∉ S → l' z = l z

/-- End of one of the first eight columns: choose the digit `mk` that clears
the column, and carry. -/
def colEndA (mk : VarName) (rest : Prog Word) : Prog Word :=
  .seq (.assign .local "col" (.op .add [.var .local "L", .var .local "c"]))
  (.seq (.assign .local "dg" (.op .and [.var .local "col", .const 4294967295#64]))
  (.seq (.assign .local mk (.op .and [.panOp .mul [.var .local "dg", .const 3834012553#64],
    .const 4294967295#64]))
  (.seq (.assign .local "pr" (.panOp .mul [.var .local mk, .const 3632069959#64]))
  (.seq (.assign .local "col2" (.op .add [.var .local "dg",
    .op .and [.var .local "pr", .const 4294967295#64]]))
  (.seq (.assign .local "c" (.op .add [.shift .lsr (.var .local "col") (.const 32#64),
    .var .local "H", .shift .lsr (.var .local "col2") (.const 32#64),
    .shift .lsr (.var .local "pr") (.const 32#64)]))
  (.seq (.assign .local "L" (.const 0#64)) (.seq (.assign .local "H" (.const 0#64)) rest)))))))

set_option maxHeartbeats 8000000 in
theorem colEndA_wp (hE : GuestEnv E) {mk : VarName} {rest : Prog Word}
    {l g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {f : FfiState σ} {Lw Hw cw w1 w2 w3 w4 w5 : Word}
    (hmk : (["col", "dg", "pr", "col2", "c", "L", "H"].contains mk) = false)
    (hL : l "L" = some (.word Lw)) (hH : l "H" = some (.word Hw)) (hc : l "c" = some (.word cw))
    (hcol : l "col" = some (.word w1)) (hdg : l "dg" = some (.word w2))
    (hm0 : l mk = some (.word w3)) (hpr : l "pr" = some (.word w4))
    (hcol2 : l "col2" = some (.word w5))
    (hLb : Lw.toNat < 2 ^ 37) (hHb : Hw.toNat < 2 ^ 37) (hcb : cw.toNat < 2 ^ 38)
    (h : ∀ l' cw' mw pw', Keep ["col", "dg", mk, "pr", "col2", "c", "L", "H"] l l' →
      l' "c" = some (.word cw') → l' mk = some (.word mw) → l' "L" = some (.word 0#64) →
      l' "H" = some (.word 0#64) → l' "pr" = some (.word pw') →
      (∃ w, l' "col" = some (.word w)) → (∃ w, l' "dg" = some (.word w)) →
      (∃ w, l' "col2" = some (.word w)) → mw.toNat < 2 ^ 32 → cw'.toNat < 2 ^ 38 →
      2 ^ 32 * cw'.toNat = Lw.toNat + cw.toNat + 2 ^ 32 * Hw.toNat + mw.toNat * 3632069959 →
      WPs E ⟨l', g, m, f⟩ rest Q) :
    WPs E ⟨l, g, m, f⟩ (colEndA mk rest) Q := by
  have n1 : (mk == "col") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have n2 : (mk == "dg") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have n3 : (mk == "pr") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have n4 : (mk == "col2") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have n5 : (mk == "c") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have n6 : (mk == "L") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have n7 : (mk == "H") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have r1 : ("col" == mk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have r2 : ("dg" == mk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have r3 : ("pr" == mk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have r4 : ("col2" == mk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have r5 : ("c" == mk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have r6 : ("L" == mk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  have r7 : ("H" == mk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd hmk (by decide)
  unfold colEndA
  refine WPs.seq (fun a => a = ⟨updatePanValueMap l "col" (.word (Lw + cw)), g, m, f⟩)
    (WPs.assign (old := w1) hcol (of_eval (w := Lw + cw) (by ev [hL, hc]))
      ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw)))
      "dg" (.word ((Lw + cw) &&& 4294967295#64)), g, m, f⟩)
    (WPs.assign (old := w2) (by lk [hdg]) (of_eval (w := (Lw + cw) &&& 4294967295#64)
      (by ev []; rfl)) ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap l "col"
      (.word (Lw + cw))) "dg" (.word ((Lw + cw) &&& 4294967295#64))) mk
      (.word ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64)), g, m, f⟩)
    (WPs.assign (old := w3) (by lk [hm0, n1, n2])
      (of_eval (w := (((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64)
        (by ev [evalPanOp]; rfl)) ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) "dg" (.word ((Lw + cw) &&& 4294967295#64))) mk (.word ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64))) "pr" (.word (((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64))), g, m, f⟩)
    (WPs.assign (old := w4) (by lk [hpr, n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7])
      (of_eval (w := (((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64)) (by ev [evalPanOp, n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7])) ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) "dg" (.word ((Lw + cw) &&& 4294967295#64))) mk (.word ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64))) "pr" (.word (((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64))) "col2" (.word (((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)))), g, m, f⟩)
    (WPs.assign (old := w5) (by lk [hcol2, n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7])
      (of_eval (w := (((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64))) (by ev [n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7]; rfl)) ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) "dg" (.word ((Lw + cw) &&& 4294967295#64))) mk (.word ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64))) "pr" (.word (((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64))) "col2" (.word (((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)))) "c" (.word (((Lw + cw) >>> (32 : Nat)) + (Hw + (((((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)) >>> (32 : Nat)) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) >>> (32 : Nat))))))), g, m, f⟩)
    (WPs.assign (old := cw) (by lk [hc, n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7])
      (of_eval (w := (((Lw + cw) >>> (32 : Nat)) + (Hw + (((((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)) >>> (32 : Nat)) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) >>> (32 : Nat)))))) (by
        ev [evalF_shift hE.word, shift32, hH, eval_const, n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7])) ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) "dg" (.word ((Lw + cw) &&& 4294967295#64))) mk (.word ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64))) "pr" (.word (((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64))) "col2" (.word (((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)))) "c" (.word (((Lw + cw) >>> (32 : Nat)) + (Hw + (((((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)) >>> (32 : Nat)) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) >>> (32 : Nat))))))) "L" (.word 0#64)), g, m, f⟩)
    (WPs.assign (old := Lw) (by lk [hL, n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7]) (of_eval (eval_const _ _))
      ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) "dg" (.word ((Lw + cw) &&& 4294967295#64))) mk (.word ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64))) "pr" (.word (((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64))) "col2" (.word (((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)))) "c" (.word (((Lw + cw) >>> (32 : Nat)) + (Hw + (((((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)) >>> (32 : Nat)) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) >>> (32 : Nat))))))) "L" (.word 0#64)) "H" (.word 0#64)), g, m, f⟩)
    (WPs.assign (old := Hw) (by lk [hH, n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7]) (of_eval (eval_const _ _))
      ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  obtain ⟨hmb, hcb', heq⟩ := colEndA_num Lw Hw cw hLb hHb hcb
  refine h (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) "dg" (.word ((Lw + cw) &&& 4294967295#64))) mk (.word ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64))) "pr" (.word (((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64))) "col2" (.word (((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)))) "c" (.word (((Lw + cw) >>> (32 : Nat)) + (Hw + (((((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)) >>> (32 : Nat)) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) >>> (32 : Nat))))))) "L" (.word 0#64)) "H" (.word 0#64))
    (((Lw + cw) >>> (32 : Nat)) + (Hw + (((((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)) >>> (32 : Nat)) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) >>> (32 : Nat))))) ((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) (((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) (fun z hz => ?_) (by lk [n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7]) (by lk [n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7])
    (by lk [n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7]) (by lk [n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7]) (by lk [n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7]) ⟨(Lw + cw), by lk [n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7]⟩
    ⟨((Lw + cw) &&& 4294967295#64), by lk [n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7]⟩
    ⟨(((Lw + cw) &&& 4294967295#64) + ((((((Lw + cw) &&& 4294967295#64) * 3834012553#64) &&& 4294967295#64) * 3632069959#64) &&& 4294967295#64)), by lk [n1, n2, n3, n4, n5, n6, n7, r1, r2, r3, r4, r5, r6, r7]⟩ hmb hcb' heq
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hz
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hz
  simp [update_lookup, a1, a2, a3, a4, a5, a6, a7, a8]

/-- End of one of the last seven columns: store the digit `uk` and carry. -/
def colEndB (uk : VarName) (rest : Prog Word) : Prog Word :=
  .seq (.assign .local "col" (.op .add [.var .local "L", .var .local "c"]))
  (.seq (.assign .local uk (.op .and [.var .local "col", .const 4294967295#64]))
  (.seq (.assign .local "c" (.op .add [.shift .lsr (.var .local "col") (.const 32#64),
    .var .local "H"]))
  (.seq (.assign .local "L" (.const 0#64)) (.seq (.assign .local "H" (.const 0#64)) rest))))

set_option maxHeartbeats 8000000 in
theorem colEndB_wp (hE : GuestEnv E) {uk : VarName} {rest : Prog Word}
    {l g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {f : FfiState σ} {Lw Hw cw w1 w3 : Word}
    (huk : (["col", "c", "L", "H"].contains uk) = false)
    (hL : l "L" = some (.word Lw)) (hH : l "H" = some (.word Hw)) (hc : l "c" = some (.word cw))
    (hcol : l "col" = some (.word w1)) (hu0 : l uk = some (.word w3))
    (hLb : Lw.toNat < 2 ^ 37) (hHb : Hw.toNat < 2 ^ 37) (hcb : cw.toNat < 2 ^ 38)
    (h : ∀ l' cw' uw, Keep ["col", uk, "c", "L", "H"] l l' →
      l' "c" = some (.word cw') → l' uk = some (.word uw) → l' "L" = some (.word 0#64) →
      l' "H" = some (.word 0#64) → (∃ w, l' "col" = some (.word w)) → uw.toNat < 2 ^ 32 →
      cw'.toNat < 2 ^ 38 →
      2 ^ 32 * cw'.toNat + uw.toNat = Lw.toNat + cw.toNat + 2 ^ 32 * Hw.toNat →
      WPs E ⟨l', g, m, f⟩ rest Q) :
    WPs E ⟨l, g, m, f⟩ (colEndB uk rest) Q := by
  have n1 : (uk == "col") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd huk (by decide)
  have n2 : (uk == "c") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd huk (by decide)
  have n3 : (uk == "L") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd huk (by decide)
  have n4 : (uk == "H") = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd huk (by decide)
  have r1 : ("col" == uk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd huk (by decide)
  have r2 : ("c" == uk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd huk (by decide)
  have r3 : ("L" == uk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd huk (by decide)
  have r4 : ("H" == uk) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact absurd huk (by decide)
  unfold colEndB
  refine WPs.seq (fun a => a = ⟨(updatePanValueMap l "col" (.word (Lw + cw))), g, m, f⟩)
    (WPs.assign (old := w1) hcol (of_eval (w := (Lw + cw)) (by ev [hL, hc]))
      ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨(updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) uk (.word ((Lw + cw) &&& 4294967295#64))), g, m, f⟩)
    (WPs.assign (old := w3) (by lk [hu0, n1, n2, n3, n4, r1, r2, r3, r4]) (of_eval (w := ((Lw + cw) &&& 4294967295#64)) (by ev []; rfl))
      ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) uk (.word ((Lw + cw) &&& 4294967295#64))) "c" (.word (((Lw + cw) >>> (32 : Nat)) + Hw))), g, m, f⟩)
    (WPs.assign (old := cw) (by lk [hc, n1, n2, n3, n4, r1, r2, r3, r4]) (of_eval (w := (((Lw + cw) >>> (32 : Nat)) + Hw)) (by
      ev [evalF_shift hE.word, shift32, hH, eval_const, n1, n2, n3, n4, r1, r2, r3, r4])) ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) uk (.word ((Lw + cw) &&& 4294967295#64))) "c" (.word (((Lw + cw) >>> (32 : Nat)) + Hw))) "L" (.word 0#64)), g, m, f⟩)
    (WPs.assign (old := Lw) (by lk [hL, n1, n2, n3, n4, r1, r2, r3, r4]) (of_eval (eval_const _ _))
      ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  refine WPs.seq (fun a => a = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) uk (.word ((Lw + cw) &&& 4294967295#64))) "c" (.word (((Lw + cw) >>> (32 : Nat)) + Hw))) "L" (.word 0#64)) "H" (.word 0#64)), g, m, f⟩)
    (WPs.assign (old := Hw) (by lk [hH, n1, n2, n3, n4, r1, r2, r3, r4]) (of_eval (eval_const _ _))
      ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  have hcolN : (Lw + cw).toNat = Lw.toNat + cw.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  have huN : ((Lw + cw) &&& 4294967295#64).toNat = (Lw.toNat + cw.toNat) % 2 ^ 32 := by rw [and32_toNat, hcolN]
  have hcN : (((Lw + cw) >>> (32 : Nat)) + Hw).toNat = (Lw.toNat + cw.toNat) / 2 ^ 32 + Hw.toNat := by
    rw [BitVec.toNat_add, shr32_toNat, hcolN]
    exact Nat.mod_eq_of_lt (by omega)
  refine h (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap l "col" (.word (Lw + cw))) uk (.word ((Lw + cw) &&& 4294967295#64))) "c" (.word (((Lw + cw) >>> (32 : Nat)) + Hw))) "L" (.word 0#64)) "H" (.word 0#64))
    (((Lw + cw) >>> (32 : Nat)) + Hw) ((Lw + cw) &&& 4294967295#64) (fun z hz => ?_) (by lk [n1, n2, n3, n4, r1, r2, r3, r4]) (by lk [n1, n2, n3, n4, r1, r2, r3, r4]) (by lk [n1, n2, n3, n4, r1, r2, r3, r4]) (by lk [n1, n2, n3, n4, r1, r2, r3, r4])
    ⟨(Lw + cw), by lk [n1, n2, n3, n4, r1, r2, r3, r4]⟩ (by rw [huN]; omega) (by rw [hcN]; omega) (by rw [hcN, huN]; omega)
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or] at hz
  obtain ⟨a1, a2, a3, a4, a5⟩ := hz
  simp [update_lookup, a1, a2, a3, a4, a5]

theorem tv_var_var {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {f : FfiState σ} {l : VarName → Option (PanValue Word)} {x y : VarName} {X Y : Word}
    (hx : l x = some (.word X)) (hy : l y = some (.word Y))
    (nx : (["pr", "L", "H"].contains x) = false) (ny : (["pr", "L", "H"].contains y) = false)
    (bx : X.toNat < 2 ^ 32) (by' : Y.toNat < 2 ^ 32) :
    TermVal E g m f l (.var .local x, .var .local y) (X, Y) := by
  have ex : x ≠ "pr" ∧ x ≠ "L" ∧ x ≠ "H" := by
    refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; exact absurd nx (by decide))
  have ey : y ≠ "pr" ∧ y ≠ "L" ∧ y ≠ "H" := by
    refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; exact absurd ny (by decide))
  refine ⟨fun l' hl' => ⟨?_, ?_⟩, bx, by'⟩
  · rw [evalF_local]
    exact (hl' x ex.1 ex.2.1 ex.2.2).trans hx
  · rw [evalF_local]
    exact (hl' y ey.1 ey.2.1 ey.2.2).trans hy

theorem tv_var_const {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {f : FfiState σ} {l : VarName → Option (PanValue Word)} {x : VarName} {X : Word} (c : Word)
    (hx : l x = some (.word X)) (nx : (["pr", "L", "H"].contains x) = false)
    (bx : X.toNat < 2 ^ 32) (bc : c.toNat < 2 ^ 32) :
    TermVal E g m f l (.var .local x, .const c) (X, c) := by
  have ex : x ≠ "pr" ∧ x ≠ "L" ∧ x ≠ "H" := by
    refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; exact absurd nx (by decide))
  refine ⟨fun l' hl' => ⟨?_, eval_const _ _⟩, bx, bc⟩
  rw [evalF_local]
  exact (hl' x ex.1 ex.2.1 ex.2.2).trans hx

/-- One column keeps everything outside the written names. -/
theorem keep_step {S T : List VarName} {l0 l l' l'' : VarName → Option (PanValue Word)}
    (h0 : Keep S l0 l) (h1 : PLH l l') (h2 : Keep T l' l'')
    (hS : "pr" ∈ S ∧ "L" ∈ S ∧ "H" ∈ S) (hT : ∀ t ∈ T, t ∈ S) : Keep S l0 l'' := by
  intro z hz
  have a1 : z ≠ "pr" := fun e => hz (e ▸ hS.1)
  have a2 : z ≠ "L" := fun e => hz (e ▸ hS.2.1)
  have a3 : z ≠ "H" := fun e => hz (e ▸ hS.2.2)
  have a4 : z ∉ T := fun h => hz (hT z h)
  exact (h2 z a4).trans ((h1 z a1 a2 a3).trans (h0 z hz))

theorem or_shl32 {x y : Word} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) :
    (x ||| (y <<< (32 : Nat))).toNat = x.toNat + 2 ^ 32 * y.toNat := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega),
    Nat.or_comm]
  have h := Nat.shiftLeft_add_eq_or_of_lt hx y.toNat
  rw [Nat.shiftLeft_eq] at h
  rw [← h]
  omega

/-- Low halves plus `2^32` times high halves of the products give the products. -/
theorem col_sum : ∀ (vals : List (Word × Word)),
    (vals.map fun v => v.1.toNat * v.2.toNat % 2 ^ 32).sum +
      2 ^ 32 * (vals.map fun v => v.1.toNat * v.2.toNat / 2 ^ 32).sum =
    (vals.map fun v => v.1.toNat * v.2.toNat).sum
  | [] => by simp
  | v :: vs => by
    have ih := col_sum vs
    simp only [List.map_cons, List.sum_cons]
    generalize (vs.map fun v => v.1.toNat * v.2.toNat % 2 ^ 32).sum = a at ih ⊢
    generalize (vs.map fun v => v.1.toNat * v.2.toNat / 2 ^ 32).sum = b at ih ⊢
    generalize (vs.map fun v => v.1.toNat * v.2.toNat).sum = c at ih ⊢
    generalize v.1.toNat * v.2.toNat = t
    omega

end InitECandidate.Solver.GuestBound
