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

end InitECandidate.Solver.GuestBound
