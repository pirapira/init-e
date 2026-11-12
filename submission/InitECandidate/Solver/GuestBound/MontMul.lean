import InitECandidate.Solver.GuestBound.MontCols
import InitECandidate.Solver.GuestBound.MontAlg
import InitECandidate.Solver.GuestBound.HtabDiff

/-!
# Montgomery multiplication in the bn254 base field: `fq_mul`

After the columns, the digits are packed into four limbs and reduced once.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {Q : Result σ → Prop}

local notation "REDUCE" => ((Prog.decCall "lt" Shape.one "u256_lt" [(Exp.var VarKind.local "r"), (Exp.rStruct [(Exp.const (BitVec.ofNat 64 4332616871279656263)), (Exp.const (BitVec.ofNat 64 10917124144477883021)), (Exp.const (BitVec.ofNat 64 13281191951274694749)), (Exp.const (BitVec.ofNat 64 3486998266802970665))])] (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "lt") (Exp.const (BitVec.ofNat 64 0))) (Prog.call none "u256_sub" [(Exp.var VarKind.local "r"), (Exp.rStruct [(Exp.const (BitVec.ofNat 64 4332616871279656263)), (Exp.const (BitVec.ofNat 64 10917124144477883021)), (Exp.const (BitVec.ofNat 64 13281191951274694749)), (Exp.const (BitVec.ofNat 64 3486998266802970665))])]) Prog.skip) (Prog.return (Exp.var VarKind.local "r")))) : Prog Word)
local notation "PACK" => ((Exp.rStruct [(Exp.op BinOp.or [(Exp.var VarKind.local "u0"), (Exp.shift Shift.lsl (Exp.var VarKind.local "u1") (Exp.const (BitVec.ofNat 64 32)))]), (Exp.op BinOp.or [(Exp.var VarKind.local "u2"), (Exp.shift Shift.lsl (Exp.var VarKind.local "u3") (Exp.const (BitVec.ofNat 64 32)))]), (Exp.op BinOp.or [(Exp.var VarKind.local "u4"), (Exp.shift Shift.lsl (Exp.var VarKind.local "u5") (Exp.const (BitVec.ofNat 64 32)))]), (Exp.op BinOp.or [(Exp.var VarKind.local "u6"), (Exp.shift Shift.lsl (Exp.var VarKind.local "c") (Exp.const (BitVec.ofNat 64 32)))])]) : Exp Word)

theorem shiftl32 (w : Word) : RiscV.panRiscVShift .lsl w 32#64 = some (w <<< (32 : Nat)) := by
  unfold RiscV.panRiscVShift
  rfl

set_option maxHeartbeats 8000000 in
/-- `lt = u256_lt(r, p); if lt == 0 { return u256_sub(r, p); } return r;` -/
theorem reduce_tail (hE : GuestEnv E) (s : St σ) (r : Result σ) (c0 c1 c2 c3 : Word)
    (hrl : s.locals "r" = some (.rStruct [.word c0, .word c1, .word c2, .word c3]))
    (h : Runs E s REDUCE r) :
    Stopped r ∨ ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] = if limbsVal [c0, c1, c2, c3] < bnP then limbsVal [c0, c1, c2, c3]
        else limbsVal [c0, c1, c2, c3] - bnP := by
  rcases runs_decCall_inv h with herr | ⟨ps2, cb2, vals2, cl2, rb2, hl2, hvals2, hbind2, hcal2,
    hout2⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams2 := (fun_of_index 46 hE.functions (by guest_decl_at 46) (by decide +kernel) hl2).2
  simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local, hrl,
    evalF_rStruct, eval_const, Option.map_some, Option.some.injEq] at hvals2
  subst hvals2
  rw [hparams2] at hbind2
  simp [bindPanValueParameters] at hbind2
  have hlt := u256_lt_spec hE ps2 cb2 hl2 ⟨cl2, s.globals, s.memory, s.ffi⟩ rb2 c0 c1 c2 c3
    4332616871279656263#64 10917124144477883021#64 13281191951274694749#64 3486998266802970665#64
    (by rw [← hbind2]; simp [updatePanValueMap]) (by rw [← hbind2]; simp [updatePanValueMap]) hcal2
  subst hlt
  obtain ⟨r2, -, hrun2, rfl⟩ := hout2
  obtain ⟨r3, h3, hrest⟩ := runs_seq.mp hrun2
  rw [bnP_limbs] at h3
  have hCb : limbsVal [c0, c1, c2, c3] < 2 ^ 256 := by
    have := c0.isLt; have := c1.isLt; have := c2.isLt; have := c3.isLt
    simp only [limbsVal]
    omega
  simp only [bnP] at h3 ⊢
  rw [runs_ite] at h3
  by_cases hlt : limbsVal [c0, c1, c2, c3] <
      21888242871839275222246405745257275088696311157297823662689037894645226208583
  · simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      eval_const, hlt, if_true, if_false, evalPanCmp] at h3
    rw [runs_skip] at h3
    subst h3
    simp only at hrest
    rw [runs_return] at hrest
    simp (config := { decide := true }) only [evalF_local, update_lookup, hrl, payload_words4,
      if_true, if_false] at hrest
    subst hrest
    exact Or.inr ⟨_, c0, c1, c2, c3, rfl, (if_pos hlt).symm⟩
  · simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      eval_const, hlt, if_true, if_false, evalPanCmp] at h3
    have herror : r3.isError = true → Stopped (restorePanValueFfiLocal "lt" (s.locals "lt") r2) := by
      intro herr
      have hr2 : r2.isError = true := by
        cases r3 with
        | error l g m f =>
          simp only at hrest
          subst hrest
          rfl
        | _ => cases herr
      exact Stopped.restore (Stopped.of_error hr2)
    rcases runs_call_inv none h3 with herr | ⟨ps3, cb3, vals3, cl3, rb3, hl3, hvals3, hbind3,
      hcal3, hout3⟩
    · exact Or.inl (herror herr)
    have hparams3 := (fun_of_index 57 hE.functions (by guest_decl_at 57) (by decide +kernel)
      hl3).2
    simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, hrl, evalF_rStruct, eval_const, Option.map_some, Option.some.injEq, if_true,
      if_false] at hvals3
    subst hvals3
    rw [hparams3] at hbind3
    simp [bindPanValueParameters] at hbind3
    obtain ⟨l3, e0, e1, e2, e3, rfl, he⟩ := u256_sub_mod hE ps3 cb3 hl3
      ⟨cl3, s.globals, s.memory, s.ffi⟩ rb3 c0 c1 c2 c3 4332616871279656263#64 10917124144477883021#64 13281191951274694749#64 3486998266802970665#64
      (by rw [← hbind3]; simp [updatePanValueMap]) (by rw [← hbind3]; simp [updatePanValueMap])
      hcal3
    simp only [CallOutcome] at hout3
    rcases hout3 with herr | ⟨l', rfl⟩
    · exact Or.inl (herror herr)
    simp only at hrest
    subst hrest
    refine Or.inr ⟨_, e0, e1, e2, e3, rfl, ?_⟩
    rw [he, bnP_limbs]
    refine Eq.trans ?_ (if_neg hlt).symm
    simp only [bnP]
    omega

theorem and32_lt (w : Word) : (w &&& 4294967295#64).toNat < 2 ^ 32 := by
  rw [and32_toNat]
  exact Nat.mod_lt _ (by norm_num)

theorem shr32_lt (w : Word) : (w >>> (32 : Nat)).toNat < 2 ^ 32 := by
  rw [shr32_toNat]
  have := w.isLt
  omega

theorem eval_lo (hE : GuestEnv E) {s : St σ} {x : VarName} {ws : List (PanValue Word)} {i : Nat}
    {w : Word} (hx : s.locals x = some (.rStruct ws)) (hi : ws[i]? = some (.word w)) :
    E.eval s (.op .and [.rField i (.var .local x), .const 4294967295#64]) =
      some (.word (w &&& 4294967295#64)) := by
  simp [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_rField, evalF_local, hx, hi,
    eval_const, wordsProj_cons, wordsProj_nil, wordOp]
  rfl

theorem eval_hi (hE : GuestEnv E) {s : St σ} {x : VarName} {ws : List (PanValue Word)} {i : Nat}
    {w : Word} (hx : s.locals x = some (.rStruct ws)) (hi : ws[i]? = some (.word w)) :
    E.eval s (.shift .lsr (.rField i (.var .local x)) (.const 32#64)) =
      some (.word (w >>> (32 : Nat))) := by
  simp [evalF_shift hE.word, evalF_rField, evalF_local, hx, hi, eval_const, shift32]

theorem digits_val (a0 a1 a2 a3 : Word) :
    (a0 &&& 4294967295#64).toNat * 1 + (a0 >>> (32 : Nat)).toNat * 2 ^ 32 + (a1 &&& 4294967295#64).toNat * 2 ^ 64 + (a1 >>> (32 : Nat)).toNat * 2 ^ 96 + (a2 &&& 4294967295#64).toNat * 2 ^ 128 + (a2 >>> (32 : Nat)).toNat * 2 ^ 160 + (a3 &&& 4294967295#64).toNat * 2 ^ 192 + (a3 >>> (32 : Nat)).toNat * 2 ^ 224 =
      limbsVal [a0, a1, a2, a3] := by
  simp only [limbsVal, and32_toNat, shr32_toNat]
  omega

theorem pk0 : (3632069959#64 : Word).toNat = 3632069959 := by decide
theorem pk1 : (1008765974#64 : Word).toNat = 1008765974 := by decide
theorem pk2 : (1752287885#64 : Word).toNat = 1752287885 := by decide
theorem pk3 : (2541841041#64 : Word).toNat = 2541841041 := by decide
theorem pk4 : (2172737629#64 : Word).toNat = 2172737629 := by decide
theorem pk5 : (3092268470#64 : Word).toNat = 3092268470 := by decide
theorem pk6 : (3778125865#64 : Word).toNat = 3778125865 := by decide
theorem pk7 : (811880050#64 : Word).toNat = 811880050 := by decide

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1000 in
/-- `fq_mul` is Montgomery multiplication: on canonical operands the result is
canonical and equals `a * b / 2^256` modulo `p`. -/
theorem fq_mul_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq_mul" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha : s.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hb : s.locals "b" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) (hB : limbsVal [b0, b1, b2, b3] < bnP)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧ limbsVal [d0, d1, d2, d3] < bnP ∧
      limbsVal [d0, d1, d2, d3] * 2 ^ 256 % bnP =
        limbsVal [a0, a1, a2, a3] * limbsVal [b0, b1, b2, b3] % bnP := by
  have hbody := (fun_of_index 652 hE.functions (by guest_decl_at 652) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧ limbsVal [d0, d1, d2, d3] < bnP ∧
      limbsVal [d0, d1, d2, d3] * 2 ^ 256 % bnP =
        limbsVal [a0, a1, a2, a3] * limbsVal [b0, b1, b2, b3] % bnP)) r h
  refine WPs.dec (of_eval (eval_lo hE (x := "a") (ws := [.word a0, .word a1, .word a2, .word a3]) (i := 0) (w := a0) (by lk [ha]) rfl)) ?_
  refine WPs.dec (of_eval (eval_hi hE (x := "a") (ws := [.word a0, .word a1, .word a2, .word a3]) (i := 0) (w := a0) (by lk [ha]) rfl)) ?_
  refine WPs.dec (of_eval (eval_lo hE (x := "a") (ws := [.word a0, .word a1, .word a2, .word a3]) (i := 1) (w := a1) (by lk [ha]) rfl)) ?_
  refine WPs.dec (of_eval (eval_hi hE (x := "a") (ws := [.word a0, .word a1, .word a2, .word a3]) (i := 1) (w := a1) (by lk [ha]) rfl)) ?_
  refine WPs.dec (of_eval (eval_lo hE (x := "a") (ws := [.word a0, .word a1, .word a2, .word a3]) (i := 2) (w := a2) (by lk [ha]) rfl)) ?_
  refine WPs.dec (of_eval (eval_hi hE (x := "a") (ws := [.word a0, .word a1, .word a2, .word a3]) (i := 2) (w := a2) (by lk [ha]) rfl)) ?_
  refine WPs.dec (of_eval (eval_lo hE (x := "a") (ws := [.word a0, .word a1, .word a2, .word a3]) (i := 3) (w := a3) (by lk [ha]) rfl)) ?_
  refine WPs.dec (of_eval (eval_hi hE (x := "a") (ws := [.word a0, .word a1, .word a2, .word a3]) (i := 3) (w := a3) (by lk [ha]) rfl)) ?_
  refine WPs.dec (of_eval (eval_lo hE (x := "b") (ws := [.word b0, .word b1, .word b2, .word b3]) (i := 0) (w := b0) (by lk [hb]) rfl)) ?_
  refine WPs.dec (of_eval (eval_hi hE (x := "b") (ws := [.word b0, .word b1, .word b2, .word b3]) (i := 0) (w := b0) (by lk [hb]) rfl)) ?_
  refine WPs.dec (of_eval (eval_lo hE (x := "b") (ws := [.word b0, .word b1, .word b2, .word b3]) (i := 1) (w := b1) (by lk [hb]) rfl)) ?_
  refine WPs.dec (of_eval (eval_hi hE (x := "b") (ws := [.word b0, .word b1, .word b2, .word b3]) (i := 1) (w := b1) (by lk [hb]) rfl)) ?_
  refine WPs.dec (of_eval (eval_lo hE (x := "b") (ws := [.word b0, .word b1, .word b2, .word b3]) (i := 2) (w := b2) (by lk [hb]) rfl)) ?_
  refine WPs.dec (of_eval (eval_hi hE (x := "b") (ws := [.word b0, .word b1, .word b2, .word b3]) (i := 2) (w := b2) (by lk [hb]) rfl)) ?_
  refine WPs.dec (of_eval (eval_lo hE (x := "b") (ws := [.word b0, .word b1, .word b2, .word b3]) (i := 3) (w := b3) (by lk [hb]) rfl)) ?_
  refine WPs.dec (of_eval (eval_hi hE (x := "b") (ws := [.word b0, .word b1, .word b2, .word b3]) (i := 3) (w := b3) (by lk [hb]) rfl)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine mont_cols hE (Aw0 := (a0 &&& 4294967295#64)) (Aw1 := (a0 >>> (32 : Nat))) (Aw2 := (a1 &&& 4294967295#64)) (Aw3 := (a1 >>> (32 : Nat))) (Aw4 := (a2 &&& 4294967295#64)) (Aw5 := (a2 >>> (32 : Nat))) (Aw6 := (a3 &&& 4294967295#64)) (Aw7 := (a3 >>> (32 : Nat))) (Bw0 := (b0 &&& 4294967295#64)) (Bw1 := (b0 >>> (32 : Nat))) (Bw2 := (b1 &&& 4294967295#64)) (Bw3 := (b1 >>> (32 : Nat))) (Bw4 := (b2 &&& 4294967295#64)) (Bw5 := (b2 >>> (32 : Nat))) (Bw6 := (b3 &&& 4294967295#64)) (Bw7 := (b3 >>> (32 : Nat)))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by lk []) (and32_lt _)
    (by lk []) (shr32_lt _)
    (by lk []) (and32_lt _)
    (by lk []) (shr32_lt _)
    (by lk []) (and32_lt _)
    (by lk []) (shr32_lt _)
    (by lk []) (and32_lt _)
    (by lk []) (shr32_lt _)
    (by lk []) (and32_lt _)
    (by lk []) (shr32_lt _)
    (by lk []) (and32_lt _)
    (by lk []) (shr32_lt _)
    (by lk []) (and32_lt _)
    (by lk []) (shr32_lt _)
    (by lk []) (and32_lt _)
    (by lk []) (shr32_lt _)
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (by lk [])
    (fun l' mw0 mw1 mw2 mw3 mw4 mw5 mw6 mw7 uw0 uw1 uw2 uw3 uw4 uw5 uw6 cw c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 hK hu0 bu0 hu1 bu1 hu2 bu2 hu3 bu3 hu4 bu4 hu5 bu5 hu6 bu6 bm0 bm1 bm2 bm3 bm4 bm5 bm6 bm7 hc e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 => ?_)
  rw [pk1] at e1
  rw [pk1, pk2] at e2
  rw [pk1, pk2, pk3] at e3
  rw [pk1, pk2, pk3, pk4] at e4
  rw [pk1, pk2, pk3, pk4, pk5] at e5
  rw [pk1, pk2, pk3, pk4, pk5, pk6] at e6
  rw [pk1, pk2, pk3, pk4, pk5, pk6, pk7] at e7
  rw [pk1, pk2, pk3, pk4, pk5, pk6, pk7] at e8
  rw [pk2, pk3, pk4, pk5, pk6, pk7] at e9
  rw [pk3, pk4, pk5, pk6, pk7] at e10
  rw [pk4, pk5, pk6, pk7] at e11
  rw [pk5, pk6, pk7] at e12
  rw [pk6, pk7] at e13
  rw [pk7] at e14
  have hs := mont_spec (a0 &&& 4294967295#64).toNat (a0 >>> (32 : Nat)).toNat (a1 &&& 4294967295#64).toNat (a1 >>> (32 : Nat)).toNat (a2 &&& 4294967295#64).toNat (a2 >>> (32 : Nat)).toNat (a3 &&& 4294967295#64).toNat (a3 >>> (32 : Nat)).toNat
    (b0 &&& 4294967295#64).toNat (b0 >>> (32 : Nat)).toNat (b1 &&& 4294967295#64).toNat (b1 >>> (32 : Nat)).toNat (b2 &&& 4294967295#64).toNat (b2 >>> (32 : Nat)).toNat (b3 &&& 4294967295#64).toNat (b3 >>> (32 : Nat)).toNat
    mw0.toNat mw1.toNat mw2.toNat mw3.toNat mw4.toNat mw5.toNat mw6.toNat mw7.toNat uw0.toNat uw1.toNat uw2.toNat uw3.toNat uw4.toNat uw5.toNat uw6.toNat cw.toNat c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 _ _
    e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14
    (digits_val a0 a1 a2 a3) (digits_val b0 b1 b2 b3) hA hB bm0 bm1 bm2 bm3 bm4 bm5 bm6 bm7
  have hcw := hs.1
  refine Exists.elim hs.2 (fun R hR => ?_)
  have hRdef := hR.1
  have hfin1 := hR.2.1
  have hfin2 := hR.2.2
  clear hs hR
  have hpack : limbsVal [uw0 ||| (uw1 <<< (32 : Nat)), uw2 ||| (uw3 <<< (32 : Nat)),
      uw4 ||| (uw5 <<< (32 : Nat)), uw6 ||| (cw <<< (32 : Nat))] = R := by
    rw [hRdef]
    simp only [limbsVal, or_shl32 bu0 bu1, or_shl32 bu2 bu3, or_shl32 bu4 bu5, or_shl32 bu6 hcw]
    clear * -
    omega
  have hev : E.eval ⟨l', s.globals, s.memory, s.ffi⟩ PACK = some (.rStruct [.word (uw0 ||| (uw1 <<< (32 : Nat))), .word (uw2 ||| (uw3 <<< (32 : Nat))), .word (uw4 ||| (uw5 <<< (32 : Nat))), .word (uw6 ||| (cw <<< (32 : Nat)))]) := by
    simp [evalF_rStruct, evalArgs_cons, evalArgs_nil, evalF_op hE.word, evalF_shift hE.word,
      evalF_local, hu0, hu1, hu2, hu3, hu4, hu5, hu6, hc, eval_const, wordsProj_cons,
      wordsProj_nil, wordOp, shiftl32]
    have key : ∀ x y : Word, OrOp.or x (OrOp.or y 0#64) = x ||| y := by
      intro x y
      show x ||| (y ||| 0#64) = x ||| y
      rw [BitVec.or_zero]
    exact ⟨key _ _, key _ _, key _ _, key _ _⟩
  refine WPs.dec_ev (fun v hv => ?_)
  have hv' : v = _ := Option.some.inj (hev.symm.trans hv).symm
  subst hv'
  intro rb hrb
  have ht := reduce_tail hE ⟨updatePanValueMap l' "r" (.rStruct [.word (uw0 ||| (uw1 <<< (32 : Nat))), .word (uw2 ||| (uw3 <<< (32 : Nat))), .word (uw4 ||| (uw5 <<< (32 : Nat))), .word (uw6 ||| (cw <<< (32 : Nat)))]), s.globals, s.memory, s.ffi⟩ rb
    (uw0 ||| (uw1 <<< (32 : Nat))) (uw2 ||| (uw3 <<< (32 : Nat))) (uw4 ||| (uw5 <<< (32 : Nat))) (uw6 ||| (cw <<< (32 : Nat))) (by lk []) hrb
  clear * - ht hpack hfin1 hfin2
  rcases ht with hst | ⟨lr, d0, d1, d2, d3, rfl, hd⟩
  · exact Or.inl hst
  · rw [hpack] at hd
    refine Or.inr ⟨_, d0, d1, d2, d3, rfl, ?_, ?_⟩
    · rw [hd]
      exact hfin1
    · rw [hd]
      exact hfin2

end InitECandidate.Solver.GuestBound
