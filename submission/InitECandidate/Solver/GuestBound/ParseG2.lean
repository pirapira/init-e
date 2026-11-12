import InitECandidate.Solver.GuestBound.ParseG1

/-!
# `bn254_parse_g2` gives a canonical point or reports an error

As for `bn254_parse_g1`, with `Fq2` coordinates; the on-curve check runs on
three temporaries and writes nothing else. Part of the canonicity chain for
`fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word}

theorem izb_quiet : keepFn quietLeaf Guest.Software.guestAst 1 "is_zero_bytes" = true := by
  decide +kernel

theorem and4_bits (p0 p1 p2 p3 : Prop) [Decidable p0] [Decidable p1] [Decidable p2]
    [Decidable p3] :
    evalPanCmp .equal (AndOp.and (if p0 then (1 : Word) else 0)
      (AndOp.and (if p1 then (1 : Word) else 0) (AndOp.and (if p2 then (1 : Word) else 0)
      (AndOp.and (if p3 then (1 : Word) else 0) 18446744073709551615#64)))) 0#64 =
      if p0 ∧ p1 ∧ p2 ∧ p3 then 0 else 1 := by
  by_cases h0 : p0 <;> by_cases h1 : p1 <;> by_cases h2 : p2 <;> by_cases h3 : p3 <;>
    simp [h0, h1, h2, h3] <;> decide

theorem b2re_lt : limbsVal [(4321547867055981224#64 : Word), 147241268046680925#64,
    2789960110459671136#64, 2671978398120978541#64] < bnP := by decide

theorem b2im_lt : limbsVal [(4100506350182530919#64 : Word), 7345568344173317438#64,
    15513160039642431658#64, 90557763186888013#64] < bnP := by decide

theorem zero_lt : limbsVal [(0#64 : Word), 0#64, 0#64, 0#64] < bnP := by decide

/-- Two stores filling a two-coefficient buffer with canonical values. -/
theorem WPs.store2_stepK2 (hE : GuestEnv E) {a v a' v' : Exp Word} {rest : Prog Word}
    {D hp pv0 w0 w1 w2 w3 u0 u1 u2 u3 : Word} {All Cn : List Word}
    (ha : E.eval s a = some (.word D))
    (hv : E.eval s v = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (ha' : ∀ m1, E.eval ⟨s.locals, s.globals, m1, s.ffi⟩ a' = some (.word (D + 32#64)))
    (hv' : ∀ m1, E.eval ⟨s.locals, s.globals, m1, s.ffi⟩ v' =
      some (.rStruct [.word u0, .word u1, .word u2, .word u3]))
    (hlt : limbsVal [w0, w1, w2, w3] < bnP) (hlt' : limbsVal [u0, u1, u2, u3] < bnP)
    (hB : BufsK 2 pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr)
    (h : ∀ m', BufsK 2 pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.store a v) (.seq (.store a' v') rest)) Q := by
  have gD := hB.geo D hD
  have hpb := hB.hpb
  refine WPs.seq_store4 hE (addr := coefAddr D 0) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3)
    (of_eval (by rw [coefAddr_zero]; exact ha)) hv ?_
  refine WPs.seq_store4 hE (addr := coefAddr D 1) (w0 := u0) (w1 := u1) (w2 := u2) (w3 := u3)
    (of_eval (ha' _)) (hv' _) ?_
  refine h _ (hB.write hD hDl (fun x _ hx => ?_)
    (CanonN.snoc (k := 1) (by omega) (CanonN.snoc (k := 0) (by omega) (CanonN.nil _ _) hlt)
      hlt'))
  show set4 (set4 s.memory _ _ _ _ _) _ _ _ _ _ x = _
  rw [set4_outN (n := 2) (by omega) (by omega) hx, set4_outN (n := 2) (by omega) (by omega) hx]

/-- `fq2_mul(d, a, b); rest` over `BufsK 2`. -/
theorem WPs.fq2_mul_stepK2 (hE : GuestEnv E) {eD eA eB : Exp Word} {rest : Prog Word}
    {D A B hp pv0 : Word} {All Cn : List Word}
    (h2 : E.eval s eD = some (.word D)) (h3 : E.eval s eA = some (.word A))
    (h4 : E.eval s eB = some (.word B))
    (hB : BufsK 2 pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hA : A ∈ Cn) (hBc : B ∈ Cn)
    (h : ∀ m', BufsK 2 pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fq2_mul" [eD, eA, eB]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gA := hB.geo A (hB.sub A hA)
  have gB := hB.geo B (hB.sub B hBc)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := fq2mul_ret hE hret h2 h3 h4 (by omega) (by omega) (by omega)
    (hB.can A hA) (hB.can B hBc)
  subst g ffi
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

set_option maxHeartbeats 64000000 in
theorem bn254_parse_g2_bufs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "bn254_parse_g2" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (O hp pv0 : Word) (m0 : Word → Option (PanValue Word))
    (Wr All Cn : List Word) (hout : s.locals "out" = some (.word O))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : BufsK 2 pv0 m0 Wr hp All Cn s.memory)
    (hO0 : O ∈ All) (hO1 : O + 2#64 * 32#64 ∈ All) (hO2 : O + 2#64 * (2#64 * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 2#64 * 32#64).toNat ∨ O + 2#64 * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (2#64 * 32#64)).toNat ∨ O + 2#64 * (2#64 * 32#64) ∈ Wr) (h : Runs E s body r) :
    Stopped r ∨ ParseRet s 2 pv0 m0 Wr hp All Cn [O + 2#64 * (2#64 * 32#64), O + 2#64 * 32#64, O] r := by
  have hbody := (fun_of_index 687 hE.functions (by guest_decl_at 687) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hF2 : (2#64 : Word).toNat = 2 := by decide
  have hK2 : (2 : Nat) = 1 ∨ (2 : Nat) = 2 ∨ (2 : Nat) = 12 := Or.inr (Or.inl rfl)
  have e64 : (2#64 * 32#64 : Word) = 64#64 := by decide
  have e128 : (2#64 * (2#64 * 32#64) : Word) = 128#64 := by decide
  have hez : (64#64 : Word).toNat = 32 * 2 := by decide
  have gO0 := hB0.geo O hO0
  have gO1 := hB0.geo _ hO1
  have gO2 := hB0.geo _ hO2
  have hqbe := keepFn_sound (quietKeeper E) hE.functions 2 "u256_from_be" u256_from_be_quiet
  have hqz := keepFn_sound (quietKeeper E) hE.functions 1 "is_zero_bytes" izb_quiet
  have hqe := keepFn_sound (quietKeeper E) hE.functions 1 "memeq" memeq_quiet
  refine (?_ : WPs E s _ (ParseRet s 2 pv0 m0 Wr hp All Cn [O + 2#64 * (2#64 * 32#64), O + 2#64 * 32#64, O])) r h
  refine WPs.decCall_struct4 (fun b0 b1 b2 b3 g m ffi hret => ?_)
  obtain ⟨hg', hm, hf⟩ := hret.quiet hqbe
  subst g m ffi
  refine WPs.decCall_struct4 (fun a0 a1 a2 a3 g m ffi hret => ?_)
  obtain ⟨hg', hm, hf⟩ := hret.quiet hqbe
  subst g m ffi
  refine WPs.decCall_struct4 (fun d0 d1 d2 d3 g m ffi hret => ?_)
  obtain ⟨hg', hm, hf⟩ := hret.quiet hqbe
  subst g m ffi
  refine WPs.decCall_struct4 (fun c0 c1 c2 c3 g m ffi hret => ?_)
  obtain ⟨hg', hm, hf⟩ := hret.quiet hqbe
  subst g m ffi
  try dsimp only
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg', hm, hf, hv⟩ := u256lt_ret hE hret (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := 4332616871279656263#64) (b1 := 10917124144477883021#64)
    (b2 := 13281191951274694749#64) (b3 := 3486998266802970665#64) (by lk [])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  rw [bnP_limbs]
  try dsimp only
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg', hm, hf, hv⟩ := u256lt_ret hE hret (a0 := b0) (a1 := b1) (a2 := b2) (a3 := b3)
    (b0 := 4332616871279656263#64) (b1 := 10917124144477883021#64)
    (b2 := 13281191951274694749#64) (b3 := 3486998266802970665#64) (by lk [])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  rw [bnP_limbs]
  try dsimp only
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg', hm, hf, hv⟩ := u256lt_ret hE hret (a0 := c0) (a1 := c1) (a2 := c2) (a3 := c3)
    (b0 := 4332616871279656263#64) (b1 := 10917124144477883021#64)
    (b2 := 13281191951274694749#64) (b3 := 3486998266802970665#64) (by lk [])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  rw [bnP_limbs]
  try dsimp only
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg', hm, hf, hv⟩ := u256lt_ret hE hret (a0 := d0) (a1 := d1) (a2 := d2) (a3 := d3)
    (b0 := 4332616871279656263#64) (b1 := 10917124144477883021#64)
    (b2 := 13281191951274694749#64) (b3 := 3486998266802970665#64) (by lk [])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  rw [bnP_limbs]
  try dsimp only
  by_cases hall : limbsVal [a0, a1, a2, a3] < bnP ∧ limbsVal [b0, b1, b2, b3] < bnP ∧ limbsVal [c0, c1, c2, c3] < bnP ∧ limbsVal [d0, d1, d2, d3] < bnP
  swap
  · refine WPs.seqG (fun _ => False) (WPs.ite (w := 1#64) (fun x hx => by
      rw [eval_cmp_inv hE (of_eval (w := AndOp.and (if limbsVal [a0, a1, a2, a3] < bnP then (1 : Word) else 0)
        (AndOp.and (if limbsVal [b0, b1, b2, b3] < bnP then (1 : Word) else 0)
        (AndOp.and (if limbsVal [c0, c1, c2, c3] < bnP then (1 : Word) else 0)
        (AndOp.and (if limbsVal [d0, d1, d2, d3] < bnP then (1 : Word) else 0) 18446744073709551615#64)))) (by ev [])) (of_eval (eval_const _ _)) x hx,
        and4_bits, if_neg hall]
      rfl) ?_) (fun _ hf => hf.elim)
    rw [if_neg (by decide)]
    refine WPs.ret (w := 1#64) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, s.memory, 1#64, rfl, hB0, fun h => absurd h (by decide)⟩
  refine WPs.guard0 (fun x hx => by
    rw [eval_cmp_inv hE (of_eval (w := AndOp.and (if limbsVal [a0, a1, a2, a3] < bnP then (1 : Word) else 0)
        (AndOp.and (if limbsVal [b0, b1, b2, b3] < bnP then (1 : Word) else 0)
        (AndOp.and (if limbsVal [c0, c1, c2, c3] < bnP then (1 : Word) else 0)
        (AndOp.and (if limbsVal [d0, d1, d2, d3] < bnP then (1 : Word) else 0) 18446744073709551615#64)))) (by ev [])) (of_eval (eval_const _ _)) x hx,
      and4_bits, if_pos hall]
    rfl) ?_
  obtain ⟨hx0, hx1, hy0, hy1⟩ := hall
  refine WPs.decCall_word (fun zz g m ffi hret => ?_)
  obtain ⟨hg', hm, hf⟩ := hret.quiet hqz
  subst g m ffi
  try dsimp only
  generalize hL : updatePanValueMap _ "z" (PanValue.word zz) = L
  have L_out : L "out" = some (.word O) := by rw [← hL]; lk [hout]
  have L_x0 : L "x0" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]) := by
    rw [← hL]; lk []
  have L_x1 : L "x1" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]) := by
    rw [← hL]; lk []
  have L_y0 : L "y0" = some (.rStruct [.word c0, .word c1, .word c2, .word c3]) := by
    rw [← hL]; lk []
  have L_y1 : L "y1" = some (.rStruct [.word d0, .word d1, .word d2, .word d3]) := by
    rw [← hL]; lk []
  refine WPs.seqG (fun st => st = ⟨L, s.globals, s.memory, s.ffi⟩)
    (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.ecp_set_inf_stepK hE hF2 hK2 (O := O) (eval_const _ _) (by lk [L_out]) hB0 hO0
        hO1 hO2 w0 w1 w2 (fun m hB' => ?_)
      refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      exact ⟨_, m, 0#64, rfl, hB'.mono (fun B hB'' => by simp [hB'']), fun _ => hB'⟩
  rintro _ rfl
  refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg', hm, hf, p0, p1, p2, p3, hv, hx0'⟩ := fqtomont_ret hE hret (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (by lk [L_x0]) hx0
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  have L_x1' : (updatePanValueMap L "x0" (.rStruct [.word p0, .word p1, .word p2, .word p3]))
      "x1" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]) := by lk [L_x1]
  refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg', hm, hf, q0, q1, q2, q3, hv, hx1'⟩ := fqtomont_ret hE hret (a0 := b0) (a1 := b1) (a2 := b2) (a3 := b3)
    (by lk [L_x1]) hx1
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg', hm, hf, r0, r1, r2, r3, hv, hy0'⟩ := fqtomont_ret hE hret (a0 := c0) (a1 := c1) (a2 := c2) (a3 := c3)
    (by lk [L_y0]) hy0
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg', hm, hf, t0, t1, t2, t3, hv, hy1'⟩ := fqtomont_ret hE hret (a0 := d0) (a1 := d1) (a2 := d2) (a3 := d3)
    (by lk [L_y1]) hy1
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  try dsimp only
  generalize hL1 : updatePanValueMap _ "y1" (PanValue.rStruct [.word t0, .word t1, .word t2,
    .word t3]) = L1
  have L1_out : L1 "out" = some (.word O) := by rw [← hL1]; lk [L_out]
  have L1_x0 : L1 "x0" = some (.rStruct [.word p0, .word p1, .word p2, .word p3]) := by
    rw [← hL1]; lk []
  have L1_x1 : L1 "x1" = some (.rStruct [.word q0, .word q1, .word q2, .word q3]) := by
    rw [← hL1]; lk []
  have L1_y0 : L1 "y0" = some (.rStruct [.word r0, .word r1, .word r2, .word r3]) := by
    rw [← hL1]; lk []
  have L1_y1 : L1 "y1" = some (.rStruct [.word t0, .word t1, .word t2, .word t3]) := by
    rw [← hL1]; lk []
  have hB := hB0
  refine WPs.store2_stepK2 hE (D := O) (by lk [L1_out]) (by lk [L1_x0])
    (fun m1 => by ev [L1_out]) (fun m1 => by lk [L1_x1]) hx0' hx1' hB hO0 w0 (fun m hB => ?_)
  try dsimp only
  refine WPs.store2_stepK2 hE (D := O + 2#64 * 32#64) (by rw [e64]; ev [L1_out]) (by lk [L1_y0])
    (fun m1 => by rw [e64, BitVec.add_assoc]; ev [L1_out]) (fun m1 => by lk [L1_y1]) hy0' hy1'
    hB hO1 w1 (fun m hB => ?_)
  try dsimp only
  refine WPs.store2_stepK2 hE (D := O + 2#64 * (2#64 * 32#64)) (by rw [e128]; ev [L1_out])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
    (fun m1 => by rw [e128, BitVec.add_assoc]; ev [L1_out])
    (fun m1 => by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) cone_lt zero_lt
    hB hO2 w2 (fun m hB => ?_)
  try dsimp only
  -- the curve equation, on three temporaries
  refine WPs.decCall_ret (fun v g m' ffi hret => ?_)
  obtain ⟨hg', hm, hf, hv⟩ := heap_mark_ret hE hret hg
  simp only [List.cons.injEq, and_true] at hv
  subst g m' ffi v
  try dsimp only
  refine WPs.fe_alloc_stepK hE hez (eval_const _ _) hg hB (fun q1' l0 a0' hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_stepK hE hez (eval_const _ _) (by lk []) hB (fun q2' l1 a1' hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_stepK hE hez (eval_const _ _) (by lk []) hB (fun q3' l2 a2' hB => ?_)
  try dsimp only
  generalize hL2 : updatePanValueMap _ "b2" (PanValue.word q2') = L2
  generalize hG : updatePanValueMap _ "heap_ptr" (PanValue.word q3') = G
  have hGq : G "heap_ptr" = some (.word q3') := by rw [← hG]; lk []
  have L2_out : L2 "out" = some (.word O) := by rw [← hL2]; lk [L1_out]
  have L2_t1 : L2 "t1" = some (.word hp) := by rw [← hL2]; lk []
  have L2_t2 : L2 "t2" = some (.word q1') := by rw [← hL2]; lk []
  have L2_b2 : L2 "b2" = some (.word q2') := by rw [← hL2]; lk []
  have L2_mark : L2 "mark" = some (.word hp) := by rw [← hL2]; lk []
  refine WPs.store2_stepK2 hE (D := q2') (by lk [L2_b2])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) (fun m1 => by ev [L2_b2])
    (fun m1 => by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) b2re_lt b2im_lt
    hB (by simp) (Or.inl l2) (fun m hB => ?_)
  try dsimp only
  refine WPs.fq2_mul_stepK2 hE (D := hp) (A := O + 2#64 * 32#64) (B := O + 2#64 * 32#64) (by lk [L2_t1])
    (by rw [e64]; ev [L2_out]) (by rw [e64]; ev [L2_out]) hB (by simp) (Or.inl l0) (by simp)
    (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fq2_mul_stepK2 hE (D := q1') (A := O) (B := O) (by lk [L2_t2]) (by lk [L2_out])
    (by lk [L2_out]) hB (by simp) (Or.inl l1) (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fq2_mul_stepK2 hE (D := q1') (A := q1') (B := O) (by lk [L2_t2]) (by lk [L2_t2])
    (by lk [L2_out]) hB (by simp) (Or.inl l1) (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_add_stepK hE hF2 (by omega) (D := q1') (A := q1') (B := q2') (eval_const _ _)
    (by lk [L2_t2]) (by lk [L2_t2]) (by lk [L2_b2]) hB (by simp) (Or.inl l1) (by simp) (by simp)
    (fun m hB => ?_)
  try dsimp only
  refine WPs.decCall_word (fun ze g m' ffi hret => ?_)
  obtain ⟨hg', hm, hf⟩ := hret.quiet hqe
  subst g m' ffi
  try dsimp only
  refine WPs.seq_call_ret (fun vs g m4 ffi hret => ?_)
  obtain ⟨hg', hm', hf⟩ := release_ret hE hret (mv := hp) (pv := q3') (by lk [L2_mark]) hGq
  subst g m4 ffi
  simp only [← hG, hp_update_update]
  rw [update_same _ _ _ hg]
  have hR1 : BufsK 2 pv0 m0 Wr hp All Cn m :=
    BufsK.restrict hB0 hB (fun B hB' => ⟨hB0.sub B hB', by simp [hB']⟩)
  have hR2 : BufsK 2 pv0 m0 Wr hp All ([O + 2#64 * (2#64 * 32#64), O + 2#64 * 32#64, O] ++ Cn) m := by
    refine BufsK.restrict hB0 hB (fun B hB' => ?_)
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hB'
    rcases hB' with rfl | rfl | rfl | hB'
    · exact ⟨hO2, by simp⟩
    · exact ⟨hO1, by simp⟩
    · exact ⟨hO0, by simp⟩
    · exact ⟨hB0.sub B hB', by simp [hB']⟩
  generalize hL4 : updatePanValueMap L2 "eq" (PanValue.word ze) = L4
  refine WPs.seqG (fun st => st = ⟨L4, s.globals, m, s.ffi⟩) (WPs.ite_both (fun w _ => ?_))
    ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.ret (w := 1#64) (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      exact ⟨_, m, 1#64, rfl, hR1, fun h => absurd h (by decide)⟩
  rintro _ rfl
  refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  exact ⟨_, m, 0#64, rfl, hR1, fun _ => hR2⟩

end InitECandidate.Solver.GuestBound
