import InitECandidate.Solver.GuestBound.ParseSteps

/-!
# `bn254_parse_g1` gives a canonical point or reports an error

An accepted point (result 0) has canonical coordinates in the output; in every
case only the output is written. Part of the canonicity chain for `fq12_inv`
(issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word}

theorem three_lt : limbsVal [(8797723225643362519#64 : Word), 2263834496217719225#64,
    3696305541684646532#64, 3035258219084094862#64] < bnP := by decide

/-- A parser returned `e`; the buffers known canonical stay so, and for `e = 0`
the output point is canonical too. -/
def ParseRet (s : St σ) (K : Nat) (pv0 : Word) (m0 : Word → Option (PanValue Word))
    (Wr : List Word) (hp : Word) (All Cn Out : List Word) (r : Result σ) : Prop :=
  ∃ l m' e, r = .returned l s.globals m' s.ffi [.word e] ∧ BufsK K pv0 m0 Wr hp All Cn m' ∧
    (e = 0#64 → BufsK K pv0 m0 Wr hp All (Out ++ Cn) m')

set_option maxHeartbeats 32000000 in
theorem bn254_parse_g1_bufs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "bn254_parse_g1" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (O hp pv0 : Word) (m0 : Word → Option (PanValue Word))
    (Wr All Cn : List Word) (hout : s.locals "out" = some (.word O))
    (hB : BufsK 1 pv0 m0 Wr hp All Cn s.memory)
    (hO0 : O ∈ All) (hO1 : O + 1#64 * 32#64 ∈ All) (hO2 : O + 2#64 * (1#64 * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 1#64 * 32#64).toNat ∨ O + 1#64 * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (1#64 * 32#64)).toNat ∨ O + 2#64 * (1#64 * 32#64) ∈ Wr) (h : Runs E s body r) :
    Stopped r ∨ ParseRet s 1 pv0 m0 Wr hp All Cn [O + 2#64 * (1#64 * 32#64), O + 1#64 * 32#64, O] r := by
  have hbody := (fun_of_index 686 hE.functions (by guest_decl_at 686) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpp : 0 < bnP := by decide
  have hF1 : (1#64 : Word).toNat = 1 := by decide
  have hK1 : (1 : Nat) = 1 ∨ (1 : Nat) = 2 ∨ (1 : Nat) = 12 := Or.inl rfl
  have e32 : (1#64 * 32#64 : Word) = 32#64 := by decide
  have e64 : (2#64 * (1#64 * 32#64) : Word) = 64#64 := by decide
  have hqbe := keepFn_sound (quietKeeper E) hE.functions 2 "u256_from_be" u256_from_be_quiet
  have hqz := keepFn_sound (quietKeeper E) hE.functions 1 "u256_is_zero" u256_is_zero_quiet
  have hqe := keepFn_sound (quietKeeper E) hE.functions 2 "u256_eq" u256_eq_quiet
  refine (?_ : WPs E s _ (ParseRet s 1 pv0 m0 Wr hp All Cn [O + 2#64 * (1#64 * 32#64), O + 1#64 * 32#64, O])) r h
  refine WPs.decCall_struct4 (fun x0 x1 x2 x3 g m ffi hret => ?_)
  obtain ⟨hg, hm, hf⟩ := hret.quiet hqbe
  subst g m ffi
  refine WPs.decCall_struct4 (fun y0 y1 y2 y3 g m ffi hret => ?_)
  obtain ⟨hg, hm, hf⟩ := hret.quiet hqbe
  subst g m ffi
  try dsimp only
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, hv⟩ := u256lt_ret hE hret (a0 := x0) (a1 := x1) (a2 := x2) (a3 := x3)
    (b0 := 4332616871279656263#64) (b1 := 10917124144477883021#64)
    (b2 := 13281191951274694749#64) (b3 := 3486998266802970665#64) (by lk [])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  rw [bnP_limbs]
  try dsimp only
  by_cases hxl : limbsVal [x0, x1, x2, x3] < bnP
  swap
  · rw [if_neg hxl]
    refine WPs.seqG (fun _ => False) (WPs.ite (w := 1#64) (fun x hx => by
      rw [eval_cmp_inv hE (of_eval (w := (0 : Word)) (by lk [])) (of_eval (eval_const _ _)) x hx]
      rfl) ?_) (fun _ hf => hf.elim)
    rw [if_neg (by decide)]
    refine WPs.ret (w := 1#64) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, s.memory, 1#64, rfl, hB, fun h => absurd h (by decide)⟩
  rw [if_pos hxl]
  refine WPs.guard0 (fun x hx => by
    rw [eval_cmp_inv hE (of_eval (w := (1 : Word)) (by lk [])) (of_eval (eval_const _ _)) x hx]
    rfl) ?_
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, hv⟩ := u256lt_ret hE hret (a0 := y0) (a1 := y1) (a2 := y2) (a3 := y3)
    (b0 := 4332616871279656263#64) (b1 := 10917124144477883021#64)
    (b2 := 13281191951274694749#64) (b3 := 3486998266802970665#64) (by lk [])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  rw [bnP_limbs]
  try dsimp only
  by_cases hyl : limbsVal [y0, y1, y2, y3] < bnP
  swap
  · rw [if_neg hyl]
    refine WPs.seqG (fun _ => False) (WPs.ite (w := 1#64) (fun x hx => by
      rw [eval_cmp_inv hE (of_eval (w := (0 : Word)) (by lk [])) (of_eval (eval_const _ _)) x hx]
      rfl) ?_) (fun _ hf => hf.elim)
    rw [if_neg (by decide)]
    refine WPs.ret (w := 1#64) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, s.memory, 1#64, rfl, hB, fun h => absurd h (by decide)⟩
  rw [if_pos hyl]
  refine WPs.guard0 (fun x hx => by
    rw [eval_cmp_inv hE (of_eval (w := (1 : Word)) (by lk [])) (of_eval (eval_const _ _)) x hx]
    rfl) ?_
  refine WPs.decCall_word (fun zx g m ffi hret => ?_)
  obtain ⟨hg, hm, hf⟩ := hret.quiet hqz
  subst g m ffi
  refine WPs.decCall_word (fun zy g m ffi hret => ?_)
  obtain ⟨hg, hm, hf⟩ := hret.quiet hqz
  subst g m ffi
  try dsimp only
  generalize hL : updatePanValueMap _ "yz" (PanValue.word zy) = L
  have L_out : L "out" = some (.word O) := by rw [← hL]; lk [hout]
  have L_x : L "x" = some (.rStruct [.word x0, .word x1, .word x2, .word x3]) := by
    rw [← hL]; lk []
  have L_y : L "y" = some (.rStruct [.word y0, .word y1, .word y2, .word y3]) := by
    rw [← hL]; lk []
  -- (0, 0) is the point at infinity
  refine WPs.seqG (fun st => st = ⟨L, s.globals, s.memory, s.ffi⟩)
    (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.ecp_set_inf_stepK hE hF1 hK1 (O := O) (eval_const _ _) (by lk [L_out]) hB hO0
        hO1 hO2 w0 w1 w2 (fun m hB' => ?_)
      refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      exact ⟨_, m, 0#64, rfl, hB'.mono (fun B hB'' => by simp [hB'']), fun _ => hB'⟩
  rintro _ rfl
  -- to Montgomery form, then the curve equation
  refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, a0, a1, a2, a3, hv, hal⟩ := fqtomont_ret hE hret (a0 := x0) (a1 := x1)
    (a2 := x2) (a3 := x3) (by lk [L_x]) hxl
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, b0, b1, b2, b3, hv, hbl⟩ := fqtomont_ret hE hret (a0 := y0) (a1 := y1)
    (a2 := y2) (a3 := y3) (by lk [L_y]) hyl
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  try dsimp only
  refine WPs.decCall_fqmul hE (a0 := b0) (a1 := b1) (a2 := b2) (a3 := b3) (b0 := b0) (b1 := b1)
    (b2 := b2) (b3 := b3) (by lk []) (by lk []) hbl hbl (fun l0 l1 l2 l3 hll _ => ?_)
  refine WPs.decCall_fqmul hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b0 := a0) (b1 := a1)
    (b2 := a2) (b3 := a3) (by lk []) (by lk []) hal hal (fun r0 r1 r2 r3 hrl _ => ?_)
  try dsimp only
  refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, s0, s1, s2, s3, hv, hsl⟩ := fqmul_ret hE hret (a0 := r0) (a1 := r1)
    (a2 := r2) (a3 := r3) (b0 := a0) (b1 := a1) (b2 := a2) (b3 := a3) (by lk []) (by lk [])
    hrl hal
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, t0, t1, t2, t3, hv, htl⟩ := fqadd_ret hE hret (a0 := s0) (a1 := s1)
    (a2 := s2) (a3 := s3) (b0 := 8797723225643362519#64) (b1 := 2263834496217719225#64)
    (b2 := 3696305541684646532#64) (b3 := 3035258219084094862#64) (by lk [])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) hsl three_lt
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  try dsimp only
  refine WPs.decCall_word (fun ze g m ffi hret => ?_)
  obtain ⟨hg, hm, hf⟩ := hret.quiet hqe
  subst g m ffi
  try dsimp only
  generalize hL3 : updatePanValueMap _ "eq" (PanValue.word ze) = L3
  have L3_out : L3 "out" = some (.word O) := by rw [← hL3]; lk [L_out]
  have L3_x : L3 "x" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]) := by
    rw [← hL3]; lk []
  have L3_y : L3 "y" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]) := by
    rw [← hL3]; lk []
  refine WPs.seqG (fun st => st = ⟨L3, s.globals, s.memory, s.ffi⟩)
    (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.ret (w := 1#64) (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      exact ⟨_, s.memory, 1#64, rfl, hB, fun h => absurd h (by decide)⟩
  rintro _ rfl
  refine WPs.store_stepK1 hE (D := O) (by lk [L3_out]) (by lk [L3_x]) hal hB hO0 w0
    (fun m hB => ?_)
  refine WPs.store_stepK1 hE (D := O + 1#64 * 32#64) (by rw [e32]; ev [L3_out]) (by lk [L3_y]) hbl hB
    hO1 w1 (fun m hB => ?_)
  refine WPs.store_stepK1 hE (D := O + 2#64 * (1#64 * 32#64)) (by rw [e64]; ev [L3_out])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) cone_lt hB hO2 w2
    (fun m hB => ?_)
  refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  exact ⟨_, m, 0#64, rfl, hB.mono (fun B hB'' => by simp [hB'']), fun _ => hB⟩

end InitECandidate.Solver.GuestBound
