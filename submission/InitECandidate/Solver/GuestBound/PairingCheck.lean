import InitECandidate.Solver.GuestBound.PairingRound

/-!
# `bn254_pairing_check`: step bound

Once the constant table is set up (`bn_gamma` nonzero, pointing at canonical
coefficients below the heap pointer), every non-error run of
`bn254_pairing_check` takes at most `10^88` steps. The loop over the pairs has
an unconditional cost; `fq12_inv` after it is bounded by `fq12_inv_cost`,
whose precondition (a canonical operand) is what the loop invariant provides.
This closes the two `fq12_inv` loops up to the start-up facts (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `var x = alloc(n); body` for a constant `n`, in budget form. -/
theorem alloc_step_n (hE : GuestEnv E) {x : VarName} {body : Prog Word} {pv nv : Word} {N : Nat}
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hle : panValueExpsStepCost [(Exp.const nv : Exp Word)] + 84 + 1 ≤ N)
    (h : ∀ qv : Word, pv.toNat + nv.toNat ≤ qv.toNat → InHeap qv →
      WPc E ⟨updatePanValueMap s.locals x (.word pv),
        updatePanValueMap s.globals "heap_ptr" (.word qv), s.memory, s.ffi⟩ body
        (N - (panValueExpsStepCost [(Exp.const nv : Exp Word)] + 84 + 1))
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPc E s (.decCall x .one "alloc" [.const nv] body) N Q := by
  refine WPc.decCall_sub (Fn.«alloc» hE) hle (fun v g m ffi hret => ?_)
  obtain ⟨hv, hm, hf, qv, hg, h1, h2⟩ := alloc_ret hE hret.ret (eval_const _ _) hp hpH
  simp only [List.cons.injEq, and_true] at hv
  subst v m ffi g
  exact h qv h1 h2

theorem pc_loop_cost' (hE : GuestEnv E) : Costs E PC_LOOP 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  have h : ∃ B, Costs E PC_LOOP B ∧ B ≤ 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem pc_tail_cost (hE : GuestEnv E) : Costs E PC_TAIL 1000000000000000000000000000000000000000000000000000000000000000 := by
  have h : ∃ B, Costs E PC_TAIL B ∧ B ≤ 1000000000000000000000000000000000000000000000000000000000000000 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem pc_last_cost (hE : GuestEnv E) : Costs E PC_LAST 1000 := by
  have h : ∃ B, Costs E PC_LAST B ∧ B ≤ 1000 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 128000000 in
theorem bn254_pairing_check_cost (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "bn254_pairing_check" E.functions = some (parameters, body))
    (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (Gt pv Pw : Word)
    (hpairs : s.locals "pairs" = some (.word Pw))
    (hgm : s.globals "bn_gamma" = some (.word Gt)) (hGt0 : Gt ≠ 0#64)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  have hbody := (fun_of_index 691 hE.functions (by guest_decl_at 691) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  refine WPc.steps (Q := fun _ => True) ?_ hrun hne
  -- bn254_init is a no-op
  refine WPc.seq_sub (fun st => st = s)
    (WPc.of_costs (Costs.callDest none _ (Fn.«bn254_init» hE))
      (WPs.call_ret (fun vs g m ffi hret => ?_))) (by budget) ?_
  · obtain ⟨hg, hm, hf⟩ := initnoop_ret hE hret hgm hGt0
    subst g m ffi
    rfl
  intro st' hst'
  rw [hst']
  refine WPc.decCall_sub (Fn.«heap_mark» hE) (by budget) (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, hv⟩ := heap_mark_ret hE hret.ret hp
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  try dsimp only
  refine alloc_step_n hE (nv := 96#64) hp hpH (by budget) (fun q1 h0 i0 => ?_)
  rw [show (96#64 : Word).toNat = 96 by decide] at h0
  try dsimp only
  refine alloc_step_n hE (nv := 192#64) (by lk []) i0 (by budget) (fun q2 h1 i1 => ?_)
  rw [show (192#64 : Word).toNat = 192 by decide] at h1
  try dsimp only
  refine alloc_step_n hE (nv := 96#64) (by lk []) i1 (by budget) (fun q3 h2 i2 => ?_)
  rw [show (96#64 : Word).toNat = 96 by decide] at h2
  try dsimp only
  refine alloc_step_n hE (nv := 192#64) (by lk []) i2 (by budget) (fun q4 h3 i3 => ?_)
  rw [show (192#64 : Word).toNat = 192 by decide] at h3
  try dsimp only
  refine alloc_step_n hE (nv := 1152#64) (by lk []) i3 (by budget) (fun q5 h4 i4 => ?_)
  rw [show (1152#64 : Word).toNat = 1152 by decide] at h4
  try dsimp only
  refine alloc_step_n hE (nv := 1152#64) (by lk []) i4 (by budget) (fun q6 h5 i5 => ?_)
  rw [show (1152#64 : Word).toNat = 1152 by decide] at h5
  try dsimp only
  refine alloc_step_n hE (nv := 384#64) (by lk []) i5 (by budget) (fun q7 h6 i6 => ?_)
  rw [show (384#64 : Word).toNat = 384 by decide] at h6
  try dsimp only
  refine alloc_step_n hE (nv := 384#64) (by lk []) i6 (by budget) (fun q8 h7 i7 => ?_)
  rw [show (384#64 : Word).toNat = 384 by decide] at h7
  try dsimp only
  refine alloc_step_n hE (nv := 384#64) (by lk []) i7 (by budget) (fun q9 h8 i8 => ?_)
  rw [show (384#64 : Word).toNat = 384 by decide] at h8
  try dsimp only
  refine alloc_step_n hE (nv := 384#64) (by lk []) i8 (by budget) (fun q10 h9 i9 => ?_)
  rw [show (384#64 : Word).toNat = 384 by decide] at h9
  try dsimp only
  refine alloc_step_n hE (nv := 384#64) (by lk []) i9 (by budget) (fun q11 h10 i10 => ?_)
  rw [show (384#64 : Word).toNat = 384 by decide] at h10
  try dsimp only
  unfold InHeap at hpH i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10
  have geo : PCGeo pv q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 :=
    ⟨hpH.2, i0.2, i1.2, i2.2, i3.2, i4.2, i5.2, i6.2, i7.2, i8.2, i9.2, i10.2, h0,
      h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, i10.1⟩
  generalize hL : updatePanValueMap _ "res" (PanValue.word q10) = L
  generalize hG : updatePanValueMap _ "heap_ptr" (PanValue.word q11) = G
  have hGq : G "heap_ptr" = some (.word q11) := by rw [← hG]; lk []
  have hGg : G "bn_gamma" = some (.word Gt) := by rw [← hG]; lk [hgm]
  have L_pairs : L "pairs" = some (.word Pw) := by rw [← hL]; lk [hpairs]
  have L_g1 : L "g1" = some (.word pv) := by rw [← hL]; lk [hpairs]
  have L_g2 : L "g2" = some (.word q1) := by rw [← hL]; lk [hpairs]
  have L_t1 : L "t1" = some (.word q2) := by rw [← hL]; lk [hpairs]
  have L_t2 : L "t2" = some (.word q3) := by rw [← hL]; lk [hpairs]
  have L_Q : L "Q" = some (.word q4) := by rw [← hL]; lk [hpairs]
  have L_P : L "P" = some (.word q5) := by rw [← hL]; lk [hpairs]
  have L_fnum : L "fnum" = some (.word q6) := by rw [← hL]; lk [hpairs]
  have L_fden : L "fden" = some (.word q7) := by rw [← hL]; lk [hpairs]
  have L_anum : L "anum" = some (.word q8) := by rw [← hL]; lk [hpairs]
  have L_aden : L "aden" = some (.word q9) := by rw [← hL]; lk [hpairs]
  have L_mark : L "mark" = some (.word pv) := by rw [← hL]; lk [hpairs]
  have hB0 : Bufs q11 s.memory [q10, q9, q8, q7, q6, q5 + 768#64, q5 + 384#64, q5, q4 + 768#64, q4 + 384#64, q4] q11 [q10, q9, q8, q7, q6, q5 + 768#64, q5 + 384#64, q5, q4 + 768#64, q4 + 384#64, q4] [] s.memory :=
    (BufsK.ofChain (K := 12) geo.chain12 geo.hb geo.ahp s.memory).to12
  -- anum = aden = 1
  refine WPc.seq_sub (fun st => ∃ m, st = ⟨L, G, m, s.ffi⟩ ∧
      Bufs q11 s.memory [q10, q9, q8, q7, q6, q5 + 768#64, q5 + 384#64, q5, q4 + 768#64, q4 + 384#64, q4] q11 [q10, q9, q8, q7, q6, q5 + 768#64, q5 + 384#64, q5, q4 + 768#64, q4 + 384#64, q4] [q8] m)
    (WPc.of_costs (Costs.callDest none _ (Fn.«fe_set_one» hE))
      (WPs.of_seq_skip (WPs.fe_set_one_step hE (D := q8) (eval_const _ _) (by lk [L_anum]) hB0
        (by simp) (Or.inr (by simp)) (fun m hB => WPs.skip ⟨m, rfl, hB⟩)))) (by budget) ?_
  rintro _ ⟨m1, rfl, hB1⟩
  refine WPc.seq_sub (fun st => ∃ m, st = ⟨L, G, m, s.ffi⟩ ∧
      Bufs q11 s.memory [q10, q9, q8, q7, q6, q5 + 768#64, q5 + 384#64, q5, q4 + 768#64, q4 + 384#64, q4] q11 [q10, q9, q8, q7, q6, q5 + 768#64, q5 + 384#64, q5, q4 + 768#64, q4 + 384#64, q4] [q9, q8] m)
    (WPc.of_costs (Costs.callDest none _ (Fn.«fe_set_one» hE))
      (WPs.of_seq_skip (WPs.fe_set_one_step hE (D := q9) (eval_const _ _) (by lk [L_aden]) hB1
        (by simp) (Or.inr (by simp)) (fun m hB => WPs.skip ⟨m, rfl, hB⟩)))) (by budget) ?_
  rintro _ ⟨m2, rfl, hB2⟩
  refine WPc.dec_sub (by budget) (fun v hv => ?_)
  rw [eval_const] at hv
  cases hv
  refine WPc.dec_sub (by budget) (fun v hv => ?_)
  rw [eval_const] at hv
  cases hv
  try dsimp only
  generalize hL2 : updatePanValueMap (updatePanValueMap L "nontrivial" (PanValue.word 0#64)) "i"
    (PanValue.word 0#64) = L2
  have L2_pairs : L2 "pairs" = some (.word Pw) := by rw [← hL2]; lk [L_pairs]
  have L2_g1 : L2 "g1" = some (.word pv) := by rw [← hL2]; lk [L_g1]
  have L2_g2 : L2 "g2" = some (.word q1) := by rw [← hL2]; lk [L_g2]
  have L2_t1 : L2 "t1" = some (.word q2) := by rw [← hL2]; lk [L_t1]
  have L2_t2 : L2 "t2" = some (.word q3) := by rw [← hL2]; lk [L_t2]
  have L2_Q : L2 "Q" = some (.word q4) := by rw [← hL2]; lk [L_Q]
  have L2_P : L2 "P" = some (.word q5) := by rw [← hL2]; lk [L_P]
  have L2_fnum : L2 "fnum" = some (.word q6) := by rw [← hL2]; lk [L_fnum]
  have L2_fden : L2 "fden" = some (.word q7) := by rw [← hL2]; lk [L_fden]
  have L2_anum : L2 "anum" = some (.word q8) := by rw [← hL2]; lk [L_anum]
  have L2_aden : L2 "aden" = some (.word q9) := by rw [← hL2]; lk [L_aden]
  have L2_mark : L2 "mark" = some (.word pv) := by rw [← hL2]; lk [L_mark]
  -- the loop over the pairs
  refine WPc.seq_sub
    (fun a => a.globals = G ∧ a.ffi = s.ffi ∧
      (∀ x, x ≠ "i" → x ≠ "nontrivial" → a.locals x = L2 x) ∧
      (∃ iw : Word, a.locals "i" = some (.word iw)) ∧
      (∃ nw : Word, a.locals "nontrivial" = some (.word nw)) ∧
      Bufs q11 a.memory [q10, q9, q8, q7, q6, q5 + 768#64, q5 + 384#64, q5, q4 + 768#64, q4 + 384#64, q4] q11 [q10, q9, q8, q7, q6, q5 + 768#64, q5 + 384#64, q5, q4 + 768#64, q4 + 384#64, q4] [q9, q8] a.memory)
    (WPc.of_costs (pc_loop_cost' hE) (WPs.loopG
      (I := fun a => a.globals = G ∧ a.ffi = s.ffi ∧
        (∀ x, x ≠ "i" → x ≠ "nontrivial" → a.locals x = L2 x) ∧
        (∃ iw : Word, a.locals "i" = some (.word iw)) ∧
        (∃ nw : Word, a.locals "nontrivial" = some (.word nw)) ∧
        Bufs q11 a.memory [q10, q9, q8, q7, q6, q5 + 768#64, q5 + 384#64, q5, q4 + 768#64, q4 + 384#64, q4] q11 [q10, q9, q8, q7, q6, q5 + 768#64, q5 + 384#64, q5, q4 + 768#64, q4 + 384#64, q4] [q9, q8] a.memory)
      ⟨rfl, rfl, fun _ _ _ => rfl, ⟨0#64, by rw [← hL2]; lk []⟩, ⟨0#64, by rw [← hL2]; lk []⟩,
        ((hB2.toK).rebase).to12⟩ ?_ (fun a k hI _ => hI))) (by budget) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, ⟨iw, hi⟩, ⟨nw, hnt⟩, hB⟩ -
    simp only at hg hf hloc hi hnt hB
    subst ga fa
    refine WPs.conseq (pc_round hE (st := ⟨la, G, ma, s.ffi⟩) (Pw := Pw) (iw := iw) (nw := nw)
      (mk := pv) geo ((hloc _ (by decide) (by decide)).trans L2_pairs) hi hnt
      ((hloc _ (by decide) (by decide)).trans L2_g1) ((hloc _ (by decide) (by decide)).trans L2_g2)
      ((hloc _ (by decide) (by decide)).trans L2_t1) ((hloc _ (by decide) (by decide)).trans L2_t2)
      ((hloc _ (by decide) (by decide)).trans L2_Q) ((hloc _ (by decide) (by decide)).trans L2_P)
      ((hloc _ (by decide) (by decide)).trans L2_fnum)
      ((hloc _ (by decide) (by decide)).trans L2_fden)
      ((hloc _ (by decide) (by decide)).trans L2_anum)
      ((hloc _ (by decide) (by decide)).trans L2_aden)
      ((hloc _ (by decide) (by decide)).trans L2_mark) hGq hGg hB) ?_
    intro r hr
    cases r with
    | normal l g m f =>
      obtain ⟨hg', hf', hl', hi', hn', hB'⟩ := hr
      exact ⟨hg', hf', fun x h1 h2 => (hl' x h1 h2).trans (hloc x h1 h2), hi', hn', hB'⟩
    | continued l g m f => exact hr
    | broke l g m f => exact hr
    | _ => trivial
  -- after the loop only `fq12_inv` needs a fact: `aden` is canonical
  rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, -, -, hB⟩
  simp only at hg hf hloc hB
  subst ga fa
  have la_aden : la "aden" = some (.word q9) := (hloc _ (by decide) (by decide)).trans L2_aden
  refine WPc.dec_sub (by budget) (fun v hv => ?_)
  rw [eval_const] at hv
  cases hv
  try dsimp only
  refine WPc.seq_sub (fun _ => True)
    (WPc.ite_both
      (B₁ := panValueExpsStepCost [(Exp.var VarKind.local "aden" : Exp Word),
        Exp.var VarKind.local "aden"] + 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000 + 0 + 1 + 1000000000000000000000000000000000000000000000000000000000000000 + 1) (B₂ := 1) (fun w _ => ?_))
    (by budget)
    (fun _ _ => WPc.of_costs_le (pc_last_cost hE) (by budget) (WPs.of_true (fun _ => trivial)))
  split
  · exact WPc.of_costs Costs.skip (WPs.skip trivial)
  · refine WPc.mono (WPc.seq (B₂ := 1000000000000000000000000000000000000000000000000000000000000000) (fun _ => True)
      (WPc.call_at (B := 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000) (fq12inv_costAt hE (D := q9) (A := q9) (pv := q11)
        (by lk [la_aden]) (by lk [la_aden]) hGq ⟨geo.hb, geo.ahp⟩ geo.a10
        (by have := geo.o11; have := geo.o12; omega) (hB.can q9 (by simp)))
        (WPs.of_true (fun r => by cases r <;> trivial)))
      (fun _ _ => WPc.of_costs (pc_tail_cost hE) (WPs.of_true (fun r => by cases r <;> trivial))))
      (by budget) (fun _ h => h)

end InitECandidate.Solver.GuestBound
