import InitECandidate.Solver.GuestBound.FeBufs

/-!
# `ecp_double` on `Fq12` points keeps coefficients below `p`

Twenty field operations on seven temporaries, then three copies into the
output point, stated with the `Bufs` invariant so that callers can use it as
one more step. Part of the canonicity chain for `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word}

theorem add_lit_toNat {P : Word} {k : Nat} (hk : k < 2 ^ 32) (h : P.toNat + k < 2 ^ 64) :
    (P + BitVec.ofNat 64 k).toNat = P.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Result of a point operation: the listed buffers are now canonical. -/
def BufsRet (s : St σ) (pv0 : Word) (m0 : Word → Option (PanValue Word)) (Wr : List Word)
    (hp : Word) (All Cn : List Word) (r : Result σ) : Prop :=
  ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧ Bufs pv0 m0 Wr hp All Cn m'

set_option maxHeartbeats 32000000 in
theorem ecp_double12_bufs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "ecp_double" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (P O hp pv0 : Word) (m0 : Word → Option (PanValue Word))
    (Wr All Cn : List Word)
    (hfld : s.locals "fld" = some (.word 12#64)) (hpt : s.locals "pt" = some (.word P))
    (hout : s.locals "out" = some (.word O)) (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : Bufs pv0 m0 Wr hp All Cn s.memory)
    (hP0 : P ∈ Cn) (hP1 : P + 384#64 ∈ Cn) (hP2 : P + 768#64 ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + 384#64 ∈ All) (hO2 : O + 768#64 ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 384#64).toNat ∨ O + 384#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 768#64).toNat ∨ O + 768#64 ∈ Wr) (h : Runs E s body r) :
    Stopped r ∨ BufsRet s pv0 m0 Wr hp All ((O + 768#64) :: (O + 384#64) :: O :: Cn) r := by
  have hbody := (fun_of_index 673 hE.functions (by guest_decl_at 673) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have gO0 := hB0.geo O hO0
  have gO1 := hB0.geo _ hO1
  have gO2 := hB0.geo _ hO2
  refine (?_ : WPs E s _ (BufsRet s pv0 m0 Wr hp All ((O + 768#64) :: (O + 384#64) :: O :: Cn))) r h
  refine WPs.dec (w := 384#64) (of_eval (by ev [evalPanOp, hfld])) ?_
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg', hm, hf, hv⟩ := heap_mark_ret hE hret hg
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  refine WPs.dec (w := P) (of_eval (by lk [hpt])) ?_
  refine WPs.dec (w := P + 384#64) (of_eval (by ev [hpt])) ?_
  refine WPs.dec (w := P + 768#64) (of_eval (by ev [evalPanOp, hpt])) ?_
  try dsimp only
  have hB := hB0
  refine WPs.fe_alloc_step hE (by lk []) hg hB (fun q1 l0 a0 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q2 l1 a1 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q3 l2 a2 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q4 l3 a3 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q5 l4 a4 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q6 l5 a5 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q7 l6 a6 hB => ?_)
  try dsimp only
  have hgq : (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap
      (updatePanValueMap (updatePanValueMap (updatePanValueMap s.globals "heap_ptr" (.word q1))
      "heap_ptr" (.word q2)) "heap_ptr" (.word q3)) "heap_ptr" (.word q4)) "heap_ptr"
      (.word q5)) "heap_ptr" (.word q6)) "heap_ptr" (.word q7)) "heap_ptr" = some (.word q7) := by
    lk []
  refine WPs.fe_sqr_step hE (D := q5) (A := P) (by lk [hfld]) (by lk []) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l5) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := hp) (A := q5) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) (Or.inl l0) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q1) (A := P + 384#64) (B := P + 768#64) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l1) (by simp [hP0, hP1, hP2]) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q5) (A := P) (B := P + 384#64) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l5) (by simp [hP0, hP1, hP2]) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q2) (A := q5) (B := q1) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l2) (by simp [hP0, hP1, hP2]) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sqr_step hE (D := q5) (A := hp) (by lk [hfld]) (by lk []) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l5) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := q6) (A := q2) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) (Or.inl l6) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sub_step hE (D := q3) (A := q5) (B := q6) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hB
    (by simp) (Or.inl l3) (by simp [hP0, hP1, hP2]) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sqr_step hE (D := q4) (A := q1) (by lk [hfld]) (by lk []) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l4) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q5) (A := q3) (B := q1) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l5) (by simp [hP0, hP1, hP2]) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := q5) (A := q5) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) (Or.inl l5) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := q6) (A := q2) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) (Or.inl l6) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sub_step hE (D := q6) (A := q6) (B := q3) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hB
    (by simp) (Or.inl l6) (by simp [hP0, hP1, hP2]) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q6) (A := hp) (B := q6) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l6) (by simp [hP0, hP1, hP2]) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sqr_step hE (D := hp) (A := P + 384#64) (by lk [hfld]) (by lk []) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l0) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := hp) (A := hp) (B := q4) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l0) (by simp [hP0, hP1, hP2]) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := hp) (A := hp) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) (Or.inl l0) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sub_step hE (D := q6) (A := q6) (B := hp) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hB
    (by simp) (Or.inl l6) (by simp [hP0, hP1, hP2]) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q1) (A := q1) (B := q4) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) (Or.inl l1) (by simp [hP0, hP1, hP2]) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := q1) (A := q1) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) (Or.inl l1) (by simp [hP0, hP1, hP2]) (fun m hB => ?_)
  try dsimp only
  -- copies into the output point
  refine WPs.fe_copy_step hE (D := O) (S := q5) (by lk [hout]) (by lk []) (by lk []) hB
    (by simp [hO0]) w0 (by simp) (fun e => by have := congrArg BitVec.toNat e; omega)
    (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_copy_step hE (D := O + 384#64) (S := q6) (by ev [hout]) (by lk []) (by lk []) hB
    (by simp [hO1]) w1 (by simp) (fun e => by have := congrArg BitVec.toNat e; omega)
    (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_copy_step hE (D := O + 768#64) (S := q1) (by ev [evalPanOp, hout]) (by lk [])
    (by lk []) hB (by simp [hO2]) w2 (by simp)
    (fun e => by have := congrArg BitVec.toNat e; omega) (fun m hB => ?_)
  try dsimp only
  refine WPs.seq_call_ret (fun vs g m4 ffi hret => ?_)
  obtain ⟨hg', hm, hf⟩ := release_ret hE hret (mv := hp) (pv := q7) (by lk []) hgq
  subst g m4 ffi
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal, hp_update_update]
  rw [update_same _ _ _ hg]
  refine ⟨_, m, rfl, Bufs.restrict hB0 hB (fun B hB' => ?_)⟩
  simp only [List.mem_cons] at hB'
  rcases hB' with rfl | rfl | rfl | hB'
  · exact ⟨hO2, by simp⟩
  · exact ⟨hO1, by simp⟩
  · exact ⟨hO0, by simp⟩
  · exact ⟨hB0.sub B hB', by simp [hB']⟩

end InitECandidate.Solver.GuestBound
