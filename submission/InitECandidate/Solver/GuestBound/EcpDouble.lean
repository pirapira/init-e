import InitECandidate.Solver.GuestBound.FeBufs

/-!
# `ecp_double` on `Fq12` points keeps coefficients below `p`

Twenty field operations on seven temporaries, then three copies into the
output point. Part of the canonicity chain for `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)}

theorem add_lit_toNat {P : Word} {k : Nat} (hk : k < 2 ^ 32) (h : P.toNat + k < 2 ^ 64) :
    (P + BitVec.ofNat 64 k).toNat = P.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

set_option maxRecDepth 8000 in
/-- The three coordinates of a point below the heap pointer, all canonical. -/
theorem Bufs.init3 {P pv : Word} (hpH : InHeap pv) (alP : P.toNat % 8 = 0)
    (bP : P.toNat + 1152 ≤ pv.toNat) (c0 : CanonN m P 12) (c1 : CanonN m (P + 384#64) 12)
    (c2 : CanonN m (P + 768#64) 12) :
    Bufs pv m pv [P, P + 384#64, P + 768#64] [P, P + 384#64, P + 768#64] m := by
  have hH := hpH
  unfold InHeap at hH
  have e1 : (P + 384#64).toNat = P.toNat + 384 := add_lit_toNat (k := 384) (by omega) (by omega)
  have e2 : (P + 768#64).toNat = P.toNat + 768 := add_lit_toNat (k := 768) (by omega) (by omega)
  refine ⟨hH.1, hH.2, Nat.le_refl _, ?_, ?_, fun _ h => h, ?_, fun _ _ => rfl⟩
  · intro B hB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl <;> constructor <;> omega
  · intro B hB C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB hC
    rcases hB with rfl | rfl | rfl <;> rcases hC with rfl | rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr (Or.inl (by omega)) | exact Or.inr (Or.inr (by omega))
  · intro B hB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl
    · exact c0
    · exact c1
    · exact c2

/-- One 384-byte copy into `O` from a canonical source above it. -/
theorem copy_canon {O T : Word} {m1 m2 : Word → Option (PanValue Word)}
    (hcopy : CopyInv m1 O T 384 m2) (alO : O.toNat % 8 = 0) (alT : T.toNat % 8 = 0)
    (bT : T.toNat + 384 < 2 ^ 63) (bO : O.toNat + 384 ≤ T.toNat) (cT : CanonN m1 T 12) :
    CanonN m2 O 12 := by
  obtain ⟨c, hpc, hlc⟩ := cT.poly
  exact CanonN.of_poly (PolyAt.of_copy (n := 12) hcopy alO alT (by omega) (by omega) hpc) hlc

set_option maxHeartbeats 32000000 in
theorem ecp_double12_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "ecp_double" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (P O pv : Word)
    (hfld : s.locals "fld" = some (.word 12#64)) (hpt : s.locals "pt" = some (.word P))
    (hout : s.locals "out" = some (.word O)) (hp : s.globals "heap_ptr" = some (.word pv))
    (hpH : InHeap pv) (alP : P.toNat % 8 = 0) (bP : P.toNat + 1152 ≤ pv.toNat)
    (alO : O.toNat % 8 = 0) (bO : O.toNat + 1152 ≤ pv.toNat)
    (c0 : CanonN s.memory P 12) (c1 : CanonN s.memory (P + 384#64) 12)
    (c2 : CanonN s.memory (P + 768#64) 12) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, x.toNat < pv.toNat → (x.toNat < O.toNat ∨ O.toNat + 1152 ≤ x.toNat) →
        m' x = s.memory x) ∧
      CanonN m' O 12 ∧ CanonN m' (O + 384#64) 12 ∧ CanonN m' (O + 768#64) 12 := by
  have hbody := (fun_of_index 673 hE.functions (by guest_decl_at 673) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hH := hpH
  unfold InHeap at hH
  have h384 : (384#64 : Word).toNat = 384 := by decide
  have o1 : (O + 384#64).toNat = O.toNat + 384 := add_lit_toNat (k := 384) (by omega) (by omega)
  have o2 : (O + 768#64).toNat = O.toNat + 768 := add_lit_toNat (k := 768) (by omega) (by omega)
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, x.toNat < pv.toNat → (x.toNat < O.toNat ∨ O.toNat + 1152 ≤ x.toNat) →
        m' x = s.memory x) ∧
      CanonN m' O 12 ∧ CanonN m' (O + 384#64) 12 ∧ CanonN m' (O + 768#64) 12)) r h
  refine WPs.dec (w := 384#64) (of_eval (by ev [evalPanOp, hfld])) ?_
  try dsimp only
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  try dsimp only
  obtain ⟨hg, hm, hf, hv⟩ := heap_mark_ret hE hret hp
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  refine WPs.dec (w := P) (of_eval (by lk [hpt])) ?_
  try dsimp only
  refine WPs.dec (w := P + 384#64) (of_eval (by ev [hpt])) ?_
  try dsimp only
  refine WPs.dec (w := P + 768#64) (of_eval (by ev [evalPanOp, hpt])) ?_
  try dsimp only
  have hB := Bufs.init3 hpH alP bP c0 c1 c2
  refine WPs.fe_alloc_step hE (by lk []) hp hB (fun q1 l0 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q2 l1 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q3 l2 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q4 l3 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q5 l4 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q6 l5 hB => ?_)
  try dsimp only
  refine WPs.fe_alloc_step hE (by lk []) (by lk []) hB (fun q7 l6 hB => ?_)
  try dsimp only
  have hgq : (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap
      (updatePanValueMap (updatePanValueMap (updatePanValueMap s.globals "heap_ptr" (.word q1))
      "heap_ptr" (.word q2)) "heap_ptr" (.word q3)) "heap_ptr" (.word q4)) "heap_ptr"
      (.word q5)) "heap_ptr" (.word q6)) "heap_ptr" (.word q7)) "heap_ptr" = some (.word q7) := by
    lk []
  refine WPs.fe_sqr_step hE (D := q5) (A := P) (by lk [hfld]) (by lk []) (by lk [hpt]) hgq hB
    (by simp) l5 (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := pv) (A := q5) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) (Nat.le_refl _) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q1) (A := P + 384#64) (B := P + 768#64) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) l1 (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q5) (A := P) (B := P + 384#64) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) l5 (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q2) (A := q5) (B := q1) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) l2 (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sqr_step hE (D := q5) (A := pv) (by lk [hfld]) (by lk []) (by lk [hpt]) hgq hB
    (by simp) l5 (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := q6) (A := q2) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) l6 (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sub_step hE (D := q3) (A := q5) (B := q6) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hB
    (by simp) l3 (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sqr_step hE (D := q4) (A := q1) (by lk [hfld]) (by lk []) (by lk [hpt]) hgq hB
    (by simp) l4 (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q5) (A := q3) (B := q1) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) l5 (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := q5) (A := q5) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) l5 (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := q6) (A := q2) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) l6 (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sub_step hE (D := q6) (A := q6) (B := q3) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hB
    (by simp) l6 (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q6) (A := pv) (B := q6) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) l6 (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sqr_step hE (D := pv) (A := P + 384#64) (by lk [hfld]) (by lk []) (by lk [hpt]) hgq hB
    (by simp) (Nat.le_refl _) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := pv) (A := pv) (B := q4) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) (Nat.le_refl _) (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := pv) (A := pv) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) (Nat.le_refl _) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_sub_step hE (D := q6) (A := q6) (B := pv) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hB
    (by simp) l6 (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_step hE (D := q1) (A := q1) (B := q4) (by lk [hfld]) (by lk []) (by lk [hpt]) (by lk [hpt]) hgq hB
    (by simp) l1 (by simp) (by simp) (fun m hB => ?_)
  try dsimp only
  refine WPs.fe_mul_small_step hE (D := q1) (A := q1) (by lk [hfld]) (by lk []) (by lk [hpt]) (eval_const _ _) hB
    (by simp) l1 (by simp) (fun m hB => ?_)
  try dsimp only
  -- copies into the output point
  have gT1 := hB.geo q5 (by simp)
  have gT2 := hB.geo q6 (by simp)
  have gS := hB.geo q1 (by simp)
  have hq7 := hB.hpb
  have cT1 := hB.can q5 (by simp)
  have cT2 := hB.can q6 (by simp)
  have cS := hB.can q1 (by simp)
  have hlow := hB.low
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  try dsimp only
  obtain ⟨hg, hf, hcp1⟩ := memcpy_ret hE hret (dst := O) (src := q5) (nW := 384#64)
    (by lk [hout]) (by lk []) (by lk [])
    ⟨by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega⟩
  subst g ffi
  rw [h384] at hcp1
  refine WPs.seq_call_ret (fun vs g m2 ffi hret => ?_)
  try dsimp only
  obtain ⟨hg, hf, hcp2⟩ := memcpy_ret hE hret (dst := O + 384#64) (src := q6) (nW := 384#64)
    (by ev [hout]) (by lk []) (by lk [])
    ⟨by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega⟩
  subst g ffi
  rw [h384] at hcp2
  refine WPs.seq_call_ret (fun vs g m3 ffi hret => ?_)
  try dsimp only
  obtain ⟨hg, hf, hcp3⟩ := memcpy_ret hE hret (dst := O + 768#64) (src := q1) (nW := 384#64)
    (by ev [evalPanOp, hout]) (by lk []) (by lk [])
    ⟨by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega⟩
  subst g ffi
  rw [h384] at hcp3
  refine WPs.seq_call_ret (fun vs g m4 ffi hret => ?_)
  try dsimp only
  obtain ⟨hg, hm, hf⟩ := release_ret hE hret (mv := pv) (pv := q7) (by lk []) hgq
  subst g m4 ffi
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  have hGs : updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap
      (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap s.globals
      "heap_ptr" (.word q1)) "heap_ptr" (.word q2)) "heap_ptr" (.word q3)) "heap_ptr" (.word q4))
      "heap_ptr" (.word q5)) "heap_ptr" (.word q6)) "heap_ptr" (.word q7)) "heap_ptr" (.word pv) =
      s.globals := by
    funext y
    simp only [update_lookup]
    by_cases hy : y = "heap_ptr"
    · subst hy
      simp [hp]
    · simp [hy]
  rw [hGs]
  -- frames of the three copies
  have f1 : ∀ x : Word, (x.toNat < O.toNat ∨ O.toNat + 384 ≤ x.toNat) → m1 x = m x :=
    fun x hx => hcp1.cells x (by omega)
  have f2 : ∀ x : Word, (x.toNat < O.toNat + 384 ∨ O.toNat + 768 ≤ x.toNat) → m2 x = m1 x :=
    fun x hx => hcp2.cells x (by rw [o1]; omega)
  have f3 : ∀ x : Word, (x.toNat < O.toNat + 768 ∨ O.toNat + 1152 ≤ x.toNat) → m3 x = m2 x :=
    fun x hx => hcp3.cells x (by rw [o2]; omega)
  have cT2' : CanonN m1 q6 12 := cT2.frame (by omega) (fun x h1 h2 => f1 x (by omega))
  have cS' : CanonN m2 q1 12 :=
    (cS.frame (m' := m1) (by omega) (fun x h1 h2 => f1 x (by omega))).frame (by omega)
      (fun x h1 h2 => f2 x (by omega))
  have k1 : CanonN m1 O 12 := copy_canon hcp1 alO gT1.1 (by omega) (by omega) cT1
  have k2 : CanonN m2 (O + 384#64) 12 :=
    copy_canon hcp2 (by rw [o1]; omega) gT2.1 (by omega) (by rw [o1]; omega) cT2'
  have k3 : CanonN m3 (O + 768#64) 12 :=
    copy_canon hcp3 (by rw [o2]; omega) gS.1 (by omega) (by rw [o2]; omega) cS'
  refine ⟨_, m3, rfl, ?_, ?_, ?_, k3⟩
  · intro x hx hxO
    rw [f3 x (by omega), f2 x (by omega), f1 x (by omega)]
    exact hlow x hx
  · exact (k1.frame (m' := m2) (by omega) (fun x h1 h2 => f2 x (by omega))).frame (by omega)
      (fun x h1 h2 => f3 x (by omega))
  · exact k2.frame (by rw [o1]; omega) (fun x h1 h2 => f3 x (by rw [o1] at h1 h2; omega))

end InitECandidate.Solver.GuestBound
