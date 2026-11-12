import InitECandidate.Solver.GuestBound.EcpAddK

/-!
# `ecp_mul` for any field size keeps coefficients below `p`

Double-and-add over `ecp_add` and `ecp_double`; the loop invariant is one
`BufsK` with the accumulator and the base point canonical (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word} {K : Nat}

theorem u256_bit_length_quiet :
    keepFn quietLeaf Guest.Software.guestAst 3 "u256_bit_length" = true := by
  decide +kernel

theorem u256_bit_quiet : keepFn quietLeaf Guest.Software.guestAst 3 "u256_bit" = true := by
  decide +kernel

/-- A fresh point at the old heap pointer joins `All`. -/
theorem BufsK.alloc3 {F pv0 hp hp' : Word} {All Cn : List Word} (hF : F.toNat = K)
    (hK : K ≤ 12) (h : BufsK K pv0 m0 Wr hp All Cn m)
    (hle : hp.toNat + 96 * K ≤ hp'.toNat) (hb : hp'.toNat ≤ 2952790016)
    (ha' : hp'.toNat % 8 = 0) :
    BufsK K pv0 m0 Wr hp' ((hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: All) Cn m := by
  have hpb := h.hpb
  have hpa := h.hpa
  have hez := esz_toNat hF hK
  have h2ez := esz2_toNat hF hK
  have e1 : (hp + F * 32#64).toNat = hp.toNat + 32 * K := by rw [add_toNat_small (by omega), hez]
  have e2 : (hp + 2#64 * (F * 32#64)).toNat = hp.toNat + 64 * K := by rw [add_toNat_small (by omega), h2ez]
  have h1 := h.alloc (hp' := hp + F * 32#64) (by omega) (by omega) (by omega)
  have h2 := h1.alloc (hp' := hp + 2#64 * (F * 32#64)) (by omega) (by omega) (by omega)
  exact h2.alloc (by omega) hb ha'

/-- `var x = alloc(3 * esz); body`: a point joins `All`. -/
theorem WPs.pt_alloc_stepK (hE : GuestEnv E) {x : VarName} {e : Exp Word} {body : Prog Word}
    {F hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K) (hK : K ≤ 12)
    (he : E.eval s e = some (.word (3#64 * (F * 32#64))))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (h : ∀ hp' : Word, pv0.toNat ≤ hp.toNat → hp.toNat + 96 * K ≤ hp'.toNat →
      (hp + F * 32#64).toNat = hp.toNat + 32 * K → (hp + 2#64 * (F * 32#64)).toNat = hp.toNat + 64 * K →
      BufsK K pv0 m0 Wr hp' ((hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: All) Cn s.memory →
      WPs E ⟨updatePanValueMap s.locals x (.word hp),
        updatePanValueMap s.globals "heap_ptr" (.word hp'), s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "alloc" [e] body) Q := by
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hv, hm, hf, qv, hg', h1, h2⟩ := alloc_ret hE hret he hg ⟨hB.hpb, hB.hpa⟩
  simp only [List.cons.injEq, and_true] at hv
  subst v m ffi g
  rw [esz3_toNat hF hK] at h1
  have hpb := hB.hpb
  have hez := esz_toNat hF hK
  have h2ez := esz2_toNat hF hK
  exact h qv hB.ple h1 (by rw [add_toNat_small (by omega), hez])
    (by rw [add_toNat_small (by omega), h2ez]) (hB.alloc3 hF hK h1 h2.1 h2.2)

theorem ecpaddK_ret (hE : GuestEnv E) {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} {e1 e2 e3 e4 : Exp Word} {F O P1 P2 hp pv0 : Word}
    {All Cn : List Word} (hF : F.toNat = K) (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (h : CalleeRet E s "ecp_add" [e1, e2, e3, e4] vs g m ffi)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word O))
    (h3 : E.eval s e3 = some (.word P1)) (h4 : E.eval s e4 = some (.word P2))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (m1a : P1 ∈ Cn) (m1b : P1 + F * 32#64 ∈ Cn) (m1c : P1 + 2#64 * (F * 32#64) ∈ Cn)
    (m2a : P2 ∈ Cn) (m2b : P2 + F * 32#64 ∈ Cn) (m2c : P2 + 2#64 * (F * 32#64) ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + F * 32#64 ∈ All) (hO2 : O + 2#64 * (F * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + F * 32#64).toNat ∨ O + F * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (F * 32#64)).toNat ∨ O + 2#64 * (F * 32#64) ∈ Wr)
    (rel1 : O = P1 ∨ O.toNat + 96 * K ≤ P1.toNat ∨ P1.toNat + 96 * K ≤ O.toNat)
    (rel2 : O = P2 ∨ O.toNat + 96 * K ≤ P2.toNat ∨ P2.toNat + 96 * K ≤ O.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧ BufsK K pv0 m0 Wr hp All ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn) m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 674 hE.functions (by guest_decl_at 674) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases ecp_addK_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    F O P1 P2 hp pv0 m0 Wr All Cn hF hK
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hg hB0
    m1a m1b m1c m2a m2b m2c hO0 hO1 hO2 w0 w1 w2 rel1 rel2 hrun with hst | ⟨l', m', heq, hB⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hB⟩

theorem WPs.ecp_add_stepK (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {rest : Prog Word}
    {F O P1 P2 hp pv0 : Word} {All Cn : List Word} (hF : F.toNat = K)
    (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (h1 : E.eval s e1 = some (.word F)) (h2 : E.eval s e2 = some (.word O))
    (h3 : E.eval s e3 = some (.word P1)) (h4 : E.eval s e4 = some (.word P2))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (m1a : P1 ∈ Cn) (m1b : P1 + F * 32#64 ∈ Cn) (m1c : P1 + 2#64 * (F * 32#64) ∈ Cn)
    (m2a : P2 ∈ Cn) (m2b : P2 + F * 32#64 ∈ Cn) (m2c : P2 + 2#64 * (F * 32#64) ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + F * 32#64 ∈ All) (hO2 : O + 2#64 * (F * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + F * 32#64).toNat ∨ O + F * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (F * 32#64)).toNat ∨ O + 2#64 * (F * 32#64) ∈ Wr)
    (rel1 : O = P1 ∨ O.toNat + 96 * K ≤ P1.toNat ∨ P1.toNat + 96 * K ≤ O.toNat)
    (rel2 : O = P2 ∨ O.toNat + 96 * K ≤ P2.toNat ∨ P2.toNat + 96 * K ≤ O.toNat)
    (h : ∀ m', BufsK K pv0 m0 Wr hp All ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "ecp_add" [e1, e2, e3, e4]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hB⟩ := ecpaddK_ret hE hF hK hret h1 h2 h3 h4 hg hB0 m1a m1b m1c m2a m2b m2c
    hO0 hO1 hO2 w0 w1 w2 rel1 rel2
  subst g ffi
  exact h m1 hB

set_option maxHeartbeats 64000000 in
theorem ecp_mulK_bufs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "ecp_mul" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (F O P hp pv0 : Word) (m0 : Word → Option (PanValue Word))
    (Wr All Cn : List Word) (hF : F.toNat = K) (hK : K = 1 ∨ K = 2 ∨ K = 12)
    (hfld : s.locals "fld" = some (.word F)) (hout : s.locals "out" = some (.word O))
    (hpt : s.locals "pt" = some (.word P)) (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : BufsK K pv0 m0 Wr hp All Cn s.memory)
    (hP0 : P ∈ Cn) (hP1 : P + F * 32#64 ∈ Cn) (hP2 : P + 2#64 * (F * 32#64) ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + F * 32#64 ∈ All) (hO2 : O + 2#64 * (F * 32#64) ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + F * 32#64).toNat ∨ O + F * 32#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 2#64 * (F * 32#64)).toNat ∨ O + 2#64 * (F * 32#64) ∈ Wr) (h : Runs E s body r) :
    Stopped r ∨ BufsRetK s K pv0 m0 Wr hp All ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn) r := by
  have hbody := (fun_of_index 675 hE.functions (by guest_decl_at 675) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hK12 : K ≤ 12 := by omega
  have hK1 : 1 ≤ K := by omega
  have hez := esz_toNat hF hK12
  have h2ez := esz2_toNat hF hK12
  have hpb0 := hB0.hpb
  have gP0 := hB0.geo P (hB0.sub P hP0)
  have gP2 := hB0.geo _ (hB0.sub _ hP2)
  have gO0 := hB0.geo O hO0
  have gO2 := hB0.geo _ hO2
  have p2 : (P + 2#64 * (F * 32#64)).toNat = P.toNat + 64 * K := by rw [add_toNat_small (by omega), h2ez]
  have o2 : (O + 2#64 * (F * 32#64)).toNat = O.toNat + 64 * K := by rw [add_toNat_small (by omega), h2ez]
  have hq1 := keepFn_sound (quietKeeper E) hE.functions 3 "u256_bit_length" u256_bit_length_quiet
  have hq2 := keepFn_sound (quietKeeper E) hE.functions 3 "u256_bit" u256_bit_quiet
  refine (?_ : WPs E s _ (BufsRetK s K pv0 m0 Wr hp All ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn))) r h
  refine WPs.dec (w := 3#64 * (F * 32#64)) (of_eval (by ev [evalPanOp, hfld])) ?_
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg', hm, hf, hv⟩ := heap_mark_ret hE hret hg
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  try dsimp only
  have hB := hB0
  refine WPs.pt_alloc_stepK hE hF hK12 (by lk []) hg hB (fun q1 l0 a0 t0a t0b hB => ?_)
  try dsimp only
  refine WPs.pt_alloc_stepK hE hF hK12 (by lk []) (by lk []) hB (fun q2 l1 a1 t1a t1b hB => ?_)
  try dsimp only
  generalize hL : updatePanValueMap _ "base" (PanValue.word q1) = L
  generalize hG : updatePanValueMap _ "heap_ptr" (PanValue.word q2) = G
  have hGq : G "heap_ptr" = some (.word q2) := by rw [← hG]; lk []
  have L_fld : L "fld" = some (.word F) := by rw [← hL]; lk [hfld]
  have L_out : L "out" = some (.word O) := by rw [← hL]; lk [hout]
  have L_pt : L "pt" = some (.word P) := by rw [← hL]; lk [hpt]
  have L_mark : L "mark" = some (.word hp) := by rw [← hL]; lk []
  have L_acc : L "acc" = some (.word hp) := by rw [← hL]; lk []
  have L_base : L "base" = some (.word q1) := by rw [← hL]; lk []
  have L_psz : L "psz" = some (.word (3#64 * (F * 32#64))) := by rw [← hL]; lk []
  refine WPs.ecp_set_inf_stepK hE hF hK (O := hp) (by lk [L_fld]) (by lk [L_acc]) hB (by simp)
    (by simp) (by simp) (Or.inl l0) (Or.inl (by omega)) (Or.inl (by omega)) (fun m hB => ?_)
  try dsimp only
  refine WPs.pt_copy_stepK hE hF hK (O := q1) (P := P) (by lk [L_base]) (by lk [L_pt])
    (by lk [L_psz]) hB (by simp [hP0]) (by simp [hP1]) (by simp [hP2]) (by simp) (by simp)
    (by simp) (Or.inl l1) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inr (Or.inr (by omega)))
    (fun m hB => ?_)
  try dsimp only
  refine WPs.decCall_word (fun lw g m' ffi hret => ?_)
  obtain ⟨hg', hm, hf⟩ := hret.quiet hq1
  subst g m' ffi
  try dsimp only
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  generalize hL2 : updatePanValueMap (updatePanValueMap L "len" (PanValue.word lw)) "i"
    (PanValue.word 0#64) = L2
  have L2_fld : L2 "fld" = some (.word F) := by rw [← hL2]; lk [L_fld]
  have L2_out : L2 "out" = some (.word O) := by rw [← hL2]; lk [L_out]
  have L2_mark : L2 "mark" = some (.word hp) := by rw [← hL2]; lk [L_mark]
  have L2_acc : L2 "acc" = some (.word hp) := by rw [← hL2]; lk [L_acc]
  have L2_base : L2 "base" = some (.word q1) := by rw [← hL2]; lk [L_base]
  have L2_psz : L2 "psz" = some (.word (3#64 * (F * 32#64))) := by rw [← hL2]; lk [L_psz]
  refine WPs.seqG
    (fun st => st.globals = G ∧ st.ffi = s.ffi ∧ (∀ x, x ≠ "i" → st.locals x = L2 x) ∧
      (∃ iw : Word, st.locals "i" = some (.word iw)) ∧
      BufsK K pv0 m0 Wr q2 ((q1 + 2#64 * (F * 32#64)) :: (q1 + F * 32#64) :: q1 :: (hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: All) ((q1 + 2#64 * (F * 32#64)) :: (q1 + F * 32#64) :: q1 :: (hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: Cn) st.memory)
    (WPs.loopG
      (I := fun st => st.globals = G ∧ st.ffi = s.ffi ∧ (∀ x, x ≠ "i" → st.locals x = L2 x) ∧
        (∃ iw : Word, st.locals "i" = some (.word iw)) ∧
        BufsK K pv0 m0 Wr q2 ((q1 + 2#64 * (F * 32#64)) :: (q1 + F * 32#64) :: q1 :: (hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: All) ((q1 + 2#64 * (F * 32#64)) :: (q1 + F * 32#64) :: q1 :: (hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: Cn) st.memory)
      ⟨rfl, rfl, fun _ _ => rfl, ⟨0#64, by rw [← hL2]; lk []⟩, hB⟩ ?_
      (fun a k hI _ => hI)) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg', hf, hloc, ⟨iw, hi⟩, hB⟩ -
    simp only at hg' hf hloc hi hB
    subst ga fa
    obtain ⟨m, hm⟩ : ∃ m, m = ma := ⟨_, rfl⟩
    rw [← hm] at hB ⊢
    have la_fld := (hloc _ (by decide)).trans L2_fld
    have la_acc := (hloc _ (by decide)).trans L2_acc
    have la_base := (hloc _ (by decide)).trans L2_base
    refine WPs.decCall_ret (fun v g m' ffi hret => ?_)
    obtain ⟨hg', hm', hf⟩ := hret.quiet hq2
    subst g m' ffi
    try dsimp only
    generalize hLb : updatePanValueMap la "bit" v = Lb
    have Lb_fld : Lb "fld" = some (.word F) := by rw [← hLb]; lk [la_fld]
    have Lb_acc : Lb "acc" = some (.word hp) := by rw [← hLb]; lk [la_acc]
    have Lb_base : Lb "base" = some (.word q1) := by rw [← hLb]; lk [la_base]
    have Lb_i : Lb "i" = some (.word iw) := by rw [← hLb]; lk [hi]
    refine WPs.seq (fun st => ∃ m, st = ⟨Lb, G, m, s.ffi⟩ ∧
        BufsK K pv0 m0 Wr q2 ((q1 + 2#64 * (F * 32#64)) :: (q1 + F * 32#64) :: q1 :: (hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: All) ((q1 + 2#64 * (F * 32#64)) :: (q1 + F * 32#64) :: q1 :: (hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: Cn) m)
      (WPs.ite_both (fun w1 _ => ?_)) ?_
    · split
      · exact WPs.skip ⟨_, _, _, _, rfl, m, rfl, hB⟩
      · refine WPs.of_seq_skip ?_
        refine WPs.ecp_add_stepK hE hF hK (O := hp) (P1 := hp) (P2 := q1) (by lk [Lb_fld])
          (by lk [Lb_acc]) (by lk [Lb_acc]) (by lk [Lb_base]) hGq hB (by simp) (by simp)
          (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (Or.inl l0)
          (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl rfl) (Or.inr (Or.inl (by omega)))
          (fun m hB => ?_)
        exact WPs.skip ⟨_, _, _, _, rfl, m, rfl, hB.mono (fun B hB' => by
          simp only [List.mem_cons] at hB'
          repeat (rcases hB' with h | hB'; (subst h; simp); skip)
          simp [hB'])⟩
    rintro _ ⟨m, rfl, hB⟩
    refine WPs.seq_assign (old := iw) (w := iw + 1#64) (by lk [Lb_i]) (of_eval (by ev [Lb_i])) ?_
    try dsimp only
    have hpost : ∀ m2, BufsK K pv0 m0 Wr q2 ((q1 + 2#64 * (F * 32#64)) :: (q1 + F * 32#64) :: q1 :: (hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: All) ((q1 + 2#64 * (F * 32#64)) :: (q1 + F * 32#64) :: q1 :: (hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: Cn) m2 →
        (fun r' => match restorePanValueFfiLocal "bit" (la "bit") r' with
          | .normal l g m f => (fun st : St σ => st.globals = G ∧ st.ffi = s.ffi ∧
              (∀ x, x ≠ "i" → st.locals x = L2 x) ∧
              (∃ iw : Word, st.locals "i" = some (.word iw)) ∧
              BufsK K pv0 m0 Wr q2 ((q1 + 2#64 * (F * 32#64)) :: (q1 + F * 32#64) :: q1 :: (hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: All) ((q1 + 2#64 * (F * 32#64)) :: (q1 + F * 32#64) :: q1 :: (hp + 2#64 * (F * 32#64)) :: (hp + F * 32#64) :: hp :: Cn) st.memory) ⟨l, g, m, f⟩
          | .continued _ _ _ _ | .broke _ _ _ _ => False
          | r => BufsRetK s K pv0 m0 Wr hp All ((O + 2#64 * (F * 32#64)) :: (O + F * 32#64) :: O :: Cn) r)
          (.normal (updatePanValueMap Lb "i" (.word (iw + 1#64))) G m2 s.ffi) := by
      intro m2 hB2
      simp only [restorePanValueFfiLocal]
      refine ⟨?_, ?_, fun x hx => ?_, ⟨iw + 1#64, ?_⟩, hB2⟩
      · first | rfl | trivial
      · first | rfl | trivial
      · refine Eq.trans ?_ (hloc x hx)
        rw [← hLb]
        by_cases hb : x = "bit"
        · subst hb
          simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
        · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hb, hx]
      · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
    refine WPs.ite_both (fun w2 _ => ?_)
    split
    · exact WPs.skip (hpost m hB)
    · refine WPs.of_seq_skip ?_
      refine WPs.ecp_double_stepK hE hF hK (O := q1) (P := q1) (by lk [Lb_fld]) (by lk [Lb_base])
        (by lk [Lb_base]) hGq hB (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (Or.inl l1) (Or.inl (by omega)) (Or.inl (by omega)) (fun m hB => ?_)
      exact WPs.skip (hpost m (hB.mono (fun B hB' => by
        simp only [List.mem_cons] at hB'
        repeat (rcases hB' with h | hB'; (subst h; simp); skip)
        simp [hB'])))
  rintro ⟨la, ga, ma, fa⟩ ⟨hg', hf, hloc, -, hB⟩
  simp only at hg' hf hloc hB
  subst ga fa
  obtain ⟨m, hm⟩ : ∃ m, m = ma := ⟨_, rfl⟩
  rw [← hm] at hB ⊢
  refine WPs.pt_copy_stepK hE hF hK (O := O) (P := hp)
    (by lk [(hloc _ (by decide)).trans L2_out]) (by lk [(hloc _ (by decide)).trans L2_acc])
    (by lk [(hloc _ (by decide)).trans L2_psz]) hB (by simp) (by simp) (by simp)
    (by simp [hO0]) (by simp [hO1]) (by simp [hO2]) w0 w1 w2 (Or.inr (Or.inl (by omega)))
    (fun m hB => ?_)
  try dsimp only
  refine WPs.seq_call_ret (fun vs g m4 ffi hret => ?_)
  obtain ⟨hg', hm', hf⟩ := release_ret hE hret (mv := hp) (pv := q2)
    (by lk [(hloc _ (by decide)).trans L2_mark]) hGq
  subst g m4 ffi
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal, ← hG, hp_update_update]
  rw [update_same _ _ _ hg]
  refine ⟨_, m, rfl, BufsK.restrict hB0 hB (fun B hB' => ?_)⟩
  simp only [List.mem_cons] at hB'
  rcases hB' with rfl | rfl | rfl | hB'
  · exact ⟨hO2, by simp⟩
  · exact ⟨hO1, by simp⟩
  · exact ⟨hO0, by simp⟩
  · exact ⟨hB0.sub B hB', by simp [hB']⟩

end InitECandidate.Solver.GuestBound
