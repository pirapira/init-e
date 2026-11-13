import InitECandidate.Solver.GuestBound.TrieCalls

/-!
# `_create_branch_from_two_leaves` against the world invariant

A fresh branch receives two entries; each is the value slot (`+160`, `+168`)
when its remaining key is empty, and otherwise a new leaf stored in the child
slot selected by the first nibble of the key. The key must lie in an immutable
block, which is where the nibble bound for the slot index comes from
(`WorldTJ.im_nibs`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A statement in last position. -/
theorem WPs.last {p : Prog Word} (h : WPs E s (.seq p .skip) Q) : WPs E s p Q := by
  intro r hr
  refine h r (runs_seq.mpr ⟨r, hr, ?_⟩)
  cases r <;> first | exact runs_skip.mpr rfl | rfl

set_option maxHeartbeats 2000000 in
/-- Entry 1 of `_create_branch_from_two_leaves`. -/
theorem attach1 (hE : GuestEnv E) {br k l v vl : Word} {R : Reg} {ℓc : Nat}
    (hbr : s.locals "br" = some (.word br)) (hk : s.locals "k1" = some (.word k))
    (hl : s.locals "l1" = some (.word l)) (hv : s.locals "v1" = some (.word v))
    (hvl : s.locals "vl1" = some (.word vl)) (hW : WorldTJ R s.globals s.memory)
    (hvr : VRange R v vl)
    (hK : R.Kd br 3#64) (hcv : R.Cv br ℓc)
    (hseg : l ≠ 0#64 → ∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ k.toNat ∧
      k.toNat + l.toNat ≤ hi.toNat)
    (hQ : ∀ l' g' m' R', R.Le R' → WorldTJ R' g' m' → (∀ x, x ≠ "lf1" → l' x = s.locals x) →
      (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) →
      (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr) → Q (.normal l' g' m' s.ffi)) :
    WPs E s (.ite (.cmp .equal (.var .local "l1") (.const 0#64))
      (.seq (.store (.op .add [.var .local "br", .const 160#64]) (.var .local "v1"))
        (.store (.op .add [.var .local "br", .const 168#64]) (.var .local "vl1")))
      (.decCall "lf1" .one "node_new_leaf"
        [.op .add [.var .local "k1", .const 1#64], .op .sub [.var .local "l1", .const 1#64],
          .var .local "v1", .var .local "vl1"]
        (.store (.op .add [.var .local "br", .const 32#64,
          .panOp .mul [.loadByte (.var .local "k1"), .const 8#64]]) (.var .local "lf1")))) Q := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  rw [evalF_local, hl] at hx
  rw [eval_const] at hy
  simp only [Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · rename_i h0
    have hl0 : l ≠ 0#64 := by
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    obtain ⟨lo, hi, hI, h1, h2⟩ := hseg hl0
    have hlpos : 1 ≤ l.toNat := by
      by_contra hc
      exact hl0 (BitVec.eq_of_toNat_eq (by simp; omega))
    have hhi := hi.isLt
    have ek1 : (k + 1#64).toNat = k.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
      omega
    have el1 : (l - 1#64).toNat = l.toNat - 1 := by
      rw [BitVec.toNat_sub, show (1#64 : Word).toNat = 1 by decide]
      omega
    refine WPs.decCall_ret (fun v' g1 m1 f1 hret => ?_)
    obtain ⟨a, rfl, rfl, hW1, hg1, hm1⟩ := node_new_leaf_ret hE hret (nib := k + 1#64)
      (nlen := l - 1#64) (vptr := v) (vlen := vl) (of_eval (eval_addc hE 1#64 hk))
      (of_eval (by ev [hl])) (of_eval (by lk [hv])) (of_eval (by lk [hvl])) hW
      (Or.inr ⟨lo, hi, hI, by omega, by omega,
        hW.im_nibs hI (p := k + 1#64) (c := (l - 1#64).toNat) (by omega) (by omega)⟩) hvr ℓc
    have hK1 : (R.addNd a 1#64 ℓc ℓc).Kd br 3#64 := Or.inl hK
    obtain ⟨hNdb, hRdb, hlob, htopb, -⟩ := hW1.kd hK1
    have hsz : nodeSize 3#64 = 176 := by decide
    obtain ⟨b0, hb0, h16⟩ := hW1.im_nibs (Rg := R.addNd a 1#64 ℓc ℓc) hI (p := k) (c := 1) h1
      (by omega) 0 (by omega)
    have hoff : off k 0 = k := by simp [off]
    rw [hoff] at hb0
    have eS : (br + BitVec.ofNat 64 (32 + 8 * b0.toNat)).toNat = br.toNat + (32 + 8 * b0.toNat) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    refine WPs.last (WPs.seq_store_inv hE (addr := br + BitVec.ofNat 64 (32 + 8 * b0.toNat))
      (w := a) (eval_slot_addr hE (by lk [hbr]) (of_eval (by lk [hk])) hb0 h16) (of_eval (by lk [])) ?_)
    refine WPs.skip ?_
    simp only [restorePanValueFfiLocal]
    refine hQ _ _ _ (R.addNd a 1#64 ℓc ℓc) (Reg.Le.addNd R a 1#64 ℓc ℓc)
      (hW1.node_child hNdb hRdb (Or.inr ⟨rfl, b0.toNat, h16, rfl⟩)
        (Or.inr ((hW1.kd (Reg.addNd_kd R a 1#64 ℓc ℓc)).1))
        (fun ℓc' hcv' _ => by
          have := hW1.cv_unique hcv' (Or.inl hcv)
          subst this
          exact Reg.addNd_lv R a 1#64 _ _))
      (fun x hx => by simp [restorePanValueLocal, update_lookup, hx]) hg1 (fun addr ha => ?_)
    rw [setCell_ne _ (NE (by unfold HBASE at ha hlob; omega))]
    exact hm1 addr ha
  · rename_i h0
    obtain ⟨hNdb, hRdb, hlob, htopb, -⟩ := hW.kd hK
    have hsz : nodeSize 3#64 = 176 := by decide
    obtain ⟨hin0, hs0⟩ := branch_val_cell (a := br) (c := 160) (Or.inl rfl) (by omega)
    obtain ⟨hin8, hs8⟩ := branch_val_cell (a := br) (c := 168) (Or.inr rfl) (by omega)
    have W2 := hW.node_value (vp := v) (vl := vl) hNdb hRdb (Or.inr ⟨rfl, rfl, rfl⟩) hvr
    refine WPs.seq_store hE (addr := br + 160#64) (w := v) (eval_addc hE 160#64 hbr)
      (of_eval (by lk [hv])) ?_
    refine WPs.store hE (addr := br + 168#64) (w := vl) (eval_addc hE 168#64 (by lk [hbr]))
      (of_eval (by lk [hvl])) ?_
    refine hQ _ _ _ R (Reg.Le.refl R) W2 (fun _ _ => rfl) (fun _ _ => rfl) (fun addr ha => ?_)
    show setCell (setCell s.memory (br + 160#64) v) (br + 168#64) vl addr = _
    rw [setCell_ne _ (NE (by unfold HBASE at ha hlob; omega)),
      setCell_ne _ (NE (by unfold HBASE at ha hlob; omega))]

set_option maxHeartbeats 2000000 in
/-- Entry 2 of `_create_branch_from_two_leaves`. -/
theorem attach2 (hE : GuestEnv E) {br k l v vl : Word} {R : Reg} {ℓc : Nat}
    (hbr : s.locals "br" = some (.word br)) (hk : s.locals "k2" = some (.word k))
    (hl : s.locals "l2" = some (.word l)) (hv : s.locals "v2" = some (.word v))
    (hvl : s.locals "vl2" = some (.word vl)) (hW : WorldTJ R s.globals s.memory)
    (hvr : VRange R v vl)
    (hK : R.Kd br 3#64) (hcv : R.Cv br ℓc)
    (hseg : l ≠ 0#64 → ∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ k.toNat ∧
      k.toNat + l.toNat ≤ hi.toNat)
    (hQ : ∀ l' g' m' R', R.Le R' → WorldTJ R' g' m' → (∀ x, x ≠ "lf2" → l' x = s.locals x) →
      (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) →
      (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr) → Q (.normal l' g' m' s.ffi)) :
    WPs E s (.ite (.cmp .equal (.var .local "l2") (.const 0#64))
      (.seq (.store (.op .add [.var .local "br", .const 160#64]) (.var .local "v2"))
        (.store (.op .add [.var .local "br", .const 168#64]) (.var .local "vl2")))
      (.decCall "lf2" .one "node_new_leaf"
        [.op .add [.var .local "k2", .const 1#64], .op .sub [.var .local "l2", .const 1#64],
          .var .local "v2", .var .local "vl2"]
        (.store (.op .add [.var .local "br", .const 32#64,
          .panOp .mul [.loadByte (.var .local "k2"), .const 8#64]]) (.var .local "lf2")))) Q := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  rw [evalF_local, hl] at hx
  rw [eval_const] at hy
  simp only [Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · rename_i h0
    have hl0 : l ≠ 0#64 := by
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    obtain ⟨lo, hi, hI, h1, h2⟩ := hseg hl0
    have hlpos : 1 ≤ l.toNat := by
      by_contra hc
      exact hl0 (BitVec.eq_of_toNat_eq (by simp; omega))
    have hhi := hi.isLt
    have ek1 : (k + 1#64).toNat = k.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
      omega
    have el1 : (l - 1#64).toNat = l.toNat - 1 := by
      rw [BitVec.toNat_sub, show (1#64 : Word).toNat = 1 by decide]
      omega
    refine WPs.decCall_ret (fun v' g1 m1 f1 hret => ?_)
    obtain ⟨a, rfl, rfl, hW1, hg1, hm1⟩ := node_new_leaf_ret hE hret (nib := k + 1#64)
      (nlen := l - 1#64) (vptr := v) (vlen := vl) (of_eval (eval_addc hE 1#64 hk))
      (of_eval (by ev [hl])) (of_eval (by lk [hv])) (of_eval (by lk [hvl])) hW
      (Or.inr ⟨lo, hi, hI, by omega, by omega,
        hW.im_nibs hI (p := k + 1#64) (c := (l - 1#64).toNat) (by omega) (by omega)⟩) hvr ℓc
    have hK1 : (R.addNd a 1#64 ℓc ℓc).Kd br 3#64 := Or.inl hK
    obtain ⟨hNdb, hRdb, hlob, htopb, -⟩ := hW1.kd hK1
    have hsz : nodeSize 3#64 = 176 := by decide
    obtain ⟨b0, hb0, h16⟩ := hW1.im_nibs (Rg := R.addNd a 1#64 ℓc ℓc) hI (p := k) (c := 1) h1
      (by omega) 0 (by omega)
    have hoff : off k 0 = k := by simp [off]
    rw [hoff] at hb0
    have eS : (br + BitVec.ofNat 64 (32 + 8 * b0.toNat)).toNat = br.toNat + (32 + 8 * b0.toNat) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    refine WPs.last (WPs.seq_store_inv hE (addr := br + BitVec.ofNat 64 (32 + 8 * b0.toNat))
      (w := a) (eval_slot_addr hE (by lk [hbr]) (of_eval (by lk [hk])) hb0 h16) (of_eval (by lk [])) ?_)
    refine WPs.skip ?_
    simp only [restorePanValueFfiLocal]
    refine hQ _ _ _ (R.addNd a 1#64 ℓc ℓc) (Reg.Le.addNd R a 1#64 ℓc ℓc)
      (hW1.node_child hNdb hRdb (Or.inr ⟨rfl, b0.toNat, h16, rfl⟩)
        (Or.inr ((hW1.kd (Reg.addNd_kd R a 1#64 ℓc ℓc)).1))
        (fun ℓc' hcv' _ => by
          have := hW1.cv_unique hcv' (Or.inl hcv)
          subst this
          exact Reg.addNd_lv R a 1#64 _ _))
      (fun x hx => by simp [restorePanValueLocal, update_lookup, hx]) hg1 (fun addr ha => ?_)
    rw [setCell_ne _ (NE (by unfold HBASE at ha hlob; omega))]
    exact hm1 addr ha
  · rename_i h0
    obtain ⟨hNdb, hRdb, hlob, htopb, -⟩ := hW.kd hK
    have hsz : nodeSize 3#64 = 176 := by decide
    obtain ⟨hin0, hs0⟩ := branch_val_cell (a := br) (c := 160) (Or.inl rfl) (by omega)
    obtain ⟨hin8, hs8⟩ := branch_val_cell (a := br) (c := 168) (Or.inr rfl) (by omega)
    have W2 := hW.node_value (vp := v) (vl := vl) hNdb hRdb (Or.inr ⟨rfl, rfl, rfl⟩) hvr
    refine WPs.seq_store hE (addr := br + 160#64) (w := v) (eval_addc hE 160#64 hbr)
      (of_eval (by lk [hv])) ?_
    refine WPs.store hE (addr := br + 168#64) (w := vl) (eval_addc hE 168#64 (by lk [hbr]))
      (of_eval (by lk [hvl])) ?_
    refine hQ _ _ _ R (Reg.Le.refl R) W2 (fun _ _ => rfl) (fun _ _ => rfl) (fun addr ha => ?_)
    show setCell (setCell s.memory (br + 160#64) v) (br + 168#64) vl addr = _
    rw [setCell_ne _ (NE (by unfold HBASE at ha hlob; omega)),
      setCell_ne _ (NE (by unfold HBASE at ha hlob; omega))]

set_option maxHeartbeats 4000000 in
/-- `_create_branch_from_two_leaves`: a new branch with the two entries; the
registry grows by the branch and up to two leaves. -/
theorem create_branch_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_create_branch_from_two_leaves" E.functions =
      some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (k1 l1 v1 vl1 k2 l2 v2 vl2 : Word)
    (hk1 : s.locals "k1" = some (.word k1)) (hl1 : s.locals "l1" = some (.word l1))
    (hv1 : s.locals "v1" = some (.word v1)) (hvl1 : s.locals "vl1" = some (.word vl1))
    (hk2 : s.locals "k2" = some (.word k2)) (hl2 : s.locals "l2" = some (.word l2))
    (hv2 : s.locals "v2" = some (.word v2)) (hvl2 : s.locals "vl2" = some (.word vl2))
    (hW : WorldTJ Rg s.globals s.memory)
    (hseg1 : l1 ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ k1.toNat ∧
      k1.toNat + l1.toNat ≤ hi.toNat)
    (hseg2 : l2 ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ k2.toNat ∧
      k2.toNat + l2.toNat ≤ hi.toNat)
    (hvr1 : VRange Rg v1 vl1) (hvr2 : VRange Rg v2 vl2)
    (ℓ : Nat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' a R', r = .returned l g' m' s.ffi [.word a] ∧ Rg.Le R' ∧
      R'.Kd a 3#64 ∧ R'.Lv a ℓ ∧ WorldTJ R' g' m' ∧
      (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 272 hE.functions (by guest_decl_at 272) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' a R', r = .returned l g' m' s.ffi [.word a] ∧
    Rg.Le R' ∧ R'.Kd a 3#64 ∧ R'.Lv a ℓ ∧ WorldTJ R' g' m' ∧
    (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  refine WPs.decCall_ret (fun v g1 m1 f1 hret => ?_)
  obtain ⟨br, rfl, rfl, hW1, hg1, hm1⟩ := node_new_branch_ret hE hret hW ℓ
  have hle1 := Reg.Le.addNd Rg br 3#64 ℓ (ℓ + 1)
  refine WPs.seqG (fun a => ∃ R', (Rg.addNd br 3#64 ℓ (ℓ + 1)).Le R' ∧ WorldTJ R' a.globals a.memory ∧
      a.ffi = s.ffi ∧
      (∀ x, x ≠ "lf1" → a.locals x = updatePanValueMap s.locals "br" (.word br) x) ∧
      (∀ x, x ≠ "heap_ptr" → a.globals x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        a.memory addr = s.memory addr)
    (attach1 hE (br := br) (k := k1) (l := l1) (v := v1) (vl := vl1) (by lk []) (by lk [hk1]) (by lk [hl1]) (by lk [hv1]) (by lk [hvl1]) hW1
      (hvr1.mono hle1.Cn)
      (Reg.addNd_kd Rg br 3#64 ℓ (ℓ + 1)) (Reg.addNd_cv Rg br 3#64 ℓ (ℓ + 1))
      (fun h0 => hseg1 h0)
      (fun l' g' m' R' hle hw hl hg hm => ⟨R', hle, hw, rfl, hl,
        fun x hx => (hg x hx).trans (hg1 x hx),
        fun addr ha => (hm addr ha).trans (hm1 addr ha)⟩)) ?_
  rintro ⟨la, ga, ma, fa⟩ ⟨R1, hle2, hW2, hfa, hla, hga, hma⟩
  dsimp only at hW2 hfa hla hga hma
  subst hfa
  refine WPs.seqG (fun a => ∃ R', R1.Le R' ∧ WorldTJ R' a.globals a.memory ∧
      a.ffi = s.ffi ∧ (∀ x, x ≠ "lf2" → a.locals x = la x) ∧
      (∀ x, x ≠ "heap_ptr" → a.globals x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        a.memory addr = s.memory addr)
    (attach2 hE (br := br) (k := k2) (l := l2) (v := v2) (vl := vl2) (by dsimp only; rw [hla _ (by decide)]; lk []) (by dsimp only; rw [hla _ (by decide)]; lk [hk2])
      (by dsimp only; rw [hla _ (by decide)]; lk [hl2]) (by dsimp only; rw [hla _ (by decide)]; lk [hv2])
      (by dsimp only; rw [hla _ (by decide)]; lk [hvl2]) hW2
      ((hvr2.mono hle1.Cn).mono hle2.Cn)
      (hle2.Kd _ _ (Reg.addNd_kd Rg br 3#64 ℓ (ℓ + 1)))
      (hle2.Cv _ _ (Reg.addNd_cv Rg br 3#64 ℓ (ℓ + 1))) (fun h0 => by
        obtain ⟨lo, hi, hI, hr⟩ := hseg2 h0
        exact ⟨lo, hi, hle2.Im _ _ hI, hr⟩)
      (fun l' g' m' R' hle hw hl hg hm => ⟨R', hle, hw, rfl, hl,
        fun x hx => (hg x hx).trans (hga x hx),
        fun addr ha => (hm addr ha).trans (hma addr ha)⟩)) ?_
  rintro ⟨lb, gb, mb, fb⟩ ⟨R2, hle3, hW3, hfb, hlb, hgb, hmb⟩
  dsimp only at hW3 hfb hlb hgb hmb
  subst hfb
  refine WPs.ret (w := br) (of_eval (by
    rw [evalF_local]
    show lb "br" = _
    rw [hlb _ (by decide), hla _ (by decide)]
    lk [])) ?_
  simp only [restorePanValueFfiLocal]
  exact ⟨_, _, _, br, R2, rfl, hle1.trans (hle2.trans hle3),
    hle3.Kd _ _ (hle2.Kd _ _ (Reg.addNd_kd Rg br 3#64 ℓ (ℓ + 1))),
    hle3.Lv _ _ (hle2.Lv _ _ (Reg.addNd_lv Rg br 3#64 ℓ (ℓ + 1))), hW3, hgb, hmb⟩

end InitECandidate.Solver.GuestBound
