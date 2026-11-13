import InitECandidate.Solver.GuestBound.TrieDelDefs

/-!
# `_delete_ext_finish` against the world invariant

`node` is an extension at level `L` whose subtree was replaced by `nc` (null,
or a registered node at the extension's child level). The result is null, the
relinked extension, or a new leaf / extension with the concatenated segment,
at level `L`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

set_option maxHeartbeats 16000000 in
theorem delete_ext_finish_world (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "_delete_ext_finish" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (node seg sl nc : Word) (L : Nat)
    (hnode : s.locals "node" = some (.word node)) (hsegv : s.locals "seg" = some (.word seg))
    (hslv : s.locals "sl" = some (.word sl)) (hncv : s.locals "nc" = some (.word nc))
    (hW : WorldTJ Rg s.globals s.memory) (hK : Rg.Kd node 2#64) (hL : Rg.Lv node L)
    (hseg : Rd s.memory (node + 32#64) seg) (hsl : Rd s.memory (node + 40#64) sl)
    (hnc : nc = 0#64 ∨ ∃ k, Rg.Kd nc k ∧ Rg.Lv nc (L + sl.toNat))
    (h : Runs E s body r) : Stopped r ∨ DelQ Rg s L r := by
  have hbody := (fun_of_index 277 hE.functions (by guest_decl_at 277) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (DelQ Rg s L)) r h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  obtain ⟨hNd, hRd, hlo, htop, h8⟩ := hW.kd hK
  have hsz2 : nodeSize 2#64 = 56 := by decide
  have hcvn : Rg.Cv node (L + sl.toNat) := hW.cv_ext hK hL hsl
  -- the extension's own segment
  obtain ⟨sp0, nl0, r1, r2, hc0⟩ := hW.seg hNd hRd (Or.inr rfl)
  have e1 : sp0 = seg := Rd.inj r1 hseg
  have e2 : nl0 = sl := Rd.inj r2 hsl
  subst e1 e2
  obtain ⟨nlx, cx, rx2, hsl1, -, -⟩ := hW.ext hK
  have e3 : nlx = nl0 := Rd.inj rx2 hsl
  subst e3
  have hsegI : nlx ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ sp0.toNat ∧
      sp0.toNat + nlx.toNat ≤ hi.toNat := by
    intro hne
    rcases hc0 with h0 | ⟨lo, hi, hI, h1, h2, -⟩
    · exact absurd h0 hne
    · exact ⟨lo, hi, hI, h1, h2⟩
  refine WPs.seqG (fun a => a = s ∧ nc ≠ 0#64) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    rw [evalF_local, hncv] at hx
    rw [eval_const] at hy
    simp only [Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    · exact WPs.ret (w := 0#64) (of_eval (eval_const _ _))
        ⟨_, s.globals, s.memory, 0#64, Rg, rfl, Reg.Le.refl Rg, Or.inl rfl, hW, fun _ _ => rfl,
          fun _ _ => rfl⟩
  rintro a ⟨ha, hne⟩
  rw [ha]
  clear ha a
  obtain ⟨k, hKc, hLc⟩ : ∃ k, Rg.Kd nc k ∧ Rg.Lv nc (L + nlx.toNat) := by
    rcases hnc with h0 | h1
    · exact absurd h0 hne
    · exact h1
  obtain ⟨hNdc, hRdc, hloc, htopc, hc8⟩ := hW.kd hKc
  obtain ⟨hk3, -, -, -⟩ := hW.node_kind hNdc hRdc
  refine WPs.dec (w := k) (eval_load_rd hE (eval_addc hE 0#64 hncv)
    (by rw [BitVec.add_zero]; exact hRdc)) ?_
  refine WPs.conseq (Q' := DelQ Rg s L) ?_ (fun r h => h.restore _ _)
  have e48 : (node + 48#64).toNat = node.toNat + 48 := by bv_omega
  -- a branch: relink
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals "ck" (.word k), s.globals, s.memory,
      s.ffi⟩ ∧ k ≠ 3#64) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    rw [eval_const] at hy
    rw [evalF_local] at hx
    simp (config := { decide := true }) [update_lookup] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    · have W1 := hW.node_child (c := nc) hNd hRd (Or.inl ⟨rfl, rfl⟩) (Or.inr hNdc)
        (fun ℓc hcv _ => by
          have := hW.cv_unique hcv hcvn
          subst this
          exact hLc)
      refine WPs.seq_store hE (addr := node + 48#64) (w := nc)
        (eval_addc hE 48#64 (by lk [hnode])) (of_eval (by lk [hncv])) ?_
      refine WPs.ret (w := node) (of_eval (by lk [hnode])) ?_
      refine ⟨_, _, _, node, Rg, rfl, Reg.Le.refl Rg, Or.inr ⟨2#64, hK, by decide, hL⟩, W1,
        fun _ _ => rfl, fun addr ha => ?_⟩
      show setCell s.memory (node + 48#64) nc addr = _
      rw [setCell_ne _ (NE (by unfold HBASE at ha hlo; omega))]
  rintro _ ⟨rfl, hk3ne⟩
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals "ck" (.word k), s.globals, s.memory,
      s.ffi⟩ ∧ k ≠ 0#64) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    rw [eval_const] at hy
    rw [evalF_local] at hx
    simp (config := { decide := true }) [update_lookup] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
  rintro _ ⟨rfl, hk0ne⟩
  have hkne : ∀ c : Word, k ≠ c → k.toNat ≠ c.toNat :=
    fun c hc he => hc (BitVec.eq_of_toNat_eq he)
  have hk12 : k = 1#64 ∨ k = 2#64 := by
    have a0 := hkne 0#64 hk0ne
    have a3 := hkne 3#64 hk3ne
    simp at a0 a3
    by_cases h1 : k.toNat = 1
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simp; omega))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simp; omega))
  -- the child's segment
  obtain ⟨sp2, nl2, q1, q2, hc2⟩ := hW.seg hNdc hRdc hk12
  have hsz : 56 ≤ nodeSize k := by
    rcases hk12 with rfl | rfl <;> simp [nodeSize]
  have c32 : (nc + 32#64).toNat = nc.toNat + 32 := by bv_omega
  have c40 : (nc + 40#64).toNat = nc.toNat + 40 := by bv_omega
  have c48 : (nc + 48#64).toNat = nc.toNat + 48 := by bv_omega
  refine WPs.decCall_ret (fun vc g1 m1 f1 hret => ?_)
  obtain ⟨cat, rfl, rfl, hW1, ecat, hpo, hkeep, hg1, hm1⟩ := nibbles_concat_ret hE hret
    (a := sp0) (al := nlx) (b := sp2) (bl := nl2) (of_eval (by lk [hsegv]))
    (of_eval (by lk [hslv]))
    (eval_load_inv2 hE (of_eval (eval_addc hE 32#64 (by lk [hncv]))) q1)
    (eval_load_inv2 hE (of_eval (eval_addc hE 40#64 (by lk [hncv]))) q2) hW hsegI
    (fun hne => by
      rcases hc2 with h0 | ⟨lo, hi, hI, h1, h2, -⟩
      · exact absurd h0 hne
      · exact ⟨lo, hi, hI, h1, h2⟩)
  refine WPs.conseq (Q' := DelQ Rg s L) ?_ (fun r h => h.restore _ _)
  obtain ⟨hbel, -⟩ := hW.nd_below hpo hKc
  have q2' : Rd m1 (nc + 40#64) nl2 := by
    unfold Rd at q2 ⊢
    rw [hkeep _ (by omega) (by omega)]
    exact q2
  have hcat64 := (cat + (nlx + nl2)).isLt
  have esum : (nlx + nl2).toNat = nlx.toNat + nl2.toNat := by
    rw [BitVec.toNat_add]
    omega
  refine WPs.dec (w := nlx + nl2) (eval_add2_inv hE (of_eval (by lk [hslv]))
    (eval_load_inv2 hE (of_eval (eval_addc hE 40#64 (by lk [hncv]))) q2')) ?_
  refine WPs.conseq (Q' := DelQ Rg s L) ?_ (fun r h => h.restore _ _)
  have hIc : (Rg.addIm cat (cat + (nlx + nl2))).Im cat (cat + (nlx + nl2)) := Or.inr ⟨rfl, rfl⟩
  have hle1 := Reg.Le.addIm Rg cat (cat + (nlx + nl2))
  have hnibs : NibSeg m1 cat (nlx + nl2) :=
    hW1.im_nibs hIc (p := cat) (c := (nlx + nl2).toNat) (Nat.le_refl _) (by omega)
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
      s.locals "ck" (.word k)) "cat" (.word cat)) "cl" (.word (nlx + nl2)), g1, m1, s.ffi⟩ ∧
      k ≠ 2#64) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    rw [eval_const] at hy
    rw [evalF_local] at hx
    simp (config := { decide := true }) [update_lookup] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    · rename_i h0
      -- the child is an extension: one extension with both segments
      have hk2 : k = 2#64 := by
        by_contra hne2
        exact h0 (by rw [hwv]; simp [evalPanCmp, hne2])
      subst hk2
      obtain ⟨nly, c2, ry2, -, ry3, hcy⟩ := hW.ext hKc
      have e4 : nly = nl2 := Rd.inj ry2 q2
      subst e4
      have hcl : c2 ≠ 0#64 → Rg.Lv c2 (L + nlx.toNat + nly.toNat) :=
        fun hc0 => hW.ext_lv hKc (hW.cv_ext hKc hLc q2) ry3 hc0
      have ry3' : Rd m1 (nc + 48#64) c2 := by
        unfold Rd at ry3 ⊢
        rw [hkeep _ (by omega) (by omega)]
        exact ry3
      refine WPs.tail_call (fun vs g2 m2 f2 hret2 l => ?_)
      obtain ⟨a, rfl, rfl, hW2, hg2, hm2⟩ := node_new_ext_ret hE hret2 (nib := cat)
        (nlen := nlx + nly) (child := c2) (of_eval (by lk [])) (of_eval (by lk []))
        (eval_load_inv2 hE (of_eval (eval_addc hE 48#64 (by lk [hncv]))) ry3') (by omega)
        (by
          rcases hcy with h0 | ⟨j, hj⟩
          · exact Or.inl h0
          · exact Or.inr (hW.kd hj).1) hW1
        ⟨cat, cat + (nlx + nly), hIc, Nat.le_refl _, by omega, hnibs⟩ L
        (fun hc0 => by
          have := hcl hc0
          rw [esum]
          rw [Nat.add_assoc] at this
          exact this)
      exact ⟨l, g2, m2, a, _, rfl, hle1.trans (Reg.Le.addNd _ a 2#64 _ _),
        Or.inr ⟨2#64, Reg.addNd_kd _ a 2#64 _ _, by decide, Reg.addNd_lv _ a 2#64 _ _⟩, hW2,
        fun x hx => (hg2 x hx).trans (hg1 x hx), fun addr ha => (hm2 addr ha).trans (hm1 addr ha)⟩
  rintro _ ⟨rfl, hk2ne⟩
  -- the child is a leaf: one leaf with both segments
  obtain ⟨v1, hv1⟩ := eval_load_any hE (s := ⟨updatePanValueMap (updatePanValueMap
      (updatePanValueMap s.locals "ck" (.word k)) "cat" (.word cat)) "cl" (.word (nlx + nl2)),
      g1, m1, s.ffi⟩) (a := .op .add [.var .local "nc", .const 48#64]) (addr := nc + 48#64)
    (of_eval (eval_addc hE 48#64 (by lk [hncv])))
  obtain ⟨vl1, hvl1⟩ := eval_load_any hE (s := ⟨updatePanValueMap (updatePanValueMap
      (updatePanValueMap s.locals "ck" (.word k)) "cat" (.word cat)) "cl" (.word (nlx + nl2)),
      g1, m1, s.ffi⟩) (a := .op .add [.var .local "nc", .const 56#64]) (addr := nc + 56#64)
    (of_eval (eval_addc hE 56#64 (by lk [hncv])))
  refine WPs.tail_call (fun vs g2 m2 f2 hret2 l => ?_)
  obtain ⟨a, rfl, rfl, hW2, hg2, hm2⟩ := node_new_leaf_retV hE hret2 (nib := cat)
    (nlen := nlx + nl2) (vptr := v1) (vlen := vl1) (of_eval (by lk [])) (of_eval (by lk []))
    hv1 hvl1 hW1 (Or.inr ⟨cat, cat + (nlx + nl2), hIc, Nat.le_refl _, by omega, hnibs⟩) L
  exact ⟨l, g2, m2, a, _, rfl, hle1.trans (Reg.Le.addNd _ a 1#64 _ _),
    Or.inr ⟨1#64, Reg.addNd_kd _ a 1#64 _ _, by decide, Reg.addNd_lv _ a 1#64 _ _⟩, hW2,
    fun x hx => (hg2 x hx).trans (hg1 x hx), fun addr ha => (hm2 addr ha).trans (hm1 addr ha)⟩

end InitECandidate.Solver.GuestBound
