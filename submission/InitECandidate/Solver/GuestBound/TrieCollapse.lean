import InitECandidate.Solver.GuestBound.TrieDelExt
import InitECandidate.Solver.GuestBound.HtabDiff

/-!
# `_collapse_branch` against the world invariant

After a deletion a branch may be left with no child (it becomes a leaf
holding the branch value), or with one child and no value (it merges with the
child: an extension by the child's nibble, or the child's leaf / extension
with that nibble prepended). Otherwise it stays.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem less16 (jj : Nat) (h : jj ≤ 16) :
    evalPanCmp .less (BitVec.ofNat 64 jj) (16#64 : Word) = if jj < 16 then 1#64 else 0#64 := by
  interval_cases jj <;> rfl

/-- The heap pointer of an invariant state. -/
theorem WorldTJ.heap_ptr {Rg : Reg} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} (h : WorldTJ Rg g m) :
    ∃ pv, g "heap_ptr" = some (.word pv) ∧ InHeap pv ∧ HBASE ≤ pv.toNat := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, -⟩ := h
  have := hW.jrn.lo
  have := hW.jrn.hi
  exact ⟨pv, hp, hpH, by omega⟩

/-- Invariant of the slot scan. -/
def CsI (s : St σ) (node : Word) (a : St σ) : Prop :=
  a.globals = s.globals ∧ a.memory = s.memory ∧ a.ffi = s.ffi ∧
    a.locals "node" = some (.word node) ∧
    ∃ (jj : Nat) (cnt ix : Word), a.locals "i" = some (.word (BitVec.ofNat 64 jj)) ∧ jj ≤ 16 ∧
      a.locals "count" = some (.word cnt) ∧ cnt.toNat ≤ jj ∧
      a.locals "idx" = some (.word ix) ∧ ix.toNat < 16 ∧
      (cnt ≠ 0#64 → ∃ c, Rd s.memory (node + BitVec.ofNat 64 (32 + 8 * ix.toNat)) c ∧ c ≠ 0#64)

set_option maxHeartbeats 32000000 in
theorem collapse_branch_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_collapse_branch" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (node : Word) (ℓ : Nat)
    (hnode : s.locals "node" = some (.word node))
    (hW : WorldTJ Rg s.globals s.memory) (hK : Rg.Kd node 3#64) (hL : Rg.Lv node ℓ)
    (h : Runs E s body r) : Stopped r ∨ DelQ Rg s ℓ r := by
  have hbody := (fun_of_index 276 hE.functions (by guest_decl_at 276) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (DelQ Rg s ℓ)) r h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have off0 : ∀ a : Word, off a 0 = a := fun a => by simp [off]
  obtain ⟨hNd, hRd, hlo, htop, h8⟩ := hW.kd hK
  have hsz3 : nodeSize 3#64 = 176 := by decide
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DelQ Rg s ℓ) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DelQ Rg s ℓ) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DelQ Rg s ℓ) ?_ (fun r h => h.restore _ _)
  refine WPs.seqG (fun a => CsI s node a)
    (WPs.loopG (I := CsI s node)
      ⟨rfl, rfl, rfl, by lk [hnode], 0, 0#64, 0#64, by lk [], Nat.zero_le _, by lk [],
        Nat.le_refl _, by lk [], by decide, fun h0 => absurd rfl h0⟩ ?_ (fun a k hI _ => hI)) ?_
  · -- one slot
    rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, qnode, jj, cnt, ix, qi, hj16, qcnt, hcj, qix, hix, hnz⟩
      ⟨w, cc, hcond, hw⟩
    dsimp only at hg hm hf qnode qi qcnt qix
    subst hg hm hf
    have hc' := eval_cmp_inv hE (op := .less)
      (of_eval (w := BitVec.ofNat 64 jj) (by lk [qi])) (of_eval (eval_const _ (16#64))) _
      (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc'
    rw [less16 jj hj16] at hc'
    have hjj : jj < 16 := by
      by_contra hge
      rw [if_neg hge] at hc'
      rw [hc'] at hw
      simp at hw
    have ejj : (BitVec.ofNat 64 jj : Word).toNat = jj := by
      rw [BitVec.toNat_ofNat]
      omega
    obtain ⟨c, rc, -⟩ := hW.slot hK hjj
    have hslot : E.eval (⟨la, s.globals, s.memory, s.ffi⟩ : St σ) (.op .add [.var .local "node",
        .const 32#64, .panOp .mul [.var .local "i", .const 8#64]]) =
        some (.word (node + BitVec.ofNat 64 (32 + 8 * jj))) := by
      have := eval_slot_idx hE (s := ⟨la, s.globals, s.memory, s.ffi⟩) (x := "node") (ix := "i")
        qnode qi (by rw [ejj]; exact hjj)
      rw [ejj] at this
      exact this
    refine WPs.seqG (fun a' => a'.globals = s.globals ∧ a'.memory = s.memory ∧ a'.ffi = s.ffi ∧
        a'.locals "node" = some (.word node) ∧
        a'.locals "i" = some (.word (BitVec.ofNat 64 jj)) ∧
        ∃ cnt' ix' : Word, a'.locals "count" = some (.word cnt') ∧ cnt'.toNat ≤ jj + 1 ∧
          a'.locals "idx" = some (.word ix') ∧ ix'.toNat < 16 ∧
          (cnt' ≠ 0#64 → ∃ c, Rd s.memory (node + BitVec.ofNat 64 (32 + 8 * ix'.toNat)) c ∧
            c ≠ 0#64)) (WPs.ite_both (fun w2 hw2 => ?_)) ?_
    · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw2
      have hxc := eval_load_inv2 hE (of_eval hslot) rc _ hx
      rw [eval_const] at hy
      simp only [Option.some.injEq, PanValue.word.injEq] at hxc hy
      subst hxc hy
      split
      · exact WPs.skip ⟨rfl, rfl, rfl, qnode, qi, cnt, ix, qcnt, by omega, qix, hix, hnz⟩
      · rename_i h0
        have hcne : x ≠ 0#64 := by
          rintro rfl
          exact h0 (by rw [hwv]; simp [evalPanCmp])
        have ec1 : (cnt + 1#64).toNat = cnt.toNat + 1 := by
          rw [BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
          omega
        refine WPs.seq_asg (old := cnt) (w := cnt + 1#64) qcnt (of_eval (by ev [qcnt])) ?_
        refine WPs.assign (old := ix) (w := BitVec.ofNat 64 jj) (by lk [qix])
          (of_eval (by lk [qi])) ?_
        exact ⟨rfl, rfl, rfl, by lk [qnode], by lk [qi], cnt + 1#64, BitVec.ofNat 64 jj,
          by lk [], by omega, by lk [], by rw [ejj]; exact hjj, fun _ => by
            rw [ejj]
            exact ⟨x, rc, hcne⟩⟩
    · rintro ⟨lb, gb, mb, fb⟩ ⟨hg, hm, hf, pnode, pi, cnt', ix', pcnt, hc1, pix, hix', hnz'⟩
      dsimp only at hg hm hf pnode pi pcnt pix
      subst hg hm hf
      refine WPs.assign (old := BitVec.ofNat 64 jj) (w := BitVec.ofNat 64 (jj + 1)) pi
        (of_eval (by ev [pi, ofNat_succ])) ?_
      exact ⟨rfl, rfl, rfl, by lk [pnode], jj + 1, cnt', ix', by lk [], by omega, by lk [pcnt],
        hc1, by lk [pix], hix', hnz'⟩
  -- after the scan
  rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, qnode, jj, cnt, ix, qi, hj16, qcnt, hcj, qix, hix, hnz⟩
  dsimp only at hg hm hf qnode qi qcnt qix
  subst hg hm hf
  refine WPs.dec_ev (fun vv hvv => ?_)
  obtain ⟨addr', vl, -, rfl, -⟩ := eval_load_one hE.mem hvv
  refine WPs.conseq (Q' := DelQ Rg s ℓ) ?_ (fun r h => h.restore _ _)
  refine WPs.name_locals (fun Lc hLc => ?_)
  dsimp only at hLc
  have rnode : Lc "node" = some (.word node) := by rw [hLc]; lk [qnode]
  have rcnt : Lc "count" = some (.word cnt) := by rw [hLc]; lk [qcnt]
  have rix : Lc "idx" = some (.word ix) := by rw [hLc]; lk [qix]
  have rvl : Lc "vl" = some (.word vl) := by rw [hLc]; lk []
  clear hLc
  -- no child: a leaf with the branch value
  refine WPs.seqG (fun a' => a' = ⟨Lc, s.globals, s.memory, s.ffi⟩ ∧ cnt ≠ 0#64)
    (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    simp only [evalF_local, eval_const, rcnt, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    · refine WPs.seqG (fun a'' => a'' = ⟨Lc, s.globals, s.memory, s.ffi⟩)
        (WPs.ite_both (fun w2 _ => ?_)) ?_
      · split
        · exact WPs.skip rfl
        · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
      rintro _ rfl
      obtain ⟨v160, hv160⟩ := eval_load_any hE (s := ⟨Lc, s.globals, s.memory, s.ffi⟩)
        (a := .op .add [.var .local "node", .const 160#64]) (addr := node + 160#64)
        (of_eval (eval_addc hE 160#64 rnode))
      refine WPs.tail_call (fun vs g2 m2 f2 hret2 l => ?_)
      obtain ⟨a, rfl, rfl, hW2, hg2, hm2⟩ := node_new_leaf_retV hE hret2 (nib := node)
        (nlen := 0#64) (vptr := v160) (vlen := vl) (of_eval (by lk [rnode]))
        (of_eval (eval_const _ _)) hv160 (of_eval (by lk [rvl])) hW (Or.inl rfl) ℓ
      exact ⟨l, g2, m2, a, _, rfl, Reg.Le.addNd Rg a 1#64 _ _,
        Or.inr ⟨1#64, Reg.addNd_kd Rg a 1#64 _ _, by decide, Reg.addNd_lv Rg a 1#64 _ _⟩, hW2,
        hg2, hm2⟩
  rintro _ ⟨rfl, hcnt0⟩
  obtain ⟨c, rc, hcne⟩ := hnz hcnt0
  refine WPs.seqG (fun a' => a' = ⟨Lc, s.globals, s.memory, s.ffi⟩)
    (WPs.ite_both (fun w _ => ?_)) ?_
  swap
  · rintro _ rfl
    refine WPs.ret (w := node) (of_eval (by lk [rnode])) ?_
    exact ⟨_, s.globals, s.memory, node, Rg, rfl, Reg.Le.refl Rg,
      Or.inr ⟨3#64, hK, by decide, hL⟩, hW, fun _ _ => rfl, fun _ _ => rfl⟩
  split
  · exact WPs.skip rfl
  -- one child and no value: merge with the child
  obtain ⟨c', rc', hcc⟩ := hW.slot hK hix
  have ec : c' = c := Rd.inj rc' rc
  subst ec
  obtain ⟨kc, hKc⟩ : ∃ k, Rg.Kd c' k := by
    rcases hcc with h0 | h1
    · exact absurd h0 hcne
    · exact h1
  have hLc : Rg.Lv c' (ℓ + 1) := hW.slot_lv hK (hW.cv_br hK hL) hix rc hcne
  obtain ⟨hNdc, hRdc, hloc, htopc, hc8⟩ := hW.kd hKc
  obtain ⟨hk3, -, -, -⟩ := hW.node_kind hNdc hRdc
  refine WPs.dec (w := c') (eval_load_inv2 hE (of_eval (eval_slot_idx hE rnode rix hix)) rc) ?_
  refine WPs.dec (w := kc) (eval_load_rd hE (eval_addc hE (a := c') 0#64 (by lk []))
    (by rw [BitVec.add_zero]; exact hRdc)) ?_
  refine WPs.name_locals (fun Ld hLd => ?_)
  dsimp only at hLd
  have tix : Ld "idx" = some (.word ix) := by rw [hLd]; lk [rix]
  have tch : Ld "child" = some (.word c') := by rw [hLd]; lk []
  have tck : Ld "ck" = some (.word kc) := by rw [hLd]; lk []
  clear hLd
  refine WPs.seqG (fun a' => a' = ⟨Ld, s.globals, s.memory, s.ffi⟩ ∧ kc ≠ 0#64)
    (WPs.ite_both (fun w2 hw2 => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw2
    simp only [evalF_local, eval_const, tck, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
  rintro _ ⟨rfl, hk0ne⟩
  obtain ⟨pv, hp, hpH, hpB⟩ := hW.heap_ptr
  have hpE := hpH.1
  have hp8 := hpH.2
  obtain ⟨hbelc, -⟩ := hW.nd_below hp hKc
  refine WPs.decCall_alloc hE (pv := pv) (nv := 8#64) (eval_const _ _) hp hpH
    (fun qv hq hqH => ?_)
  have hq' : pv.toNat + 8 ≤ qv.toNat := hq
  have hqE := hqH.1
  have ep1 : (pv + 1#64).toNat = pv.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
    omega
  refine WPs.seq_storeByte_nib hE (addr := pv) (of_eval (by lk []))
    (fun y hy => ⟨ix, of_eval (w := ix) (by lk [tix]) y hy, by omega⟩)
    (fun m1 wn hd hfr hwn hby => ?_)
  dsimp only at hfr hby
  have hkeep1 : ∀ A : Word, A.toNat % 8 = 0 → A.toNat ≠ pv.toNat → m1 A = s.memory A := by
    intro A _ hA
    exact hfr A (by omega)
  have hW1 : WorldTJ (Rg.addIm pv (pv + 1#64))
      (updatePanValueMap s.globals "heap_ptr" (.word qv)) m1 :=
    WorldTJ.fresh_nibs hW hp (by simp [updatePanValueMap]) hqH (by omega)
      (fun x hx => by simp [update_lookup, hx])
      (fun A h8' hlt => hkeep1 A h8' (by omega))
      (fun A hA => hfr A (by unfold HBASE at hA hpB; omega)) (by omega)
      (by
        intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        rw [off0, hby, if_pos rfl]
        exact ⟨wn, rfl, hwn⟩)
  have hI1 : (Rg.addIm pv (pv + 1#64)).Im pv (pv + 1#64) := Or.inr ⟨rfl, rfl⟩
  have hle1 := Reg.Le.addIm Rg pv (pv + 1#64)
  have hg1 : ∀ x, x ≠ "heap_ptr" → updatePanValueMap s.globals "heap_ptr" (.word qv) x =
      s.globals x := fun x hx => by simp [update_lookup, hx]
  have hm1 : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m1 addr = s.memory addr := fun A hA => hfr A (by unfold HBASE at hA hpB; omega)
  have hkne : ∀ c : Word, kc ≠ c → kc.toNat ≠ c.toNat :=
    fun c hc he => hc (BitVec.eq_of_toNat_eq he)
  refine WPs.name_locals (fun Le hLe => ?_)
  dsimp only at hLe
  have uch : Le "child" = some (.word c') := by rw [hLe]; lk [tch]
  have uck : Le "ck" = some (.word kc) := by rw [hLe]; lk [tck]
  have unib : Le "nib" = some (.word pv) := by rw [hLe]; lk []
  clear hLe
  -- the child is a branch: an extension by its nibble
  refine WPs.seqG (fun a' => a' = ⟨Le, updatePanValueMap s.globals "heap_ptr" (.word qv), m1,
      s.ffi⟩ ∧ kc ≠ 3#64) (WPs.ite_both (fun w3 hw3 => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw3
    simp only [evalF_local, eval_const, uck, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    · refine WPs.tail_call (fun vs g2 m2 f2 hret2 l => ?_)
      obtain ⟨a, rfl, rfl, hW2, hg2, hm2⟩ := node_new_ext_ret hE hret2 (nib := pv)
        (nlen := 1#64) (child := c') (of_eval (by lk [unib])) (of_eval (eval_const _ _))
        (of_eval (by lk [uch])) (by decide) (Or.inr (hle1.Nd _ hNdc)) hW1
        ⟨pv, pv + 1#64, hI1, Nat.le_refl _, by
          rw [show (1#64 : Word).toNat = 1 by decide]
          omega,
          hW1.im_nibs hI1 (p := pv) (c := (1#64 : Word).toNat) (Nat.le_refl _) (by
            rw [show (1#64 : Word).toNat = 1 by decide]
            omega)⟩ ℓ (fun _ => hle1.Lv _ _ hLc)
      simp only [restorePanValueFfiLocal]
      exact ⟨_, g2, m2, a, _, rfl, hle1.trans (Reg.Le.addNd _ a 2#64 _ _),
        Or.inr ⟨2#64, Reg.addNd_kd _ a 2#64 _ _, by decide, Reg.addNd_lv _ a 2#64 _ _⟩, hW2,
        fun x hx => (hg2 x hx).trans (hg1 x hx), fun addr ha => (hm2 addr ha).trans (hm1 addr ha)⟩
  rintro _ ⟨rfl, hk3ne⟩
  have hk12 : kc = 1#64 ∨ kc = 2#64 := by
    have a0 := hkne 0#64 hk0ne
    have a3 := hkne 3#64 hk3ne
    simp at a0 a3
    by_cases h1 : kc.toNat = 1
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simp; omega))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simp; omega))
  obtain ⟨sp2, nl2, q1, q2, hc2⟩ := hW.seg hNdc hRdc hk12
  have hsz : 56 ≤ nodeSize kc := by
    rcases hk12 with rfl | rfl <;> simp [nodeSize]
  have c32 : (c' + 32#64).toNat = c'.toNat + 32 := by bv_omega
  have c40 : (c' + 40#64).toNat = c'.toNat + 40 := by bv_omega
  have c48 : (c' + 48#64).toNat = c'.toNat + 48 := by bv_omega
  have rdm1 : ∀ {A w : Word}, A.toNat % 8 = 0 → A.toNat + 8 ≤ pv.toNat → Rd s.memory A w →
      Rd m1 A w := by
    intro A w hA8 hAp hr
    unfold Rd at hr ⊢
    rw [hkeep1 A hA8 (by omega)]
    exact hr
  have q1' := rdm1 (by omega) (by omega) q1
  have q2' := rdm1 (by omega) (by omega) q2
  refine WPs.decCall_ret (fun vc g2 m2 f2 hret => ?_)
  obtain ⟨cat, rfl, rfl, hW2, ecat, hpo, hkeep2, hg2, hm2⟩ := nibbles_concat_ret hE hret
    (a := pv) (al := 1#64) (b := sp2) (bl := nl2) (of_eval (by lk [unib]))
    (of_eval (eval_const _ _))
    (eval_load_inv2 hE (of_eval (eval_addc hE 32#64 (by lk [uch]))) q1')
    (eval_load_inv2 hE (of_eval (eval_addc hE 40#64 (by lk [uch]))) q2') hW1
    (fun _ => ⟨pv, pv + 1#64, hI1, Nat.le_refl _, by
      rw [show (1#64 : Word).toNat = 1 by decide]
      omega⟩)
    (fun hne => by
      rcases hc2 with h0 | ⟨lo, hi, hI, h1, h2, -⟩
      · exact absurd h0 hne
      · exact ⟨lo, hi, Or.inl hI, h1, h2⟩)
  have hqo : cat = qv := by
    simp (config := { decide := true }) [update_lookup] at hpo
    exact hpo.symm
  subst hqo
  have h1n : (1#64 : Word).toNat = 1 := by decide
  rw [h1n] at ecat
  have hcat64 := (cat + (1#64 + nl2)).isLt
  have esum : (1#64 + nl2).toNat = 1 + nl2.toNat := by
    rw [BitVec.toNat_add, h1n]
    omega
  have rdm2 : ∀ {A w : Word}, A.toNat % 8 = 0 → A.toNat + 8 ≤ pv.toNat → Rd s.memory A w →
      Rd m2 A w := by
    intro A w hA8 hAp hr
    have h1' := rdm1 hA8 hAp hr
    unfold Rd at h1' ⊢
    rw [hkeep2 A hA8 (by omega)]
    exact h1'
  have q2'' := rdm2 (by omega) (by omega) q2
  have hIc : ((Rg.addIm pv (pv + 1#64)).addIm cat (cat + (1#64 + nl2))).Im cat
      (cat + (1#64 + nl2)) := Or.inr ⟨rfl, rfl⟩
  have hle2 := hle1.trans (Reg.Le.addIm (Rg.addIm pv (pv + 1#64)) cat (cat + (1#64 + nl2)))
  have hnibs : NibSeg m2 cat (1#64 + nl2) :=
    hW2.im_nibs hIc (p := cat) (c := (1#64 + nl2).toNat) (Nat.le_refl _) (by omega)
  have hg12 : ∀ x, x ≠ "heap_ptr" → g2 x = s.globals x :=
    fun x hx => (hg2 x hx).trans (hg1 x hx)
  have hm12 : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m2 addr = s.memory addr := fun A hA => (hm2 A hA).trans (hm1 A hA)
  refine WPs.name_locals (fun Lf hLf => ?_)
  dsimp only at hLf
  have vch : Lf "child" = some (.word c') := by rw [hLf]; lk [uch]
  have vck : Lf "ck" = some (.word kc) := by rw [hLf]; lk [uck]
  have vcat : Lf "cat" = some (.word cat) := by rw [hLf]; lk []
  clear hLf
  have hlen : ∀ y, E.eval (⟨Lf, g2, m2, s.ffi⟩ : St σ) (.op .add [.const 1#64,
      .load .one (.op .add [.var .local "child", .const 40#64])]) = some y →
      y = .word (1#64 + nl2) :=
    eval_add2_inv hE (of_eval (eval_const _ _))
      (eval_load_inv2 hE (of_eval (eval_addc hE 40#64 vch)) q2'')
  obtain ⟨v48, hv48⟩ := eval_load_any hE (s := ⟨Lf, g2, m2, s.ffi⟩)
    (a := .op .add [.var .local "child", .const 48#64]) (addr := c' + 48#64)
    (of_eval (eval_addc hE 48#64 vch))
  obtain ⟨v56, hv56⟩ := eval_load_any hE (s := ⟨Lf, g2, m2, s.ffi⟩)
    (a := .op .add [.var .local "child", .const 56#64]) (addr := c' + 56#64)
    (of_eval (eval_addc hE 56#64 vch))
  -- the child is a leaf: the leaf with its nibble prepended
  refine WPs.seqG (fun a' => a' = ⟨Lf, g2, m2, s.ffi⟩ ∧ kc ≠ 1#64)
    (WPs.ite_both (fun w4 hw4 => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw4
    simp only [evalF_local, eval_const, vck, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    · refine WPs.tail_call (fun vs g3 m3 f3 hret3 l => ?_)
      obtain ⟨a, rfl, rfl, hW3, hg3, hm3⟩ := node_new_leaf_retV hE hret3 (nib := cat)
        (nlen := 1#64 + nl2) (vptr := v48) (vlen := v56) (of_eval (by lk [vcat])) hlen hv48 hv56
        hW2 (Or.inr ⟨cat, cat + (1#64 + nl2), hIc, Nat.le_refl _, by omega, hnibs⟩) ℓ
      simp only [restorePanValueFfiLocal]
      exact ⟨_, g3, m3, a, _, rfl, hle2.trans (Reg.Le.addNd _ a 1#64 _ _),
        Or.inr ⟨1#64, Reg.addNd_kd _ a 1#64 _ _, by decide, Reg.addNd_lv _ a 1#64 _ _⟩, hW3,
        fun x hx => (hg3 x hx).trans (hg12 x hx),
        fun addr ha => (hm3 addr ha).trans (hm12 addr ha)⟩
  rintro _ ⟨rfl, hk1ne⟩
  -- the child is an extension: the extension with its nibble prepended
  have hk2 : kc = 2#64 := by
    rcases hk12 with h1 | h2
    · exact absurd h1 hk1ne
    · exact h2
  subst hk2
  obtain ⟨nly, c2, ry2, -, ry3, hcy⟩ := hW.ext hKc
  have e4 : nly = nl2 := Rd.inj ry2 q2
  subst e4
  have hcl : c2 ≠ 0#64 → Rg.Lv c2 (ℓ + 1 + nly.toNat) :=
    fun hc0 => hW.ext_lv hKc (hW.cv_ext hKc hLc q2) ry3 hc0
  have ry3'' := rdm2 (by omega) (by omega) ry3
  refine WPs.tail_call (fun vs g3 m3 f3 hret3 l => ?_)
  obtain ⟨a, rfl, rfl, hW3, hg3, hm3⟩ := node_new_ext_ret hE hret3 (nib := cat)
    (nlen := 1#64 + nly) (child := c2) (of_eval (by lk [vcat])) hlen
    (eval_load_inv2 hE (of_eval (eval_addc hE 48#64 vch)) ry3'') (by omega)
    (by
      rcases hcy with h0 | ⟨j, hj⟩
      · exact Or.inl h0
      · exact Or.inr (hle2.Nd _ (hW.kd hj).1)) hW2
    ⟨cat, cat + (1#64 + nly), hIc, Nat.le_refl _, by omega, hnibs⟩ ℓ
    (fun hc0 => by
      have := hle2.Lv _ _ (hcl hc0)
      rw [esum]
      rw [Nat.add_assoc] at this
      exact this)
  simp only [restorePanValueFfiLocal]
  exact ⟨_, g3, m3, a, _, rfl, hle2.trans (Reg.Le.addNd _ a 2#64 _ _),
    Or.inr ⟨2#64, Reg.addNd_kd _ a 2#64 _ _, by decide, Reg.addNd_lv _ a 2#64 _ _⟩, hW3,
    fun x hx => (hg3 x hx).trans (hg12 x hx), fun addr ha => (hm3 addr ha).trans (hm12 addr ha)⟩

end InitECandidate.Solver.GuestBound
