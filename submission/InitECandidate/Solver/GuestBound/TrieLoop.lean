import InitECandidate.Solver.GuestBound.TrieLoopStep

/-!
# `_mpt_insert_node` against the world invariant

The loop walks down the trie; each iteration replaces the current node by `r`
(stored into the slot chosen by the previous iteration, or returned as the
result on the first one). The invariant `InsI` keeps the world invariant with
a registry that only grows, the current node null or registered, the pending
slot null or a child slot of a registered node, and the level within the key.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Loop invariant of `_mpt_insert_node`. -/
def InsI (Rg : Reg) (s : St σ) (key klen vptr vlen lv0 : Word) (a : St σ) : Prop :=
  ∃ R lv nd sl res gw, Rg.Le R ∧ WorldTJ R a.globals a.memory ∧ a.ffi = s.ffi ∧
    (∀ x, x ≠ "heap_ptr" → a.globals x = s.globals x) ∧
    (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      a.memory addr = s.memory addr) ∧
    a.locals "key" = some (.word key) ∧ a.locals "klen" = some (.word klen) ∧
    a.locals "vptr" = some (.word vptr) ∧ a.locals "vlen" = some (.word vlen) ∧
    a.locals "level" = some (.word lv) ∧ a.locals "node" = some (.word nd) ∧
    a.locals "slot" = some (.word sl) ∧ a.locals "result" = some (.word res) ∧
    a.locals "go" = some (.word gw) ∧
    (((∃ k, R.Kd res k ∧ k ≠ 0#64 ∧ R.Lv res lv0.toNat) ∧ (gw ≠ 0#64 → sl ≠ 0#64)) ∨
      (sl = 0#64 ∧ gw ≠ 0#64 ∧ lv = lv0)) ∧
    (gw ≠ 0#64 → lv.toNat ≤ klen.toNat ∧ (nd = 0#64 ∨ ∃ k, R.Kd nd k) ∧
      (nd ≠ 0#64 → R.Lv nd lv.toNat) ∧ (sl = 0#64 ∨ SlotOf R sl lv.toNat))

/-- A child slot is not the null pointer. -/
theorem WorldTJ.slot_ne {R : Reg} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {x : Word} {ℓ : Nat} (h : WorldTJ R g m)
    (hs : SlotOf R x ℓ) : x ≠ 0#64 := by
  obtain ⟨a, hcv, hs⟩ := hs
  rintro rfl
  rcases hs with ⟨hk, hx⟩ | ⟨hk, i, hi, hx⟩
  · obtain ⟨hNd, hRd, hlo, htop, -⟩ := h.kd hk
    have hsz : nodeSize 2#64 = 56 := by decide
    have e : (a + 48#64).toNat = a.toNat + 48 := by bv_omega
    have := congrArg BitVec.toNat hx
    unfold HBASE at hlo
    simp at this
    omega
  · obtain ⟨hNd, hRd, hlo, htop, -⟩ := h.kd hk
    have hsz : nodeSize 3#64 = 176 := by decide
    have e : (a + BitVec.ofNat 64 (32 + 8 * i)).toNat = a.toNat + (32 + 8 * i) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have := congrArg BitVec.toNat hx
    unfold HBASE at hlo
    simp at this
    omega

/-- A child slot is a heap cell, and storing a registered node there keeps the world. -/
theorem WorldTJ.slot_store {R : Reg} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {x c : Word} {ℓ : Nat} (h : WorldTJ R g m)
    (hs : SlotOf R x ℓ) (hc : c = 0#64 ∨ R.Nd c) (hlc : c ≠ 0#64 → R.Lv c ℓ) :
    WorldTJ R g (setCell m x c) ∧ HBASE ≤ x.toNat ∧ x.toNat + 8 ≤ 2952790016 := by
  obtain ⟨a, hcv, hs⟩ := hs
  have hl : ∀ ℓc, R.Cv a ℓc → c ≠ 0#64 → R.Lv c ℓc := by
    intro ℓc hcv' hc0
    have := h.cv_unique hcv' hcv
    subst this
    exact hlc hc0
  rcases hs with ⟨hk, rfl⟩ | ⟨hk, i, hi, rfl⟩
  · obtain ⟨hNd, hRd, hlo, htop, -⟩ := h.kd hk
    have hsz : nodeSize 2#64 = 56 := by decide
    have e : (a + 48#64).toNat = a.toNat + 48 := by bv_omega
    exact ⟨h.node_child hNd hRd (Or.inl ⟨rfl, rfl⟩) hc hl, by omega, by omega⟩
  · obtain ⟨hNd, hRd, hlo, htop, -⟩ := h.kd hk
    have hsz : nodeSize 3#64 = 176 := by decide
    have e : (a + BitVec.ofNat 64 (32 + 8 * i)).toNat = a.toNat + (32 + 8 * i) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    exact ⟨h.node_child hNd hRd (Or.inr ⟨rfl, i, hi, rfl⟩) hc hl, by omega, by omega⟩

set_option maxHeartbeats 32000000 in
theorem mpt_insert_node_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_mpt_insert_node" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (node key klen level vptr vlen : Word)
    (hnode : s.locals "node" = some (.word node)) (hkey : s.locals "key" = some (.word key))
    (hklen : s.locals "klen" = some (.word klen))
    (hlevel : s.locals "level" = some (.word level))
    (hvp : s.locals "vptr" = some (.word vptr)) (hvl : s.locals "vlen" = some (.word vlen))
    (hW : WorldTJ Rg s.globals s.memory) (hnd : node = 0#64 ∨ ∃ k, Rg.Kd node k)
    (hLn : node ≠ 0#64 → Rg.Lv node level.toNat) (hlv : level.toNat ≤ klen.toNat)
    (hblk : klen ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (h : Runs E s body r) : Stopped r ∨ InsQ Rg s level.toNat r := by
  have hbody := (fun_of_index 275 hE.functions (by guest_decl_at 275) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (InsQ Rg s level.toNat)) r h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := InsQ Rg s level.toNat) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := InsQ Rg s level.toNat) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := 1#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := InsQ Rg s level.toNat) ?_ (fun r h => h.restore _ _)
  refine WPs.seqG (fun a => InsI Rg s key klen vptr vlen level a ∧
      a.locals "go" = some (.word 0#64))
    (WPs.loopG (I := InsI Rg s key klen vptr vlen level)
      ⟨Rg, level, node, 0#64, 0#64, 1#64, Reg.Le.refl Rg, hW, rfl, fun _ _ => rfl,
        fun _ _ => rfl, by lk [hkey], by lk [hklen], by lk [hvp], by lk [hvl], by lk [hlevel],
        by lk [hnode], by lk [], by lk [], by lk [], Or.inr ⟨rfl, by decide, rfl⟩,
        fun _ => ⟨hlv, hnd, hLn, Or.inl rfl⟩⟩ ?_ ?_) ?_
  · -- one iteration
    rintro ⟨la, ga, ma, fa⟩ ⟨R, lv, nd, sl, res, gw, hle, hW', hf, hg, hm, k1, k2, k3, k4, k5,
      k6, k7, k8, k9, hres, hI⟩ ⟨w, cc, hcond, hw⟩
    dsimp only at hW' hf hg hm k1 k2 k3 k4 k5 k6 k7 k8 k9
    subst hf
    have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := gw) (by lk [k9]))
      (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hgw : gw ≠ 0#64 := by
      rintro rfl
      rw [hcv] at hw
      simp [evalPanCmp] at hw
    obtain ⟨hlv', hnd', hLn', hsl'⟩ := hI hgw
    have hkeyR : klen ≠ 0#64 → ∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
        key.toNat + klen.toNat ≤ hi.toNat := by
      intro h0
      obtain ⟨lo, hi, hI', hr⟩ := hblk h0
      exact ⟨lo, hi, by rw [hle.Im]; exact hI', hr⟩
    refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
    refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
    refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
    refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
    refine WPs.seq_asg (old := gw) (w := 0#64) (by lk [k9]) (of_eval (eval_const _ _)) ?_
    refine WPs.name_locals (fun L hLL => ?_)
    dsimp only at hLL
    have hLoc : InsLoc L key klen vptr vlen lv nd sl res :=
      ⟨by rw [hLL]; lk [k1], by rw [hLL]; lk [k2], by rw [hLL]; lk [k3], by rw [hLL]; lk [k4],
        by rw [hLL]; lk [k5], by rw [hLL]; lk [k6], by rw [hLL]; lk [k7], by rw [hLL]; lk [k8],
        by rw [hLL]; lk [], by rw [hLL]; lk [], by rw [hLL]; lk [], by rw [hLL]; lk [],
        by rw [hLL]; lk []⟩
    clear hLL
    refine WPs.seqG (fun a' => a'.ffi = s.ffi ∧
        InsMid R ga ma key klen vptr vlen lv sl res a'.locals a'.globals a'.memory)
      (ins_step hE (s := ⟨L, ga, ma, s.ffi⟩) hLoc hW' hnd' hLn' hlv' hkeyR
        (fun l' g' m' hmid => ⟨rfl, hmid⟩)) ?_
    rintro ⟨l2, g2, m2, f2⟩ ⟨hf2, R', rv, kk, gw', nn, ns, nlv, nd', hle', hW2, hg2, hm2, j1,
      j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, hKr, hkk, hLr, hgo'⟩
    dsimp only at hf2 hW2 hg2 hm2 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13
    subst hf2
    -- the result goes to the pending slot, or becomes the result
    refine WPs.seqG (fun a2 => a2.ffi = s.ffi ∧ a2.globals = g2 ∧ WorldTJ R' g2 a2.memory ∧
        (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
          a2.memory addr = m2 addr) ∧
        (∃ res', a2.locals "result" = some (.word res') ∧
          ∃ k, R'.Kd res' k ∧ k ≠ 0#64 ∧ R'.Lv res' level.toNat) ∧
        ∀ x, x ≠ "result" → a2.locals x = l2 x) (WPs.ite_both (fun w2 hw2 => ?_)) ?_
    · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw2
      rw [eval_const] at hy
      rw [evalF_local] at hx
      dsimp only at hx
      rw [j7] at hx
      simp only [Option.some.injEq, PanValue.word.injEq] at hx hy
      subst hx hy
      split
      · rename_i h0
        have hsl0 : sl ≠ 0#64 := by
          rintro rfl
          rw [h0] at hwv
          simp [evalPanCmp] at hwv
        have hSlot : SlotOf R' sl lv.toNat := (hsl'.resolve_left hsl0).mono hle'
        have hres' : ∃ k, R'.Kd res k ∧ k ≠ 0#64 ∧ R'.Lv res level.toNat := by
          rcases hres with ⟨⟨k, hk, hk0, hkl⟩, -⟩ | ⟨h1, -⟩
          · exact ⟨k, hle'.Kd _ _ hk, hk0, hle'.Lv _ _ hkl⟩
          · exact absurd h1 hsl0
        obtain ⟨W3, hb1, hb2⟩ := hW2.slot_store hSlot (c := rv) (Or.inr (hW2.kd hKr).1)
          (fun _ => hLr)
        refine WPs.store hE (addr := sl) (w := rv) (by rw [evalF_local]; exact j7)
          (of_eval (by rw [evalF_local]; exact j9)) ?_
        refine ⟨rfl, rfl, W3, fun addr ha => ?_, ⟨res, j8, hres'⟩, fun _ _ => rfl⟩
        show setCell m2 sl rv addr = _
        rw [setCell_ne _ (NE (by unfold HBASE at ha hb1; omega))]
      · rename_i h0
        have hsl0 : sl = 0#64 := by
          by_contra hne
          exact h0 (by rw [hwv]; simp [evalPanCmp, hne])
        have hlv0 : lv = level := by
          rcases hres with ⟨-, hns⟩ | ⟨-, -, h3⟩
          · exact absurd hsl0 (hns hgw)
          · exact h3
        refine WPs.assign (old := res) (w := rv) j8 (of_eval (by rw [evalF_local]; exact j9)) ?_
        exact ⟨rfl, rfl, hW2, fun _ _ => rfl,
          ⟨rv, by lk [], kk, hKr, hkk, by rw [← hlv0]; exact hLr⟩,
          fun x hx => by simp [update_lookup, hx]⟩
    rintro ⟨l3, g3, m3, f3⟩ ⟨hf3, hg3, hW3, hm3, ⟨res', hr3, k', hk', hk0', hkl'⟩, hfr⟩
    dsimp only at hf3 hg3 hW3 hm3 hr3 hfr
    subst hf3 hg3
    have p1 : l3 "key" = some (.word key) := by rw [hfr _ (by decide)]; exact j1
    have p2 : l3 "klen" = some (.word klen) := by rw [hfr _ (by decide)]; exact j2
    have p3 : l3 "vptr" = some (.word vptr) := by rw [hfr _ (by decide)]; exact j3
    have p4 : l3 "vlen" = some (.word vlen) := by rw [hfr _ (by decide)]; exact j4
    have p5 : l3 "level" = some (.word lv) := by rw [hfr _ (by decide)]; exact j5
    have p6 : l3 "node" = some (.word nd') := by rw [hfr _ (by decide)]; exact j6
    have p7 : l3 "slot" = some (.word sl) := by rw [hfr _ (by decide)]; exact j7
    have p10 : l3 "go" = some (.word gw') := by rw [hfr _ (by decide)]; exact j10
    have p11 : l3 "next_node" = some (.word nn) := by rw [hfr _ (by decide)]; exact j11
    have p12 : l3 "next_slot" = some (.word ns) := by rw [hfr _ (by decide)]; exact j12
    have p13 : l3 "next_level" = some (.word nlv) := by rw [hfr _ (by decide)]; exact j13
    refine WPs.seq_asg (old := nd') (w := nn) p6 (of_eval (by lk [p11])) ?_
    refine WPs.seq_asg (old := sl) (w := ns) (by lk [p7]) (of_eval (by lk [p12])) ?_
    refine WPs.assign (old := lv) (w := nlv) (by lk [p5]) (of_eval (by lk [p13])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨R', nlv, nn, ns, res', gw', hle.trans hle', hW3, rfl,
      fun x hx => (hg2 x hx).trans (hg x hx),
      fun addr ha => ((hm3 addr ha).trans (hm2 addr ha)).trans (hm addr ha),
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p1],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p2],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p3],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p4],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hr3],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p10],
      Or.inl ⟨⟨k', hk', hk0', hkl'⟩, fun hgw' => ?_⟩, fun hgw' => ?_⟩
    · rcases hgo' with h0 | ⟨-, hnn, hnl, hns, hl1, hl2⟩
      · exact absurd h0 hgw'
      · exact hW3.slot_ne hns
    · rcases hgo' with h0 | ⟨-, hnn, hnl, hns, hl1, hl2⟩
      · exact absurd h0 hgw'
      · exact ⟨hl2, hnn, hnl, Or.inr hns⟩
  · -- the loop ends
    rintro a k ⟨R, lv, nd, sl, res, gw, hle, hW', hf, hg, hm, k1, k2, k3, k4, k5, k6, k7, k8, k9,
      hres, hI⟩ hcond
    have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := gw) (by lk [k9]))
      (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hgw : gw = 0#64 := by
      by_contra hne
      simp [evalPanCmp, hne] at hcv
    subst hgw
    exact ⟨⟨R, lv, nd, sl, res, 0#64, hle, hW', hf, hg, hm, k1, k2, k3, k4, k5, k6, k7, k8, k9,
      hres, hI⟩, k9⟩
  · rintro a ⟨⟨R, lv, nd, sl, res, gw, hle, hW', hf, hg, hm, k1, k2, k3, k4, k5, k6, k7, k8, k9,
      hres, hI⟩, hgo0⟩
    have hgw : gw = 0#64 := by
      rw [k9] at hgo0
      simpa using hgo0
    obtain ⟨k, hk, hk0, hkl⟩ : ∃ k, R.Kd res k ∧ k ≠ 0#64 ∧ R.Lv res level.toNat := by
      rcases hres with ⟨h1, -⟩ | ⟨-, h2, -⟩
      · exact h1
      · exact absurd hgw h2
    refine WPs.ret (w := res) (of_eval (by lk [k8])) ?_
    exact ⟨_, a.globals, a.memory, res, R, k, by rw [hf], hle, hk, hk0, hkl, hW', hg, hm⟩

end InitECandidate.Solver.GuestBound
