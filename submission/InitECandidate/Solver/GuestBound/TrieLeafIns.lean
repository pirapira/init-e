import InitECandidate.Solver.GuestBound.TrieRets

/-!
# `_insert_into_leaf` against the world invariant

Either the leaf's value is replaced in place (same key), or the leaf is split:
a branch with the two remainders, under an extension when the keys share a
prefix. The returned node is registered with a kind other than 0.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A word load from a known address reads a fixed word, if it reads at all. -/
theorem eval_load_any (hE : GuestEnv E) {a : Exp Word} {addr : Word}
    (ha : ∀ y, E.eval s a = some y → y = .word addr) :
    ∃ w : Word, ∀ y, E.eval s (.load .one a) = some y → y = .word w := by
  by_cases hm : ∃ w, Rd s.memory addr w
  · obtain ⟨w, hw⟩ := hm
    exact ⟨w, eval_load_inv2 hE ha hw⟩
  · refine ⟨0#64, fun y hy => ?_⟩
    obtain ⟨addr', w', ha', rfl, hm'⟩ := eval_load_one hE.mem hy
    have := ha _ ha'
    simp only [PanValue.word.injEq] at this
    subst this
    exact absurd ⟨w', hm'⟩ hm

/-- Result of the insertion helpers: a registered node of kind other than 0
at level `L`, in a registry that grew by nodes. -/
def InsQ (Rg : Reg) (s : St σ) (L : Nat) (r : Result σ) : Prop :=
  ∃ l g' m' a R' k, r = .returned l g' m' s.ffi [.word a] ∧ Rg.Le R' ∧ R'.Kd a k ∧ k ≠ 0#64 ∧
    R'.Lv a L ∧ WorldTJ R' g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr

theorem InsQ.restore {Rg : Reg} {s : St σ} {L : Nat} {r : Result σ} (x : VarName)
    (old : Option (PanValue Word)) (h : InsQ Rg s L r) :
    InsQ Rg s L (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g', m', a, R', k, rfl, hq⟩ := h
  exact ⟨_, g', m', a, R', k, rfl, hq⟩

set_option maxHeartbeats 8000000 in
theorem insert_leaf_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_insert_into_leaf" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (node rk rl vptr vlen : Word)
    (hnode : s.locals "node" = some (.word node)) (hrk : s.locals "rk" = some (.word rk))
    (hrl : s.locals "rl" = some (.word rl)) (hvp : s.locals "vptr" = some (.word vptr))
    (hvl : s.locals "vlen" = some (.word vlen)) (hW : WorldTJ Rg s.globals s.memory)
    (hK : Rg.Kd node 1#64)
    (hseg : rl ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ rk.toNat ∧
      rk.toNat + rl.toNat ≤ hi.toNat)
    (L : Nat) (hL : Rg.Lv node L)
    (h : Runs E s body r) : Stopped r ∨ InsQ Rg s L r := by
  have hbody := (fun_of_index 273 hE.functions (by guest_decl_at 273) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (InsQ Rg s L)) r h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  obtain ⟨hNd, hRd, hlo, htop, h8⟩ := hW.kd hK
  have hsz : nodeSize 1#64 = 64 := by decide
  obtain ⟨sp, nl, r1, r2, hc⟩ := hW.seg hNd hRd (Or.inl rfl)
  have e32 : (node + 32#64).toNat = node.toNat + 32 := by bv_omega
  have e40 : (node + 40#64).toNat = node.toNat + 40 := by bv_omega
  have e48 : (node + 48#64).toNat = node.toNat + 48 := by bv_omega
  have e56 : (node + 56#64).toNat = node.toNat + 56 := by bv_omega
  refine WPs.dec (w := sp) (eval_load_rd hE (eval_addc hE 32#64 hnode) r1) ?_
  refine WPs.conseq (Q' := InsQ Rg s L) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := nl) (eval_load_rd hE (eval_addc hE 40#64 (by lk [hnode])) r2) ?_
  refine WPs.conseq (Q' := InsQ Rg s L) ?_ (fun r h => h.restore _ _)
  generalize hL2 : updatePanValueMap (updatePanValueMap s.locals "ek" (.word sp)) "el"
    (.word nl) = L2
  have qnode : L2 "node" = some (.word node) := by rw [← hL2]; lk [hnode]
  have qrk : L2 "rk" = some (.word rk) := by rw [← hL2]; lk [hrk]
  have qrl : L2 "rl" = some (.word rl) := by rw [← hL2]; lk [hrl]
  have qvp : L2 "vptr" = some (.word vptr) := by rw [← hL2]; lk [hvp]
  have qvl : L2 "vlen" = some (.word vlen) := by rw [← hL2]; lk [hvl]
  have qek : L2 "ek" = some (.word sp) := by rw [← hL2]; lk []
  have qel : L2 "el" = some (.word nl) := by rw [← hL2]; lk []
  refine WPs.seqG (fun a => a.globals = s.globals ∧ a.memory = s.memory ∧ a.ffi = s.ffi ∧
      ∀ x, x ≠ "eq" → a.locals x = L2 x) (WPs.ite_both (fun w hw => ?_)) ?_
  · split
    · exact WPs.skip ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
    · refine WPs.decCall_word (fun e g m ffi hret => ?_)
      obtain ⟨rfl, rfl, rfl⟩ := CalleeRet.quiet
        (keepFn_sound (quietKeeper E) hE.functions 1 "memeq" memeq_quiet) hret
      refine WPs.ite_both (fun w2 hw2 => ?_)
      split
      · refine WPs.skip ?_
        simp only [restorePanValueFfiLocal]
        exact ⟨trivial, trivial, trivial,
          fun x hx => by simp [restorePanValueLocal, update_lookup, hx]⟩
      · -- same key: replace the value
        have hin48 : node.toNat ≤ (node + 48#64).toNat ∧
            (node + 48#64).toNat + 8 ≤ node.toNat + nodeSize 1#64 := by omega
        have hin56 : node.toNat ≤ (node + 56#64).toNat ∧
            (node + 56#64).toNat + 8 ≤ node.toNat + nodeSize 1#64 := by omega
        have hs48 : ¬ StructCell node 1#64 (node + 48#64) := by
          rintro (h | ⟨hk, -⟩ | ⟨hk, -⟩)
          · have := congrArg BitVec.toNat h
            omega
          · exact absurd hk (by decide)
          · exact absurd hk (by decide)
        have hs56 : ¬ StructCell node 1#64 (node + 56#64) := by
          rintro (h | ⟨hk, -⟩ | ⟨hk, -⟩)
          · have := congrArg BitVec.toNat h
            omega
          · exact absurd hk (by decide)
          · exact absurd hk (by decide)
        have W1 := hW.node_other vptr hNd hRd hin48 hs48
          (fun _ => ⟨NE (by omega), NE (by omega)⟩)
        obtain ⟨-, hRd1, -, -, -⟩ := W1.kd hK
        have W2 := W1.node_other vlen hNd hRd1 hin56 hs56
          (fun _ => ⟨NE (by omega), NE (by omega)⟩)
        refine WPs.seq_store hE (addr := node + 48#64) (w := vptr)
          (eval_addc hE 48#64 (by lk [qnode])) (of_eval (by lk [qvp])) ?_
        refine WPs.seq_store hE (addr := node + 56#64) (w := vlen)
          (eval_addc hE 56#64 (by lk [qnode])) (of_eval (by lk [qvl])) ?_
        refine WPs.ret (w := node) (of_eval (by lk [qnode])) ?_
        simp only [restorePanValueFfiLocal]
        refine ⟨_, _, _, node, Rg, 1#64, rfl, Reg.Le.refl Rg, hK, by decide, hL, W2,
          fun _ _ => rfl, fun addr ha => ?_⟩
        show setCell (setCell s.memory (node + 48#64) vptr) (node + 56#64) vlen addr = _
        rw [setCell_ne _ (NE (by unfold HBASE at ha hlo; omega)),
          setCell_ne _ (NE (by unfold HBASE at ha hlo; omega))]
  rintro ⟨la, ga, ma, fa⟩ ⟨hga, hma, hfa, hla⟩
  dsimp only at hga hma hfa hla
  subst hga hma hfa
  have pnode : la "node" = some (.word node) := by rw [hla _ (by decide)]; exact qnode
  have prk : la "rk" = some (.word rk) := by rw [hla _ (by decide)]; exact qrk
  have prl : la "rl" = some (.word rl) := by rw [hla _ (by decide)]; exact qrl
  have pvp : la "vptr" = some (.word vptr) := by rw [hla _ (by decide)]; exact qvp
  have pvl : la "vlen" = some (.word vlen) := by rw [hla _ (by decide)]; exact qvl
  have pek : la "ek" = some (.word sp) := by rw [hla _ (by decide)]; exact qek
  have pel : la "el" = some (.word nl) := by rw [hla _ (by decide)]; exact qel
  refine WPs.decCall_ret (fun vp g m ffi hret => ?_)
  obtain ⟨p, rfl, rfl, rfl, rfl, hp1, hp2⟩ := common_prefix_ret hE hret (a := sp) (al := nl)
    (b := rk) (bl := rl) (of_eval (by lk [pek])) (of_eval (by lk [pel])) (of_eval (by lk [prk]))
    (of_eval (by lk [prl]))
  refine WPs.conseq (Q' := InsQ Rg s L) ?_ (fun r h => h.restore _ _)
  -- the leaf's segment, when it is not empty
  have hblk : nl ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ sp.toNat ∧
      sp.toNat + nl.toNat ≤ hi.toNat := by
    intro hnl
    rcases hc with h0 | ⟨lo, hi, hI, h1, h2, -⟩
    · exact absurd h0 hnl
    · exact ⟨lo, hi, hI, h1, h2⟩
  have enp : (nl - p).toNat = nl.toNat - p.toNat := by
    rw [BitVec.toNat_sub]
    omega
  have erp : (rl - p).toNat = rl.toNat - p.toNat := by
    rw [BitVec.toNat_sub]
    omega
  have hseg1 : nl - p ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ (sp + p).toNat ∧
      (sp + p).toNat + (nl - p).toNat ≤ hi.toNat := by
    intro hne
    have hnl : nl ≠ 0#64 := by
      rintro rfl
      exact hne (BitVec.eq_of_toNat_eq (by rw [enp]; simp))
    obtain ⟨lo, hi, hI, h1, h2⟩ := hblk hnl
    have := hi.isLt
    have esp : (sp + p).toNat = sp.toNat + p.toNat := by
      rw [BitVec.toNat_add]
      omega
    exact ⟨lo, hi, hI, by omega, by omega⟩
  have hseg2 : rl - p ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ (rk + p).toNat ∧
      (rk + p).toNat + (rl - p).toNat ≤ hi.toNat := by
    intro hne
    have hnl : rl ≠ 0#64 := by
      rintro rfl
      exact hne (BitVec.eq_of_toNat_eq (by rw [erp]; simp))
    obtain ⟨lo, hi, hI, h1, h2⟩ := hseg hnl
    have := hi.isLt
    have esp : (rk + p).toNat = rk.toNat + p.toNat := by
      rw [BitVec.toNat_add]
      omega
    exact ⟨lo, hi, hI, by omega, by omega⟩
  obtain ⟨v1, hv1⟩ := eval_load_any hE (s := ⟨updatePanValueMap la "pl" (.word p), s.globals,
    s.memory, s.ffi⟩) (a := .op .add [.var .local "node", .const 48#64]) (addr := node + 48#64)
    (of_eval (eval_addc hE 48#64 (by lk [pnode])))
  obtain ⟨vl1, hvl1⟩ := eval_load_any hE (s := ⟨updatePanValueMap la "pl" (.word p), s.globals,
    s.memory, s.ffi⟩) (a := .op .add [.var .local "node", .const 56#64]) (addr := node + 56#64)
    (of_eval (eval_addc hE 56#64 (by lk [pnode])))
  refine WPs.decCall_ret (fun vb g m ffi hret => ?_)
  obtain ⟨br, R1, rfl, rfl, hle1, hK1, hLb, hW1, hg1, hm1⟩ := create_branch_ret hE hret
    (k1 := sp + p) (l1 := nl - p) (v1 := v1) (vl1 := vl1) (k2 := rk + p) (l2 := rl - p)
    (v2 := vptr) (vl2 := vlen) (of_eval (by ev [pek])) (of_eval (by ev [pel])) hv1 hvl1
    (of_eval (by ev [prk])) (of_eval (by ev [prl])) (of_eval (by lk [pvp]))
    (of_eval (by lk [pvl])) hW hseg1 hseg2 (L + p.toNat)
  refine WPs.conseq (Q' := InsQ Rg s L) ?_ (fun r h => h.restore _ _)
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap (updatePanValueMap la "pl" (.word p)) "br"
      (.word br), g, m, s.ffi⟩ ∧ p.toNat = 0) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    rw [eval_const] at hx
    rw [evalF_local] at hy
    simp (config := { decide := true }) [update_lookup] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      by_contra hne
      have hl : (0#64 : Word) < p := by rw [BitVec.lt_def]; simp; omega
      rw [h0] at hwv
      simp [evalPanCmp, hl] at hwv
    · rename_i h0
      have hppos : 1 ≤ p.toNat := by
        by_contra hc0
        have hl : ¬ (0#64 : Word) < p := by rw [BitVec.lt_def]; simp; omega
        exact h0 (by rw [hwv]; simp [evalPanCmp, hl])
      have hnl : nl ≠ 0#64 := by
        rintro rfl
        simp at hp1
        omega
      obtain ⟨lo, hi, hI, h1, h2⟩ := hblk hnl
      have hI1 : R1.Im lo hi := hle1.Im _ _ hI
      refine WPs.tail_call (fun vs g2 m2 f2 hret2 l => ?_)
      obtain ⟨a, rfl, rfl, hW2, hg2, hm2⟩ := node_new_ext_ret hE hret2 (nib := sp) (nlen := p)
        (child := br) (of_eval (by lk [pek])) (of_eval (by lk [])) (of_eval (by lk [])) hppos
        (Or.inr (hW1.kd hK1).1) hW1
        ⟨lo, hi, hI1, h1, by omega, hW1.im_nibs hI1 (p := sp) (c := p.toNat) h1 (by omega)⟩
        L (fun _ => hLb)
      exact ⟨l, g2, m2, a, R1.addNd a 2#64 L (L + p.toNat), 2#64, rfl,
        hle1.trans (Reg.Le.addNd R1 a 2#64 L (L + p.toNat)),
        Reg.addNd_kd R1 a 2#64 L (L + p.toNat), by decide,
        Reg.addNd_lv R1 a 2#64 L (L + p.toNat), hW2, fun x hx => (hg2 x hx).trans (hg1 x hx),
        fun addr ha => (hm2 addr ha).trans (hm1 addr ha)⟩
  · rintro _ ⟨rfl, hp0⟩
    refine WPs.ret (w := br) (of_eval (by lk [])) ?_
    have e0 : L + p.toNat = L := by omega
    rw [e0] at hLb
    exact ⟨_, g, m, br, R1, 3#64, rfl, hle1, hK1, by decide, hLb, hW1, hg1, hm1⟩

end InitECandidate.Solver.GuestBound
