import InitECandidate.Solver.GuestBound.TrieLeafIns
import InitECandidate.Solver.GuestBound.ResolveStep

/-!
# `_split_extension` against the world invariant

An extension whose segment diverges from the key at offset `pl` (below the
segment length) is replaced by a branch: the rest of the segment hangs under
the nibble `seg[pl]` (directly, or through a shorter extension), and the new
value goes to the branch's value slot or to a new leaf under `rk[pl]`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Name the locals of the current state. -/
theorem WPs.name_locals {p : Prog Word}
    (h : ∀ L, L = s.locals → WPs E ⟨L, s.globals, s.memory, s.ffi⟩ p Q) : WPs E s p Q :=
  h s.locals rfl

/-- Result of `_split_extension`: a registered branch. -/
def BrQ (Rg : Reg) (s : St σ) (Lb : Nat) (r : Result σ) : Prop :=
  ∃ l g' m' a R', r = .returned l g' m' s.ffi [.word a] ∧ Rg.Le R' ∧ R'.Kd a 3#64 ∧
    R'.Lv a Lb ∧ WorldTJ R' g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr

theorem BrQ.restore {Rg : Reg} {s : St σ} {Lb : Nat} {r : Result σ} (x : VarName)
    (old : Option (PanValue Word)) (h : BrQ Rg s Lb r) :
    BrQ Rg s Lb (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g', m', a, R', rfl, hq⟩ := h
  exact ⟨_, g', m', a, R', rfl, hq⟩

set_option maxHeartbeats 16000000 in
theorem split_ext_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_split_extension" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (node rk rl vptr vlen pl sl : Word)
    (hnode : s.locals "node" = some (.word node)) (hrk : s.locals "rk" = some (.word rk))
    (hrl : s.locals "rl" = some (.word rl)) (hvp : s.locals "vptr" = some (.word vptr))
    (hvl : s.locals "vlen" = some (.word vlen)) (hpl : s.locals "pl" = some (.word pl))
    (hW : WorldTJ Rg s.globals s.memory) (hK : Rg.Kd node 2#64)
    (hsl : Rd s.memory (node + 40#64) sl) (hlt : pl.toNat < sl.toNat)
    (hprl : pl.toNat ≤ rl.toNat)
    (hseg : rl ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ rk.toNat ∧
      rk.toNat + rl.toNat ≤ hi.toNat)
    (ℓ0 : Nat) (hL0 : Rg.Lv node ℓ0)
    (h : Runs E s body r) : Stopped r ∨ BrQ Rg s (ℓ0 + pl.toNat) r := by
  have hbody := (fun_of_index 274 hE.functions (by guest_decl_at 274) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (BrQ Rg s (ℓ0 + pl.toNat))) r h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have off0 : ∀ a : Word, off a 0 = a := fun a => by simp [off]
  obtain ⟨hNd, hRd, hlo, htop, h8⟩ := hW.kd hK
  obtain ⟨sp, nl0, r1, r2', hc⟩ := hW.seg hNd hRd (Or.inr rfl)
  obtain ⟨nl, c, r2, hn1, r3, hch⟩ := hW.ext hK
  have e1 : sl = nl0 := Rd.inj hsl r2'
  subst e1
  obtain ⟨lo, hi, hI, hb1, hb2⟩ : ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ sp.toNat ∧
      sp.toNat + sl.toNat ≤ hi.toNat := by
    rcases hc with h0 | ⟨lo, hi, hI, h1, h2, -⟩
    · rw [h0] at hlt
      simp at hlt
    · exact ⟨lo, hi, hI, h1, h2⟩
  have hhi := hi.isLt
  have hcN : c = 0#64 ∨ Rg.Nd c := by
    rcases hch with h0 | ⟨k, hk⟩
    · exact Or.inl h0
    · exact Or.inr (hW.kd hk).1
  refine WPs.dec (w := sp) (eval_load_rd hE (eval_addc hE 32#64 hnode) r1) ?_
  refine WPs.conseq (Q' := BrQ Rg s (ℓ0 + pl.toNat)) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := sl) (eval_load_rd hE (eval_addc hE 40#64 (by lk [hnode])) hsl) ?_
  refine WPs.conseq (Q' := BrQ Rg s (ℓ0 + pl.toNat)) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := c) (eval_load_rd hE (eval_addc hE 48#64 (by lk [hnode])) r3) ?_
  refine WPs.conseq (Q' := BrQ Rg s (ℓ0 + pl.toNat)) ?_ (fun r h => h.restore _ _)
  refine WPs.decCall_ret (fun vb g1 m1 f1 hret => ?_)
  have hcvn : Rg.Cv node (ℓ0 + sl.toNat) := hW.cv_ext hK hL0 hsl
  have hcl : c ≠ 0#64 → Rg.Lv c (ℓ0 + sl.toNat) := fun hc0 => hW.ext_lv hK hcvn r3 hc0
  obtain ⟨br, rfl, rfl, hW1, hg1, hm1⟩ := node_new_branch_ret hE hret hW (ℓ0 + pl.toNat)
  refine WPs.conseq (Q' := BrQ Rg s (ℓ0 + pl.toNat)) ?_ (fun r h => h.restore _ _)
  have esal : (sl - pl).toNat = sl.toNat - pl.toNat := by
    rw [BitVec.toNat_sub]
    omega
  refine WPs.dec (w := sl - pl) (of_eval (by ev [hpl])) ?_
  refine WPs.conseq (Q' := BrQ Rg s (ℓ0 + pl.toNat)) ?_ (fun r h => h.restore _ _)
  refine WPs.name_locals (fun L hL => ?_)
  dsimp only at hL
  have qnode : L "node" = some (.word node) := by rw [hL]; lk [hnode]
  have qrk : L "rk" = some (.word rk) := by rw [hL]; lk [hrk]
  have qrl : L "rl" = some (.word rl) := by rw [hL]; lk [hrl]
  have qvp : L "vptr" = some (.word vptr) := by rw [hL]; lk [hvp]
  have qvl : L "vlen" = some (.word vlen) := by rw [hL]; lk [hvl]
  have qpl : L "pl" = some (.word pl) := by rw [hL]; lk [hpl]
  have qseg : L "seg" = some (.word sp) := by rw [hL]; lk []
  have qchild : L "child" = some (.word c) := by rw [hL]; lk []
  have qbr : L "br" = some (.word br) := by rw [hL]; lk []
  have qsal : L "sal" = some (.word (sl - pl)) := by rw [hL]; lk []
  clear hL
  have hK1 : (Rg.addNd br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)).Kd br 3#64 :=
    Reg.addNd_kd Rg br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)
  have hcvb : (Rg.addNd br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)).Cv br (ℓ0 + pl.toNat + 1) :=
    Reg.addNd_cv Rg br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)
  have hI1 : (Rg.addNd br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)).Im lo hi := hI
  have hcN1 : c = 0#64 ∨ (Rg.addNd br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)).Nd c := hcN.imp id Or.inl
  have esp : (sp + pl).toNat = sp.toNat + pl.toNat := by
    rw [BitVec.toNat_add]
    omega
  have hszb : nodeSize 3#64 = 176 := by decide
  -- the old child under `seg[pl]`, when one nibble remains
  refine WPs.seqG (fun a => ∃ m', a = ⟨L, g1, m', s.ffi⟩ ∧ WorldTJ (Rg.addNd br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)) g1 m' ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr) (WPs.ite_both (fun w hw => ?_)) ?_
  · split
    · exact WPs.skip ⟨m1, rfl, hW1, hm1⟩
    · rename_i h0
      obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
      simp only [evalF_local, eval_const, qsal, Option.some.injEq, PanValue.word.injEq] at hx hy
      subst hx hy
      have hsal1 : sl.toNat - pl.toNat = 1 := by
        by_contra hne
        have hne' : sl - pl ≠ 1#64 := fun e => hne (by rw [← esal, e]; rfl)
        exact h0 (by rw [hwv]; simp [evalPanCmp, hne'])
      obtain ⟨hNdb, hRdb, hlob, htopb, -⟩ := hW1.kd hK1
      obtain ⟨b0, hb0, h16⟩ := hW1.im_nibs hI1 (p := sp + pl) (c := 1) (by omega) (by omega) 0
        (by omega)
      rw [off0] at hb0
      have eS : (br + BitVec.ofNat 64 (32 + 8 * b0.toNat)).toNat =
          br.toNat + (32 + 8 * b0.toNat) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      refine WPs.last (WPs.seq_store_inv hE (addr := br + BitVec.ofNat 64 (32 + 8 * b0.toNat))
        (w := c) (eval_slot_addr hE qbr (of_eval (by ev [qseg, qpl])) hb0 h16)
        (of_eval (by lk [qchild])) ?_)
      refine WPs.skip ⟨_, rfl, hW1.node_child hNdb hRdb (Or.inr ⟨rfl, b0.toNat, h16, rfl⟩) hcN1
          (fun ℓc' hcv' hc0 => by
            have := hW1.cv_unique hcv' hcvb
            subst this
            have hlc := hcl hc0
            rw [show ℓ0 + sl.toNat = ℓ0 + pl.toNat + 1 by omega] at hlc
            exact Or.inl hlc),
        fun addr ha => ?_⟩
      show setCell m1 _ _ addr = _
      rw [setCell_ne _ (NE (by unfold HBASE at ha hlob; omega))]
      exact hm1 addr ha
  rintro _ ⟨m2, rfl, hW2, hm2⟩
  -- a shorter extension under `seg[pl]`, when more remain
  refine WPs.seqG (fun a => ∃ R', (Rg.addNd br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)).Le R' ∧ WorldTJ R' a.globals a.memory ∧
      a.ffi = s.ffi ∧ (∀ x, x ≠ "ex" → a.locals x = L x) ∧
      (∀ x, x ≠ "heap_ptr" → a.globals x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        a.memory addr = s.memory addr) (WPs.ite_both (fun w hw => ?_)) ?_
  · split
    · exact WPs.skip ⟨_, Reg.Le.refl _, hW2, rfl, fun _ _ => rfl, hg1, hm2⟩
    · rename_i h0
      obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
      simp only [evalF_local, eval_const, qsal, Option.some.injEq, PanValue.word.injEq] at hx hy
      subst hx hy
      have hsal2 : 2 ≤ sl.toNat - pl.toNat := by
        by_contra hc0
        have hl : ¬ (1#64 : Word) < sl - pl := by
          rw [BitVec.lt_def, esal]
          simp
          omega
        exact h0 (by rw [hwv]; simp [evalPanCmp, hl])
      have e1 : (sp + (pl + 1#64)).toNat = sp.toNat + pl.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
        omega
      have e2 : (sl - pl - 1#64).toNat = sl.toNat - pl.toNat - 1 := by
        rw [BitVec.toNat_sub, esal, show (1#64 : Word).toNat = 1 by decide]
        omega
      refine WPs.decCall_ret (fun ve g3 m3 f3 hret3 => ?_)
      obtain ⟨ex, hvs, rfl, hW3, hg3, hm3⟩ := node_new_ext_ret hE hret3
        (nib := sp + (pl + 1#64)) (nlen := sl - pl - 1#64) (child := c)
        (of_eval (by ev [qseg, qpl])) (of_eval (by ev [qsal])) (of_eval (by lk [qchild]))
        (by omega) hcN1 hW2
        ⟨lo, hi, hI1, by omega, by omega,
          hW2.im_nibs hI1 (p := sp + (pl + 1#64)) (c := (sl - pl - 1#64).toNat) (by omega)
            (by omega)⟩
        (ℓ0 + pl.toNat + 1) (fun hc0 => by
          have hlc := hcl hc0
          rw [show ℓ0 + sl.toNat = ℓ0 + pl.toNat + 1 + (sl - pl - 1#64).toNat by omega] at hlc
          exact Or.inl hlc)
      simp only [List.cons.injEq, and_true] at hvs
      subst hvs
      have hK3 : ((Rg.addNd br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)).addNd ex 2#64 (ℓ0 + pl.toNat + 1) (ℓ0 + pl.toNat + 1 + (sl - pl - 1#64).toNat)).Kd br 3#64 := Or.inl hK1
      obtain ⟨hNdb, hRdb, hlob, htopb, -⟩ := hW3.kd hK3
      obtain ⟨b0, hb0, h16⟩ := hW3.im_nibs (Rg := (Rg.addNd br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)).addNd ex 2#64 (ℓ0 + pl.toNat + 1) (ℓ0 + pl.toNat + 1 + (sl - pl - 1#64).toNat)) hI1
        (p := sp + pl) (c := 1) (by omega) (by omega) 0 (by omega)
      rw [off0] at hb0
      have eS : (br + BitVec.ofNat 64 (32 + 8 * b0.toNat)).toNat =
          br.toNat + (32 + 8 * b0.toNat) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      refine WPs.last (WPs.seq_store_inv hE (addr := br + BitVec.ofNat 64 (32 + 8 * b0.toNat))
        (w := ex) (eval_slot_addr hE (by lk [qbr]) (of_eval (by ev [qseg, qpl])) hb0 h16)
        (of_eval (by lk [])) ?_)
      refine WPs.skip ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨_, Reg.Le.addNd _ ex 2#64 _ _,
        hW3.node_child hNdb hRdb (Or.inr ⟨rfl, b0.toNat, h16, rfl⟩)
          (Or.inr (hW3.kd (Reg.addNd_kd _ ex 2#64 _ _)).1)
          (fun ℓc' hcv' _ => by
            have := hW3.cv_unique hcv' (Or.inl hcvb)
            subst this
            exact Reg.addNd_lv _ ex 2#64 _ _), by first | rfl | trivial,
        fun x hx => by simp [restorePanValueLocal, update_lookup, hx],
        fun x hx => (hg3 x hx).trans (hg1 x hx), fun addr ha => ?_⟩
      show setCell m3 _ _ addr = _
      rw [setCell_ne _ (NE (by unfold HBASE at ha hlob; omega))]
      exact (hm3 addr ha).trans (hm2 addr ha)
  rintro ⟨la, ga, ma, fa⟩ ⟨R2, hle2, hW4, hfa, hla, hga, hma⟩
  dsimp only at hW4 hfa hla hga hma
  subst hfa
  have prk : la "rk" = some (.word rk) := by rw [hla _ (by decide)]; exact qrk
  have prl : la "rl" = some (.word rl) := by rw [hla _ (by decide)]; exact qrl
  have pvp : la "vptr" = some (.word vptr) := by rw [hla _ (by decide)]; exact qvp
  have pvl : la "vlen" = some (.word vlen) := by rw [hla _ (by decide)]; exact qvl
  have ppl : la "pl" = some (.word pl) := by rw [hla _ (by decide)]; exact qpl
  have pbr : la "br" = some (.word br) := by rw [hla _ (by decide)]; exact qbr
  have erl : (rl - pl).toNat = rl.toNat - pl.toNat := by
    rw [BitVec.toNat_sub]
    omega
  have hK2 : R2.Kd br 3#64 := hle2.Kd _ _ hK1
  refine WPs.dec (w := rl - pl) (of_eval (by ev [prl, ppl])) ?_
  refine WPs.conseq (Q' := BrQ Rg s (ℓ0 + pl.toNat)) ?_ (fun r h => h.restore _ _)
  refine WPs.seqG (fun a => ∃ R', R2.Le R' ∧ WorldTJ R' a.globals a.memory ∧ a.ffi = s.ffi ∧
      a.locals "br" = some (.word br) ∧ (∀ x, x ≠ "heap_ptr" → a.globals x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        a.memory addr = s.memory addr) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    simp (config := { decide := true }) [evalF_local, eval_const, update_lookup] at hx hy
    subst hx hy
    obtain ⟨hNdb, hRdb, hlob, htopb, -⟩ := hW4.kd hK2
    split
    · rename_i h0
      -- a new leaf under `rk[pl]`
      have hkal : 1 ≤ rl.toNat - pl.toNat := by
        by_contra hc0
        have : rl - pl = 0#64 := BitVec.eq_of_toNat_eq (by rw [erl]; simp; omega)
        rw [h0, this] at hwv
        simp [evalPanCmp] at hwv
      have hrl0 : rl ≠ 0#64 := by
        rintro rfl
        simp at hkal
      obtain ⟨lo2, hi2, hI2, hc1, hc2⟩ := hseg hrl0
      have hI2' : R2.Im lo2 hi2 := by rw [hle2.Im]; exact hI2
      have hhi2 := hi2.isLt
      have erk : (rk + pl).toNat = rk.toNat + pl.toNat := by
        rw [BitVec.toNat_add]
        omega
      have e1 : (rk + (pl + 1#64)).toNat = rk.toNat + pl.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
        omega
      have e2 : (rl - pl - 1#64).toNat = rl.toNat - pl.toNat - 1 := by
        rw [BitVec.toNat_sub, erl, show (1#64 : Word).toNat = 1 by decide]
        omega
      refine WPs.dec_ev (fun vi hvi => ?_)
      obtain ⟨b1, rfl, hb1⟩ := loadByte_byteAt hE hvi (addr := rk + pl)
        (of_eval (by ev [prk, ppl]))
      obtain ⟨b1', hb1', h16⟩ := hW4.im_nibs hI2' (p := rk + pl) (c := 1) (by omega) (by omega)
        0 (by omega)
      rw [off0] at hb1'
      have eb : b1' = b1 := by
        have hb1m : byteAt ma (rk + pl) = some b1 := hb1
        rw [hb1m] at hb1'
        exact (Option.some.inj hb1').symm
      subst eb
      have eS : (br + BitVec.ofNat 64 (32 + 8 * b1'.toNat)).toNat =
          br.toNat + (32 + 8 * b1'.toNat) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      refine WPs.seqG (fun a => a = ⟨updatePanValueMap (updatePanValueMap la "kal"
          (.word (rl - pl))) "idx" (.word b1'), ga, ma, s.ffi⟩)
        (WPs.ite_both (fun w2 _ => ?_)) ?_
      · split
        · exact WPs.skip rfl
        · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
      rintro _ rfl
      refine WPs.decCall_ret (fun vlf g5 m5 f5 hret5 => ?_)
      obtain ⟨lf, rfl, rfl, hW5, hg5, hm5⟩ := node_new_leaf_ret hE hret5
        (nib := rk + (pl + 1#64)) (nlen := rl - pl - 1#64) (vptr := vptr) (vlen := vlen)
        (of_eval (by ev [prk, ppl])) (of_eval (by ev [])) (of_eval (by lk [pvp]))
        (of_eval (by lk [pvl])) hW4
        (Or.inr ⟨lo2, hi2, hI2', by omega, by omega,
          hW4.im_nibs hI2' (p := rk + (pl + 1#64)) (c := (rl - pl - 1#64).toNat) (by omega)
            (by omega)⟩) (ℓ0 + pl.toNat + 1)
      have hK5 : (R2.addNd lf 1#64 (ℓ0 + pl.toNat + 1) (ℓ0 + pl.toNat + 1)).Kd br 3#64 :=
        Or.inl hK2
      obtain ⟨hNdb5, hRdb5, -, -, -⟩ := hW5.kd hK5
      refine WPs.last (WPs.seq_store_inv hE (addr := br + BitVec.ofNat 64 (32 + 8 * b1'.toNat))
        (w := lf) (of_eval (eval_slot_idx hE (by lk [pbr]) (by lk []) h16))
        (of_eval (by lk [])) ?_)
      refine WPs.skip ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨_, Reg.Le.addNd R2 lf 1#64 _ _,
        hW5.node_child hNdb5 hRdb5 (Or.inr ⟨rfl, b1'.toNat, h16, rfl⟩)
          (Or.inr (hW5.kd (Reg.addNd_kd R2 lf 1#64 _ _)).1)
          (fun ℓc' hcv' _ => by
            have := hW5.cv_unique hcv' (Or.inl (hle2.Cv _ _ hcvb))
            subst this
            exact Reg.addNd_lv R2 lf 1#64 _ _), by first | rfl | trivial,
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, pbr],
        fun x hx => (hg5 x hx).trans (hga x hx), fun addr ha => ?_⟩
      show setCell m5 _ _ addr = _
      rw [setCell_ne _ (NE (by unfold HBASE at ha hlob; omega))]
      exact (hm5 addr ha).trans (hma addr ha)
    · -- the key ends here: the branch's value slot
      obtain ⟨hin0, hs0⟩ := branch_val_cell (a := br) (c := 160) (Or.inl rfl) (by omega)
      obtain ⟨hin8, hs8⟩ := branch_val_cell (a := br) (c := 168) (Or.inr rfl) (by omega)
      have W1 := hW4.node_other vptr hNdb hRdb hin0 hs0 (fun hj => by
        rcases hj with hj | hj <;> exact absurd hj (by decide))
      obtain ⟨-, hRdb1, -, -, -⟩ := W1.kd hK2
      have W2 := W1.node_other vlen hNdb hRdb1 hin8 hs8 (fun hj => by
        rcases hj with hj | hj <;> exact absurd hj (by decide))
      refine WPs.seq_store hE (addr := br + 160#64) (w := vptr)
        (eval_addc hE 160#64 (by lk [pbr])) (of_eval (by lk [pvp])) ?_
      refine WPs.store hE (addr := br + 168#64) (w := vlen) (eval_addc hE 168#64 (by lk [pbr]))
        (of_eval (by lk [pvl])) ?_
      refine ⟨R2, Reg.Le.refl R2, W2, rfl, by lk [pbr], hga, fun addr ha => ?_⟩
      show setCell (setCell ma (br + 160#64) vptr) (br + 168#64) vlen addr = _
      rw [setCell_ne _ (NE (by unfold HBASE at ha hlob; omega)),
        setCell_ne _ (NE (by unfold HBASE at ha hlob; omega))]
      exact hma addr ha
  rintro ⟨lb, gb, mb, fb⟩ ⟨R3, hle3, hW6, hfb, hlbr, hgb, hmb⟩
  dsimp only at hW6 hfb hlbr hgb hmb
  subst hfb
  refine WPs.ret (w := br) (of_eval (by rw [evalF_local]; exact hlbr)) ?_
  exact ⟨_, gb, mb, br, R3, rfl, (Reg.Le.addNd Rg br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1)).trans (hle2.trans hle3),
    hle3.Kd _ _ hK2, hle3.Lv _ _ (hle2.Lv _ _ (Reg.addNd_lv Rg br 3#64 (ℓ0 + pl.toNat) (ℓ0 + pl.toNat + 1))), hW6, hgb,
    hmb⟩

end InitECandidate.Solver.GuestBound
