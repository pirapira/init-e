import InitECandidate.Solver.GuestBound.TrieLoopBranch

/-!
# The insertion loop: an extension node

When the whole segment is a prefix of the remaining key the walk descends to
the extension's child; otherwise the extension is split.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

set_option maxHeartbeats 16000000 in
theorem ins_ext (hE : GuestEnv E) {R0 : Reg} {key klen vptr vlen lv nd sl res : Word}
    (hL : InsLoc s.locals key klen vptr vlen lv nd sl res)
    (hW : WorldTJ R0 s.globals s.memory) (hK : R0.Kd nd 2#64) (hLn : R0.Lv nd lv.toNat)
    (hlv : lv.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, R0.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hQ : ∀ l' g' m', InsMid R0 s.globals s.memory key klen vptr vlen lv sl res l' g' m' →
      Q (.normal l' g' m' s.ffi)) :
    WPs E s (.dec "seg" .one (.load .one (.op .add [.var .local "node", .const 32#64]))
      (.dec "sl" .one (.load .one (.op .add [.var .local "node", .const 40#64]))
        (.decCall "pl" .one "common_prefix_length"
          [.var .local "seg", .var .local "sl",
            .op .add [.var .local "key", .var .local "level"],
            .op .sub [.var .local "klen", .var .local "level"]]
          (.ite (.cmp .equal (.var .local "pl") (.var .local "sl"))
            (.seq (.assign .local "r" (.var .local "node"))
              (.seq (.assign .local "next_node"
                  (.load .one (.op .add [.var .local "node", .const 48#64])))
                (.seq (.assign .local "next_slot" (.op .add [.var .local "node", .const 48#64]))
                  (.seq (.assign .local "next_level"
                      (.op .add [.var .local "level", .var .local "pl"]))
                    (.assign .local "go" (.const 1#64))))))
            (.decCall "br" .one "_split_extension"
              [.var .local "node", .op .add [.var .local "key", .var .local "level"],
                .op .sub [.var .local "klen", .var .local "level"], .var .local "vptr",
                .var .local "vlen", .var .local "pl"]
              (.ite (.cmp .lower (.const 0#64) (.var .local "pl"))
                (.call (some (some (.local, "r"), none)) "node_new_ext"
                  [.var .local "seg", .var .local "pl", .var .local "br"])
                (.assign .local "r" (.var .local "br")))))))) Q := by
  obtain ⟨hNd, hRd, hlo, htop, h8⟩ := hW.kd hK
  obtain ⟨sp, nl0, r1, r2', hc⟩ := hW.seg hNd hRd (Or.inr rfl)
  obtain ⟨sgl, c, r2, hn1, r3, hch⟩ := hW.ext hK
  have e1 : sgl = nl0 := Rd.inj r2 r2'
  subst e1
  obtain ⟨lo, hi, hI, hb1, hb2⟩ : ∃ lo hi, R0.Im lo hi ∧ lo.toNat ≤ sp.toNat ∧
      sp.toNat + sgl.toNat ≤ hi.toNat := by
    rcases hc with h0 | ⟨lo, hi, hI, h1, h2, -⟩
    · rw [h0] at hn1
      simp at hn1
    · exact ⟨lo, hi, hI, h1, h2⟩
  have hhi := hi.isLt
  obtain ⟨e, hrest⟩ := key_rest hlv hkey
  refine WPs.dec (w := sp) (eval_load_rd hE (eval_addc hE 32#64 hL.node) r1) ?_
  refine WPs.dec (w := sgl) (eval_load_rd hE (eval_addc hE 40#64 (by lk [hL.node])) r2) ?_
  refine WPs.decCall_ret (fun vp g m ffi hret => ?_)
  obtain ⟨p, rfl, rfl, rfl, rfl, hp1, hp2⟩ := common_prefix_ret hE hret (a := sp) (al := sgl)
    (b := key + lv) (bl := klen - lv) (of_eval (by lk [])) (of_eval (by lk []))
    (of_eval (by ev [hL.key, hL.level])) (of_eval (by ev [hL.klen, hL.level]))
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qkey : L "key" = some (.word key) := by rw [hLL]; lk [hL.key]
  have qklen : L "klen" = some (.word klen) := by rw [hLL]; lk [hL.klen]
  have qvp : L "vptr" = some (.word vptr) := by rw [hLL]; lk [hL.vptr]
  have qvl : L "vlen" = some (.word vlen) := by rw [hLL]; lk [hL.vlen]
  have qlv : L "level" = some (.word lv) := by rw [hLL]; lk [hL.level]
  have qnode : L "node" = some (.word nd) := by rw [hLL]; lk [hL.node]
  have qslot : L "slot" = some (.word sl) := by rw [hLL]; lk [hL.slot]
  have qres : L "result" = some (.word res) := by rw [hLL]; lk [hL.result]
  have qr : L "r" = some (.word 0#64) := by rw [hLL]; lk [hL.r]
  have qgo : L "go" = some (.word 0#64) := by rw [hLL]; lk [hL.go]
  have qnn : L "next_node" = some (.word 0#64) := by rw [hLL]; lk [hL.nn]
  have qns : L "next_slot" = some (.word 0#64) := by rw [hLL]; lk [hL.ns]
  have qnl : L "next_level" = some (.word 0#64) := by rw [hLL]; lk [hL.nl]
  have qseg : L "seg" = some (.word sp) := by rw [hLL]; lk []
  have qsl : L "sl" = some (.word sgl) := by rw [hLL]; lk []
  have qpl : L "pl" = some (.word p) := by rw [hLL]; lk []
  clear hLL
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  simp only [evalF_local, qpl, qsl, Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · rename_i h0
    -- the key leaves the segment: split
    have hne : p ≠ sgl := by
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    have hlt : p.toNat < sgl.toNat := by
      by_contra hcn
      exact hne (BitVec.eq_of_toNat_eq (by omega))
    refine WPs.decCall_ret (fun vb g1 m1 f1 hret1 => ?_)
    obtain ⟨br, R1, rfl, rfl, hle1, hK1, hLb, hW1, hg1, hm1⟩ := split_ext_ret hE hret1 (node := nd)
      (rk := key + lv) (rl := klen - lv) (vptr := vptr) (vlen := vlen) (pl := p) (sl := sgl)
      (of_eval (by lk [qnode])) (of_eval (by ev [qkey, qlv])) (of_eval (by ev [qklen, qlv]))
      (of_eval (by lk [qvp])) (of_eval (by lk [qvl])) (of_eval (by lk [qpl])) hW hK r2 hlt hp2
      (fun h0 => by
        obtain ⟨lo', hi', hI', h1, h2, h3⟩ := hrest h0
        exact ⟨lo', hi', hI', h1, h2⟩) lv.toNat hLn
    refine WPs.ite_both (fun w2 hw2 => ?_)
    obtain ⟨x, y, hx, hy, hwv2⟩ := cmp_word_inv hE hw2
    rw [eval_const] at hx
    rw [evalF_local] at hy
    simp (config := { decide := true }) [update_lookup, qpl] at hx hy
    subst hx hy
    split
    · rename_i h2
      -- no common prefix: the branch replaces the extension
      have hp0 : p.toNat = 0 := by
        by_contra hne
        have hl : (0#64 : Word) < p := by rw [BitVec.lt_def]; simp; omega
        rw [h2] at hwv2
        simp [evalPanCmp, hl] at hwv2
      rw [hp0, Nat.add_zero] at hLb
      refine WPs.assign (old := 0#64) (w := br) (by lk [qr]) (of_eval (by lk [])) ?_
      simp only [restorePanValueFfiLocal]
      exact hQ _ _ _ ⟨R1, br, 3#64, 0#64, 0#64, 0#64, 0#64, nd, hle1, hW1, hg1, hm1,
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qkey],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qklen],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qvp],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qvl],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qlv],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qnode],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qslot],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup,
          qres],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qr],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qnn],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qns],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qnl],
        hK1, by decide, hLb, Or.inl rfl⟩
    · rename_i h2
      -- a shorter extension on top of the branch
      have hppos : 1 ≤ p.toNat := by
        by_contra hc0
        have hl : ¬ (0#64 : Word) < p := by rw [BitVec.lt_def]; simp; omega
        exact h2 (by rw [hwv2]; simp [evalPanCmp, hl])
      have hI1 : R1.Im lo hi := hle1.Im _ _ hI
      refine WPs.callA_ret (fun ve g2 m2 f2 hret2 => ?_)
      obtain ⟨ex, hvs, rfl, hW2, hg2, hm2⟩ := node_new_ext_ret hE hret2 (nib := sp) (nlen := p)
        (child := br) (of_eval (by lk [qseg])) (of_eval (by lk [qpl])) (of_eval (by lk []))
        hppos (Or.inr (hW1.kd hK1).1) hW1
        ⟨lo, hi, hI1, hb1, by omega, hW1.im_nibs hI1 (p := sp) (c := p.toNat) hb1 (by omega)⟩
        lv.toNat (fun _ => hLb)
      simp only [List.cons.injEq, and_true] at hvs
      subst hvs
      simp only [restorePanValueFfiLocal]
      exact hQ _ _ _ ⟨R1.addNd ex 2#64 lv.toNat (lv.toNat + p.toNat), ex, 2#64, 0#64, 0#64, 0#64,
        0#64, nd, hle1.trans (Reg.Le.addNd R1 ex 2#64 _ _), hW2, fun x hx => (hg2 x hx).trans (hg1 x hx),
        fun addr ha => (hm2 addr ha).trans (hm1 addr ha),
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qkey],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qklen],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qvp],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qvl],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qlv],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qnode],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qslot],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup,
          qres],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qnn],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qns],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qnl],
        Reg.addNd_kd R1 ex 2#64 _ _, by decide, Reg.addNd_lv R1 ex 2#64 _ _, Or.inl rfl⟩
  · rename_i h0
    -- the whole segment matches: descend to the child
    have hpe : p = sgl := by
      by_contra hne
      exact h0 (by rw [hwv]; simp [evalPanCmp, hne])
    subst hpe
    have elp : (lv + p).toNat = lv.toNat + p.toNat := by
      rw [BitVec.toNat_add]
      have := klen.isLt
      omega
    refine WPs.seq_asg (old := 0#64) (w := nd) qr (of_eval (by lk [qnode])) ?_
    refine WPs.seq_asg (old := 0#64) (w := c) (by lk [qnn])
      (eval_load_rd hE (eval_addc hE 48#64 (by lk [qnode])) r3) ?_
    refine WPs.seq_asg (old := 0#64) (w := nd + 48#64) (by lk [qns])
      (of_eval (eval_addc hE 48#64 (by lk [qnode]))) ?_
    refine WPs.seq_asg (old := 0#64) (w := lv + p) (by lk [qnl])
      (of_eval (by ev [qlv, qpl])) ?_
    refine WPs.assign (old := 0#64) (w := 1#64) (by lk [qgo]) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact hQ _ _ _ ⟨R0, nd, 2#64, 1#64, c, nd + 48#64, lv + p, nd, Reg.Le.refl R0, hW,
      fun _ _ => rfl, fun _ _ => rfl,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qkey],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qklen],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qvp],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qvl],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qlv],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qnode],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qslot],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qres],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      hK, by decide, hLn, Or.inr ⟨rfl, hch, fun hc0 => by
        rw [elp]
        exact hW.ext_lv hK (hW.cv_ext hK hLn r2) r3 hc0,
        ⟨nd, by rw [elp]; exact hW.cv_ext hK hLn r2, Or.inl ⟨hK, rfl⟩⟩, by omega, by omega⟩⟩

end InitECandidate.Solver.GuestBound
