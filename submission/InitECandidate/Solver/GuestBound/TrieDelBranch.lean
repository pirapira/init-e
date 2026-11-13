import InitECandidate.Solver.GuestBound.TrieDelPush

/-!
# The descent loop of the delete walk: a branch node

At the end of the key the branch value is cleared and the branch collapsed;
otherwise a record is pushed and the walk descends through the slot selected
by the next nibble.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

set_option maxHeartbeats 16000000 in
theorem dl_branch (hE : GuestEnv E) {Rg R : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {fv lim sp : Word} {ℓ0 : Nat}
    {key klen lv nd topv resv : Word}
    (c : DlCtx Rg R G M fv lim sp ℓ0 key klen lv nd topv resv s)
    (hK : R.Kd nd 3#64) (hLn : R.Lv nd lv.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hQ : ∀ l' g' m' gw' lv', DlS Rg G M fv lim ℓ0 key klen l' g' m' gw' lv' →
      (gw' = 0#64 ∨ lv.toNat < lv'.toNat) → Q (.normal l' g' m' s.ffi)) :
    WPs E s (.ite (.cmp .equal (.var .local "level") (.var .local "klen"))
      (.ite (.cmp .equal (.load .one (.op .add [.var .local "node", .const 168#64]))
          (.const 0#64))
        (.assign .local "res" (.var .local "node"))
        (.seq (.store (.op .add [.var .local "node", .const 160#64]) (.const 0#64))
          (.seq (.store (.op .add [.var .local "node", .const 168#64]) (.const 0#64))
            (.call (some (some (.local, "res"), none)) "_collapse_branch"
              [.var .local "node"]))))
      (.dec "idx" .one (.loadByte (.op .add [.var .local "key", .var .local "level"]))
        (.decCall "fr2" .one "scratch_alloc" [.const 40#64]
          (.seq (.store (.op .add [.var .local "fr2", .const 0#64]) (.var .local "top"))
            (.seq (.store (.op .add [.var .local "fr2", .const 8#64]) (.var .local "node"))
              (.seq (.store (.op .add [.var .local "fr2", .const 16#64]) (.const 3#64))
                (.seq (.store (.op .add [.var .local "fr2", .const 32#64]) (.var .local "idx"))
                  (.seq (.assign .local "top" (.var .local "fr2"))
                    (.seq (.assign .local "node" (.load .one (.op .add [.var .local "node",
                        .const 32#64, .panOp .mul [.var .local "idx", .const 8#64]])))
                      (.seq (.assign .local "level"
                          (.op .add [.var .local "level", .const 1#64]))
                        (.assign .local "go" (.const 1#64)))))))))))) Q := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hL := c.loc
  have hW := c.w
  have hF := c.hF
  have hfs := c.fs
  have hsl := c.sl
  have hlim := lim.isLt
  have hlvk := c.lv
  have hklen := klen.isLt
  obtain ⟨hNd, hRd, hlo, htop, h8⟩ := hW.kd hK
  have hsz3 : nodeSize 3#64 = 176 := by decide
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  rw [evalF_local, hL.level] at hx
  rw [evalF_local, hL.klen] at hy
  simp only [Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · rename_i h0
    -- push a record and descend
    have hne : lv ≠ klen := by
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    have hlt : lv.toNat < klen.toNat := by
      by_contra hc
      exact hne (BitVec.eq_of_toNat_eq (by omega))
    have hk0 : klen ≠ 0#64 := by
      rintro rfl
      simp at hlt
    obtain ⟨lo, hi, hI, h1, h2⟩ := hkey hk0
    have hhi := hi.isLt
    have ekl : (key + lv).toNat = key.toNat + lv.toNat := by
      rw [BitVec.toNat_add]
      omega
    have el1 : (lv + 1#64).toNat = lv.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
      omega
    refine WPs.dec_ev (fun vi hvi => ?_)
    obtain ⟨b, rfl, hb⟩ := loadByte_byteAt hE hvi (addr := key + lv)
      (of_eval (by ev [hL.key, hL.level]))
    obtain ⟨b', hb', h16⟩ := hW.im_nibs hI (p := key + lv) (c := 1) (by omega) (by omega) 0
      (by omega)
    rw [show off (key + lv) 0 = key + lv by simp [off]] at hb'
    have eb : b' = b := by
      rw [hb] at hb'
      exact (Option.some.inj hb').symm
    subst eb
    obtain ⟨cc, hrc, hcc⟩ := hW.slot hK h16
    have eS : (nd + BitVec.ofNat 64 (32 + 8 * b'.toNat)).toNat = nd.toNat + (32 + 8 * b'.toNat) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    refine WPs.decCall_ret (fun vq g1 m1 f1 hret1 => ?_)
    obtain ⟨rfl, rfl, q, rfl, rfl, hq1, hq2, hq8⟩ := scratchalloc_ret hE hret1 (pv := sp)
      (fv := fv) (nv := 40#64) (eval_const _ _) c.gsp c.gfv c.fs
    have hq2' : q.toNat + 40 ≤ sp.toNat := by simpa using hq2
    obtain ⟨c0, c1, c2, c4, hfr⟩ := rec4 s.memory q topv nd 3#64 b' (by omega)
    obtain ⟨hbelow, hprev⟩ := c.below (Reg.Le.refl R) hq2' hfr
    have W4 := hW.scratch (g' := updatePanValueMap s.globals "scratch_ptr" (.word q))
      (fun x hx => by simp [update_lookup, hx]) (fun a ha => hfr a (by omega))
    have rc4 := hrc
    unfold Rd at rc4
    rw [← hfr (nd + BitVec.ofNat 64 (32 + 8 * b'.toNat)) (by omega)] at rc4
    have hq0 : q ≠ 0#64 := by
      rintro rfl
      simp at hq1
      omega
    have hst4 := DelStack.br (R := R) (sp := q) (lim := lim) (ℓ0 := ℓ0) hq0 hq8
      (Nat.le_refl _) (by omega) hprev c0 c1 c2 (by decide) c4 h16 hK hLn hbelow
    rw [← el1] at hst4
    refine WPs.seq_store hE (addr := q + 0#64) (w := topv) (eval_addc hE 0#64 (by lk []))
      (of_eval (by lk [hL.top])) ?_
    refine WPs.seq_store hE (addr := q + 8#64) (w := nd) (eval_addc hE 8#64 (by lk []))
      (of_eval (by lk [hL.node])) ?_
    refine WPs.seq_store hE (addr := q + 16#64) (w := 3#64) (eval_addc hE 16#64 (by lk []))
      (of_eval (eval_const _ _)) ?_
    refine WPs.seq_store hE (addr := q + 32#64) (w := b') (eval_addc hE 32#64 (by lk []))
      (of_eval (by lk [])) ?_
    refine WPs.seq_asg (old := topv) (w := q) (by lk [hL.top]) (of_eval (by lk [])) ?_
    refine WPs.seq_asg (old := nd) (w := cc) (by lk [hL.node])
      (eval_load_inv2 hE (of_eval (eval_slot_idx hE (by lk [hL.node]) (by lk []) h16)) rc4) ?_
    refine WPs.seq_asg (old := lv) (w := lv + 1#64) (by lk [hL.level])
      (of_eval (by ev [hL.level])) ?_
    refine WPs.assign (old := 0#64) (w := 1#64) (by lk [hL.go]) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact hQ _ _ _ 1#64 (lv + 1#64) (c.push (R' := R) (Reg.Le.refl R) (q := q) (nd' := cc)
      (res' := resv) hq1 hq2' W4 (fun x hx => by simp [update_lookup, hx])
      (by simp [update_lookup]) hfr
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.key])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.klen])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.res])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      hst4 (by omega) hcc
      (fun hc0 => by
        rw [el1]
        exact hW.slot_lv hK (hW.cv_br hK hLn) h16 hrc hc0)) (Or.inr (by omega))
  · -- the key ends at this branch
    refine WPs.ite_both (fun w2 _ => ?_)
    split
    · -- clear the value and collapse
      obtain ⟨hin0, hs0⟩ := branch_val_cell (a := nd) (c := 160) (Or.inl rfl) (by omega)
      obtain ⟨hin8, hs8⟩ := branch_val_cell (a := nd) (c := 168) (Or.inr rfl) (by omega)
      have W1 := hW.node_other 0#64 hNd hRd hin0 hs0 (fun hj => by
        rcases hj with hj | hj <;> exact absurd hj (by decide))
      obtain ⟨-, hRd1, -, -, -⟩ := W1.kd hK
      have W2 := W1.node_other 0#64 hNd hRd1 hin8 hs8 (fun hj => by
        rcases hj with hj | hj <;> exact absurd hj (by decide))
      refine WPs.seq_store hE (addr := nd + 160#64) (w := 0#64) (eval_addc hE 160#64 hL.node)
        (of_eval (eval_const _ _)) ?_
      refine WPs.seq_store hE (addr := nd + 168#64) (w := 0#64)
        (eval_addc hE 168#64 (by lk [hL.node])) (of_eval (eval_const _ _)) ?_
      refine WPs.callA_ret (fun v g1 m1 f1 hret => ?_)
      obtain ⟨a, R1, rfl, rfl, hle1, ha, hW1, hg1, hm1⟩ := collapse_branch_ret hE hret
        (node := nd) (ℓ := lv.toNat) (of_eval (by lk [hL.node])) W2 hK hLn
      refine hQ _ _ _ 0#64 lv (c.stop (res' := a) (nd' := nd) hle1 hW1 hg1 (fun addr hA => ?_)
        (by lk [hL.key]) (by lk [hL.klen]) (by lk [hL.level]) (by lk [hL.node]) (by lk [hL.top])
        (by lk []) (by lk [hL.go]) ha) (Or.inl rfl)
      rw [hm1 addr hA]
      show setCell (setCell s.memory (nd + 160#64) 0#64) (nd + 168#64) 0#64 addr = _
      rw [setCell_ne _ (NE (by unfold HBASE at hA hlo; omega)),
        setCell_ne _ (NE (by unfold HBASE at hA hlo; omega))]
    · -- no value here: nothing to delete
      refine WPs.assign (old := resv) (w := nd) hL.res (of_eval (by lk [hL.node])) ?_
      exact hQ _ _ _ 0#64 lv (c.stop (res' := nd) (nd' := nd) (Reg.Le.refl R) hW
        (fun _ _ => rfl) (fun _ _ => rfl) (by lk [hL.key]) (by lk [hL.klen]) (by lk [hL.level])
        (by lk [hL.node]) (by lk [hL.top]) (by lk []) (by lk [hL.go])
        (Or.inr ⟨3#64, hK, by decide, hLn⟩)) (Or.inl rfl)

end InitECandidate.Solver.GuestBound
