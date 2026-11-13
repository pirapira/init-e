import InitECandidate.Solver.GuestBound.TrieLoopDefs

/-!
# The insertion loop: a branch node

At the end of the key the value goes to the branch's value cells; otherwise
the walk descends through the child slot selected by the next nibble.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `x = e; rest` for a word-valued local. -/
theorem WPs.seq_asg {x : VarName} {e : Exp Word} {q : Prog Word} {w old : Word}
    (hx : s.locals x = some (.word old)) (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : WPs E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩ q Q) :
    WPs E s (.seq (.assign .local x e) q) Q :=
  WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩)
    (WPs.assign hx he rfl) (fun _ h' => h' ▸ h)

set_option maxHeartbeats 8000000 in
theorem ins_branch (hE : GuestEnv E) {R0 : Reg} {key klen vptr vlen lv nd sl res : Word}
    (hL : InsLoc s.locals key klen vptr vlen lv nd sl res)
    (hW : WorldTJ R0 s.globals s.memory) (hK : R0.Kd nd 3#64) (hLn : R0.Lv nd lv.toNat)
    (hlv : lv.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, R0.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hQ : ∀ l' g' m', InsMid R0 s.globals s.memory key klen vptr vlen lv sl res l' g' m' →
      Q (.normal l' g' m' s.ffi)) :
    WPs E s (.ite (.cmp .equal (.var .local "level") (.var .local "klen"))
      (.seq (.store (.op .add [.var .local "node", .const 160#64]) (.var .local "vptr"))
        (.seq (.store (.op .add [.var .local "node", .const 168#64]) (.var .local "vlen"))
          (.assign .local "r" (.var .local "node"))))
      (.dec "idx" .one (.loadByte (.op .add [.var .local "key", .var .local "level"]))
        (.seq (.assign .local "r" (.var .local "node"))
          (.seq (.assign .local "next_node" (.load .one (.op .add [.var .local "node",
              .const 32#64, .panOp .mul [.var .local "idx", .const 8#64]])))
            (.seq (.assign .local "next_slot" (.op .add [.var .local "node", .const 32#64,
                .panOp .mul [.var .local "idx", .const 8#64]]))
              (.seq (.assign .local "next_level"
                  (.op .add [.var .local "level", .const 1#64]))
                (.assign .local "go" (.const 1#64)))))))) Q := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  obtain ⟨hNd, hRd, hlo, htop, h8⟩ := hW.kd hK
  have hsz : nodeSize 3#64 = 176 := by decide
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  rw [evalF_local, hL.level] at hx
  rw [evalF_local, hL.klen] at hy
  simp only [Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · rename_i h0
    -- descend
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
      have := klen.isLt
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
    obtain ⟨c, hrc, hcc⟩ := hW.slot hK h16
    refine WPs.seq_asg (old := 0#64) (w := nd) (by lk [hL.r]) (of_eval (by lk [hL.node])) ?_
    refine WPs.seq_asg (old := 0#64) (w := c) (by lk [hL.nn])
      (eval_load_inv2 hE (of_eval (eval_slot_idx hE (by lk [hL.node]) (by lk []) h16)) hrc) ?_
    refine WPs.seq_asg (old := 0#64) (w := nd + BitVec.ofNat 64 (32 + 8 * b'.toNat))
      (by lk [hL.ns]) (of_eval (eval_slot_idx hE (by lk [hL.node]) (by lk []) h16)) ?_
    refine WPs.seq_asg (old := 0#64) (w := lv + 1#64) (by lk [hL.nl])
      (of_eval (by ev [hL.level])) ?_
    refine WPs.assign (old := 0#64) (w := 1#64) (by lk [hL.go]) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    refine hQ _ _ _ ⟨R0, nd, 3#64, 1#64, c, nd + BitVec.ofNat 64 (32 + 8 * b'.toNat),
      lv + 1#64, nd, Reg.Le.refl R0, hW, fun _ _ => rfl, fun _ _ => rfl,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.key],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.klen],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.vptr],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.vlen],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.level],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.node],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.slot],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.result],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      hK, by decide, hLn, Or.inr ⟨rfl, hcc, fun hc0 => by
        rw [el1]
        exact hW.slot_lv hK (hW.cv_br hK hLn) h16 hrc hc0,
        ⟨nd, by rw [el1]; exact hW.cv_br hK hLn, Or.inr ⟨hK, b'.toNat, h16, rfl⟩⟩, by omega,
        by omega⟩⟩
  · rename_i h0
    -- the key ends at this branch
    obtain ⟨hin0, hs0⟩ := branch_val_cell (a := nd) (c := 160) (Or.inl rfl) (by omega)
    obtain ⟨hin8, hs8⟩ := branch_val_cell (a := nd) (c := 168) (Or.inr rfl) (by omega)
    have W1 := hW.node_other vptr hNd hRd hin0 hs0 (fun hj => by
      rcases hj with hj | hj <;> exact absurd hj (by decide))
    obtain ⟨-, hRd1, -, -, -⟩ := W1.kd hK
    have W2 := W1.node_other vlen hNd hRd1 hin8 hs8 (fun hj => by
      rcases hj with hj | hj <;> exact absurd hj (by decide))
    refine WPs.seq_store hE (addr := nd + 160#64) (w := vptr) (eval_addc hE 160#64 hL.node)
      (of_eval (by lk [hL.vptr])) ?_
    refine WPs.seq_store hE (addr := nd + 168#64) (w := vlen)
      (eval_addc hE 168#64 (by lk [hL.node])) (of_eval (by lk [hL.vlen])) ?_
    refine WPs.assign (old := 0#64) (w := nd) (by lk [hL.r]) (of_eval (by lk [hL.node])) ?_
    refine hQ _ _ _ ⟨R0, nd, 3#64, 0#64, 0#64, 0#64, 0#64, nd, Reg.Le.refl R0, W2,
      fun _ _ => rfl, fun addr ha => ?_, by lk [hL.key], by lk [hL.klen], by lk [hL.vptr],
      by lk [hL.vlen], by lk [hL.level], by lk [hL.node], by lk [hL.slot], by lk [hL.result],
      by lk [], by lk [hL.go], by lk [hL.nn], by lk [hL.ns], by lk [hL.nl], hK, by decide,
      hLn, Or.inl rfl⟩
    show setCell (setCell s.memory (nd + 160#64) vptr) (nd + 168#64) vlen addr = _
    rw [setCell_ne _ (NE (by unfold HBASE at ha hlo; omega)),
      setCell_ne _ (NE (by unfold HBASE at ha hlo; omega))]

end InitECandidate.Solver.GuestBound
