import InitECandidate.Solver.GuestBound.TrieDecStep3
import InitECandidate.Solver.GuestBound.RlpItemFrame
import InitECandidate.Solver.GuestBound.TrieCalls

/-!
# The witness decoder: mode 0 — a branch record

`result` is stored in the current slot of the branch.  If slots remain, the
record advances (mode 2); otherwise the branch value is read from the 17th
slice, the branch gets its RLP cache, and the record is popped.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

local notation "BR" => ((Prog.dec "br" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]))
                                        (Prog.dec "i" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 32))]))
                                          (Prog.seq
                                            (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "result"))
                                            (Prog.seq
                                            (Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "result") (Exp.const (BitVec.ofNat 64 0)))
                                              (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 40))]) (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 40))])), (Exp.const (BitVec.ofNat 64 1))]))
                                              Prog.skip)
                                            (Prog.seq
                                            (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))
                                            (Prog.ite (Exp.cmp Cmp.less (Exp.var VarKind.local "i") (Exp.const (BitVec.ofNat 64 16)))
                                              (Prog.seq
                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 32))]) (Exp.var VarKind.local "i"))
                                                (Prog.seq
                                                (Prog.assign VarKind.local "slot" (Exp.var VarKind.local "i"))
                                                (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 2)))))
                                              (Prog.dec "arr2" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 24))]))
                                                (Prog.decCall "bv" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) "rlp_item" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr2"), (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 16)), (Exp.const (BitVec.ofNat 64 16))])])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr2"), (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 16)), (Exp.const (BitVec.ofNat 64 16))]), (Exp.const (BitVec.ofNat 64 8))]))]
                                                  (Prog.dec "occ" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 40))]))
                                                    (Prog.seq
                                                      (Prog.ite (Exp.cmp Cmp.equal (Exp.rField 0 (Exp.var VarKind.local "bv")) (Exp.const (BitVec.ofNat 64 0)))
                                                        (Prog.seq
                                                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 160))]) (Exp.rField 1 (Exp.var VarKind.local "bv")))
                                                          (Prog.seq
                                                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 168))]) (Exp.rField 2 (Exp.var VarKind.local "bv")))
                                                          (Prog.ite (Exp.cmp Cmp.notEqual (Exp.rField 2 (Exp.var VarKind.local "bv")) (Exp.const (BitVec.ofNat 64 0)))
                                                            (Prog.assign VarKind.local "occ" (Exp.op BinOp.add [(Exp.var VarKind.local "occ"), (Exp.const (BitVec.ofNat 64 1))]))
                                                            Prog.skip)))
                                                        Prog.skip)
                                                      (Prog.seq
                                                      (Prog.ite (Exp.cmp Cmp.lower (Exp.var VarKind.local "occ") (Exp.const (BitVec.ofNat 64 2)))
                                                        (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 9))])
                                                        Prog.skip)
                                                      (Prog.seq
                                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 48))])))
                                                      (Prog.seq
                                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "br"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 56))])))
                                                      (Prog.seq
                                                      (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))])))
                                                      (Prog.assign VarKind.local "result" (Exp.var VarKind.local "br")))))))))))))))) : Prog Word)

set_option maxHeartbeats 32000000 in
/-- A branch record takes `result` into its current slot. -/
theorem dc_br (hE : GuestEnv E) (I : DecIface E) {R0 R : Reg}
    {G : VarName → Option (PanValue Word)} {M : Word → Option (PanValue Word)}
    {F : FfiState σ} {fv lim dbv : Word} {L0 : Nat} {a : St σ}
    {sp topv resv cp cn md sl gv prev kd b iw : Word} {ℓt : Nat}
    (c : D0Ctx I R0 R G M F fv lim dbv a s sp topv resv cp cn md sl gv)
    (h1 : topv ≠ 0#64) (h2 : topv.toNat % 8 = 0) (h3 : sp.toNat ≤ topv.toNat)
    (h4 : topv.toNat + 88 ≤ lim.toNat)
    (r0 : Rd s.memory topv prev) (r8 : Rd s.memory (topv + 8#64) kd) (hkd : kd ≠ 1#64)
    (r16 : Rd s.memory (topv + 16#64) b) (r32 : Rd s.memory (topv + 32#64) iw)
    (hi : iw.toNat < 16) (hKb : R.Kd b 3#64) (hLb : R.Lv b ℓt)
    (htail : DStk R s.memory lim.toNat L0 (topv.toNat + 88) prev ℓt)
    (hres : DRes R (ℓt + 1) resv) :
    WPs E s BR (DcPost I R0 G M F fv lim dbv L0 a) := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hlim := lim.isLt
  have hfs := c.fs
  have hF := c.hF
  have hspl := c.spl
  have e8 : (topv + 8#64).toNat = topv.toNat + 8 := by bv_omega
  have e16 : (topv + 16#64).toNat = topv.toNat + 16 := by bv_omega
  have e32 : (topv + 32#64).toNat = topv.toNat + 32 := by bv_omega
  have e40 : (topv + 40#64).toNat = topv.toNat + 40 := by bv_omega
  obtain ⟨hNdb, hRdb, hblo, hbhi, hb8⟩ := c.w.kd hKb
  have hsz3 : nodeSize 3#64 = 176 := by decide
  rw [hsz3] at hbhi
  have eslot : (b + BitVec.ofNat 64 (32 + 8 * iw.toNat)).toNat = b.toNat + (32 + 8 * iw.toNat) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have restoreP : ∀ {x : VarName} {old : Option (PanValue Word)} {r : Result σ},
      ("db" == x) = false → ("top" == x) = false → ("result" == x) = false →
      ("cur_p" == x) = false → ("cur_n" == x) = false → ("mode" == x) = false →
      ("slot" == x) = false → ("go" == x) = false →
      DcPost I R0 G M F fv lim dbv L0 a r →
      DcPost I R0 G M F fv lim dbv L0 a (restorePanValueFfiLocal x old r) :=
    fun a1 a2 a3 a4 a5 a6 a7 a8 h => h.restore a1 a2 a3 a4 a5 a6 a7 a8
  have hgs0 : ∀ (l : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word)),
      (⟨l, s.globals, m, s.ffi⟩ : St σ).globals "scratch_ptr" = some (.word sp) :=
    fun _ _ => c.gs
  refine WPs.dec (w := b) (eval_load_rd hE (eval_addc hE 16#64 c.qtop) r16) ?_
  refine WPs.conseq (Q' := DcPost I R0 G M F fv lim dbv L0 a) ?_
    (fun r h => restoreP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h)
  refine WPs.dec (w := iw) (eval_load_rd hE (eval_addc hE 32#64 (by lk [c.qtop])) r32) ?_
  refine WPs.conseq (Q' := DcPost I R0 G M F fv lim dbv L0 a) ?_
    (fun r h => restoreP (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) h)
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qbr : L "br" = some (.word b) := by rw [hLL]; lk []
  have qi : L "i" = some (.word iw) := by rw [hLL]; lk []
  have qdb' : L "db" = some (.word dbv) := by rw [hLL]; lk [c.qdb]
  have qtop' : L "top" = some (.word topv) := by rw [hLL]; lk [c.qtop]
  have qres' : L "result" = some (.word resv) := by rw [hLL]; lk [c.qres]
  have qcp' : L "cur_p" = some (.word cp) := by rw [hLL]; lk [c.qcp]
  have qcn' : L "cur_n" = some (.word cn) := by rw [hLL]; lk [c.qcn]
  have qmode' : L "mode" = some (.word md) := by rw [hLL]; lk [c.qmode]
  have qslot' : L "slot" = some (.word sl) := by rw [hLL]; lk [c.qslot]
  have qgo' : L "go" = some (.word gv) := by rw [hLL]; lk [c.qgo]
  clear hLL
  -- the slot store
  have hW1 := c.w.node_child hNdb hRdb (x := b + BitVec.ofNat 64 (32 + 8 * iw.toNat))
    (c := resv) (Or.inr ⟨rfl, iw.toNat, hi, rfl⟩)
    (by
      rcases hres with h | ⟨k, hK, -⟩
      · exact Or.inl h
      · exact Or.inr (c.w.kd hK).1)
    (fun ℓc hcv hr0 => by
      have := c.w.cv_unique hcv (c.w.cv_br hKb hLb)
      subst this
      rcases hres with h | ⟨k, -, hL⟩
      · exact absurd h hr0
      · exact hL)
  refine WPs.seq_store hE (addr := b + BitVec.ofNat 64 (32 + 8 * iw.toNat)) (w := resv)
    (eval_slot_idx hE (x := "br") (ix := "i") qbr qi hi) (of_eval (by lk [qres'])) ?_
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = setCell s.memory (b + BitVec.ofNat 64 (32 + 8 * iw.toNat)) resv :=
    ⟨_, rfl⟩
  rw [← hm1] at hW1 ⊢
  have hm1s : ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) → m1 x = s.memory x := by
    intro x hx
    rw [hm1]
    exact setCell_ne _ (NE (by omega))
  -- the occupancy count
  refine WPs.seqG (fun a' => ∃ m2, a' = ⟨L, s.globals, m2, s.ffi⟩ ∧
      ∀ x : Word, (x.toNat < topv.toNat + 40 ∨ topv.toNat + 48 ≤ x.toNat) → m2 x = m1 x)
    (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip ⟨_, rfl, fun _ _ => rfl⟩
    · exact WPs.last (WPs.seq_store_rng hE (s := (⟨L, s.globals, m1, s.ffi⟩ : St σ))
        (addr := topv + 40#64) (lo := topv.toNat + 40) (hi := topv.toNat + 48) (m0 := m1)
        (of_eval (eval_addc hE 40#64 qtop'))
        (fun y hy => by
          obtain ⟨_, _, w', _, _, _, rfl⟩ := eval_op2_inv hE.word hy
          exact ⟨w', rfl⟩) (by omega) (by omega) (fun _ _ => rfl)
        (fun m hm => WPs.skip ⟨m, rfl, hm⟩))
  rintro _ ⟨m2, rfl, hm2⟩
  have hW2 : WorldTJ R s.globals m2 :=
    hW1.scratch (fun x _ => rfl) (fun a ha => hm2 a (Or.inl (by omega)))
  have hm2s : ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) →
      (x.toNat < topv.toNat + 40 ∨ topv.toNat + 48 ≤ x.toNat) → m2 x = s.memory x :=
    fun x hx hx' => (hm2 x hx').trans (hm1s x hx)
  have hm2l : ∀ x : Word, x.toNat + 8 ≤ HBASE → m2 x = s.memory x := fun x hx =>
    hm2s x (Or.inl hx) (Or.inl (by unfold HBASE at hx; omega))
  -- the next slot
  have ei1 : iw + (0#64 + 1#64) = BitVec.ofNat 64 (iw.toNat + 1) := by
    apply BitVec.eq_of_toNat_eq
    have h01 : (0#64 + 1#64 : Word).toNat = 1 := by decide
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, h01]
    try omega
  have ei1b : iw + 1#64 = BitVec.ofNat 64 (iw.toNat + 1) := by
    rw [← ei1]
    congr 1
  have ej1 : (BitVec.ofNat 64 (iw.toNat + 1) : Word).toNat = iw.toNat + 1 := by
    rw [BitVec.toNat_ofNat]
    omega
  refine WPs.seq_asg (old := iw) (w := BitVec.ofNat 64 (iw.toNat + 1)) qi
    (of_eval (by ev [qi, ei1b])) ?_
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  simp (config := { decide := true }) only [evalF_local, update_lookup, if_true, eval_const,
    Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  rw [less16 (iw.toNat + 1) (by omega)] at hwv
  split
  · -- the last slot: the branch value, then pop
    rename_i hw0
    have hlast : iw.toNat + 1 = 16 := by
      by_contra hne
      rw [hwv, if_pos (by omega)] at hw0
      exact absurd hw0 (by decide)
    refine WPs.dec_w (fun arr2 => WPs.conseq (Q' := DcPost I R0 G M F fv lim dbv L0 a) ?_
      (fun r h => restoreP (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h))
    refine WPs.decCall_ret (fun v g4 m4 f4 hret =>
      WPs.conseq (Q' := DcPost I R0 G M F fv lim dbv L0 a) ?_
        (fun r h => restoreP (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) h))
    obtain ⟨pw, hev1⟩ : ∃ pw : Word,
        E.eval ⟨updatePanValueMap (updatePanValueMap L "i" (.word (BitVec.ofNat 64 (iw.toNat + 1))))
          "arr2" (.word arr2), s.globals, m2, s.ffi⟩
          (.load .one (.op .add [.var .local "arr2",
            .panOp .mul [.const 16#64, .const 16#64]])) = some (.word pw) := by
      have hret' := hret
      obtain ⟨parameters, body, values, cl, l', hlookup, hvalues, hbind, hrun⟩ := hret'
      obtain ⟨y1, vs1, g1', -, -⟩ := evalArgs_cons_inv hvalues
      obtain ⟨w2, hw2⟩ := eval_load_any hE
        (s := (⟨updatePanValueMap (updatePanValueMap L "i"
          (.word (BitVec.ofNat 64 (iw.toNat + 1)))) "arr2" (.word arr2), s.globals, m2,
          s.ffi⟩ : St σ))
        (a := .op .add [.var .local "arr2", .panOp .mul [.const 16#64, .const 16#64]])
        (addr := arr2 + 16#64 * 16#64) (of_eval (by ev []))
      have := hw2 _ g1'
      subst this
      exact ⟨w2, g1'⟩
    obtain ⟨hg4, hf4, hscr, ba, bb, bc, bd, hv⟩ := rlpitem_ret hE hret hev1 c.gs c.gfv c.fs
    simp only [List.cons.injEq, and_true] at hv
    dsimp only at hg4 hf4 hscr
    subst hg4 hf4 hv
    refine WPs.dec_w (fun occ => WPs.conseq (Q' := DcPost I R0 G M F fv lim dbv L0 a) ?_
      (fun r h => restoreP (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) h))
    have hW4 : WorldTJ R s.globals m4 :=
      hW2.scratch (fun x _ => rfl) (fun a ha => hscr a (Or.inl (by omega)))
    have hm4s : ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ x.toNat) →
        (x.toNat < topv.toNat + 40 ∨ topv.toNat + 48 ≤ x.toNat) → m4 x = s.memory x :=
      fun x hx hx' => (hscr x (by unfold HBASE at hx; omega)).trans
        (hm2s x (by unfold HBASE at hx ⊢; omega) hx')
    refine WPs.name_locals (fun L2 hLL => ?_)
    dsimp only at hLL
    have pbv : L2 "bv" = some (.rStruct [.word ba, .word bb, .word bc, .word bd]) := by
      rw [hLL]; lk []
    have pocc : L2 "occ" = some (.word occ) := by rw [hLL]; lk []
    have pbr : L2 "br" = some (.word b) := by rw [hLL]; lk [qbr]
    have pdb : L2 "db" = some (.word dbv) := by rw [hLL]; lk [qdb']
    have ptop : L2 "top" = some (.word topv) := by rw [hLL]; lk [qtop']
    have pres : L2 "result" = some (.word resv) := by rw [hLL]; lk [qres']
    have pcp : L2 "cur_p" = some (.word cp) := by rw [hLL]; lk [qcp']
    have pcn : L2 "cur_n" = some (.word cn) := by rw [hLL]; lk [qcn']
    have pmode : L2 "mode" = some (.word md) := by rw [hLL]; lk [qmode']
    have pslot : L2 "slot" = some (.word sl) := by rw [hLL]; lk [qslot']
    have pgo : L2 "go" = some (.word gv) := by rw [hLL]; lk [qgo']
    clear hLL
    have ebv : ∀ (i : Nat) (w : Word) (L' : VarName → Option (PanValue Word))
        (g' : VarName → Option (PanValue Word)) (m' : Word → Option (PanValue Word))
        (f' : FfiState σ),
        L' "bv" = some (.rStruct [.word ba, .word bb, .word bc, .word bd]) →
        [PanValue.word ba, .word bb, .word bc, .word bd][i]? = some (.word w) →
        E.eval ⟨L', g', m', f'⟩ (.rField i (.var .local "bv")) = some (.word w) := by
      intro i w L' g' m' f' h hi
      rw [eval_rField _ i "bv" _ h]
      exact hi
    have val160 := branch_val_cell (a := b) (c := 160) (Or.inl rfl) (by omega)
    have val168 := branch_val_cell (a := b) (c := 168) (Or.inr rfl) (by omega)
    have eb160 : (b + 160#64).toNat = b.toNat + 160 := by bv_omega
    have eb168 : (b + 168#64).toNat = b.toNat + 168 := by bv_omega
    refine WPs.seqG (fun a' => ∃ L3 m5, a' = ⟨L3, s.globals, m5, s.ffi⟩ ∧
        (∀ x, x ≠ "occ" → L3 x = L2 x) ∧ WorldTJ R s.globals m5 ∧
        ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) → m5 x = m4 x)
      (WPs.ite_both (fun w2 _ => ?_)) ?_
    · split
      · exact WPs.skip ⟨L2, m4, rfl, fun _ _ => rfl, hW4, fun _ _ => rfl⟩
      · refine WPs.seq_store hE (addr := b + 160#64) (w := bb) (eval_addc hE 160#64 pbr)
          (of_eval (ebv 1 bb _ _ _ _ pbv rfl)) ?_
        have W5 := hW4.node_other bb hNdb (hW4.kd hKb).2.1 val160.1 val160.2
          (fun h => absurd h (by decide))
        refine WPs.seq_store hE (addr := b + 168#64) (w := bc) (eval_addc hE 168#64 pbr)
          (of_eval (ebv 2 bc _ _ _ _ pbv rfl)) ?_
        have W6 := W5.node_other bc hNdb (W5.kd hKb).2.1 val168.1 val168.2
          (fun h => absurd h (by decide))
        have hm6 : ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) →
            setCell (setCell m4 (b + 160#64) bb) (b + 168#64) bc x = m4 x := fun x hx => by
          rw [setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]
        refine WPs.ite_both (fun w3 _ => ?_)
        split
        · exact WPs.skip ⟨L2, _, rfl, fun _ _ => rfl, W6, hm6⟩
        · exact WPs.assign (old := occ) (w := occ + 1#64) pocc (of_eval (by ev [pocc]))
            ⟨_, _, rfl, fun x hx => by simp [update_lookup, hx], W6, hm6⟩
    rintro _ ⟨L3, m5, rfl, hL3, hW5, hm5⟩
    have tbr : L3 "br" = some (.word b) := (hL3 _ (by decide)).trans pbr
    have tdb : L3 "db" = some (.word dbv) := (hL3 _ (by decide)).trans pdb
    have ttop : L3 "top" = some (.word topv) := (hL3 _ (by decide)).trans ptop
    have tres : L3 "result" = some (.word resv) := (hL3 _ (by decide)).trans pres
    have tcp : L3 "cur_p" = some (.word cp) := (hL3 _ (by decide)).trans pcp
    have tcn : L3 "cur_n" = some (.word cn) := (hL3 _ (by decide)).trans pcn
    have tmode : L3 "mode" = some (.word md) := (hL3 _ (by decide)).trans pmode
    have tslot : L3 "slot" = some (.word sl) := (hL3 _ (by decide)).trans pslot
    have tgo : L3 "go" = some (.word gv) := (hL3 _ (by decide)).trans pgo
    refine WPs.seqG (fun a' => a' = ⟨L3, s.globals, m5, s.ffi⟩) (WPs.ite_both (fun w4 _ => ?_)) ?_
    · split
      · exact WPs.skip rfl
      · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
    rintro _ rfl
    have eb8 : (b + 8#64).toNat = b.toNat + 8 := by
      rw [BitVec.toNat_add, show (8#64 : Word).toNat = 8 from rfl]
      omega
    have eb16 : (b + 16#64).toNat = b.toNat + 16 := by
      rw [BitVec.toNat_add, show (16#64 : Word).toNat = 16 from rfl]
      omega
    obtain ⟨w48, hw48⟩ := eval_load_any hE (s := (⟨L3, s.globals, m5, s.ffi⟩ : St σ))
      (of_eval (eval_addc hE 48#64 ttop))
    refine WPs.seq_store hE (addr := b + 8#64) (w := w48) (eval_addc hE 8#64 tbr) hw48 ?_
    obtain ⟨w56, hw56⟩ := eval_load_any hE
      (s := (⟨L3, s.globals, setCell m5 (b + 8#64) w48, s.ffi⟩ : St σ))
      (of_eval (eval_addc hE 56#64 ttop))
    refine WPs.seq_store hE (addr := b + 16#64) (w := w56) (eval_addc hE 16#64 tbr) hw56 ?_
    have W7 : WorldTJ R s.globals (setCell (setCell m5 (b + 8#64) w48) (b + 16#64) w56) :=
      (hW5.cache_store w48 (c := 8) (Or.inl rfl) hKb).cache_store w56 (c := 16)
        (Or.inr (Or.inl rfl)) hKb
    have hm7 : ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ x.toNat) →
        (x.toNat < topv.toNat + 40 ∨ topv.toNat + 48 ≤ x.toNat) →
        setCell (setCell m5 (b + 8#64) w48) (b + 16#64) w56 x = s.memory x := fun x hx hx' => by
      have n1 : x ≠ b + 16#64 := NE (by omega)
      have n2 : x ≠ b + 8#64 := NE (by omega)
      have n3 : x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat := by omega
      rw [setCell_ne _ n1, setCell_ne _ n2, hm5 x n3]
      exact hm4s x hx hx'
    refine WPs.seq_asg (old := topv) (w := prev) ttop
      (eval_load_rd hE (eval_addc hE 0#64 ttop) (by
        rw [BitVec.add_zero]
        unfold Rd at r0 ⊢
        dsimp only
        rw [hm7 _ (Or.inr h3) (Or.inl (by omega))]
        exact r0)) ?_
    refine WPs.assign (old := resv) (w := b) (by lk [tres]) (of_eval (by lk [tbr])) ?_
    refine ⟨_, _, _, _, rfl, ⟨R, sp, prev, b, cp, cn, md, sl, gv, ℓt, c.le, W7, c.ffi, c.glob,
      c.gs, c.fs, c.spl, c.pre,
      by lk [tdb], by lk [], by lk [], by lk [tcp], by lk [tcn], by lk [tmode],
      by lk [tslot], by lk [tgo],
      (htail.frame hlim (fun x hx _ => hm7 x (Or.inr (by omega)) (Or.inr (by omega)))).lower
        (by omega),
      fun _ _ => Or.inr ⟨3#64, hKb, hLb⟩, fun h => absurd h c.gv0, fun h => absurd h c.m2,
      fun addr ha => by
        rcases ha with ha | ha
        · exact (hm7 addr (Or.inl ha) (Or.inl (by unfold HBASE at ha; omega))).trans
            (c.mem addr (Or.inl ha))
        · exact (hm7 addr (Or.inr (by omega)) (Or.inr (by omega))).trans
            (c.mem addr (Or.inr ha))⟩, ?_⟩
    dsimp only
    rw [c.mu, dcMu_eq (sp := sp) (t := prev) (md := md)
      (gv := gv) (hgs0 _ _) (by lk []) (by lk [tmode]) (by lk [tgo])]
    dsimp only
    have hp := tT_pop hlim h1 (p := prev) (by
      rcases htail.top_in with h | h
      · exact Or.inl h
      · exact Or.inr h.1)
    have := icOf_le (setCell (setCell m5 (b + 8#64) w48) (b + 16#64) w56) prev
    have := icOf_le s.memory topv
    omega
  · -- slots remain: advance
    rename_i hw0
    have hnext : iw.toNat + 1 < 16 := by
      by_contra hge
      rw [hwv, if_neg hge] at hw0
      exact hw0 rfl
    refine WPs.seq_store hE (addr := topv + 32#64) (w := BitVec.ofNat 64 (iw.toNat + 1))
      (eval_addc hE 32#64 (by lk [qtop'])) (of_eval (by lk [])) ?_
    refine WPs.seq_asg (old := sl) (w := BitVec.ofNat 64 (iw.toNat + 1)) (by lk [qslot'])
      (of_eval (by lk [])) ?_
    refine WPs.assign (old := md) (w := 2#64) (by lk [qmode']) (of_eval (eval_const _ _)) ?_
    have hm3 : ∀ x : Word, x ≠ topv + 32#64 →
        setCell m2 (topv + 32#64) (BitVec.ofNat 64 (iw.toNat + 1)) x = m2 x :=
      fun x hx => setCell_ne _ hx
    have keep : ∀ (cc : Nat) (w : Word), cc ≤ 16 → Rd s.memory (topv + BitVec.ofNat 64 cc) w →
        Rd (setCell m2 (topv + 32#64) (BitVec.ofNat 64 (iw.toNat + 1)))
          (topv + BitVec.ofNat 64 cc) w := by
      intro cc w hcc hr
      have e : (topv + BitVec.ofNat 64 cc).toNat = topv.toNat + cc := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      unfold Rd at hr ⊢
      rw [hm3 _ (NE (by omega)), hm2s _ (Or.inr (by omega)) (Or.inl (by omega))]
      exact hr
    have r0' : Rd (setCell m2 (topv + 32#64) (BitVec.ofNat 64 (iw.toNat + 1))) topv prev := by
      unfold Rd at r0 ⊢
      rw [hm3 _ (NE (by omega)), hm2s _ (Or.inr (by omega)) (Or.inl (by omega))]
      exact r0
    have W3 : WorldTJ R s.globals (setCell m2 (topv + 32#64) (BitVec.ofNat 64 (iw.toNat + 1))) :=
      hW2.scratch (fun x _ => rfl) (fun a ha => hm3 a (NE (by omega)))
    have hrh := Rd.here m2 (topv + 32#64) (BitVec.ofNat 64 (iw.toNat + 1))
    refine ⟨_, _, _, _, rfl, ⟨R, sp, topv, resv, cp, cn, 2#64, BitVec.ofNat 64 (iw.toNat + 1), gv,
      ℓt + 1, c.le, W3, c.ffi, c.glob, c.gs, c.fs, c.spl, c.pre,
      by lk [qdb'], by lk [qtop'], by lk [qres'], by lk [qcp'], by lk [qcn'], by lk [],
      by lk [], by lk [qgo'],
      .br h1 h2 h3 h4 r0' (keep 8 kd (by omega) r8) hkd (keep 16 b (by omega) r16) hrh
        (by rw [ej1]; exact hnext) hKb hLb
        (htail.frame hlim (fun x hx _ => (hm3 x (NE (by omega))).trans
          (hm2s x (Or.inr (by omega)) (Or.inr (by omega))))),
      fun _ h => absurd rfl h, fun h => absurd h c.gv0, fun _ => h1,
      fun addr ha => by
        rcases ha with ha | ha
        · exact (hm3 addr (NE (by unfold HBASE at ha; omega))).trans
            ((hm2l addr ha).trans (c.mem addr (Or.inl ha)))
        · exact (hm3 addr (NE (by omega))).trans
            ((hm2s addr (Or.inr (by omega)) (Or.inr (by omega))).trans
              (c.mem addr (Or.inr ha)))⟩, ?_⟩
    dsimp only
    rw [c.mu, dcMu_eq (sp := sp) (t := topv)
      (md := 2#64) (gv := gv) (hgs0 _ _) (by lk [qtop']) (by lk []) (by lk [qgo'])]
    dsimp only
    rw [icOf_rd h1 hrh, icOf_rd h1 r32, ej1]
    have := rankOf_le md
    have h2r : rankOf (2#64 : Word) = 2 := by decide
    rw [h2r]
    omega

end InitECandidate.Solver.GuestBound
