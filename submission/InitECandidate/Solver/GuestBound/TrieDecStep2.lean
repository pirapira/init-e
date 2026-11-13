import InitECandidate.Solver.GuestBound.TrieDecStep1
import InitECandidate.Solver.GuestBound.TrieLeafIns
import InitECandidate.Solver.GuestBound.KeccakFrame

/-!
# The witness decoder: the iteration in mode 2

In mode 2 the decoder resolves the current slice of the top record with
`_resolve_step`: either the child is finished (null or a hash stub; mode 0) or
its RLP is to be decoded (mode 1).  The child's hash goes to `top + 80`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A store into a cache cell of a registered node (of any kind). -/
theorem WorldTJ.cache_store {R : Reg} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {a k : Word} (w : Word) {c : Nat}
    (hc : c = 8 ∨ c = 16 ∨ c = 24) (hW : WorldTJ R g m) (hK : R.Kd a k) :
    WorldTJ R g (setCell m (a + BitVec.ofNat 64 c) w) := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  obtain ⟨hNd, hRd, hlo, hhi, h8⟩ := hW.kd hK
  have hsz := nodeSize_ge k
  have e : (a + BitVec.ofNat 64 c).toNat = a.toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e32 : (a + 32#64).toNat = a.toNat + 32 := by bv_omega
  have e40 : (a + 40#64).toNat = a.toNat + 40 := by bv_omega
  have e48 : (a + 48#64).toNat = a.toNat + 48 := by bv_omega
  refine hW.node_other w hNd hRd ⟨by omega, by omega⟩ ?_
    (fun _ => ⟨NE (by omega), NE (by omega)⟩)
  rintro (h | ⟨-, h | h⟩ | ⟨-, i, hi, h⟩)
  · have := congrArg BitVec.toNat h
    omega
  · have := congrArg BitVec.toNat h
    omega
  · have := congrArg BitVec.toNat h
    omega
  · have := congrArg BitVec.toNat h
    have ei : (a + BitVec.ofNat 64 (32 + 8 * i)).toNat = a.toNat + (32 + 8 * i) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    omega

/-- The slot counter read off a record. -/
theorem icOf_rd {m : Word → Option (PanValue Word)} {t i : Word} (ht : t ≠ 0#64)
    (h : Rd m (t + 32#64) i) : icOf m t = 16 - min i.toNat 16 := by
  unfold icOf
  rw [if_neg ht]
  unfold Rd at h
  rw [h]

/-- A store into the occupancy cell (`+40`) or the hash cell (`+80`) of the top record. -/
theorem DStk.store_top {R : Reg} {m : Word → Option (PanValue Word)} {lim ℓ0 sp : Nat}
    {top : Word} {ℓ : Nat} (hlim : lim < 2 ^ 64) (w : Word) {c : Nat} (hc : c = 40 ∨ c = 80)
    (h : DStk R m lim ℓ0 sp top ℓ) :
    DStk R (setCell m (top + BitVec.ofNat 64 c) w) lim ℓ0 sp top ℓ := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  cases h with
  | nil => exact .nil
  | ext h1 h2 h3 h4 r0 r1 r2 r3 hs hi ht =>
    have e := drec_off hlim h4 c (by omega)
    have e8 := drec_off hlim h4 8 (by omega)
    have e64 := drec_off hlim h4 64 (by omega)
    have e72 := drec_off hlim h4 72 (by omega)
    exact .ext h1 h2 h3 h4 (r0.frame _ (NE (by omega))) (r1.frame _ (NE (by omega)))
      (r2.frame _ (NE (by omega))) (r3.frame _ (NE (by omega))) hs hi
      (ht.frame hlim (fun x hx _ => setCell_ne _ (NE (by omega))))
  | br h1 h2 h3 h4 r0 r1 hk r2 r3 hi hK hL ht =>
    have e := drec_off hlim h4 c (by omega)
    have e8 := drec_off hlim h4 8 (by omega)
    have e16 := drec_off hlim h4 16 (by omega)
    have e32 := drec_off hlim h4 32 (by omega)
    exact .br h1 h2 h3 h4 (r0.frame _ (NE (by omega))) (r1.frame _ (NE (by omega))) hk
      (r2.frame _ (NE (by omega))) (r3.frame _ (NE (by omega))) hi hK hL
      (ht.frame hlim (fun x hx _ => setCell_ne _ (NE (by omega))))

local notation "M2PROG" => ((Prog.dec "arr" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 24))]))
                                (Prog.decCall "r" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) "_resolve_step" [(Exp.var VarKind.local "db"), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "slot"), (Exp.const (BitVec.ofNat 64 16))])])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "slot"), (Exp.const (BitVec.ofNat 64 16))]), (Exp.const (BitVec.ofNat 64 8))]))]
                                  (Prog.ite (Exp.cmp Cmp.equal (Exp.rField 0 (Exp.var VarKind.local "r")) (Exp.const (BitVec.ofNat 64 0)))
                                    (Prog.seq
                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 80))]) (Exp.const (BitVec.ofNat 64 0)))
                                      (Prog.seq
                                      (Prog.assign VarKind.local "result" (Exp.rField 1 (Exp.var VarKind.local "r")))
                                      (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 0)))))
                                    (Prog.seq
                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 80))]) (Exp.rField 3 (Exp.var VarKind.local "r")))
                                      (Prog.seq
                                      (Prog.assign VarKind.local "cur_p" (Exp.rField 1 (Exp.var VarKind.local "r")))
                                      (Prog.seq
                                      (Prog.assign VarKind.local "cur_n" (Exp.rField 2 (Exp.var VarKind.local "r")))
                                      (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 1))))))))) : Prog Word)

set_option maxHeartbeats 16000000 in
theorem dc_mode2 (hE : GuestEnv E) (I : DecIface E) {R0 : Reg}
    {G : VarName → Option (PanValue Word)} {M : Word → Option (PanValue Word)}
    {F : FfiState σ} {fv lim dbv : Word} {L0 : Nat}
    (hGfv : G "frame_mem_ptr" = some (.word fv)) (hFv : 2952790016 ≤ fv.toNat) {a : St σ}
    (hI : DcI I R0 G M F fv lim dbv L0 a) (hmd : a.locals "mode" = some (.word 2#64))
    (hgo : ∀ gv, a.locals "go" = some (.word gv) → gv ≠ 0#64) :
    WPs E a M2PROG (DcPost I R0 G M F fv lim dbv L0 a) := by
  obtain ⟨la, ga, ma, fa⟩ := a
  obtain ⟨R, sp, topv, resv, cp, cn, md, sl, gv, ℓ, hle, hW, hf, hg, hgs, hfs, hsl, hPre, qdb,
    qtop, qres, qcp, qcn, qmode, qslot, qgo, hst, hres, hfin, hm2t, hM⟩ := hI
  dsimp only at hW hf hg hgs hPre qdb qtop qres qcp qcn qmode qslot qgo hst hM hmd hgo
  subst hf
  have hmd2 : md = 2#64 := by
    rw [qmode] at hmd
    simpa using hmd
  subst hmd2
  have hgv := hgo gv qgo
  have ht0 := hm2t rfl
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hlim := lim.isLt
  have hgfv : ga "frame_mem_ptr" = some (.word fv) :=
    (hg _ (by decide) (by decide)).trans hGfv
  have hmu0 := dcMu_eq (a := (⟨la, ga, ma, fa⟩ : St σ)) hgs qtop qmode qgo
  dsimp only at hmu0
  obtain ⟨htsp, htlim⟩ : sp.toNat ≤ topv.toNat ∧ topv.toNat + 88 ≤ lim.toNat := by
    rcases hst.top_in with h0 | h
    · exact absurd h0 ht0
    · exact h
  have e80 : (topv + 80#64).toNat = topv.toNat + 80 := by bv_omega
  have e32 : (topv + 32#64).toNat = topv.toNat + 32 := by bv_omega
  refine WPs.dec_w (fun arr => ?_)
  refine WPs.decCall_ret (fun v g1 m1 f1 hret => ?_)
  obtain ⟨pw, nw, hev2, hev3⟩ : ∃ pw nw : Word,
      E.eval ⟨updatePanValueMap la "arr" (.word arr), ga, ma, fa⟩
        (.load .one (.op .add [.var .local "arr",
          .panOp .mul [.var .local "slot", .const 16#64]])) = some (.word pw) ∧
      E.eval ⟨updatePanValueMap la "arr" (.word arr), ga, ma, fa⟩
        (.load .one (.op .add [.var .local "arr",
          .panOp .mul [.var .local "slot", .const 16#64], .const 8#64])) = some (.word nw) := by
    have hret' := hret
    obtain ⟨parameters, body, values, cl, l', hlookup, hvalues, hbind, hrun⟩ := hret'
    obtain ⟨y1, y2, y3, g1', g2', g3', -⟩ := evalArgs3_inv hvalues
    obtain ⟨w2, hw2⟩ := eval_load_any hE
      (s := (⟨updatePanValueMap la "arr" (.word arr), ga, ma, fa⟩ : St σ))
      (a := .op .add [.var .local "arr", .panOp .mul [.var .local "slot", .const 16#64]])
      (addr := arr + sl * 16#64) (of_eval (by ev [qslot]))
    obtain ⟨w3, hw3⟩ := eval_load_any hE
      (s := (⟨updatePanValueMap la "arr" (.word arr), ga, ma, fa⟩ : St σ))
      (a := .op .add [.var .local "arr", .panOp .mul [.var .local "slot", .const 16#64],
        .const 8#64])
      (addr := arr + (sl * 16#64 + 8#64)) (of_eval (by ev [qslot]))
    have := hw2 _ g2'
    subst this
    have := hw3 _ g3'
    subst this
    exact ⟨w2, w3, g2', g3'⟩
  obtain ⟨hf1, R', r0, r1, r2, r3, rfl, hle', hW', hg', hmem, hfinr⟩ :=
    I.resolve R _ _ _ _ dbv pw nw sp fv ℓ _ _ _ _ hret (by lk [qdb]) hev2 hev3 hW hPre hgs hgfv
      hfs hFv
  dsimp only at hf1 hg' hmem
  subst hf1
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qr : L "r" = some (.rStruct [.word r0, .word r1, .word r2, .word r3]) := by
    rw [hLL]; lk []
  have qdb' : L "db" = some (.word dbv) := by rw [hLL]; lk [qdb]
  have qtop' : L "top" = some (.word topv) := by rw [hLL]; lk [qtop]
  have qres' : L "result" = some (.word resv) := by rw [hLL]; lk [qres]
  have qcp' : L "cur_p" = some (.word cp) := by rw [hLL]; lk [qcp]
  have qcn' : L "cur_n" = some (.word cn) := by rw [hLL]; lk [qcn]
  have qmode' : L "mode" = some (.word 2#64) := by rw [hLL]; lk [qmode]
  have qslot' : L "slot" = some (.word sl) := by rw [hLL]; lk [qslot]
  have qgo' : L "go" = some (.word gv) := by rw [hLL]; lk [qgo]
  clear hLL
  have er : ∀ (i : Nat) (w : Word) (L' : VarName → Option (PanValue Word))
      (g' : VarName → Option (PanValue Word)) (m' : Word → Option (PanValue Word))
      (f' : FfiState σ), L' "r" = some (.rStruct [.word r0, .word r1, .word r2, .word r3]) →
      [PanValue.word r0, .word r1, .word r2, .word r3][i]? = some (.word w) →
      E.eval ⟨L', g', m', f'⟩ (.rField i (.var .local "r")) = some (.word w) := by
    intro i w L' g' m' f' h hi
    rw [eval_rField _ i "r" _ h]
    exact hi
  have hglob : ∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g1 x = G x :=
    fun x h1 h2 => (hg' x h1).trans (hg x h1 h2)
  have hgs' : g1 "scratch_ptr" = some (.word sp) := (hg' _ (by decide)).trans hgs
  have hPre' := I.pre_mono hPre hle' (fun x h1 _ => hg' x h1)
  have hst1 : DStk R' m1 lim.toNat L0 sp.toNat topv ℓ :=
    (hst.mono hle').frame hlim (fun x hx _ => hmem x (Or.inr hx))
  have hmset : ∀ (w : Word) (x : Word), x ≠ topv + 80#64 → setCell m1 (topv + 80#64) w x = m1 x :=
    fun w x hx => setCell_ne _ hx
  have hW2 : ∀ w : Word, WorldTJ R' g1 (setCell m1 (topv + 80#64) w) := fun w =>
    hW'.scratch (fun x _ => rfl) (fun a ha => hmset w a (NE (by omega)))
  have hst2 : ∀ w : Word, DStk R' (setCell m1 (topv + 80#64) w) lim.toNat L0 sp.toNat topv ℓ :=
    fun w => hst1.store_top hlim w (c := 80) (Or.inr rfl)
  have hMM : ∀ (w : Word) (addr : Word), (addr.toNat + 8 ≤ HBASE ∨ lim.toNat ≤ addr.toNat) →
      setCell m1 (topv + 80#64) w addr = M addr := fun w addr ha =>
    (hmset w addr (NE (by unfold HBASE at ha; omega))).trans
      ((hmem addr (by omega)).trans (hM addr ha))
  have hic : ∀ w : Word, icOf (setCell m1 (topv + 80#64) w) topv = icOf ma topv := fun w =>
    icOf_congr (fun _ => (hmset w _ (NE (by omega))).trans (hmem _ (Or.inr (by omega))))
  have h0r : rankOf (0#64 : Word) = 0 := by decide
  have h1r : rankOf (1#64 : Word) = 1 := by decide
  have h2r : rankOf (2#64 : Word) = 2 := by decide
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  rw [er 0 r0 _ _ _ _ qr rfl] at hx
  simp only [eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · -- a child to decode: mode 1
    refine WPs.seq_store hE (addr := topv + 80#64) (w := r3) (eval_addc hE 80#64 qtop')
      (of_eval (er 3 r3 _ _ _ _ qr rfl)) ?_
    refine WPs.seq_asg (old := cp) (w := r1) qcp' (of_eval (er 1 r1 _ _ _ _ qr rfl)) ?_
    refine WPs.seq_asg (old := cn) (w := r2) (by lk [qcn'])
      (of_eval (er 2 r2 _ _ _ _ (by lk [qr]) rfl)) ?_
    refine WPs.assign (old := 2#64) (w := 1#64) (by lk [qmode']) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨_, _, _, _, rfl, ⟨R', sp, topv, resv, r1, r2, 1#64, sl, gv, ℓ, hle.trans hle',
      hW2 r3, rfl, hglob, hgs', hfs, hsl, hPre',
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qdb'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qtop'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qres'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qslot'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo'],
      hst2 r3, fun h _ => absurd rfl h, fun h => absurd h hgv, fun h => absurd h (by decide),
      hMM r3⟩, ?_⟩
    rw [hmu0, dcMu_eq (sp := sp) (t := topv) (md := 1#64) (gv := gv) hgs'
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qtop'])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo'])]
    dsimp only
    rw [hic, h1r, h2r]
    omega
  · -- a finished child: mode 0
    rename_i hw0
    have hr0 : r0 = 0#64 := by
      by_contra hne
      apply hw0
      rw [hwv]
      simp [evalPanCmp, hne]
    refine WPs.seq_store hE (addr := topv + 80#64) (w := 0#64) (eval_addc hE 80#64 qtop')
      (of_eval (eval_const _ _)) ?_
    refine WPs.seq_asg (old := resv) (w := r1) qres' (of_eval (er 1 r1 _ _ _ _ qr rfl)) ?_
    refine WPs.assign (old := 2#64) (w := 0#64) (by lk [qmode']) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨_, _, _, _, rfl, ⟨R', sp, topv, r1, cp, cn, 0#64, sl, gv, ℓ, hle.trans hle',
      hW2 0#64, rfl, hglob, hgs', hfs, hsl, hPre',
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qdb'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qtop'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qcp'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qcn'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qslot'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo'],
      hst2 0#64, fun _ _ => hfinr hr0, fun h => absurd h hgv, fun h => absurd h (by decide),
      hMM 0#64⟩, ?_⟩
    rw [hmu0, dcMu_eq (sp := sp) (t := topv) (md := 0#64) (gv := gv) hgs'
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qtop'])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo'])]
    dsimp only
    rw [hic, h0r, h2r]
    omega

end InitECandidate.Solver.GuestBound
