import InitECandidate.Solver.GuestBound.TrieDecStep2
import InitECandidate.Solver.GuestBound.TrieRets
import InitECandidate.Solver.GuestBound.ResolveStep

/-!
# The witness decoder: mode 0 — exit, the child hash, and an extension record

In mode 0 a finished node `result` is handed to the top record.  With an empty
stack the loop ends.  Otherwise the hash remembered in the record is stored in
the node's hash cache, and an extension record is popped: the extension is
created over `result`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem restore_ne (l : VarName → Option (PanValue Word)) (x y : VarName)
    (old : Option (PanValue Word)) (h : (y == x) = false) :
    restorePanValueLocal l x old y = l y := by
  unfold restorePanValueLocal
  rw [h]
  rfl

/-- The postcondition of an iteration does not see a restored scratch local. -/
theorem DcPost.restore {I : DecIface E} {R0 : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {F : FfiState σ} {fv lim dbv : Word} {L0 : Nat}
    {a : St σ} {r : Result σ} {x : VarName} {old : Option (PanValue Word)}
    (h : DcPost I R0 G M F fv lim dbv L0 a r)
    (h1 : ("db" == x) = false) (h2 : ("top" == x) = false) (h3 : ("result" == x) = false)
    (h4 : ("cur_p" == x) = false) (h5 : ("cur_n" == x) = false) (h6 : ("mode" == x) = false)
    (h7 : ("slot" == x) = false) (h8 : ("go" == x) = false) :
    DcPost I R0 G M F fv lim dbv L0 a (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g, m, f, rfl, ⟨R, sp, topv, resv, cp, cn, md, sl, gv, ℓ, hle, hW, hf, hg, hgs, hfs,
    hsl, hPre, qdb, qtop, qres, qcp, qcn, qmode, qslot, qgo, rest⟩, hmu⟩ := h
  dsimp only at qdb qtop qres qcp qcn qmode qslot qgo
  refine ⟨_, g, m, f, rfl, ⟨R, sp, topv, resv, cp, cn, md, sl, gv, ℓ, hle, hW, hf, hg, hgs, hfs,
    hsl, hPre, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rest⟩, ?_⟩
  · exact (restore_ne _ _ _ _ h1).trans qdb
  · exact (restore_ne _ _ _ _ h2).trans qtop
  · exact (restore_ne _ _ _ _ h3).trans qres
  · exact (restore_ne _ _ _ _ h4).trans qcp
  · exact (restore_ne _ _ _ _ h5).trans qcn
  · exact (restore_ne _ _ _ _ h6).trans qmode
  · exact (restore_ne _ _ _ _ h7).trans qslot
  · exact (restore_ne _ _ _ _ h8).trans qgo
  · have e : dcMu (⟨restorePanValueLocal l x old, g, m, f⟩ : St σ) = dcMu ⟨l, g, m, f⟩ := by
      unfold dcMu
      dsimp only
      rw [restore_ne _ _ _ _ h2, restore_ne _ _ _ _ h6, restore_ne _ _ _ _ h8]
    show dcMu (⟨restorePanValueLocal l x old, g, m, f⟩ : St σ) < dcMu a
    rw [e]
    exact hmu

/-- The facts of a mode-0 iteration at an intermediate state `s`; `a` is the
state at the start of the iteration. -/
structure D0Ctx (I : DecIface E) (R0 R : Reg) (G : VarName → Option (PanValue Word))
    (M : Word → Option (PanValue Word)) (F : FfiState σ) (fv lim dbv : Word) (a s : St σ)
    (sp topv resv cp cn md sl gv : Word) : Prop where
  le : R0.Le R
  w : WorldTJ R s.globals s.memory
  ffi : s.ffi = F
  glob : ∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → s.globals x = G x
  gs : s.globals "scratch_ptr" = some (.word sp)
  gfv : s.globals "frame_mem_ptr" = some (.word fv)
  fs : fv.toNat ≤ sp.toNat
  spl : sp.toNat ≤ lim.toNat
  hF : 2952790016 ≤ fv.toNat
  pre : I.Pre R s.globals
  qdb : s.locals "db" = some (.word dbv)
  qtop : s.locals "top" = some (.word topv)
  qres : s.locals "result" = some (.word resv)
  qcp : s.locals "cur_p" = some (.word cp)
  qcn : s.locals "cur_n" = some (.word cn)
  qmode : s.locals "mode" = some (.word md)
  qslot : s.locals "slot" = some (.word sl)
  qgo : s.locals "go" = some (.word gv)
  m1 : md ≠ 1#64
  m2 : md ≠ 2#64
  gv0 : gv ≠ 0#64
  mem : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ lim.toNat ≤ addr.toNat) → s.memory addr = M addr
  mu : dcMu a = sp.toNat * 2 ^ 73 + tT topv * 256 + icOf s.memory topv * 8 + rankOf md * 2 +
    goOf gv

theorem and_zero_w (x : Word) : (AndOp.and x (0#64) : Word) = 0#64 := by
  first
    | exact BitVec.and_zero
    | simp [AndOp.and]

local notation "HASHITE" => ((Prog.ite (Exp.op BinOp.and [(Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "hash") (Exp.const (BitVec.ofNat 64 0)))), (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "result") (Exp.const (BitVec.ofNat 64 0))))])
                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "result"), (Exp.const (BitVec.ofNat 64 24))]) (Exp.var VarKind.local "hash"))
                                      Prog.skip) : Prog Word)

set_option maxHeartbeats 4000000 in
/-- The child's hash goes to the hash cache of a non-null result. -/
theorem dc_hash (hE : GuestEnv E) {R : Reg} {resv hashv : Word} {ℓ : Nat}
    (hW : WorldTJ R s.globals s.memory) (hres : DRes R ℓ resv)
    (qres : s.locals "result" = some (.word resv))
    (qh : s.locals "hash" = some (.word hashv)) :
    WPs E s HASHITE (fun r => ∃ m', r = .normal s.locals s.globals m' s.ffi ∧
      WorldTJ R s.globals m' ∧
      ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) → m' x = s.memory x) := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  refine WPs.ite_both (fun w hw => ?_)
  split
  · exact WPs.skip ⟨s.memory, rfl, hW, fun _ _ => rfl⟩
  · rename_i hw0
    obtain ⟨va, vb, w', ha, hb, hop, hxw⟩ := eval_op2_inv hE.word hw
    have h1 := eval_cmp_inv hE (op := .notEqual) (of_eval (eval_const _ 0#64))
      (eval_cmp_inv hE (op := .notEqual) (of_eval (w := resv) (by lk [qres]))
        (of_eval (eval_const _ 0#64))) _ hb
    simp only [PanValue.word.injEq] at h1 hxw
    have hr0 : resv ≠ 0#64 := by
      rintro rfl
      subst h1 hxw
      simp [wordOp, evalPanCmp] at hop
      apply hw0
      rw [← hop]
      exact and_zero_w _
    obtain ⟨k, hK, -⟩ : ∃ k, R.Kd resv k ∧ R.Lv resv ℓ := by
      rcases hres with h | h
      · exact absurd h hr0
      · exact h
    obtain ⟨-, -, hlo, hhi, -⟩ := hW.kd hK
    have hsz := nodeSize_ge k
    have e24 : (resv + 24#64).toNat = resv.toNat + 24 := by bv_omega
    exact WPs.store hE (addr := resv + 24#64) (w := hashv) (eval_addc hE 24#64 qres)
      (of_eval (by lk [qh]))
      ⟨_, rfl, hW.cache_store hashv (c := 24) (Or.inr (Or.inr rfl)) hK,
        fun x hx => setCell_ne _ (NE (by omega))⟩

local notation "EXT" => ((Prog.seq
                                        (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "result") (Exp.const (BitVec.ofNat 64 0)))
                                          (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 8))])
                                          Prog.skip)
                                        (Prog.dec "ck" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "result"), (Exp.const (BitVec.ofNat 64 0))]))
                                          (Prog.seq
                                            (Prog.ite (Exp.op BinOp.and [(Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "ck") (Exp.const (BitVec.ofNat 64 3)))), (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "ck") (Exp.const (BitVec.ofNat 64 0))))])
                                              (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 8))])
                                              Prog.skip)
                                            (Prog.decCall "ex" Shape.one "node_new_ext" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 64))])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 72))])), (Exp.var VarKind.local "result")]
                                              (Prog.seq
                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "ex"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 48))])))
                                                (Prog.seq
                                                (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "ex"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 56))])))
                                                (Prog.seq
                                                (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))])))
                                                (Prog.assign VarKind.local "result" (Exp.var VarKind.local "ex"))))))))) : Prog Word)

set_option maxHeartbeats 16000000 in
/-- An extension record is popped: the extension is created over `result`. -/
theorem dc_ext (hE : GuestEnv E) (I : DecIface E) {R0 R : Reg}
    {G : VarName → Option (PanValue Word)} {M : Word → Option (PanValue Word)}
    {F : FfiState σ} {fv lim dbv : Word} {L0 : Nat} {a : St σ}
    {sp topv resv cp cn md sl gv prev seg sgl : Word} {ℓt : Nat}
    (c : D0Ctx I R0 R G M F fv lim dbv a s sp topv resv cp cn md sl gv)
    (h1 : topv ≠ 0#64) (h3 : sp.toNat ≤ topv.toNat) (h4 : topv.toNat + 88 ≤ lim.toNat)
    (r0 : Rd s.memory topv prev) (r64 : Rd s.memory (topv + 64#64) seg)
    (r72 : Rd s.memory (topv + 72#64) sgl) (hs1 : 1 ≤ sgl.toNat)
    (himm : ∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ seg.toNat ∧ seg.toNat + sgl.toNat ≤ hi.toNat)
    (htail : DStk R s.memory lim.toNat L0 (topv.toNat + 88) prev ℓt)
    (hres : DRes R (ℓt + sgl.toNat) resv) :
    WPs E s EXT (DcPost I R0 G M F fv lim dbv L0 a) := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hlim := lim.isLt
  have hfs := c.fs
  have hF := c.hF
  refine WPs.seqG (fun a' => a' = s ∧ resv ≠ 0#64) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    simp only [evalF_local, c.qres, eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i hw0
      exact WPs.skip ⟨rfl, by
        rintro rfl
        rw [hwv] at hw0
        simp [evalPanCmp] at hw0⟩
    · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
  intro a' ha'
  obtain ⟨ha', hr0⟩ := ha'
  rw [ha']
  clear ha' a'
  obtain ⟨k, hK, hLr⟩ : ∃ k, R.Kd resv k ∧ R.Lv resv (ℓt + sgl.toNat) := by
    rcases hres with h | h
    · exact absurd h hr0
    · exact h
  refine WPs.dec_w (fun ck => WPs.conseq (Q' := DcPost I R0 G M F fv lim dbv L0 a) ?_
    (fun r h => h.restore (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)))
  refine WPs.seqG (fun a' => a' = ⟨updatePanValueMap s.locals "ck" (.word ck), s.globals,
      s.memory, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
  rintro _ rfl
  refine WPs.decCall_ret (fun v g2 m2 f2 hret =>
    WPs.conseq (Q' := DcPost I R0 G M F fv lim dbv L0 a) ?_
      (fun r h => h.restore (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)))
  obtain ⟨lo, hi, hIm, a1, a2⟩ := himm
  obtain ⟨ex, hv, hf2, hW2, hg2, hm2⟩ := node_new_ext_ret hE hret (nib := seg) (nlen := sgl)
    (child := resv) (eval_load_rd hE (eval_addc hE 64#64 (by lk [c.qtop])) r64)
    (eval_load_rd hE (eval_addc hE 72#64 (by lk [c.qtop])) r72) (of_eval (by lk [c.qres])) hs1
    (Or.inr (c.w.kd hK).1) c.w ⟨lo, hi, hIm, a1, a2, (c.w.im_nibs hIm a1 a2).nibSeg⟩ ℓt
    (fun _ => hLr)
  simp only [List.cons.injEq, and_true] at hv
  subst hv
  dsimp only at hf2 hg2 hm2
  subst hf2
  have hKe := Reg.addNd_kd R ex 2#64 ℓt (ℓt + sgl.toNat)
  have hLe := Reg.Le.addNd R ex 2#64 ℓt (ℓt + sgl.toNat)
  obtain ⟨-, -, hexlo, hexhi, -⟩ := hW2.kd hKe
  have hsz2 : nodeSize 2#64 = 56 := by decide
  have ee8 : (ex + 8#64).toNat = ex.toNat + 8 := by bv_omega
  have ee16 : (ex + 16#64).toNat = ex.toNat + 16 := by bv_omega
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qex : L "ex" = some (.word ex) := by rw [hLL]; lk []
  have qdb' : L "db" = some (.word dbv) := by rw [hLL]; lk [c.qdb]
  have qtop' : L "top" = some (.word topv) := by rw [hLL]; lk [c.qtop]
  have qres' : L "result" = some (.word resv) := by rw [hLL]; lk [c.qres]
  have qcp' : L "cur_p" = some (.word cp) := by rw [hLL]; lk [c.qcp]
  have qcn' : L "cur_n" = some (.word cn) := by rw [hLL]; lk [c.qcn]
  have qmode' : L "mode" = some (.word md) := by rw [hLL]; lk [c.qmode]
  have qslot' : L "slot" = some (.word sl) := by rw [hLL]; lk [c.qslot]
  have qgo' : L "go" = some (.word gv) := by rw [hLL]; lk [c.qgo]
  clear hLL
  obtain ⟨w48, hw48⟩ := eval_load_any hE (s := (⟨L, g2, m2, s.ffi⟩ : St σ))
    (of_eval (eval_addc hE 48#64 qtop'))
  refine WPs.seq_store hE (addr := ex + 8#64) (w := w48) (eval_addc hE 8#64 qex) hw48 ?_
  obtain ⟨w56, hw56⟩ := eval_load_any hE
    (s := (⟨L, g2, setCell m2 (ex + 8#64) w48, s.ffi⟩ : St σ))
    (of_eval (eval_addc hE 56#64 qtop'))
  refine WPs.seq_store hE (addr := ex + 16#64) (w := w56) (eval_addc hE 16#64 qex) hw56 ?_
  have hm4 : ∀ x : Word, 2952790016 ≤ x.toNat →
      setCell (setCell m2 (ex + 8#64) w48) (ex + 16#64) w56 x = s.memory x := fun x hx => by
    rw [setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]
    exact hm2 x (Or.inr hx)
  have hm4l : ∀ x : Word, x.toNat + 8 ≤ HBASE →
      setCell (setCell m2 (ex + 8#64) w48) (ex + 16#64) w56 x = s.memory x := fun x hx => by
    rw [setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]
    exact hm2 x (Or.inl hx)
  have W4 : WorldTJ (R.addNd ex 2#64 ℓt (ℓt + sgl.toNat)) g2
      (setCell (setCell m2 (ex + 8#64) w48) (ex + 16#64) w56) :=
    (hW2.cache_store w48 (c := 8) (Or.inl rfl) hKe).cache_store w56 (c := 16)
      (Or.inr (Or.inl rfl)) hKe
  refine WPs.seq_asg (old := topv) (w := prev) qtop'
    (eval_load_rd hE (eval_addc hE 0#64 qtop') (by
      rw [BitVec.add_zero]
      unfold Rd at r0 ⊢
      dsimp only
      rw [hm4 _ (by omega)]
      exact r0)) ?_
  refine WPs.assign (old := resv) (w := ex) (by lk [qres']) (of_eval (by lk [qex])) ?_
  have hgs' : g2 "scratch_ptr" = some (.word sp) := (hg2 _ (by decide)).trans c.gs
  refine ⟨_, _, _, _, rfl, ⟨R.addNd ex 2#64 ℓt (ℓt + sgl.toNat), sp, prev, ex, cp, cn, md, sl, gv,
    ℓt, c.le.trans hLe, W4, c.ffi, fun x h1 h2 => (hg2 x h1).trans (c.glob x h1 h2), hgs',
    c.fs, c.spl, I.pre_mono c.pre hLe (fun x h1 _ => hg2 x h1),
    by lk [qdb'], by lk [], by lk [], by lk [qcp'], by lk [qcn'], by lk [qmode'],
    by lk [qslot'], by lk [qgo'],
    ((htail.mono hLe).frame hlim (fun x hx _ => hm4 x (by omega))).lower (by omega),
    fun _ _ => Or.inr ⟨2#64, hKe, Reg.addNd_lv R ex 2#64 ℓt (ℓt + sgl.toNat)⟩,
    fun h => absurd h c.gv0, fun h => absurd h c.m2,
    fun addr ha => by
      rcases ha with ha | ha
      · exact (hm4l addr ha).trans (c.mem addr (Or.inl ha))
      · exact (hm4 addr (by omega)).trans (c.mem addr (Or.inr ha))⟩, ?_⟩
  rw [c.mu, dcMu_eq (sp := sp) (t := prev) (md := md) (gv := gv) hgs' (by lk []) (by lk [qmode'])
    (by lk [qgo'])]
  dsimp only
  have hp := tT_pop hlim h1 (p := prev) (by
    rcases htail.top_in with h | h
    · exact Or.inl h
    · exact Or.inr h.1)
  have := icOf_le (setCell (setCell m2 (ex + 8#64) w48) (ex + 16#64) w56) prev
  have := icOf_le s.memory topv
  omega

end InitECandidate.Solver.GuestBound
