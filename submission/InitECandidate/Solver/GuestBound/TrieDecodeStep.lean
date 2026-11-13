import InitECandidate.Solver.GuestBound.TrieResolve
import InitECandidate.Solver.GuestBound.TrieCompact
import InitECandidate.Solver.GuestBound.TrieFrozen
import InitECandidate.Solver.GuestBound.TrieDecStep2
import InitECandidate.Solver.GuestBound.RlpSlices
import InitECandidate.Solver.GuestBound.ScratchFrame
import InitECandidate.Solver.GuestBound.TrieNibKey

/-!
# `_decode_step` against the world invariant

`_decode_step(db, p, n)` decodes one RLP node: a leaf is created at once; an
extension or a branch gets a record in the scratch arena (the branch node is
created now, the extension after its child).  This is the `decode` field of
the decoder interface `DecIface`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem rlpdecodefully_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {pv fv pw : Word}
    (h : CalleeRet E s "rlp_decode_fully" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word pw))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧ ScrMem pv fv s.memory m ∧
      ∃ a b c d : Word, vs = [.rStruct [.word a, .word b, .word c, .word d]] := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 108 hE.functions (by guest_decl_at 108) (by decide +kernel)
    hlookup).2
  obtain ⟨v2, hv2⟩ : ∃ v2, values = [.word pw, v2] := by
    simp only [evalArgs_cons, evalArgs_nil, h1] at hvalues
    cases he2 : E.eval s e2 with
    | none => rw [he2] at hvalues; simp at hvalues
    | some v2 =>
      rw [he2] at hvalues
      simp at hvalues
      exact ⟨v2, hvalues.symm⟩
  subst hv2
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases rlp_decode_fully_frame hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    pv fv pw (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hp hf
    hfp hrun with hst | ⟨l', m', a, b, c, d, heq, hk⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hk, a, b, c, d, rfl⟩

theorem slices_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {pv fv pw lenv hv0 : Word}
    (h : CalleeRet E s "rlp_list_to_slices" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word pw)) (h2 : E.eval s e2 = some (.word lenv))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (hh : s.globals "heap_ptr" = some (.word hv0)) (hhH : InHeap hv0) :
    ffi = s.ffi ∧ ∃ qv c : Word, vs = [.rStruct [.word hv0, .word c]] ∧
      g = updatePanValueMap s.globals "heap_ptr" (.word qv) ∧
      hv0.toNat + 16 * c.toNat ≤ qv.toNat ∧ InHeap qv ∧
      ∀ x : Word, (x.toNat < fv.toNat ∨ pv.toNat ≤ x.toNat) →
        (x.toNat < hv0.toNat ∨ hv0.toNat + 16 * c.toNat ≤ x.toNat) → m x = s.memory x := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 115 hE.functions (by guest_decl_at 115) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases rlp_list_to_slices_frame hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    pv fv pw lenv hv0
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hp hf hfp hh hhH hrun with hst | ⟨l', qv, m', c, heq, hb, hqH, -, hfr⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, qv, c, rfl, rfl, hb, hqH, hfr⟩

theorem compactnib_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {pw nw hv0 : Word}
    (h : CalleeRet E s "compact_to_nibbles" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word pw)) (h2 : E.eval s e2 = some (.word nw))
    (hh : s.globals "heap_ptr" = some (.word hv0)) (hhH : InHeap hv0) :
    ffi = s.ffi ∧ ∃ qv b wl : Word, vs = [.rStruct [.word hv0, .word b, .word wl]] ∧
      g = updatePanValueMap s.globals "heap_ptr" (.word qv) ∧ InHeap qv ∧
      hv0.toNat + b.toNat ≤ qv.toNat ∧ Nibs m hv0 b.toNat ∧
      ∀ x : Word, (x.toNat < hv0.toNat ∨ qv.toNat ≤ x.toNat) → m x = s.memory x := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 249 hE.functions (by guest_decl_at 249) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases compact_to_nibbles_nib hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    pw nw hv0
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hh hhH hrun with hst | ⟨l', qv, m', b, wl, heq, hqH, hb, hnb, hfr⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, qv, b, wl, rfl, rfl, hqH, hb, hnb, hfr⟩

/-- A call whose first argument is a word load evaluated it to a word. -/
theorem calleeRet_load1 (hE : GuestEnv E) {f : FunName} {a1 : Exp Word}
    {rest : List (Exp Word)} {addr : Word}
    (h : CalleeRet E s f (.load .one a1 :: rest) vs g m ffi)
    (ha : ∀ y, E.eval s a1 = some y → y = .word addr) :
    ∃ pw : Word, E.eval s (.load .one a1) = some (.word pw) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  obtain ⟨y1, vs1, g1, -, -⟩ := evalArgs_cons_inv hvalues
  obtain ⟨w, hw⟩ := eval_load_any hE ha
  have := hw _ g1
  subst this
  exact ⟨w, g1⟩

end rets

/-- What `_decode_step` guarantees for a node at level `ℓ`. -/
def DsQ (R : Reg) (s0 : St σ) (sp fv : Word) (ℓ : Nat) (r : Result σ) : Prop :=
  ∃ l g m, ∃ (R' : Reg) (d0 d1 sp' : Word),
    r = .returned l g m s0.ffi [.rStruct [.word d0, .word d1]] ∧
    R.Le R' ∧ WorldTJ R' g m ∧
    (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = s0.globals x) ∧
    g "scratch_ptr" = some (.word sp') ∧ fv.toNat ≤ sp'.toNat ∧ sp'.toNat ≤ sp.toNat ∧
    (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ addr.toNat) →
      m addr = s0.memory addr) ∧
    (d0 = 0#64 → DRes R' ℓ d1) ∧
    (d0 ≠ 0#64 → sp' = d1 ∧ d1.toNat % 8 = 0 ∧ d1.toNat + 88 ≤ sp.toNat ∧ DRecNew R' m d1 ℓ)

theorem DsQ.restore {R : Reg} {s0 : St σ} {sp fv : Word} {ℓ : Nat} {x : VarName}
    {old : Option (PanValue Word)} {r : Result σ} (h : DsQ R s0 sp fv ℓ r) :
    DsQ R s0 sp fv ℓ (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g, m, R', d0, d1, sp', rfl, hk⟩ := h
  exact ⟨_, g, m, R', d0, d1, sp', rfl, hk⟩

/-- The facts carried through `_decode_step`; `s0` is the entry state. -/
structure DsCtx (R R1 : Reg) (s0 s : St σ) (sp fv pw nw arr hpv : Word) : Prop where
  le : R.Le R1
  w : WorldTJ R1 s.globals s.memory
  ffi : s.ffi = s0.ffi
  glob : ∀ x, x ≠ "heap_ptr" → s.globals x = s0.globals x
  gs : s0.globals "scratch_ptr" = some (.word sp)
  gfv : s0.globals "frame_mem_ptr" = some (.word fv)
  fs : fv.toNat ≤ sp.toNat
  hF : 2952790016 ≤ fv.toNat
  mem : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ addr.toNat) →
    s.memory addr = s0.memory addr
  hp : s.globals "heap_ptr" = some (.word hpv)
  hpH : InHeap hpv
  hpB : HBASE ≤ hpv.toNat
  qp : s.locals "p" = some (.word pw)
  qn : s.locals "n" = some (.word nw)
  qarr : s.locals "arr" = some (.word arr)

theorem DsCtx.gs' {R R1 : Reg} {s0 s : St σ} {sp fv pw nw arr hpv : Word}
    (c : DsCtx R R1 s0 s sp fv pw nw arr hpv) : s.globals "scratch_ptr" = some (.word sp) :=
  (c.glob _ (by decide)).trans c.gs

theorem DsCtx.gfv' {R R1 : Reg} {s0 s : St σ} {sp fv pw nw arr hpv : Word}
    (c : DsCtx R R1 s0 s sp fv pw nw arr hpv) :
    s.globals "frame_mem_ptr" = some (.word fv) :=
  (c.glob _ (by decide)).trans c.gfv

local notation "BRPROG" => ((Prog.seq
                    (Prog.ite (Exp.cmp Cmp.notEqual (Exp.rField 1 (Exp.var VarKind.local "sl")) (Exp.const (BitVec.ofNat 64 17)))
                      (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 4))])
                      Prog.skip)
                    (Prog.decCall "br" Shape.one "node_new_branch" []
                      (Prog.decCall "rec2" Shape.one "scratch_alloc" [(Exp.const (BitVec.ofNat 64 88))]
                        (Prog.seq
                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec2"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.const (BitVec.ofNat 64 2)))
                          (Prog.seq
                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec2"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.var VarKind.local "br"))
                          (Prog.seq
                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec2"), (Exp.const (BitVec.ofNat 64 24))]) (Exp.var VarKind.local "arr"))
                          (Prog.seq
                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec2"), (Exp.const (BitVec.ofNat 64 32))]) (Exp.const (BitVec.ofNat 64 0)))
                          (Prog.seq
                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec2"), (Exp.const (BitVec.ofNat 64 40))]) (Exp.const (BitVec.ofNat 64 0)))
                          (Prog.seq
                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec2"), (Exp.const (BitVec.ofNat 64 48))]) (Exp.var VarKind.local "p"))
                          (Prog.seq
                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec2"), (Exp.const (BitVec.ofNat 64 56))]) (Exp.var VarKind.local "n"))
                          (Prog.return (Exp.rStruct [(Exp.const (BitVec.ofNat 64 1)), (Exp.var VarKind.local "rec2")])))))))))))) : Prog Word)

set_option maxHeartbeats 16000000 in
/-- A branch: the node is created now, and a record with slot index 0. -/
theorem ds_branch (hE : GuestEnv E) {R R1 : Reg} {s0 : St σ} {sp fv pw nw arr hpv : Word}
    (ℓ : Nat) (c : DsCtx R R1 s0 s sp fv pw nw arr hpv) :
    WPs E s BRPROG (DsQ R s0 sp fv ℓ) := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hfs := c.fs
  have hF := c.hF
  have hsp := sp.isLt
  refine WPs.guard_quiet (mpt_fail_quiet hE) ?_
  refine WPs.decCall_ret (fun v g1 m1 f1 hret =>
    WPs.conseq (Q' := DsQ R s0 sp fv ℓ) ?_ (fun r h => h.restore))
  obtain ⟨a, hv, hf1, hW1, hg1, hm1⟩ := node_new_branch_ret hE hret c.w ℓ
  subst hv
  refine WPs.decCall_ret (fun vq g2 m2 f2 hret2 =>
    WPs.conseq (Q' := DsQ R s0 sp fv ℓ) ?_ (fun r h => h.restore))
  obtain ⟨hm2, hf2, q, hvq, hg2, hq1, hq2, hq8⟩ := scratchalloc_ret hE hret2 (pv := sp)
    (fv := fv) (nv := 88#64) (eval_const _ _) ((hg1 _ (by decide)).trans c.gs')
    ((hg1 _ (by decide)).trans c.gfv') c.fs
  subst hvq hg2
  dsimp only at hm2 hf2
  have hq2' : q.toNat + 88 ≤ sp.toNat := by simpa using hq2
  have eo : ∀ k : Nat, k ≤ 80 → (q + BitVec.ofNat 64 k).toNat = q.toNat + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e8 := eo 8 (by omega)
  have e16 := eo 16 (by omega)
  have e24 := eo 24 (by omega)
  have e32 := eo 32 (by omega)
  have e40 := eo 40 (by omega)
  have e48 := eo 48 (by omega)
  have e56 := eo 56 (by omega)
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qrec : L "rec2" = some (.word q) := by rw [hLL]; lk []
  have qbr : L "br" = some (.word a) := by rw [hLL]; lk []
  have qarr : L "arr" = some (.word arr) := by rw [hLL]; lk [c.qarr]
  have qp : L "p" = some (.word pw) := by rw [hLL]; lk [c.qp]
  have qn : L "n" = some (.word nw) := by rw [hLL]; lk [c.qn]
  clear hLL
  refine WPs.seq_store hE (addr := q + 8#64) (w := 2#64) (eval_addc hE 8#64 qrec)
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := q + 16#64) (w := a) (eval_addc hE 16#64 qrec)
    (of_eval (by lk [qbr])) ?_
  refine WPs.seq_store hE (addr := q + 24#64) (w := arr) (eval_addc hE 24#64 qrec)
    (of_eval (by lk [qarr])) ?_
  refine WPs.seq_store hE (addr := q + 32#64) (w := 0#64) (eval_addc hE 32#64 qrec)
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := q + 40#64) (w := 0#64) (eval_addc hE 40#64 qrec)
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := q + 48#64) (w := pw) (eval_addc hE 48#64 qrec)
    (of_eval (by lk [qp])) ?_
  refine WPs.seq_store hE (addr := q + 56#64) (w := nw) (eval_addc hE 56#64 qrec)
    (of_eval (by lk [qn])) ?_
  generalize hmf : setCell (setCell (setCell (setCell (setCell (setCell (setCell m2 (q + 8#64) 2#64)
    (q + 16#64) a) (q + 24#64) arr) (q + 32#64) 0#64) (q + 40#64) 0#64) (q + 48#64) pw)
    (q + 56#64) nw = mf
  have keep : ∀ x : Word, ¬ (q.toNat ≤ x.toNat ∧ x.toNat < q.toNat + 88) → mf x = m2 x := by
    intro x hx
    rw [← hmf, setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]
  have r8 : Rd mf (q + 8#64) 2#64 := by
    rw [← hmf]
    exact ((((((Rd.here m2 (q + 8#64) 2#64).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))
  have r16 : Rd mf (q + 16#64) a := by
    rw [← hmf]
    exact (((((Rd.here _ (q + 16#64) a).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))
  have r32 : Rd mf (q + 32#64) 0#64 := by
    rw [← hmf]
    exact (((Rd.here _ (q + 32#64) 0#64).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))
  refine WPs.ret_pair (a := 1#64) (b := q) (of_eval (eval_const _ _)) (of_eval (by lk [qrec])) ?_
  have hLe := Reg.Le.addNd R1 a 3#64 ℓ (ℓ + 1)
  have hWf : WorldTJ (R1.addNd a 3#64 ℓ (ℓ + 1)) (updatePanValueMap g1 "scratch_ptr" (.word q)) mf := by
    have hW2 : WorldTJ (R1.addNd a 3#64 ℓ (ℓ + 1)) g1 m2 := by
      rw [hm2]
      exact hW1
    exact hW2.scratch (fun x hx => by simp [update_lookup, hx]) (fun x hx => keep x (by omega))
  refine ⟨_, _, mf, R1.addNd a 3#64 ℓ (ℓ + 1), 1#64, q, q, by rw [hf2, hf1, c.ffi],
    c.le.trans hLe, hWf,
    fun x h1 h2 => by
      simp only [update_lookup]
      rw [if_neg (by simpa using h2)]
      exact (hg1 x h1).trans (c.glob x h1),
    by simp [update_lookup], hq1, by omega,
    fun addr ha => by
      rw [keep addr (by unfold HBASE at ha; omega), hm2]
      exact (hm1 addr (by omega)).trans (c.mem addr ha),
    fun h => absurd h (by decide),
    fun _ => ⟨rfl, hq8, hq2', Or.inr ⟨2#64, a, r8, by decide, r16,
      Reg.addNd_kd R1 a 3#64 ℓ (ℓ + 1), Reg.addNd_lv R1 a 3#64 ℓ (ℓ + 1), r32⟩⟩⟩

local notation "EXPROG" => ((Prog.decCall "pi" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) "rlp_item" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr"), (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 0)), (Exp.const (BitVec.ofNat 64 16))])])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr"), (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 0)), (Exp.const (BitVec.ofNat 64 16))]), (Exp.const (BitVec.ofNat 64 8))]))]
                        (Prog.seq
                          (Prog.ite (Exp.cmp Cmp.notEqual (Exp.rField 0 (Exp.var VarKind.local "pi")) (Exp.const (BitVec.ofNat 64 0)))
                            (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 5))])
                            Prog.skip)
                          (Prog.decCall "cn" (Shape.comb [Shape.one, Shape.one, Shape.one]) "compact_to_nibbles" [(Exp.rField 1 (Exp.var VarKind.local "pi")), (Exp.rField 2 (Exp.var VarKind.local "pi"))]
                            (Prog.seq
                              (Prog.ite (Exp.cmp Cmp.notEqual (Exp.rField 2 (Exp.var VarKind.local "cn")) (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.decCall "vi" (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one]) "rlp_item" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr"), (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 1)), (Exp.const (BitVec.ofNat 64 16))])])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "arr"), (Exp.panOp PanOp.mul [(Exp.const (BitVec.ofNat 64 1)), (Exp.const (BitVec.ofNat 64 16))]), (Exp.const (BitVec.ofNat 64 8))]))]
                                  (Prog.seq
                                    (Prog.ite (Exp.cmp Cmp.notEqual (Exp.rField 0 (Exp.var VarKind.local "vi")) (Exp.const (BitVec.ofNat 64 0)))
                                      (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 6))])
                                      Prog.skip)
                                    (Prog.decCall "lf" Shape.one "node_new_leaf" [(Exp.rField 0 (Exp.var VarKind.local "cn")), (Exp.rField 1 (Exp.var VarKind.local "cn")), (Exp.rField 1 (Exp.var VarKind.local "vi")), (Exp.rField 2 (Exp.var VarKind.local "vi"))]
                                      (Prog.seq
                                        (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "lf"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "p"))
                                        (Prog.seq
                                        (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "lf"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.var VarKind.local "n"))
                                        (Prog.return (Exp.rStruct [(Exp.const (BitVec.ofNat 64 0)), (Exp.var VarKind.local "lf")])))))))
                                Prog.skip)
                              (Prog.seq
                              (Prog.ite (Exp.cmp Cmp.equal (Exp.rField 1 (Exp.var VarKind.local "cn")) (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 7))])
                                Prog.skip)
                              (Prog.decCall "rec" Shape.one "scratch_alloc" [(Exp.const (BitVec.ofNat 64 88))]
                                (Prog.seq
                                  (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.const (BitVec.ofNat 64 1)))
                                  (Prog.seq
                                  (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec"), (Exp.const (BitVec.ofNat 64 24))]) (Exp.var VarKind.local "arr"))
                                  (Prog.seq
                                  (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec"), (Exp.const (BitVec.ofNat 64 48))]) (Exp.var VarKind.local "p"))
                                  (Prog.seq
                                  (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec"), (Exp.const (BitVec.ofNat 64 56))]) (Exp.var VarKind.local "n"))
                                  (Prog.seq
                                  (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec"), (Exp.const (BitVec.ofNat 64 64))]) (Exp.rField 0 (Exp.var VarKind.local "cn")))
                                  (Prog.seq
                                  (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "rec"), (Exp.const (BitVec.ofNat 64 72))]) (Exp.rField 1 (Exp.var VarKind.local "cn")))
                                  (Prog.return (Exp.rStruct [(Exp.const (BitVec.ofNat 64 1)), (Exp.var VarKind.local "rec")])))))))))))))) : Prog Word)

set_option maxHeartbeats 32000000 in
/-- A two-item node: a leaf is created at once, an extension gets a record. -/
theorem ds_ext (hE : GuestEnv E) {R R1 : Reg} {s0 : St σ} {sp fv pw nw arr hpv : Word}
    (ℓ : Nat) (c : DsCtx R R1 s0 s sp fv pw nw arr hpv) :
    WPs E s EXPROG (DsQ R s0 sp fv ℓ) := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hfs := c.fs
  have hF := c.hF
  have hsp := sp.isLt
  have hpE := c.hpH.1
  have hpB := c.hpB
  have dq : ∀ r, DsQ R s0 sp fv ℓ r → DsQ R s0 sp fv ℓ r := fun _ h => h
  refine WPs.decCall_ret (fun v g1 m1 f1 hret =>
    WPs.conseq (Q' := DsQ R s0 sp fv ℓ) ?_ (fun r h => h.restore))
  obtain ⟨pw1, hev⟩ := calleeRet_load1 hE hret (addr := arr + 0#64 * 16#64)
    (of_eval (by ev [c.qarr]))
  obtain ⟨hg1, hf1, hk1, a0, a1, a2, a3, hv⟩ := rlpitem_ret hE hret hev c.gs' c.gfv' c.fs
  simp only [List.cons.injEq, and_true] at hv
  subst hg1 hf1 hv
  have W1 : WorldTJ R1 s.globals m1 :=
    c.w.scratch (fun _ _ => rfl) (fun x hx => hk1 x (Or.inl (by omega)))
  refine WPs.guard_quiet (mpt_fail_quiet hE) ?_
  refine WPs.decCall_ret (fun v2 g2 m2 f2 hret2 =>
    WPs.conseq (Q' := DsQ R s0 sp fv ℓ) ?_ (fun r h => h.restore))
  obtain ⟨hf2, qv, b, wl, hv2, hg2, hqH, hb, hnb, hfr2⟩ := compactnib_ret hE hret2 (pw := a1)
    (nw := a2) (hv0 := hpv)
    (by rw [eval_rField _ 1 "pi" [.word a0, .word a1, .word a2, .word a3] (by lk [])]; rfl)
    (by rw [eval_rField _ 2 "pi" [.word a0, .word a1, .word a2, .word a3] (by lk [])]; rfl)
    c.hp c.hpH
  simp only [List.cons.injEq, and_true] at hv2
  dsimp only at hf2 hg2 hfr2
  subst hf2 hv2 hg2
  have hqE := hqH.1
  have ehb : (hpv + b).toNat = hpv.toNat + b.toNat := by
    rw [BitVec.toNat_add]
    omega
  have hIm : (R1.addIm hpv (hpv + b)).Im hpv (hpv + b) := Or.inr ⟨rfl, rfl⟩
  have hLe2 := Reg.Le.addIm R1 hpv (hpv + b)
  have W2 : WorldTJ (R1.addIm hpv (hpv + b))
      (updatePanValueMap s.globals "heap_ptr" (.word qv)) m2 :=
    WorldTJ.fresh_nibs W1 c.hp (by simp [updatePanValueMap]) hqH (by omega)
      (fun x hx => by simp [update_lookup, hx]) (fun a _ ha => hfr2 a (Or.inl ha))
      (fun a ha => hfr2 a (by unfold HBASE at ha hpB; omega)) (by rw [ehb]; exact hb)
      (by rw [ehb, Nat.add_sub_cancel_left]; exact hnb)
  have hgs2 : updatePanValueMap s.globals "heap_ptr" (.word qv) "scratch_ptr" = some (.word sp) := by
    simp (config := { decide := true }) [update_lookup, c.gs']
  have hgf2 : updatePanValueMap s.globals "heap_ptr" (.word qv) "frame_mem_ptr" =
      some (.word fv) := by
    simp (config := { decide := true }) [update_lookup, c.gfv']
  have hmem2 : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ addr.toNat) →
      m2 addr = s0.memory addr := fun addr ha =>
    (hfr2 addr (by unfold HBASE at ha hpB; omega)).trans
      ((hk1 addr (by unfold HBASE at ha; omega)).trans (c.mem addr ha))
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qcn : L "cn" = some (.rStruct [.word hpv, .word b, .word wl]) := by rw [hLL]; lk []
  have qarr : L "arr" = some (.word arr) := by rw [hLL]; lk [c.qarr]
  have qp : L "p" = some (.word pw) := by rw [hLL]; lk [c.qp]
  have qn : L "n" = some (.word nw) := by rw [hLL]; lk [c.qn]
  clear hLL
  have ecn : ∀ (i : Nat) (w : Word) (L' : VarName → Option (PanValue Word))
      (g' : VarName → Option (PanValue Word)) (m' : Word → Option (PanValue Word))
      (f' : FfiState σ), L' "cn" = some (.rStruct [.word hpv, .word b, .word wl]) →
      [PanValue.word hpv, .word b, .word wl][i]? = some (.word w) →
      E.eval ⟨L', g', m', f'⟩ (.rField i (.var .local "cn")) = some (.word w) := by
    intro i w L' g' m' f' h hi
    rw [eval_rField _ i "cn" _ h]
    exact hi
  refine WPs.seqG (fun a' => a' = ⟨L, updatePanValueMap s.globals "heap_ptr" (.word qv), m2,
      s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · -- a leaf
      refine WPs.conseq (Q' := DsQ R s0 sp fv ℓ) ?_ (fun r h => by
        obtain ⟨l, g, m, R', d0, d1, sp', rfl, hk⟩ := h
        exact ⟨l, g, m, R', d0, d1, sp', rfl, hk⟩)
      refine WPs.decCall_ret (fun v3 g3 m3 f3 hret3 =>
        WPs.conseq (Q' := DsQ R s0 sp fv ℓ) ?_ (fun r h => h.restore))
      obtain ⟨pw3, hev3⟩ := calleeRet_load1 hE hret3 (addr := arr + 1#64 * 16#64)
        (of_eval (by ev [qarr]))
      obtain ⟨hg3, hf3, hk3, b0, b1, b2, b3, hv3⟩ := rlpitem_ret hE hret3 hev3 hgs2 hgf2 c.fs
      simp only [List.cons.injEq, and_true] at hv3
      subst hg3 hf3 hv3
      have W3 : WorldTJ (R1.addIm hpv (hpv + b))
          (updatePanValueMap s.globals "heap_ptr" (.word qv)) m3 :=
        W2.scratch (fun _ _ => rfl) (fun x hx => hk3 x (Or.inl (by omega)))
      refine WPs.guard_quiet (mpt_fail_quiet hE) ?_
      have qvi : updatePanValueMap L "vi" (PanValue.rStruct [.word b0, .word b1, .word b2, .word b3])
          "vi" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]) := by lk []
      have qcn' : updatePanValueMap L "vi" (PanValue.rStruct [.word b0, .word b1, .word b2, .word b3])
          "cn" = some (.rStruct [.word hpv, .word b, .word wl]) := by lk [qcn]
      refine WPs.decCall_ret (fun v4 g4 m4 f4 hret4 =>
        WPs.conseq (Q' := DsQ R s0 sp fv ℓ) ?_ (fun r h => h.restore))
      obtain ⟨lf, hv4, hf4, hW4, hg4, hm4⟩ := node_new_leaf_ret hE hret4 (nib := hpv) (nlen := b)
        (vptr := b1) (vlen := b2) (of_eval (ecn 0 hpv _ _ _ _ qcn' rfl))
        (of_eval (ecn 1 b _ _ _ _ qcn' rfl))
        (of_eval (by rw [eval_rField _ 1 "vi" _ qvi]; rfl))
        (of_eval (by rw [eval_rField _ 2 "vi" _ qvi]; rfl)) W3
        (Or.inr ⟨hpv, hpv + b, hIm, Nat.le_refl _, by omega,
          (W3.im_nibs hIm (Nat.le_refl _) (by omega)).nibSeg⟩) ℓ
      subst hv4
      dsimp only at hf4 hg4 hm4
      have hKl := Reg.addNd_kd (R1.addIm hpv (hpv + b)) lf 1#64 ℓ ℓ
      have hLe3 := Reg.Le.addNd (R1.addIm hpv (hpv + b)) lf 1#64 ℓ ℓ
      obtain ⟨-, -, hllo, hlhi, -⟩ := hW4.kd hKl
      have hsz1 : nodeSize 1#64 = 64 := by decide
      rw [hsz1] at hlhi
      have el8 : (lf + 8#64).toNat = lf.toNat + 8 := by
        rw [BitVec.toNat_add, show (8#64 : Word).toNat = 8 from rfl]
        omega
      have el16 : (lf + 16#64).toNat = lf.toNat + 16 := by
        rw [BitVec.toNat_add, show (16#64 : Word).toNat = 16 from rfl]
        omega
      refine WPs.seq_store hE (addr := lf + 8#64) (w := pw) (eval_addc hE 8#64 (by lk []))
        (of_eval (by lk [qp])) ?_
      refine WPs.seq_store hE (addr := lf + 16#64) (w := nw) (eval_addc hE 16#64 (by lk []))
        (of_eval (by lk [qn])) ?_
      have W5 := (hW4.cache_store pw (c := 8) (Or.inl rfl) hKl).cache_store nw (c := 16)
        (Or.inr (Or.inl rfl)) hKl
      refine WPs.ret_pair (a := 0#64) (b := lf) (of_eval (eval_const _ _)) (of_eval (by lk [])) ?_
      refine ⟨_, _, _, _, 0#64, lf, sp, by rw [hf4, c.ffi], c.le.trans (hLe2.trans hLe3), W5,
        fun x h1 h2 => (hg4 x h1).trans (by
          simp only [update_lookup]
          rw [if_neg (by simpa using h1)]
          exact c.glob x h1),
        (hg4 _ (by decide)).trans hgs2, c.fs, Nat.le_refl _,
        fun addr ha => by
          have n1 : addr ≠ lf + 16#64 := NE (by unfold HBASE at ha hllo; omega)
          have n2 : addr ≠ lf + 8#64 := NE (by unfold HBASE at ha hllo; omega)
          show setCell (setCell m4 (lf + 8#64) pw) (lf + 16#64) nw addr = _
          rw [setCell_ne _ n1, setCell_ne _ n2, hm4 addr (by omega),
            hk3 addr (by unfold HBASE at ha; omega)]
          exact hmem2 addr ha,
        fun _ => Or.inr ⟨1#64, hKl, Reg.addNd_lv (R1.addIm hpv (hpv + b)) lf 1#64 ℓ ℓ⟩,
        fun h => absurd rfl h⟩
  intro a' ha'
  rw [ha']
  clear ha' a'
  -- an extension: its segment must not be empty
  refine WPs.seqG (fun a' => a' = ⟨L, updatePanValueMap s.globals "heap_ptr" (.word qv), m2,
      s.ffi⟩ ∧ b ≠ 0#64) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    rw [ecn 1 b _ _ _ _ qcn rfl] at hx
    simp only [eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i hw0
      exact WPs.skip ⟨rfl, by
        rintro rfl
        rw [hwv] at hw0
        simp [evalPanCmp] at hw0⟩
    · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
  intro a' ha'
  obtain ⟨ha', hb0⟩ := ha'
  rw [ha']
  clear ha' a'
  have hb1 : 1 ≤ b.toNat := by
    by_contra hlt
    exact hb0 (BitVec.eq_of_toNat_eq (by simp; omega))
  refine WPs.decCall_ret (fun vq g5 m5 f5 hret5 =>
    WPs.conseq (Q' := DsQ R s0 sp fv ℓ) ?_ (fun r h => h.restore))
  obtain ⟨hm5, hf5, q, hvq, hg5, hq1, hq2, hq8⟩ := scratchalloc_ret hE hret5 (pv := sp)
    (fv := fv) (nv := 88#64) (eval_const _ _) hgs2 hgf2 c.fs
  subst hvq hg5
  dsimp only at hm5 hf5
  have hq2' : q.toNat + 88 ≤ sp.toNat := by simpa using hq2
  have eo : ∀ k : Nat, k ≤ 80 → (q + BitVec.ofNat 64 k).toNat = q.toNat + k := by
    intro k hk
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e8 := eo 8 (by omega)
  have e24 := eo 24 (by omega)
  have e48 := eo 48 (by omega)
  have e56 := eo 56 (by omega)
  have e64 := eo 64 (by omega)
  have e72 := eo 72 (by omega)
  have qrec : updatePanValueMap L "rec" (PanValue.word q) "rec" = some (.word q) := by lk []
  have qcn2 : updatePanValueMap L "rec" (PanValue.word q) "cn" =
      some (.rStruct [.word hpv, .word b, .word wl]) := by lk [qcn]
  refine WPs.seq_store hE (addr := q + 8#64) (w := 1#64) (eval_addc hE 8#64 qrec)
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := q + 24#64) (w := arr) (eval_addc hE 24#64 qrec)
    (of_eval (by lk [qarr])) ?_
  refine WPs.seq_store hE (addr := q + 48#64) (w := pw) (eval_addc hE 48#64 qrec)
    (of_eval (by lk [qp])) ?_
  refine WPs.seq_store hE (addr := q + 56#64) (w := nw) (eval_addc hE 56#64 qrec)
    (of_eval (by lk [qn])) ?_
  refine WPs.seq_store hE (addr := q + 64#64) (w := hpv) (eval_addc hE 64#64 qrec)
    (of_eval (ecn 0 hpv _ _ _ _ qcn2 rfl)) ?_
  refine WPs.seq_store hE (addr := q + 72#64) (w := b) (eval_addc hE 72#64 qrec)
    (of_eval (ecn 1 b _ _ _ _ qcn2 rfl)) ?_
  generalize hmf : setCell (setCell (setCell (setCell (setCell (setCell m5 (q + 8#64) 1#64)
    (q + 24#64) arr) (q + 48#64) pw) (q + 56#64) nw) (q + 64#64) hpv) (q + 72#64) b = mf
  have keep : ∀ x : Word, ¬ (q.toNat ≤ x.toNat ∧ x.toNat < q.toNat + 88) → mf x = m5 x := by
    intro x hx
    rw [← hmf, setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega))]
  have r8 : Rd mf (q + 8#64) 1#64 := by
    rw [← hmf]
    exact (((((Rd.here m5 (q + 8#64) 1#64).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))
  have r64 : Rd mf (q + 64#64) hpv := by
    rw [← hmf]
    exact (Rd.here _ (q + 64#64) hpv).frame _ (NE (by omega))
  have r72 : Rd mf (q + 72#64) b := by
    rw [← hmf]
    exact Rd.here _ (q + 72#64) b
  refine WPs.ret_pair (a := 1#64) (b := q) (of_eval (eval_const _ _)) (of_eval (by lk [])) ?_
  have hWf : WorldTJ (R1.addIm hpv (hpv + b)) (updatePanValueMap (updatePanValueMap s.globals
      "heap_ptr" (.word qv)) "scratch_ptr" (.word q)) mf := by
    have hW5 : WorldTJ (R1.addIm hpv (hpv + b))
        (updatePanValueMap s.globals "heap_ptr" (.word qv)) m5 := by
      rw [hm5]
      exact W2
    exact hW5.scratch (fun x hx => by simp [update_lookup, hx]) (fun x hx => keep x (by omega))
  refine ⟨_, _, mf, R1.addIm hpv (hpv + b), 1#64, q, q, by rw [hf5, c.ffi], c.le.trans hLe2,
    hWf,
    fun x h1 h2 => by
      simp only [update_lookup]
      rw [if_neg (by simpa using h2), if_neg (by simpa using h1)]
      exact c.glob x h1,
    by simp [update_lookup], hq1, by omega,
    fun addr ha => by
      rw [keep addr (by unfold HBASE at ha; omega), hm5]
      exact hmem2 addr ha,
    fun h => absurd h (by decide),
    fun _ => ⟨rfl, hq8, hq2', Or.inl ⟨r8, hpv, b, r64, r72, hb1,
      ⟨hpv, hpv + b, hIm, Nat.le_refl _, by omega⟩⟩⟩⟩


set_option maxHeartbeats 16000000 in
theorem decode_step_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_decode_step" E.functions = some (parameters, body))
    (R : Reg) (s : St σ) (r : Result σ) (sp fv pw nw : Word) (ℓ : Nat)
    (hpw : s.locals "p" = some (.word pw)) (hnw : s.locals "n" = some (.word nw))
    (hp : s.globals "scratch_ptr" = some (.word sp))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ sp.toNat)
    (hF : 2952790016 ≤ fv.toNat) (hW : WorldTJ R s.globals s.memory)
    (h : Runs E s body r) : Stopped r ∨ DsQ R s sp fv ℓ r := by
  have hbody := (fun_of_index 261 hE.functions (by guest_decl_at 261) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (DsQ R s sp fv ℓ)) r h
  obtain ⟨hv0, hh, hhH, hhB⟩ := hW.heap_ptr
  have hhE := hhH.1
  refine WPs.dec_ev (fun vit _ => WPs.conseq (Q' := DsQ R s sp fv ℓ) ?_ (fun r h => h.restore))
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DsQ R s sp fv ℓ) ?_ (fun r h => h.restore)
  try dsimp only
  generalize hL : updatePanValueMap (updatePanValueMap s.locals "it" vit) "e"
    (PanValue.word 0#64) = L
  have L_p : L "p" = some (.word pw) := by rw [← hL]; lk [hpw]
  have L_n : L "n" = some (.word nw) := by rw [← hL]; lk [hnw]
  refine WPs.seq (fun a => ∃ (m : Word → Option (PanValue Word)) (a0 a1 a2 a3 : Word),
      a = ⟨updatePanValueMap L "it" (.rStruct [.word a0, .word a1, .word a2, .word a3]),
        s.globals, m, s.ffi⟩ ∧ ScrMem sp fv s.memory m)
    (WPs.callHA_stop (fun s' r hr => stops_call_noReturn (mpt_fail_noReturn hE) hr)
      (fun v g m ffi hret => ?_)) ?_
  · obtain ⟨hg, hf', hk, a0, a1, a2, a3, hv⟩ := rlpdecodefully_ret hE hret (pw := pw)
      (by lk [L_p]) hp hf hfp
    simp only [List.cons.injEq, and_true] at hv
    subst g ffi v
    exact ⟨_, _, _, _, rfl, m, a0, a1, a2, a3, rfl, hk⟩
  rintro _ ⟨m, a0, a1, a2, a3, rfl, hk⟩
  generalize hL1 : updatePanValueMap L "it"
    (PanValue.rStruct [.word a0, .word a1, .word a2, .word a3]) = L1
  have L1_it : L1 "it" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]) := by
    rw [← hL1]; lk []
  have L1_p : L1 "p" = some (.word pw) := by rw [← hL1]; lk [L_p]
  have L1_n : L1 "n" = some (.word nw) := by rw [← hL1]; lk [L_n]
  have hW1 : WorldTJ R s.globals m :=
    hW.scratch (fun _ _ => rfl) (fun a ha => hk a (Or.inl (by omega)))
  have hmf : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ addr.toNat) →
      m addr = s.memory addr := fun addr ha =>
    hk addr (by unfold HBASE at ha; omega)
  refine WPs.seqG (fun a => a = ⟨L1, s.globals, m, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.seqG (fun a => a = ⟨L1, s.globals, m, s.ffi⟩) (WPs.ite_both (fun w2 _ => ?_))
        (fun a ha => by
          rw [ha]
          exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr))
      split
      · exact WPs.skip rfl
      · exact WPs.ret_pair (a := 0#64) (b := 0#64) (of_eval (eval_const _ _))
          (of_eval (eval_const _ _))
          ⟨_, _, _, R, 0#64, 0#64, sp, rfl, Reg.Le.refl R, hW1, fun _ _ _ => rfl, hp, hfp,
            Nat.le_refl _, hmf, fun _ => Or.inl rfl, fun h => absurd rfl h⟩
  intro a ha
  rw [ha]
  clear ha a
  refine WPs.decCall_ret (fun vs g2 m2 f2 hret2 =>
    WPs.conseq (Q' := DsQ R s sp fv ℓ) ?_ (fun r h => h.restore))
  obtain ⟨hf2, qv, c, hvs, hg2, hb, hqH, hfr2⟩ := slices_ret hE hret2 (pw := a1) (lenv := a2)
    (by rw [eval_rField _ 1 "it" _ L1_it]; rfl) (by rw [eval_rField _ 2 "it" _ L1_it]; rfl)
    hp hf hfp hh hhH
  simp only [List.cons.injEq, and_true] at hvs
  dsimp only at hf2 hg2 hfr2
  subst hf2 hvs hg2
  have hqE := hqH.1
  have hW2 : WorldTJ R (updatePanValueMap s.globals "heap_ptr" (.word qv)) m2 :=
    WorldTJ.grow hW1 hh (by simp [updatePanValueMap]) hqH (by omega)
      (fun x h1 _ => by simp [update_lookup, h1])
      (fun a ha => hfr2 a (Or.inl (by omega)) (Or.inl ha))
  refine WPs.dec (w := hv0) (of_eval (by
    rw [eval_rField _ 0 "sl" [.word hv0, .word c] (by lk [])]; rfl)) ?_
  refine WPs.conseq (Q' := DsQ R s sp fv ℓ) ?_ (fun r h => h.restore)
  have ctx : DsCtx R R s
      (⟨updatePanValueMap (updatePanValueMap L1 "sl" (.rStruct [.word hv0, .word c])) "arr"
        (.word hv0), updatePanValueMap s.globals "heap_ptr" (.word qv), m2, s.ffi⟩ : St σ)
      sp fv pw nw hv0 qv :=
    { le := Reg.Le.refl R, w := hW2, ffi := rfl,
      glob := fun x hx => by simp [update_lookup, hx],
      gs := hp, gfv := hf, fs := hfp, hF := hF,
      mem := fun addr ha => (hfr2 addr (by unfold HBASE at ha; omega)
        (by unfold HBASE at ha hhB; omega)).trans (hmf addr ha),
      hp := by simp [updatePanValueMap], hpH := hqH, hpB := by omega,
      qp := by lk [L1_p], qn := by lk [L1_n], qarr := by lk [] }
  refine WPs.seqG (fun a => a = (⟨updatePanValueMap (updatePanValueMap L1 "sl"
      (.rStruct [.word hv0, .word c])) "arr" (.word hv0),
      updatePanValueMap s.globals "heap_ptr" (.word qv), m2, s.ffi⟩ : St σ))
    (WPs.ite_both (fun w _ => ?_)) (fun a ha => by
      rw [ha]
      exact ds_branch hE ℓ ctx)
  split
  · exact WPs.skip rfl
  · exact (ds_ext hE ℓ ctx).conseq (fun r h => by
      obtain ⟨l, g, m, R', d0, d1, sp', rfl, hk⟩ := h
      exact ⟨l, g, m, R', d0, d1, sp', rfl, hk⟩)

/-- The `decode` field of the decoder interface. -/
theorem decode_spec (hE : GuestEnv E) (R : Reg) (s : St σ) (e1 e2 e3 : Exp Word)
    (dbv pw nw sp fv : Word) (ℓ : Nat) (v : PanValue Word)
    (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (ffi : FfiState σ)
    (hret : CalleeRet E s "_decode_step" [e1, e2, e3] [v] g m ffi)
    (h1 : E.eval s e1 = some (.word dbv)) (h2 : E.eval s e2 = some (.word pw))
    (h3 : E.eval s e3 = some (.word nw)) (hW : WorldTJ R s.globals s.memory)
    (hp : s.globals "scratch_ptr" = some (.word sp))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ sp.toNat)
    (hF : 2952790016 ≤ fv.toNat) :
    ffi = s.ffi ∧ ∃ (R' : Reg) (d0 d1 sp' : Word), v = .rStruct [.word d0, .word d1] ∧
      R.Le R' ∧ WorldTJ R' g m ∧
      (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = s.globals x) ∧
      g "scratch_ptr" = some (.word sp') ∧ fv.toNat ≤ sp'.toNat ∧ sp'.toNat ≤ sp.toNat ∧
      (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ addr.toNat) →
        m addr = s.memory addr) ∧
      (d0 = 0#64 → DRes R' ℓ d1) ∧
      (d0 ≠ 0#64 → sp' = d1 ∧ d1.toNat % 8 = 0 ∧ d1.toNat + 88 ≤ sp.toNat ∧
        DRecNew R' m d1 ℓ) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := hret
  have hparams := (fun_of_index 261 hE.functions (by guest_decl_at 261) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases decode_step_world hE parameters body hlookup R ⟨cl, s.globals, s.memory, s.ffi⟩ _
    sp fv pw nw ℓ
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hp hf hfp hF hW hrun with hst | ⟨l', g', m', R', d0, d1, sp', heq, rest⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, R', d0, d1, sp', rfl, rest⟩

/-- The decoder interface holds. -/
def decIface (hE : GuestEnv E) : DecIface E where
  Pre := fun _ _ => True
  pre_mono := fun _ _ _ => trivial
  decode := fun R s e1 e2 e3 dbv pw nw sp fv ℓ v g m ffi hret h1 h2 h3 hW _ hp hf hfp hF =>
    decode_spec hE R s e1 e2 e3 dbv pw nw sp fv ℓ v g m ffi hret h1 h2 h3 hW hp hf hfp hF
  resolve := fun R s e1 e2 e3 dbv pw nw sp fv ℓ v g m ffi hret h1 h2 h3 hW _ hp hf hfp hF =>
    resolve_spec hE R s e1 e2 e3 dbv pw nw sp fv ℓ v g m ffi hret h1 h2 h3 hW hp hf hfp hF

end InitECandidate.Solver.GuestBound
