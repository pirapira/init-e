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

end InitECandidate.Solver.GuestBound
