import InitECandidate.Solver.GuestBound.HtabNode

/-!
# Hash tables: `htab_new_leaf`

After `htab_new_node`, the key is copied into the node's key slot and the node
becomes a leaf with the next insertion-order position.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `var x = htab_new_node(t)`. -/
theorem WPs.decCall_newnode (hE : GuestEnv E) {x : VarName} {body : Prog Word} {t pv : Word}
    {v : HtabV} {kind : Nat → NodeKind} {rep : KeyRep} {det : Nat → Prop}
    (ht : s.locals "t" = some (.word t)) (hok : HtabOKd s.memory t v kind rep det)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat)
    (h : ∀ g' m' n, NewNodeRel s.memory t v kind rep det s.globals pv m' g' n →
      WPs E ⟨updatePanValueMap s.locals x (.word n), g', m', s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "htab_new_node" [.var .local "t"] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 134 hE.functions (by guest_decl_at 134) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ht, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := htab_new_node_exec hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb
    t pv v kind rep det (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hok hp hpH hend hcallee
  rcases hpost with hst | ⟨l, g', m', n, rfl, hrel⟩
  · cases rb with
    | raised lr g m f ex v =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f => exact hout.elim
    | _ => exact absurd hst (fun h => h)
  · obtain ⟨r', -, hrun', rfl⟩ := hout
    rcases h g' m' n hrel r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

/-- `st a, v; rest` where the address, if it evaluates, is `addr`. -/
theorem WPs.seq_store_inv (hE : GuestEnv E) {a val : Exp Word} {q : Prog Word} {addr w : Word}
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : ∀ y, E.eval s val = some y → y = .word w)
    (h : WPs E ⟨s.locals, s.globals, setCell s.memory addr w, s.ffi⟩ q Q) :
    WPs E s (.seq (.store a val) q) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  obtain ⟨fuel, n, hrun⟩ := h1
  rcases store_word_inv hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · cases r1 with
    | error l g m f => simp only at hrest; subst hrest; exact Or.inl trivial
    | _ => cases herr
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  have := hv y hy
  subst this
  rw [hm w rfl] at hrest
  exact h r hrest

theorem ord_slot_addr {t : Word} {v : HtabV} (hlay : HtabLayout t v) {iv : Word}
    (hi : iv.toNat ≤ v.nc.toNat) : v.order + iv * 8#64 = orderSlot v iv.toNat := by
  have hmul : (iv * 8#64).toNat = iv.toNat * 8 := by
    obtain ⟨-, -, -, h4⟩ := hlay
    have h8 : (8#64 : Word).toNat = 8 := by decide
    rw [BitVec.toNat_mul, h8]
    exact Nat.mod_eq_of_lt (by omega)
  unfold orderSlot
  congr 1

/-- Memory after the stores of `htab_new_leaf`, on top of the key copy `mc`. -/
def leafMem (mc : Word → Option (PanValue Word)) (t : Word) (v : HtabV) (n val : Word) :
    Word → Option (PanValue Word) :=
  setCell (setCell (setCell (setCell (setCell (setCell mc (nodeField v n.toNat 0) 0#64)
    (nodeField v n.toNat 8) val) (nodeField v n.toNat 16) v.cnt) (nodeField v n.toNat 24)
    (v.kl * 8#64)) (orderSlot v v.cnt.toNat) n) (t + 24#64) (v.cnt + 1#64)

local notation "LEAF_TAIL" => ((Prog.dec "klen" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 0))])) (Prog.dec "stride" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 8))])) (Prog.seq (Prog.call (some (none, none)) "memcpy" [(Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 32))])), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.var VarKind.local "stride")])]), (Exp.var VarKind.local "key"), (Exp.var VarKind.local "klen")]) (Prog.dec "nodes" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 40))])) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 0))]) (Exp.const (BitVec.ofNat 64 0))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "value")) (Prog.dec "pos" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 24))])) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 16))]) (Exp.var VarKind.local "pos")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 24))]) (Exp.panOp PanOp.mul [(Exp.var VarKind.local "klen"), (Exp.const (BitVec.ofNat 64 8))])) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 48))])), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "pos"), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "n")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 24))]) (Exp.op BinOp.add [(Exp.var VarKind.local "pos"), (Exp.const (BitVec.ofNat 64 1))])) (Prog.return (Exp.var VarKind.local "n"))))))))))))) : Prog Word)

set_option maxHeartbeats 4000000 in
/-- `htab_new_leaf` after its `htab_new_node` call. -/
theorem leaf_tail (hE : GuestEnv E) {t n keyp val : Word} {v : HtabV} {kind : Nat → NodeKind}
    {rep : KeyRep} {det : Nat → Prop} (ht : s.locals "t" = some (.word t))
    (hn : s.locals "n" = some (.word n)) (hk : s.locals "key" = some (.word keyp))
    (hv : s.locals "value" = some (.word val)) (hok : HtabOKd s.memory t v kind rep det)
    (hn1 : n.toNat ≤ v.nc.toNat) (P : CpPre (v.keys + n * v.st) keyp v.kl)
    (hslot : (v.keys + n * v.st).toNat = v.keys.toNat + n.toNat * v.st.toNat) :
    WPs E s LEAF_TAIL (fun r => ∃ l mc, r = .returned l s.globals (leafMem mc t v n val) s.ffi
      [.word n] ∧ CopyInv s.memory (v.keys + n * v.st) keyp v.kl.toNat mc) := by
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  have hcl := hwf.cnt_le
  have hT : ∀ k, k < 88 → (t + BitVec.ofNat 64 k).toNat = t.toNat + k :=
    fun k hk => hdr_toNat hlay hk
  refine WPs.dec (eval_load_rd hE (eval_addc hE 0#64 ht) hkl) ?_
  refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 8#64 (by lk [ht])) hst) ?_
  refine WPs.seq_mem (fun m' => CopyInv s.memory (v.keys + n * v.st) keyp v.kl.toNat m')
    (WPs.call_memcpy hE (dst := v.keys + n * v.st) (src := keyp) (nW := v.kl)
      (eval_add2_inv hE (eval_load_rd hE (eval_addc hE (a := t) 32#64 (by lk [ht])) hkeys)
        (of_eval (w := n * v.st) (by ev [evalPanOp, hn])))
      (of_eval (by lk [hk])) (of_eval (by lk [])) P (fun m' hc => ⟨m', rfl, hc⟩)) ?_
  intro mc c
  -- header cells are below the key slot
  have hC : ∀ k, k ≤ 80 → mc (t + BitVec.ofNat 64 k) = s.memory (t + BitVec.ofNat 64 k) := by
    intro k hk
    exact c.cells _ (Or.inl (by rw [hT k (by omega), hslot]; omega))
  have hRd : ∀ (k : Nat) (w : Word), k ≤ 80 → Rd s.memory (t + BitVec.ofNat 64 k) w →
      Rd mc (t + BitVec.ofNat 64 k) w := by
    intro k w hk h
    unfold Rd
    rw [hC k hk]
    exact h
  have hnn : ∀ (o k : Nat), o < 32 → k < 88 →
      t + BitVec.ofNat 64 k ≠ nodeField v n.toNat o :=
    fun o k ho hk h => (hdr_ne_node hlay hn1 ho hk).mp h
  refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 40#64 (by lk [ht]))
    (hRd 40 _ (by omega) hnd)) ?_
  refine WPs.seq_store hE (eval_node hE hlay (idx := "n") hn1 (by lk []) (by lk [hn]) 0#64
    (by decide)) (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (eval_node hE hlay (idx := "n") hn1 (by lk []) (by lk [hn]) 8#64
    (by decide)) (of_eval (w := val) (by lk [hv])) ?_
  refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 24#64 (by lk [ht]))
    (((hRd 24 _ (by omega) hcnt).frame _ (hnn 0 24 (by omega) (by omega))).frame _
      (hnn 8 24 (by omega) (by omega)))) ?_
  refine WPs.seq_store hE (eval_node hE hlay (idx := "n") hn1 (by lk []) (by lk [hn]) 16#64
    (by decide)) (of_eval (w := v.cnt) (by lk [])) ?_
  refine WPs.seq_store hE (eval_node hE hlay (idx := "n") hn1 (by lk []) (by lk [hn]) 24#64
    (by decide)) (of_eval (w := v.kl * 8#64) (by ev [evalPanOp])) ?_
  refine WPs.seq_store_inv hE (addr := orderSlot v v.cnt.toNat) ?_ (of_eval (w := n) (by lk [hn])) ?_
  · rw [← ord_slot_addr hlay hcl]
    exact eval_add2_inv hE (eval_load_rd hE (eval_addc hE (a := t) 48#64 (by lk [ht]))
      (((((hRd 48 _ (by omega) hord).frame _ (hnn 0 48 (by omega) (by omega))).frame _
        (hnn 8 48 (by omega) (by omega))).frame _ (hnn 16 48 (by omega) (by omega))).frame _
        (hnn 24 48 (by omega) (by omega))))
      (of_eval (w := v.cnt * 8#64) (by ev [evalPanOp]))
  refine WPs.seq_store hE (eval_addc hE (a := t) 24#64 (by lk [ht]))
    (of_eval (eval_addc hE (a := v.cnt) 1#64 (by lk []))) ?_
  refine WPs.ret (of_eval (w := n) (by lk [hn])) ?_
  exact ⟨_, mc, rfl, c⟩

end InitECandidate.Solver.GuestBound
