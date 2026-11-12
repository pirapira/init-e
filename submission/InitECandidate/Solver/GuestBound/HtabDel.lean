import InitECandidate.Solver.GuestBound.Wp
import InitECandidate.Solver.GuestBound.MemEq

/-!
# Hash tables: `htab_del` of a stored key

Deleting the key of a live leaf always removes that leaf: the lookup finds
it, the key comparison succeeds, and the stores unlink it.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The table invariant: structure, crit-bit order, and the stored keys. -/
structure HtabOK (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV)
    (kind : Nat → NodeKind) (rep : KeyRep) : Prop where
  wf : HtabWF m t v kind
  keys : HtabKeys m v kind rep
  keys8 : v.keys.toNat % 8 = 0
  kl_st : v.kl.toNat ≤ v.st.toNat
  kl8 : v.kl.toNat * 8 < 2 ^ 64
  leaf_key : ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .leaf →
    ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs 8#64 m (v.keys + BitVec.ofNat 64 i * v.st) j (rep i j)

variable {s : St σ} {Q : Result σ → Prop} {t : Word} {v : HtabV}

theorem of_eval {e : Exp Word} {w : Word} (h : E.eval s e = some (.word w)) :
    ∀ y, E.eval s e = some y → y = .word w := by
  intro y hy
  rw [h] at hy
  exact (Option.some.inj hy).symm

/-- A word load from a known address holding `w`. -/
theorem eval_load_rd (hE : GuestEnv E) {a : Exp Word} {addr w : Word}
    (ha : E.eval s a = some (.word addr)) (hw : Rd s.memory addr w) :
    ∀ y, E.eval s (.load .one a) = some y → y = .word w := by
  intro y hy
  obtain ⟨addr', w', ha', rfl, hm⟩ := eval_load_one hE.mem hy
  rw [ha] at ha'
  simp only [Option.some.injEq, PanValue.word.injEq] at ha'
  subst ha'
  rw [Rd.inj hm hw]

/-- The address of a node field. -/
theorem eval_node (hE : GuestEnv E) {t : Word} {v : HtabV} (hlay : HtabLayout t v)
    {idx : VarName} {iv : Word} (hi : iv.toNat ≤ v.nc.toNat)
    (hnodes : s.locals "nodes" = some (.word v.nodes)) (hidx : s.locals idx = some (.word iv))
    (off : Word) (hoff : off.toNat < 32) :
    E.eval s (.op .add [.var .local "nodes", .panOp .mul [.var .local idx, .const 32#64],
      .const off]) = some (.word (nodeField v iv.toNat off.toNat)) := by
  rw [← nodeField_eq hlay hi off hoff]
  ev [hnodes, hidx, evalPanOp, BitVec.add_assoc]

/-- The address of an order slot. -/
theorem eval_ord (hE : GuestEnv E) {t : Word} {v : HtabV} (hlay : HtabLayout t v)
    {idx : VarName} {iv : Word} (hi : iv.toNat ≤ v.nc.toNat)
    (horder : s.locals "order" = some (.word v.order)) (hidx : s.locals idx = some (.word iv)) :
    E.eval s (.op .add [.var .local "order", .panOp .mul [.var .local idx, .const 8#64]]) =
      some (.word (orderSlot v iv.toNat)) := by
  have hmul : (iv * 8#64).toNat = iv.toNat * 8 := by
    obtain ⟨-, -, -, h4⟩ := hlay
    have h8 : (8#64 : Word).toNat = 8 := by decide
    rw [BitVec.toNat_mul, h8]
    exact Nat.mod_eq_of_lt (by omega)
  have : v.order + iv * 8#64 = orderSlot v iv.toNat := by
    unfold orderSlot
    congr 1
  rw [← this]
  ev [horder, hidx, evalPanOp]

/-- `var x = htab_find_leaf(t, key)` for the stored key of the live leaf `Lw`. -/
theorem WPs.decCall_find (hE : GuestEnv E) {x : VarName} {body : Prog Word} {t kp Lw : Word}
    {v : HtabV} {kind : Nat → NodeKind} {rep : KeyRep}
    (ht : s.locals "t" = some (.word t)) (hkp : s.locals "key" = some (.word kp))
    (hwf : HtabWF s.memory t v kind) (hk : HtabKeys s.memory v kind rep)
    (hL : LiveN v kind Lw.toNat) (hLk : kind Lw.toNat = .leaf)
    (hkey : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs 8#64 s.memory kp j (rep Lw.toNat j))
    (h : WPs E ⟨updatePanValueMap s.locals x (.word Lw), s.globals, s.memory, s.ffi⟩ body
      (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "htab_find_leaf" [.var .local "t", .var .local "key"] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 131 hE.functions (by guest_decl_at 131) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ht, hkp, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := htab_find_self_runs hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩
    rb t v kind rep kp Lw (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hwf hk hL hLk
    (by rw [hE.bytes]; exact hkey) hcallee
  rcases hpost with hst | ⟨l, rfl⟩
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
    rcases h r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

/-- `var x = memeq(e1, e2, e3)` with both pointers equal. -/
theorem WPs.decCall_memeq (hE : GuestEnv E) {x : VarName} {body : Prog Word}
    {e1 e2 e3 : Exp Word} {pa n : Word} (h1 : E.eval s e1 = some (.word pa))
    (h2 : E.eval s e2 = some (.word pa)) (h3 : E.eval s e3 = some (.word n))
    (h : WPs E ⟨updatePanValueMap s.locals x (.word 1#64), s.globals, s.memory, s.ffi⟩ body
      (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "memeq" [e1, e2, e3] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 18 hE.functions (by guest_decl_at 18) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := memeq_self hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hcallee
  cases rb with
  | returned lr g m f vs =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpost
    obtain ⟨r', -, hrun', rfl⟩ := hout
    rcases h r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq
  | raised lr g m f ex v =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m f ev =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | _ => exact hout.elim

/-- `a; rest` where `a` is a guard that does not fire. -/
theorem WPs.guard0 {c : Exp Word} {p q : Prog Word}
    (hc : ∀ x, E.eval s c = some x → x = .word 0#64) (h : WPs E s q Q) :
    WPs E s (.seq (.ite c p .skip) q) Q := by
  refine WPs.seq (fun s' => s' = s) (WPs.ite hc ?_) (fun s' hs' => hs' ▸ h)
  split
  · exact WPs.skip ⟨_, _, _, _, rfl, rfl⟩
  · rename_i hne
    exact absurd rfl hne

/-- Sequencing when the first part only changes memory. -/
theorem WPs.seq_mem {p q : Prog Word} (P : (Word → Option (PanValue Word)) → Prop)
    (hp : WPs E s p (fun r1 => ∃ m', r1 = .normal s.locals s.globals m' s.ffi ∧ P m'))
    (hq : ∀ m', P m' → WPs E ⟨s.locals, s.globals, m', s.ffi⟩ q Q) :
    WPs E s (.seq p q) Q := by
  refine WPs.seq (fun s' => ∃ m', s' = ⟨s.locals, s.globals, m', s.ffi⟩ ∧ P m') ?_ ?_
  · exact hp.conseq (fun r ⟨m', hr, hP⟩ => ⟨_, _, _, _, hr, m', rfl, hP⟩)
  · rintro s' ⟨m', rfl, hP⟩
    exact hq m' hP

/-- `st a, v; rest`. -/
theorem WPs.seq_store (hE : GuestEnv E) {a val : Exp Word} {q : Prog Word} {addr w : Word}
    (ha : E.eval s a = some (.word addr)) (hv : ∀ y, E.eval s val = some y → y = .word w)
    (h : WPs E ⟨s.locals, s.globals, setCell s.memory addr w, s.ffi⟩ q Q) :
    WPs E s (.seq (.store a val) q) Q :=
  WPs.seq_mem (fun m' => m' = setCell s.memory addr w) (WPs.store hE ha hv ⟨_, rfl, rfl⟩)
    (fun _ hm => hm ▸ h)

-- Look up a local through declarations.
macro "lk" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := { decide := true }) [evalF_local, update_lookup, $hs,*])

set_option maxHeartbeats 1000000 in
/-- The order fix of `htab_del`: the last ordinal moves to the freed position.
When the leaf already is the last one, the stores would write what is there. -/
theorem del_phaseA (hE : GuestEnv E) {t : Word} {v : HtabV} (hlay : HtabLayout t v)
    {pos cnt1 moved : Word} (h_t : s.locals "t" = some (.word t))
    (h_nodes : s.locals "nodes" = some (.word v.nodes))
    (h_pos : s.locals "pos" = some (.word pos)) (h_count : s.locals "count" = some (.word cnt1))
    (hpnc : pos.toNat ≤ v.nc.toNat) (hcnc : cnt1.toNat ≤ v.nc.toNat)
    (hmnc : moved.toNat ≤ v.nc.toNat) (hord : Rd s.memory (t + 48#64) v.order)
    (hmoved : Rd s.memory (orderSlot v cnt1.toNat) moved)
    (hsame : pos = cnt1 → Rd s.memory (nodeField v moved.toNat 16) pos) :
    WPs E s
      (.ite (.cmp .notEqual (.var .local "pos") (.var .local "count"))
        (.dec "order" .one (.load .one (.op .add [.var .local "t", .const 48#64]))
          (.dec "moved" .one (.load .one (.op .add [.var .local "order",
              .panOp .mul [.var .local "count", .const 8#64]]))
            (.seq
              (.store (.op .add [.var .local "order", .panOp .mul [.var .local "pos",
                .const 8#64]]) (.var .local "moved"))
              (.store (.op .add [.var .local "nodes", .panOp .mul [.var .local "moved",
                .const 32#64], .const 16#64]) (.var .local "pos")))))
        .skip)
      (fun r1 => r1 = .normal s.locals s.globals
        (setCell (setCell s.memory (orderSlot v pos.toNat) moved) (nodeField v moved.toNat 16)
          pos) s.ffi) := by
  apply WPs.ite_both
  intro w hw
  simp only [evalF_cmp hE.word, evalF_local, h_pos, h_count, Option.some.injEq,
    PanValue.word.injEq] at hw
  by_cases hpc : pos = cnt1
  · subst hpc
    have hw0 : w = 0 := by rw [← hw]; simp [evalPanCmp]
    rw [if_pos hw0]
    apply WPs.skip
    rw [setCell_same hmoved, setCell_same (hsame rfl)]
  · have hw0 : w ≠ 0 := by rw [← hw]; simp [evalPanCmp, hpc]
    rw [if_neg hw0]
    refine WPs.dec (eval_load_rd hE (eval_addc hE 48#64 h_t) hord) ?_
    refine WPs.dec (eval_load_rd hE (eval_ord hE hlay (idx := "count") hcnc (by lk [])
      (by lk [h_count])) hmoved) ?_
    refine WPs.seq_store hE (eval_ord hE hlay (idx := "pos") hpnc (by lk [])
      (by lk [h_pos])) (of_eval (w := moved) (by lk [])) ?_
    refine WPs.store hE (eval_node hE hlay (idx := "moved") hmnc (by lk [h_nodes])
      (by lk []) 16#64 (by decide)) (of_eval (w := pos) (by lk [h_pos])) ?_
    simp only [restorePanValueFfiLocal]
    rw [restore_update, restore_update]
    rfl

theorem eval_cmp_inv (hE : GuestEnv E) {op : Cmp} {a b : Exp Word} {wa wb : Word}
    (ha : ∀ y, E.eval s a = some y → y = .word wa) (hb : ∀ y, E.eval s b = some y → y = .word wb) :
    ∀ x, E.eval s (.cmp op a b) = some x → x = .word (evalPanCmp op wa wb) := by
  intro x hx
  rw [evalF_cmp hE.word] at hx
  cases hea : E.eval s a with
  | none => rw [hea] at hx; cases hx
  | some ya =>
    have := ha ya hea
    subst this
    cases heb : E.eval s b with
    | none => rw [hea, heb] at hx; cases hx
    | some yb =>
      have := hb yb heb
      subst this
      rw [hea, heb] at hx
      exact (Option.some.inj hx).symm

theorem Rd.frame {m : Word → Option (PanValue Word)} {a a' w : Word} (x : Word)
    (h : Rd m a w) (hne : a ≠ a') : Rd (setCell m a' x) a w := by
  rw [rd_setCell, if_neg hne]
  exact h

theorem Rd.here (m : Word → Option (PanValue Word)) (a x : Word) : Rd (setCell m a x) a x := by
  rw [rd_setCell, if_pos rfl]

theorem update_same (l : VarName → Option (PanValue Word)) (x : VarName) (v : PanValue Word)
    (h : l x = some v) : updatePanValueMap l x v = l := by
  funext y
  simp only [update_lookup]
  by_cases hy : (y == x) = true
  · rw [if_pos hy, beq_iff_eq.mp hy, h]
  · rw [if_neg hy]

theorem update_update (l : VarName → Option (PanValue Word)) (x : VarName)
    (v v' : PanValue Word) :
    updatePanValueMap (updatePanValueMap l x v) x v' = updatePanValueMap l x v' := by
  funext y
  simp only [update_lookup]
  by_cases hy : (y == x) = true
  · simp only [hy, if_true]
  · simp only [hy]
    rfl

/-- The cell that links to the parent `p` of the deleted leaf. -/
def delX (t : Word) (v : HtabV) (g gl p : Word) : Word :=
  if g = 0#64 then t + 56#64 else if gl = p then nodeField v g.toNat 8 else nodeField v g.toNat 16

/-- Memory after unlinking the leaf `Lw` (order already fixed). -/
def delB (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV)
    (Lw rootv p g lc rc gl fr : Word) : Word → Option (PanValue Word) :=
  if rootv = Lw then setCell m (t + 56#64) 0#64
  else
    setCell (setCell (setCell (setCell m (nodeField v (if lc = Lw then rc else lc).toNat 0) g)
      (delX t v g gl p) (if lc = Lw then rc else lc)) (nodeField v p.toNat 0) fr) (t + 72#64) p

theorem delX_ne_free (hlay : HtabLayout t v) {g gl p : Word} (hg : g.toNat ≤ v.nc.toNat) :
    t + 72#64 ≠ delX t v g gl p := by
  unfold delX
  split
  · exact fun h => by have := (hdr_eq_hdr hlay (k := 72) (k' := 56) (by omega) (by omega)).mp h; omega
  · split
    · exact fun h => (hdr_ne_node hlay hg (by omega) (by omega)).mp h
    · exact fun h => (hdr_ne_node hlay hg (by omega) (by omega)).mp h

set_option maxHeartbeats 2000000 in
/-- The unlink of `htab_del`: the root is cleared, or the sibling of the leaf
takes the place of their parent, which goes to the free list. -/
theorem del_phaseB (hE : GuestEnv E) (hlay : HtabLayout t v)
    {Lw rootv p g lc rc gl fr : Word} (h_t : s.locals "t" = some (.word t))
    (h_nodes : s.locals "nodes" = some (.word v.nodes))
    (h_leaf : s.locals "leaf" = some (.word Lw)) (hroot : Rd s.memory (t + 56#64) rootv)
    (hLnc : Lw.toNat ≤ v.nc.toNat) (hfr : Rd s.memory (t + 72#64) fr)
    (hsp : rootv ≠ Lw → Rd s.memory (nodeField v Lw.toNat 0) p ∧ p.toNat ≤ v.nc.toNat ∧
      Rd s.memory (nodeField v p.toNat 0) g ∧ g.toNat ≤ v.nc.toNat ∧
      Rd s.memory (nodeField v p.toNat 8) lc ∧ Rd s.memory (nodeField v p.toNat 16) rc ∧
      (if lc = Lw then rc else lc).toNat ≤ v.nc.toNat ∧
      (g ≠ 0#64 → Rd s.memory (nodeField v g.toNat 8) gl)) :
    WPs E s
      (.ite (.cmp .equal (.var .local "leaf") (.load .one (.op .add [.var .local "t", .const 56#64])))
        (.store (.op .add [.var .local "t", .const 56#64]) (.const 0#64))
        (.dec "p" .one (.load .one (.op .add [.var .local "nodes", .panOp .mul [.var .local "leaf", .const 32#64], .const 0#64]))
          (.dec "g" .one (.load .one (.op .add [.var .local "nodes", .panOp .mul [.var .local "p", .const 32#64], .const 0#64]))
            (.dec "s" .one (.load .one (.op .add [.var .local "nodes", .panOp .mul [.var .local "p", .const 32#64], .const 8#64]))
              (.seq (.ite (.cmp .equal (.var .local "s") (.var .local "leaf"))
                  (.assign .local "s" (.load .one (.op .add [.var .local "nodes", .panOp .mul [.var .local "p", .const 32#64], .const 16#64]))) .skip)
                (.seq (.store (.op .add [.var .local "nodes", .panOp .mul [.var .local "s", .const 32#64], .const 0#64]) (.var .local "g"))
                  (.seq (.ite (.cmp .equal (.var .local "g") (.const 0#64))
                      (.store (.op .add [.var .local "t", .const 56#64]) (.var .local "s"))
                      (.ite (.cmp .equal (.load .one (.op .add [.var .local "nodes", .panOp .mul [.var .local "g", .const 32#64], .const 8#64])) (.var .local "p"))
                        (.store (.op .add [.var .local "nodes", .panOp .mul [.var .local "g", .const 32#64], .const 8#64]) (.var .local "s"))
                        (.store (.op .add [.var .local "nodes", .panOp .mul [.var .local "g", .const 32#64], .const 16#64]) (.var .local "s"))))
                    (.seq (.store (.op .add [.var .local "nodes", .panOp .mul [.var .local "p", .const 32#64], .const 0#64]) (.load .one (.op .add [.var .local "t", .const 72#64])))
                      (.store (.op .add [.var .local "t", .const 72#64]) (.var .local "p"))))))))))
      (fun r1 => r1 = .normal s.locals s.globals (delB s.memory t v Lw rootv p g lc rc gl fr)
        s.ffi) := by
  refine WPs.ite (w := evalPanCmp .equal Lw rootv) (eval_cmp_inv hE (of_eval (by lk [h_leaf]))
    (eval_load_rd hE (eval_addc hE 56#64 h_t) hroot)) ?_
  split
  · rename_i h0
    have hne : rootv ≠ Lw := by
      intro h
      subst h
      simp [evalPanCmp] at h0
    obtain ⟨hp, hpnc, hg, hgnc, hlc, hrc, hsnc, hgl⟩ := hsp hne
    simp only [delB, if_neg hne]
    refine WPs.dec (eval_load_rd hE (eval_node hE hlay (idx := "leaf") hLnc h_nodes h_leaf 0#64
      (by decide)) hp) ?_
    refine WPs.dec (eval_load_rd hE (eval_node hE hlay (idx := "p") hpnc (by lk [h_nodes])
      (by lk []) 0#64 (by decide)) hg) ?_
    refine WPs.dec (eval_load_rd hE (eval_node hE hlay (idx := "p") hpnc (by lk [h_nodes])
      (by lk []) 8#64 (by decide)) hlc) ?_
    refine WPs.seq (fun s' => s' = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
      s.locals "p" (.word p)) "g" (.word g)) "s" (.word (if lc = Lw then rc else lc)),
      s.globals, s.memory, s.ffi⟩) ?_ ?_
    · refine WPs.ite (w := evalPanCmp .equal lc Lw) (eval_cmp_inv hE (of_eval (by lk []))
        (of_eval (by lk [h_leaf]))) ?_
      split
      · rename_i h1
        have hlL : lc ≠ Lw := by
          intro h
          subst h
          simp [evalPanCmp] at h1
        refine WPs.skip ⟨_, _, _, _, rfl, ?_⟩
        rw [if_neg hlL]
      · rename_i h1
        have hlL : lc = Lw := by
          by_contra h
          exact h1 (by simp [evalPanCmp, h])
        refine WPs.assign (old := lc) (by lk []) (eval_load_rd hE (eval_node hE hlay (idx := "p")
          hpnc (by lk [h_nodes]) (by lk []) 16#64 (by decide)) hrc) ⟨_, _, _, _, rfl, ?_⟩
        rw [if_pos hlL, update_update]
    · intro s' hs'
      subst hs'
      generalize (if lc = Lw then rc else lc) = sb at hsnc ⊢
      refine WPs.seq_store hE (eval_node hE hlay (idx := "s") hsnc (by lk [h_nodes]) (by lk [])
        0#64 (by decide)) (of_eval (w := g) (by lk [])) ?_
      refine WPs.seq_mem (fun m' => m' = setCell (setCell s.memory (nodeField v sb.toNat 0) g)
        (delX t v g gl p) sb) ?_ ?_
      · refine WPs.ite (w := evalPanCmp .equal g 0#64) (eval_cmp_inv hE (of_eval (by lk []))
          (of_eval (eval_const _ _))) ?_
        split
        · rename_i h2
          have hg0 : g ≠ 0#64 := by
            intro h
            subst h
            simp [evalPanCmp] at h2
          have hgl' := (hgl hg0).frame (a' := nodeField v sb.toNat 0) g (by
            intro h
            have := (node_eq_node hlay hgnc hsnc (by omega) (by omega) (by omega)
              (by omega)).mp h
            omega)
          refine WPs.ite (w := evalPanCmp .equal gl p) (eval_cmp_inv hE (eval_load_rd hE
            (eval_node hE hlay (idx := "g") hgnc (by lk [h_nodes]) (by lk []) 8#64 (by decide))
            hgl') (of_eval (by lk []))) ?_
          split
          · rename_i h3
            have hglp : gl ≠ p := by
              intro h
              subst h
              simp [evalPanCmp] at h3
            refine WPs.store hE (eval_node hE hlay (idx := "g") hgnc (by lk [h_nodes])
              (by lk []) 16#64 (by decide)) (of_eval (w := sb) (by lk [])) ⟨_, rfl, ?_⟩
            simp only [delX, if_neg hg0, if_neg hglp]
            rfl
          · rename_i h3
            have hglp : gl = p := by
              by_contra h
              exact h3 (by simp [evalPanCmp, h])
            refine WPs.store hE (eval_node hE hlay (idx := "g") hgnc (by lk [h_nodes])
              (by lk []) 8#64 (by decide)) (of_eval (w := sb) (by lk [])) ⟨_, rfl, ?_⟩
            simp only [delX, if_neg hg0, if_pos hglp]
            rfl
        · rename_i h2
          have hg0 : g = 0#64 := by
            by_contra h
            exact h2 (by simp [evalPanCmp, h])
          refine WPs.store hE (eval_addc hE (a := t) 56#64 (by lk [h_t])) (of_eval (w := sb) (by lk []))
            ⟨_, rfl, ?_⟩
          simp only [delX, if_pos hg0]
          rfl
      · intro m' hm'
        subst hm'
        have hfr' : Rd (setCell (setCell s.memory (nodeField v sb.toNat 0) g) (delX t v g gl p)
            sb) (t + 72#64) fr :=
          (hfr.frame g (fun h => (hdr_ne_node hlay hsnc (by omega) (by omega)).mp h)).frame sb
            (delX_ne_free hlay hgnc)
        refine WPs.seq_store hE (eval_node hE hlay (idx := "p") hpnc (by lk [h_nodes]) (by lk [])
          0#64 (by decide)) (eval_load_rd hE (eval_addc hE (a := t) 72#64 (by lk [h_t])) hfr') ?_
        refine WPs.store hE (eval_addc hE (a := t) 72#64 (by lk [h_t])) (of_eval (w := p) (by lk [])) ?_
        simp only [restorePanValueFfiLocal]
        rw [restore_update, restore_update, restore_update]
        rfl
  · rename_i h0
    have heq : rootv = Lw := by
      by_contra h
      exact h0 (by simp [evalPanCmp, Ne.symm h])
    refine WPs.store hE (eval_addc hE 56#64 h_t) (of_eval (eval_const _ _)) ?_
    simp only [delB, if_pos heq]

end InitECandidate.Solver.GuestBound
