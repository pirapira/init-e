import InitECandidate.Solver.GuestBound.TrieDelStack
import InitECandidate.Solver.GuestBound.Fns.L4

/-!
# The unwind loop of the delete walk

Each iteration pops one record: an extension record calls
`_delete_ext_finish`, a branch record stores the result into the branch's slot
and calls `_collapse_branch`. The result of an iteration sits at the level of
the popped record's node, which is what the next record expects. The measure
is the address of the top record: an older record lies higher.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

local notation "UGUARD" => ((Exp.cmp Cmp.notEqual (Exp.var VarKind.local "top") (Exp.const (BitVec.ofNat 64 0))) : Exp Word)

local notation "UBODY" => ((Prog.dec "fnode" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 8))])) (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))])) (Exp.const (BitVec.ofNat 64 2))) (Prog.call (some ((some (VarKind.local, "res")), none)) "_delete_ext_finish" [(Exp.var VarKind.local "fnode"), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 24))])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 32))])), (Exp.var VarKind.local "res")]) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fnode"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 32))])), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "res")) (Prog.call (some ((some (VarKind.local, "res")), none)) "_collapse_branch" [(Exp.var VarKind.local "fnode")]))) (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))]))))) : Prog Word)

/-- The top record of a non-empty stack. -/
theorem DelStack.inv {R : Reg} {m : Word → Option (PanValue Word)} {sp lim top : Word}
    {ℓ0 ℓ : Nat} (h : DelStack R m sp lim ℓ0 top ℓ) (h0 : top ≠ 0#64) :
    ∃ prev node ℓn, top.toNat % 8 = 0 ∧ sp.toNat ≤ top.toNat ∧ top.toNat + 40 ≤ lim.toNat ∧
      (prev = 0#64 ∨ top.toNat + 40 ≤ prev.toNat) ∧ Rd m top prev ∧ Rd m (top + 8#64) node ∧
      R.Lv node ℓn ∧ DelStack R m sp lim ℓ0 prev ℓn ∧
      ((∃ seg sl, Rd m (top + 16#64) 2#64 ∧ Rd m (top + 24#64) seg ∧ Rd m (top + 32#64) sl ∧
          R.Kd node 2#64 ∧ R.Sg node seg sl ∧ ℓ = ℓn + sl.toNat) ∨
        (∃ idx kd, Rd m (top + 16#64) kd ∧ kd ≠ 2#64 ∧ Rd m (top + 32#64) idx ∧
          idx.toNat < 16 ∧ R.Kd node 3#64 ∧ ℓ = ℓn + 1)) := by
  cases h with
  | nil => exact absurd rfl h0
  | ext h1 h2 h3 h4 h5 r0 r1 r2 r3 r4 hk hl hs hp =>
    exact ⟨_, _, _, h2, h3, h4, h5, r0, r1, hl, hp, Or.inl ⟨_, _, r2, r3, r4, hk, hs, rfl⟩⟩
  | br h1 h2 h3 h4 h5 r0 r1 r2 hk2 r4 hi hk hl hp =>
    exact ⟨_, _, _, h2, h3, h4, h5, r0, r1, hl, hp, Or.inr ⟨_, _, r2, hk2, r4, hi, hk, rfl⟩⟩

section rets

variable {v : PanValue Word} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ} {Rg : Reg}

theorem delete_ext_finish_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word}
    {node seg sl nc : Word} {L : Nat}
    (h : CalleeRet E s "_delete_ext_finish" [e1, e2, e3, e4] [v] g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word node)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word seg)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word sl)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word nc)
    (hW : WorldTJ Rg s.globals s.memory) (hK : Rg.Kd node 2#64) (hL : Rg.Lv node L)
    (hseg : Rd s.memory (node + 32#64) seg) (hsl : Rd s.memory (node + 40#64) sl)
    (hnc : nc = 0#64 ∨ ∃ k, Rg.Kd nc k ∧ Rg.Lv nc (L + sl.toNat)) :
    ∃ a R', v = .word a ∧ ffi = s.ffi ∧ Rg.Le R' ∧
      (a = 0#64 ∨ ∃ k, R'.Kd a k ∧ k ≠ 0#64 ∧ R'.Lv a L) ∧ WorldTJ R' g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 277 hE.functions (by guest_decl_at 277) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  obtain ⟨y2, vs2, g2, hr2, rfl⟩ := evalArgs_cons_inv hr1
  obtain ⟨y3, vs3, g3, hr3, rfl⟩ := evalArgs_cons_inv hr2
  obtain ⟨y4, vs4, g4, hr4, rfl⟩ := evalArgs_cons_inv hr3
  rw [evalArgs_nil] at hr4
  simp only [Option.some.injEq] at hr4
  subst hr4
  have := h1 _ g1
  subst this
  have := h2 _ g2
  subst this
  have := h3 _ g3
  subst this
  have := h4 _ g4
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases delete_ext_finish_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩
    _ node seg sl nc L
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hK hL hseg hsl hnc hrun with hst | ⟨l', g', m', a, R', heq, hle, ha, hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, R', rfl, rfl, hle, ha, hw, hg, hm⟩

theorem collapse_branch_ret (hE : GuestEnv E) {e1 : Exp Word} {node : Word} {ℓ : Nat}
    (h : CalleeRet E s "_collapse_branch" [e1] [v] g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word node)
    (hW : WorldTJ Rg s.globals s.memory) (hK : Rg.Kd node 3#64) (hL : Rg.Lv node ℓ) :
    ∃ a R', v = .word a ∧ ffi = s.ffi ∧ Rg.Le R' ∧
      (a = 0#64 ∨ ∃ k, R'.Kd a k ∧ k ≠ 0#64 ∧ R'.Lv a ℓ) ∧ WorldTJ R' g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 276 hE.functions (by guest_decl_at 276) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  rw [evalArgs_nil] at hr1
  simp only [Option.some.injEq] at hr1
  subst hr1
  have := h1 _ g1
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases collapse_branch_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩
    _ node ℓ
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hK hL hrun with hst | ⟨l', g', m', a, R', heq, hle, ha, hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, R', rfl, rfl, hle, ha, hw, hg, hm⟩

end rets

/-- `br + 32 + (lds e) * 8` for a loaded nibble: a child slot. -/
theorem eval_slot_load (hE : GuestEnv E) {x : VarName} {ea : Exp Word} {br b : Word}
    (hbr : s.locals x = some (.word br))
    (hl : ∀ y, E.eval s (.load .one ea) = some y → y = .word b) (h16 : b.toNat < 16) :
    ∀ y, E.eval s (.op .add [.var .local x, .const 32#64,
        .panOp .mul [.load .one ea, .const 8#64]]) = some y →
      y = .word (br + BitVec.ofNat 64 (32 + 8 * b.toNat)) := by
  intro y hy
  cases hv : E.eval s (.load .one ea) with
  | none =>
    simp (config := { decide := true }) [evalF_op hE.word, evalF_panOp, evalArgs_cons,
      evalArgs_nil, evalF_local, hbr, hv, eval_const] at hy
  | some xb =>
    have := hl _ hv
    subst this
    simp (config := { decide := true }) [evalF_op hE.word, evalF_panOp, evalArgs_cons,
      evalArgs_nil, evalF_local, hbr, hv, eval_const, wordsProj_cons, wordsProj_nil,
      wordOp] at hy
    subst hy
    rw [slot_word_eq br b h16]

/-- Invariant of the unwind loop, relative to globals `G`, memory `M` and FFI state `F`. -/
def UwI (Rg : Reg) (G : VarName → Option (PanValue Word)) (M : Word → Option (PanValue Word))
    (F : FfiState σ) (sp lim : Word) (ℓ0 : Nat) (a : St σ) : Prop :=
  ∃ R topv resv ℓ, Rg.Le R ∧ WorldTJ R a.globals a.memory ∧ a.ffi = F ∧
    (∀ x, x ≠ "heap_ptr" → a.globals x = G x) ∧
    (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      a.memory addr = M addr) ∧
    a.locals "top" = some (.word topv) ∧ a.locals "res" = some (.word resv) ∧
    DelStack R a.memory sp lim ℓ0 topv ℓ ∧
    (resv = 0#64 ∨ ∃ k, R.Kd resv k ∧ k ≠ 0#64 ∧ R.Lv resv ℓ)

/-- The measure: the distance of the top record from the end of the address space. -/
def uwMu (a : St σ) : Nat :=
  match a.locals "top" with
  | some (.word t) => if t = 0#64 then 0 else 2 ^ 64 - t.toNat
  | _ => 0

theorem uwMu_lt {a b : St σ} {t p : Word} (a1 : a.locals "top" = some (.word t))
    (b1 : b.locals "top" = some (.word p)) (ht : t ≠ 0#64)
    (h : p = 0#64 ∨ t.toNat + 40 ≤ p.toNat) : uwMu b < uwMu a := by
  unfold uwMu
  rw [a1, b1]
  simp only [if_neg ht]
  have := t.isLt
  have := p.isLt
  rcases h with rfl | h
  · simp
    omega
  · split <;> omega

theorem uwMu_le (a : St σ) : uwMu a ≤ 2 ^ 64 := by
  unfold uwMu
  split
  · split <;> omega
  · omega

set_option maxHeartbeats 32000000 in
/-- One pop: the invariant is kept and the measure decreases. -/
theorem uw_body (hE : GuestEnv E) {Rg : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {F : FfiState σ} {sp lim : Word} {ℓ0 : Nat}
    (hsp : 2952790016 ≤ sp.toNat) {a : St σ} (hI : UwI Rg G M F sp lim ℓ0 a)
    (hct : CondTrue E a UGUARD) :
    WPs E a UBODY (fun r => ∃ l g m f, r = .normal l g m f ∧
      UwI Rg G M F sp lim ℓ0 ⟨l, g, m, f⟩ ∧ uwMu ⟨l, g, m, f⟩ < uwMu a) := by
  obtain ⟨la, ga, ma, fa⟩ := a
  obtain ⟨R, topv, resv, ℓ, hle, hW, hf, hg, hm, qtop, qres, hst, hres⟩ := hI
  obtain ⟨w, cc, hcond, hw⟩ := hct
  dsimp only at hW hf hg hm qtop qres hst
  subst hf
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := topv) (by lk [qtop]))
    (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hcond)
  simp only [PanValue.word.injEq] at hcv
  have htop : topv ≠ 0#64 := by
    rintro rfl
    rw [hcv] at hw
    simp [evalPanCmp] at hw
  obtain ⟨prev, node, ℓn, h8, h3, h4, h5, r0, r1, hln, hprev, hcase⟩ := hst.inv htop
  refine WPs.dec (w := node) (eval_load_rd hE (eval_addc hE 8#64 qtop) r1) ?_
  refine WPs.seqG (fun a' => ∃ R' res', Rg.Le R' ∧ WorldTJ R' a'.globals a'.memory ∧
      a'.ffi = fa ∧ (∀ x, x ≠ "heap_ptr" → a'.globals x = G x) ∧
      (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        a'.memory addr = M addr) ∧
      a'.locals "top" = some (.word topv) ∧ a'.locals "res" = some (.word res') ∧
      Rd a'.memory topv prev ∧ DelStack R' a'.memory sp lim ℓ0 prev ℓn ∧
      (res' = 0#64 ∨ ∃ k, R'.Kd res' k ∧ k ≠ 0#64 ∧ R'.Lv res' ℓn)) ?_ ?_
  · rcases hcase with ⟨seg, sl, r2, r3, r4, hk, hs, hℓ⟩ | ⟨idx, kd, r2, hk2, r4, hi, hk, hℓ⟩
    · -- an extension record
      subst hℓ
      refine WPs.ite (w := 1#64) (fun x hx => by
        have := eval_cmp_inv hE (op := .equal)
          (eval_load_inv2 hE (of_eval (eval_addc hE 16#64 (by lk [qtop]))) r2)
          (of_eval (w := 2#64) (eval_const _ _)) x hx
        rw [this]
        rfl) ?_
      rw [if_neg (by decide)]
      obtain ⟨hsg1, hsg2⟩ := hW.sg hs
      refine WPs.callA_ret (fun v g1 m1 f1 hret => ?_)
      obtain ⟨a, R1, rfl, rfl, hle1, ha, hW1, hg1, hm1⟩ := delete_ext_finish_ret hE hret
        (node := node) (seg := seg) (sl := sl) (nc := resv) (L := ℓn) (of_eval (by lk []))
        (eval_load_inv2 hE (of_eval (eval_addc hE 24#64 (by lk [qtop]))) r3)
        (eval_load_inv2 hE (of_eval (eval_addc hE 32#64 (by lk [qtop]))) r4)
        (of_eval (by lk [qres])) hW hk hln hsg1 hsg2 (by
          rcases hres with h0 | ⟨k, hk', -, hl'⟩
          · exact Or.inl h0
          · exact Or.inr ⟨k, hk', hl'⟩)
      refine ⟨R1, a, hle.trans hle1, hW1, rfl, fun x hx => (hg1 x hx).trans (hg x hx),
        fun addr ha' => (hm1 addr ha').trans (hm addr ha'), by lk [qtop], by lk [], ?_,
        (hprev.mono hle1).frame (fun x hx1 _ => hm1 x (Or.inr (by omega))), ha⟩
      show Rd m1 topv prev
      unfold Rd at r0 ⊢
      rw [hm1 topv (Or.inr (by omega))]
      exact r0
    · -- a branch record
      subst hℓ
      refine WPs.ite (w := 0#64) (fun x hx => by
        have := eval_cmp_inv hE (op := .equal)
          (eval_load_inv2 hE (of_eval (eval_addc hE 16#64 (by lk [qtop]))) r2)
          (of_eval (w := 2#64) (eval_const _ _)) x hx
        rw [this]
        simp [evalPanCmp, hk2]) ?_
      rw [if_pos (by decide)]
      obtain ⟨hNd, hRd, hlo, htopn, -⟩ := hW.kd hk
      have hsz3 : nodeSize 3#64 = 176 := by decide
      have eS : (node + BitVec.ofNat 64 (32 + 8 * idx.toNat)).toNat =
          node.toNat + (32 + 8 * idx.toNat) := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      have hcvn := hW.cv_br hk hln
      have W1 := hW.node_child (c := resv) hNd hRd (Or.inr ⟨rfl, idx.toNat, hi, rfl⟩)
        (by
          rcases hres with h0 | ⟨k, hk', -, -⟩
          · exact Or.inl h0
          · exact Or.inr (hW.kd hk').1)
        (fun ℓc hcv hc0 => by
          have := hW.cv_unique hcv hcvn
          subst this
          rcases hres with h0 | ⟨k, -, -, hl'⟩
          · exact absurd h0 hc0
          · exact hl')
      refine WPs.seq_store_inv hE (addr := node + BitVec.ofNat 64 (32 + 8 * idx.toNat))
        (w := resv) (eval_slot_load hE (by lk [])
          (eval_load_inv2 hE (of_eval (eval_addc hE 32#64 (by lk [qtop]))) r4) hi)
        (of_eval (by lk [qres])) ?_
      refine WPs.callA_ret (fun v g1 m1 f1 hret => ?_)
      obtain ⟨a, R1, rfl, rfl, hle1, ha, hW1, hg1, hm1⟩ := collapse_branch_ret hE hret
        (node := node) (ℓ := ℓn) (of_eval (by lk [])) W1 hk hln
      have hkeep : ∀ x : Word, sp.toNat ≤ x.toNat → m1 x = ma x := by
        intro x hx
        rw [hm1 x (Or.inr (by omega))]
        exact setCell_ne _ (NE (by omega))
      refine ⟨R1, a, hle.trans hle1, hW1, rfl, fun x hx => (hg1 x hx).trans (hg x hx),
        fun addr ha' => ?_, by lk [qtop], by lk [], ?_,
        (hprev.mono hle1).frame (fun x hx1 _ => hkeep x hx1), ha⟩
      · show m1 addr = _
        rw [hm1 addr ha']
        show setCell ma _ _ addr = _
        rw [setCell_ne _ (NE (by unfold HBASE at ha' hlo; omega))]
        exact hm addr ha'
      · show Rd m1 topv prev
        unfold Rd at r0 ⊢
        rw [hkeep topv h3]
        exact r0
  · rintro ⟨lb, gb, mb, fb⟩ ⟨R', res', hle', hW', hf', hg', hm', ptop, pres, rprev, hst', hres'⟩
    dsimp only at hW' hf' hg' hm' ptop pres rprev hst'
    subst hf'
    refine WPs.assign (old := topv) (w := prev) ptop
      (eval_load_rd hE (eval_addc hE 0#64 ptop) (by rw [BitVec.add_zero]; exact rprev)) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨_, _, _, _, rfl, ⟨R', prev, res', ℓn, hle', hW', rfl, hg', hm',
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, pres],
      hst', hres'⟩, ?_⟩
    exact uwMu_lt (t := topv) (p := prev) qtop
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup]) htop h5

theorem uw_body_cost (hE : GuestEnv E) : Costs E UBODY (10 ^ 120) := by
  have h : ∃ B, Costs E UBODY B ∧ B ≤ 10 ^ 120 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

end InitECandidate.Solver.GuestBound
