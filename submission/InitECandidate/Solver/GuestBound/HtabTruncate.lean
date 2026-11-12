import InitECandidate.Solver.GuestBound.HtabDelInv
import InitECandidate.Solver.GuestBound.Fns.L1C5

/-!
# Hash tables: `htab_truncate`

Each round deletes the entry at the last position, which always succeeds on a
table satisfying `HtabOK`, so the loop runs at most `count` times.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop} {t : Word} {v : HtabV}

/-- `htab_del(t, key)` as a statement, for the stored key of the live leaf `Lw`. -/
theorem WPs.call_del (hE : GuestEnv E) {e2 : Exp Word} {kind : Nat → NodeKind} {rep : KeyRep}
    {Lw : Word} (ht : s.locals "t" = some (.word t))
    (h2 : ∀ y, E.eval s e2 = some y → y = .word (v.keys + Lw * v.st))
    (hok : HtabOK s.memory t v kind rep) (hL : LiveN v kind Lw.toNat)
    (hLk : kind Lw.toNat = .leaf)
    (h : ∀ m', DelRel s.memory t v Lw m' → Q (.normal s.locals s.globals m' s.ffi)) :
    WPs E s (.call (some (none, none)) "htab_del" [.var .local "t", e2]) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 139 hE.functions (by guest_decl_at 139) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ht] at hvalues
  cases he : E.eval s e2 with
  | none => rw [he] at hvalues; simp at hvalues
  | some y =>
    have := h2 y he
    subst this
    rw [he] at hvalues
    simp only [Option.map_some, Option.some.injEq] at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    have hpost := htab_del_exec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb t v
      kind rep Lw (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hok hL hLk
      hcallee
    rcases hpost with hst | ⟨l, m', rfl, hrel⟩
    · cases rb with
      | raised lr g m f ex v =>
        simp only [CallOutcome] at hout
        subst hout
        exact Or.inl trivial
      | finalFfi lr g m f ev =>
        simp only [CallOutcome] at hout
        subst hout
        exact Or.inl trivial
      | error lr g m f =>
        simp only [CallOutcome] at hout
        exact Or.inl (Stopped.of_error hout)
      | _ => exact absurd hst (fun h => h)
    · simp only [CallOutcome] at hout
      rcases hout with herr | ⟨l', g', hassign, rfl⟩
      · exact Or.inl (Stopped.of_error herr)
      · simp only [assignPanValueCallResult, Option.some.injEq, Prod.mk.injEq] at hassign
        obtain ⟨rfl, rfl⟩ := hassign
        exact Or.inr (h m' hrel)

local notation "TGUARD" => ((Exp.cmp Cmp.lower (Exp.var VarKind.local "n") (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 24))]))) : Exp Word)

local notation "TBODY" => ((Prog.dec "pos" Shape.one (Exp.op BinOp.sub [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 24))])), (Exp.const (BitVec.ofNat 64 1))]) (Prog.dec "leaf" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 48))])), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "pos"), (Exp.const (BitVec.ofNat 64 8))])])) (Prog.call (some (none, none)) "htab_del" [(Exp.var VarKind.local "t"), (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 32))])), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "leaf"), (Exp.var VarKind.local "stride")])])]))) : Prog Word)

/-- The entry count stored in the header at `t`. -/
def cntOf (m : Word → Option (PanValue Word)) (t : Word) : Nat :=
  match m (t + 24#64) with
  | some (.word w) => w.toNat
  | _ => 0

theorem cntOf_rd {m : Word → Option (PanValue Word)} {w : Word} (h : Rd m (t + 24#64) w) :
    cntOf m t = w.toNat := by
  unfold cntOf
  rw [h]

/-- Loop invariant of `htab_truncate`. -/
def TruncI (t : Word) (rep : KeyRep) (g : VarName → Option (PanValue Word)) (f : FfiState σ)
    (s : St σ) : Prop :=
  s.globals = g ∧ s.ffi = f ∧ s.locals "t" = some (.word t) ∧
    ∃ v kind, HtabOK s.memory t v kind rep ∧ s.locals "stride" = some (.word v.st)

theorem eval_add2_inv (hE : GuestEnv E) {a b : Exp Word} {wa wb : Word}
    (ha : ∀ y, E.eval s a = some y → y = .word wa) (hb : ∀ y, E.eval s b = some y → y = .word wb) :
    ∀ y, E.eval s (.op .add [a, b]) = some y → y = .word (wa + wb) := by
  intro y hy
  obtain ⟨va, vb, w, hva, hvb, hw, rfl⟩ := eval_op2_inv hE.word hy
  have h1 := ha _ hva
  have h2 := hb _ hvb
  simp only [PanValue.word.injEq] at h1 h2
  subst h1 h2
  simp [wordOp] at hw
  rw [← hw]

/-- A word load whose address, if it evaluates, is `addr`. -/
theorem eval_load_inv2 (hE : GuestEnv E) {a : Exp Word} {addr w : Word}
    (ha : ∀ y, E.eval s a = some y → y = .word addr) (hw : Rd s.memory addr w) :
    ∀ y, E.eval s (.load .one a) = some y → y = .word w := by
  intro y hy
  obtain ⟨addr', w', ha', rfl, hm⟩ := eval_load_one hE.mem hy
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  rw [Rd.inj hm hw]

theorem ord_addr (hlay : HtabLayout t v) {iv : Word} (hi : iv.toNat ≤ v.nc.toNat) :
    v.order + iv * 8#64 = orderSlot v iv.toNat := by
  have hmul : (iv * 8#64).toNat = iv.toNat * 8 := by
    obtain ⟨-, -, -, h4⟩ := hlay
    have h8 : (8#64 : Word).toNat = 8 := by decide
    rw [BitVec.toNat_mul, h8]
    exact Nat.mod_eq_of_lt (by omega)
  unfold orderSlot
  congr 1

set_option maxHeartbeats 2000000 in
/-- One round of `htab_truncate` removes an entry. -/
theorem trunc_body (hE : GuestEnv E) {rep : KeyRep} {g : VarName → Option (PanValue Word)}
    {f : FfiState σ} (hI : TruncI t rep g f s) (hct : CondTrue E s TGUARD) :
    WPs E s TBODY (fun r => ∃ m', r = .normal s.locals s.globals m' s.ffi ∧
      TruncI t rep g f ⟨s.locals, s.globals, m', s.ffi⟩ ∧ cntOf m' t < cntOf s.memory t) := by
  obtain ⟨hg, hf, ht, v, kind, hok, hstride⟩ := hI
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨hkl, hst, -, hcnt, hkeys, hnd, hord, hroot, -, hfree, -⟩ := hwf.hdr
  have hcl := hwf.cnt_le
  have h1 : (1#64 : Word).toNat = 1 := by decide
  have hcpos : 1 ≤ v.cnt.toNat := by
    obtain ⟨w, k, hcond, hw⟩ := hct
    have hev := cond_of_eval hcond
    rw [evalF_cmp hE.word] at hev
    cases hb : E.eval s (.load .one (.op .add [.var .local "t", .const 24#64])) with
    | none => rw [hb] at hev; split at hev <;> simp_all
    | some y =>
      have := eval_load_rd hE (eval_addc hE 24#64 ht) hcnt y hb
      subst this
      rw [hb] at hev
      by_contra hc0
      have hz : v.cnt = 0#64 := by
        apply BitVec.eq_of_toNat_eq
        have h0 : (0#64 : Word).toNat = 0 := by decide
        omega
      rw [hz] at hev
      split at hev
      · rename_i x y' hx hy'
        simp only [Option.some.injEq, PanValue.word.injEq] at hy' hev
        subst hy'
        rw [← hev] at hw
        simp [evalPanCmp] at hw
      · cases hev
  have hc1 : (v.cnt - 1#64).toNat = v.cnt.toNat - 1 := by
    rw [BitVec.toNat_sub, h1]
    have := v.cnt.isLt
    omega
  obtain ⟨Lw, hrdL, hL1, hL2, hLk, -⟩ := hwf.order_ok (v.cnt.toNat - 1) (by omega)
  have hcnc : (v.cnt - 1#64).toNat ≤ v.nc.toNat := by omega
  have hrdL' : Rd s.memory (v.order + (v.cnt - 1#64) * 8#64) Lw := by
    rw [ord_addr hlay hcnc, hc1]
    exact hrdL
  refine WPs.dec (w := v.cnt - 1#64) (eval_sub_inv hE (eval_load_rd hE (eval_addc hE 24#64 ht)
    hcnt)) ?_
  refine WPs.dec (w := Lw) (eval_load_inv2 hE (eval_add2_inv hE (eval_load_rd hE
    (eval_addc hE (a := t) 48#64 (by lk [ht])) hord)
    (of_eval (w := (v.cnt - 1#64) * 8#64) (by ev [evalPanOp]))) hrdL') ?_
  refine WPs.call_del hE (Lw := Lw) (by lk [ht]) (eval_add2_inv hE (eval_load_rd hE
    (eval_addc hE (a := t) 32#64 (by lk [ht])) hkeys)
    (of_eval (w := Lw * v.st) (by ev [evalPanOp, hstride]))) hok
    ⟨hL1, hL2, by rw [hLk]; exact NodeKind.noConfusion⟩ hLk ?_
  intro m' hrel
  obtain ⟨v', kind', hok', hsame⟩ := htab_del_ok hok
    ⟨hL1, hL2, by rw [hLk]; exact NodeKind.noConfusion⟩ hLk hrel
  simp only [restorePanValueFfiLocal]
  rw [restore_update, restore_update]
  obtain ⟨-, hst', -, -, -, -, -, -, hcnt'⟩ := hsame
  refine ⟨m', rfl, ⟨hg, hf, ht, v', kind', hok', by rw [hst']; exact hstride⟩, ?_⟩
  rw [cntOf_rd hcnt, cntOf_rd (hcnt' ▸ hok'.wf.hdr.2.2.2.1), hc1]
  omega

theorem condCost_exp {I : St σ → Prop} (c : Exp Word) : CondCost E I c (expCost c) := by
  intro s w k _ hcond
  rw [cond_eq] at hcond
  split at hcond
  · simp only [Option.some.injEq, Prod.mk.injEq] at hcond
    rw [← hcond.2, stepCost_eq]
  · cases hcond

theorem htab_truncate.body_cost (hE : GuestEnv E) : Costs E TBODY 5220428572859803110000 := by
  have h : ∃ B, Costs E TBODY B ∧ B ≤ 5220428572859803110000 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem htab_truncate.ret_cost (hE : GuestEnv E) :
    Costs E (Prog.return (Exp.const (BitVec.ofNat 64 0)) : Prog Word) 10 := by
  have h : ∃ B, Costs E (Prog.return (Exp.const (BitVec.ofNat 64 0)) : Prog Word) B ∧ B ≤ 10 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 2000000 in
/-- Step bound of `htab_truncate(t, n)` on a table satisfying `HtabOK`. -/
theorem htab_truncate_cost (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_truncate" E.functions = some (parameters, body))
    (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (t : Word) (v : HtabV)
    (kind : Nat → NodeKind) (rep : KeyRep) (ht : s.locals "t" = some (.word t))
    (hok : HtabOK s.memory t v kind rep) (hrun : E.run fuel s body = some (r, n))
    (hne : r.isError = false) : n ≤ 500000000000000000000000000000 := by
  have hbody := (fun_of_index 140 hE.functions (by guest_decl_at 140) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hloop : Triple E (fun a => TruncI t rep s.globals s.ffi a ∧ cntOf a.memory t ≤ 92274688)
      (.while TGUARD TBODY) ((92274688 + 1) * (expCost TGUARD + 5220428572859803110000 + 1))
      (fun r => match r with
        | .normal _ _ _ _ => True
        | _ => True) := by
    refine (Triple.while_exit (I := TruncI t rep s.globals s.ffi)
      (μ := fun a => cntOf a.memory t) (Q := fun _ => True) 92274688 (condCost_exp _)
      (fun _ _ _ => trivial) ?_).consequence (fun _ h => h) (Nat.le_refl _)
      (fun r _ => by cases r <;> trivial)
    intro k
    refine Triple.of_costs (htab_truncate.body_cost hE) ?_
    rintro fuel' a r' n' ⟨hI, hk, hct⟩ hrun' hne'
    rcases trunc_body hE hI hct r' (Runs.of_run hrun') with hst | ⟨m', rfl, hI', hlt⟩
    · cases r' with
      | error l g m f => cases hne'
      | raised l g m f ex val => trivial
      | finalFfi l g m f ev => trivial
      | _ => exact absurd hst (fun h => h)
    · exact ⟨hI', by rw [← hk]; exact hlt⟩
  have hall := Triple.dec (E := E) (P := fun a => a = s)
    (P' := fun a => TruncI t rep s.globals s.ffi a ∧ cntOf a.memory t ≤ 92274688) "stride"
    Shape.one (Exp.load Shape.one (Exp.op BinOp.add [Exp.var VarKind.local "t",
      Exp.const (BitVec.ofNat 64 8)])) ?_
    (Triple.seq (Mid := fun _ => True) (Q := fun _ => True) hloop (htab_truncate.ret_cost hE))
  · have hn := (hall fuel s r n rfl hrun hne).1
    rw [stepCost_eq] at hn
    refine Nat.le_trans hn ?_
    decide +kernel
  · rintro a val rfl hval -
    have hwf := hok.wf
    obtain ⟨-, hst, -, hcnt, -⟩ := hwf.hdr
    have := eval_load_rd hE (eval_addc hE 8#64 ht) hst val hval
    subst this
    refine ⟨⟨rfl, rfl, by lk [ht], v, kind, hok, by lk []⟩, ?_⟩
    show cntOf a.memory t ≤ 92274688
    rw [cntOf_rd hcnt]
    have := hwf.cnt_le
    obtain ⟨-, -, h3, h4⟩ := hwf.layout
    omega

end InitECandidate.Solver.GuestBound
