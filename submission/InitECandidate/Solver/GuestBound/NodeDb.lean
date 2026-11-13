import InitECandidate.Solver.GuestBound.TrieMptNew
import InitECandidate.Solver.GuestBound.RlpSlicesSpec

/-!
# The node database: looked-up slices lie in the input

`nodedb_build` stores, for each witness node, the address of its entry in the
slice array.  `NodeDb R m db lim` says: `db` is a well-formed table whose cells
are frozen (`R.Cn`), and every leaf value `a` is the address of a frozen pair
`(p, n)` with `p + n ≤ lim`.  Then `nodedb_lookup` returns `<0,_,_>` or
`<1, p, n>` with `p + n ≤ lim` (issue #30, step 4).

`htab_get_val` is the underlying fact about `htab_get`: a found value is the
value cell of a leaf.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Every leaf value satisfies `P`. -/
def LV (m : Word → Option (PanValue Word)) (v : HtabV) (kind : Nat → NodeKind)
    (P : Word → Prop) : Prop :=
  ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .leaf → ∀ w, Rd m (nodeField v i 8) w → P w

/-- `return <e1, lds a>`. -/
theorem WPs.ret_pair_load (hE : GuestEnv E) {e1 a : Exp Word} {w1 : Word}
    (h1 : ∀ y, E.eval s e1 = some y → y = .word w1)
    (h : ∀ addr w, E.eval s a = some (.word addr) → Rd s.memory addr w →
      Q (.returned (fun _ => none) s.globals s.memory s.ffi [.rStruct [.word w1, .word w]])) :
    WPs E s (.return (.rStruct [e1, .load .one a])) Q := by
  refine WPs.ret_ev (fun v hv => ?_)
  rw [evalF_rStruct] at hv
  simp only [evalArgs_cons, evalArgs_nil] at hv
  cases k1 : E.eval s e1 with
  | none => rw [k1] at hv; simp at hv
  | some y1 =>
    cases k2 : E.eval s (.load .one a) with
    | none => rw [k1, k2] at hv; simp at hv
    | some y2 =>
      have := h1 _ k1
      subst this
      obtain ⟨addr, w, ha, rfl, hm⟩ := eval_load_one hE.mem k2
      rw [k1, k2] at hv
      simp at hv
      subst hv
      exact h addr w ha hm

/-- `return <e1, lds a, lds b>`. -/
theorem WPs.ret_triple_load2 (hE : GuestEnv E) {e1 a b : Exp Word} {w1 : Word}
    (h1 : ∀ y, E.eval s e1 = some y → y = .word w1)
    (h : ∀ x y p n, E.eval s a = some (.word x) → Rd s.memory x p →
      E.eval s b = some (.word y) → Rd s.memory y n →
      Q (.returned (fun _ => none) s.globals s.memory s.ffi
        [.rStruct [.word w1, .word p, .word n]])) :
    WPs E s (.return (.rStruct [e1, .load .one a, .load .one b])) Q := by
  refine WPs.ret_ev (fun v hv => ?_)
  rw [evalF_rStruct] at hv
  simp only [evalArgs_cons, evalArgs_nil] at hv
  cases k1 : E.eval s e1 with
  | none => rw [k1] at hv; simp at hv
  | some y1 =>
    cases k2 : E.eval s (.load .one a) with
    | none => rw [k1, k2] at hv; simp at hv
    | some y2 =>
      cases k3 : E.eval s (.load .one b) with
      | none => rw [k1, k2, k3] at hv; simp at hv
      | some y3 =>
        have := h1 _ k1
        subst this
        obtain ⟨x, p, ha, rfl, hm⟩ := eval_load_one hE.mem k2
        obtain ⟨y, n, hb, rfl, hn⟩ := eval_load_one hE.mem k3
        rw [k1, k2, k3] at hv
        simp at hv
        subst hv
        exact h x y p n ha hm hb hn

theorem findleaf_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {t kp : Word} {v : HtabV}
    {kind : Nat → NodeKind} {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "htab_find_leaf" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word t)) (h2 : E.eval s e2 = some (.word kp))
    (hwf : HtabWF s.memory t v kind) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ nv : Word, vs = [.word nv] ∧
      (nv = 0 ∨ (Live v kind nv ∧ kind nv.toNat = .leaf)) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 131 hE.functions (by guest_decl_at 131) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases htab_find_leaf_runs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ t v
    kind (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hwf hrun
    with hst | ⟨l', nv, heq, hk⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, nv, rfl, hk⟩

set_option maxHeartbeats 8000000 in
/-- `htab_get`: state unchanged; a found value is a leaf value. -/
theorem htab_get_val (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_get" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t kp : Word) (v : HtabV) (kind : Nat → NodeKind) (P : Word → Prop)
    (ht : s.locals "t" = some (.word t)) (hkp : s.locals "key" = some (.word kp))
    (hwf : HtabWF s.memory t v kind)
    (hlv : LV s.memory v kind P) (h : Runs E s body r) :
    Stopped r ∨ ∃ l a b, r = .returned l s.globals s.memory s.ffi [.rStruct [.word a, .word b]] ∧
      (a = 0 ∨ P b) := by
  have hbody := (fun_of_index 132 hE.functions (by guest_decl_at 132) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l a b,
    r = .returned l s.globals s.memory s.ffi [.rStruct [.word a, .word b]] ∧ (a = 0 ∨ P b))) r h
  obtain ⟨hkl, -, -, -, -, hnd, -, hroot, -⟩ := hwf.hdr
  refine WPs.decCall_ret (fun vl g m ffi hret => ?_)
  obtain ⟨hg, hm, hf', nv, hv, hres⟩ := findleaf_ret hE hret (t := t) (kp := kp) (v := v)
    (kind := kind) (by lk [ht]) (by lk [hkp]) hwf
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi vl
  refine WPs.conseq (Q' := fun r => ∃ l a b,
    r = .returned l s.globals s.memory s.ffi [.rStruct [.word a, .word b]] ∧ (a = 0 ∨ P b)) ?_
    (by rintro r ⟨l, a, b, rfl, hk⟩; exact ⟨_, a, b, rfl, hk⟩)
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals "leaf" (.word nv), s.globals,
      s.memory, s.ffi⟩ ∧ nv ≠ 0) (WPs.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .equal) (of_eval (w := nv) (by lk []))
      (of_eval (w := 0#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i hw0
      refine WPs.skip ⟨rfl, fun h0 => ?_⟩
      subst h0 hw0
      simp [evalPanCmp] at hcv
    · exact WPs.ret_pair (a := 0#64) (b := 0#64) (of_eval (eval_const _ _))
        (of_eval (eval_const _ _)) ⟨_, _, _, rfl, Or.inl rfl⟩
  rintro a ⟨rfl, hnz⟩
  rcases hres with h0 | ⟨⟨hl1, hl2, -⟩, hleaf⟩
  · exact absurd h0 hnz
  refine WPs.dec_ev (fun v1 _ => WPs.conseq (Q' := fun r => ∃ l a b,
    r = .returned l s.globals s.memory s.ffi [.rStruct [.word a, .word b]] ∧ (a = 0 ∨ P b)) ?_
    (by rintro r ⟨l, a, b, rfl, hk⟩; exact ⟨_, a, b, rfl, hk⟩))
  refine WPs.dec_ev (fun v2 _ => WPs.conseq (Q' := fun r => ∃ l a b,
    r = .returned l s.globals s.memory s.ffi [.rStruct [.word a, .word b]] ∧ (a = 0 ∨ P b)) ?_
    (by rintro r ⟨l, a, b, rfl, hk⟩; exact ⟨_, a, b, rfl, hk⟩))
  refine WPs.dec_ev (fun v3 _ => WPs.conseq (Q' := fun r => ∃ l a b,
    r = .returned l s.globals s.memory s.ffi [.rStruct [.word a, .word b]] ∧ (a = 0 ∨ P b)) ?_
    (by rintro r ⟨l, a, b, rfl, hk⟩; exact ⟨_, a, b, rfl, hk⟩))
  refine WPs.decCall_ret (fun ve g m ffi hret => WPs.conseq (Q' := fun r => ∃ l a b,
    r = .returned l s.globals s.memory s.ffi [.rStruct [.word a, .word b]] ∧ (a = 0 ∨ P b)) ?_
    (by rintro r ⟨l, a, b, rfl, hk⟩; exact ⟨_, a, b, rfl, hk⟩))
  obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet
    (keepFn_sound (quietKeeper E) hE.functions 1 "memeq" memeq_quiet) hret
  subst g m ffi
  refine WPs.seqG (fun a => a.globals = s.globals ∧ a.memory = s.memory ∧ a.ffi = s.ffi ∧
      a.locals "t" = some (.word t) ∧ a.locals "leaf" = some (.word nv))
    (WPs.ite_both (fun w hw => ?_)) ?_
  · split
    · exact WPs.skip ⟨rfl, rfl, rfl, by lk [ht], by lk []⟩
    · exact WPs.ret_pair (a := 0#64) (b := 0#64) (of_eval (eval_const _ _))
        (of_eval (eval_const _ _)) ⟨_, _, _, rfl, Or.inl rfl⟩
  rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hfa, hT, hL⟩
  simp only at hg hm hfa hT hL
  subst hg hm hfa
  have hle : nv.toNat ≤ v.nc.toNat := by have := hwf.next_le; omega
  refine WPs.ret_pair_load hE (w1 := 1#64) (of_eval (eval_const _ _)) (fun addr w ha hm => ?_)
  have := eval_node_ld (s := ⟨la, s.globals, s.memory, s.ffi⟩) hE hwf.layout hle hT hnd hL 8#64
    (by decide) _ ha
  simp only [PanValue.word.injEq] at this
  subst this
  exact ⟨_, _, _, rfl, Or.inr (hlv _ hl1 hl2 hleaf w hm)⟩

theorem htabget_val_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {t kp : Word} {v : HtabV}
    {kind : Nat → NodeKind} {P : Word → Prop} {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} (h : CalleeRet E s "htab_get" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word t)) (h2 : E.eval s e2 = some (.word kp))
    (hwf : HtabWF s.memory t v kind) (hlv : LV s.memory v kind P) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ a b : Word,
      vs = [.rStruct [.word a, .word b]] ∧ (a = 0 ∨ P b) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 132 hE.functions (by guest_decl_at 132) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases htab_get_val hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ t kp v
    kind P (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hwf hlv hrun
    with hst | ⟨l', a, b, heq, hk⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, a, b, rfl, hk⟩

/-- `a` is the address of a frozen slice `(p, n)` that ends at or below `lim`. -/
def SliceIn (R : Reg) (lim : Nat) (a : Word) : Prop :=
  ∃ p n : Word, R.Cn a p ∧ R.Cn (a + 8#64) n ∧ p.toNat + n.toNat ≤ lim

theorem SliceIn.mono {R R' : Reg} {lim : Nat} {a : Word} (hle : R.Le R') (h : SliceIn R lim a) :
    SliceIn R' lim a := by
  obtain ⟨p, n, h1, h2, h3⟩ := h
  exact ⟨p, n, hle.Cn _ _ h1, hle.Cn _ _ h2, h3⟩

/-- The node database: a frozen table whose values are frozen slices below `lim`. -/
def NodeDb (R : Reg) (m : Word → Option (PanValue Word)) (db : Word) (lim : Nat) : Prop :=
  ∃ (v : HtabV) (kind : Nat → NodeKind) (rep : KeyRep), HtabOK m db v kind rep ∧
    db.toNat % 8 = 0 ∧ LV m v kind (SliceIn R lim) ∧ ∀ a, TabFoot db v a → ∃ w, R.Cn a w

/-- The node database survives every world-preserving step. -/
theorem NodeDb.mono {R R' : Reg} {g g' : VarName → Option (PanValue Word)}
    {m m' : Word → Option (PanValue Word)} {db : Word} {lim : Nat} (h : NodeDb R m db lim)
    (hle : R.Le R') (hW : WorldTJ R g m) (hW' : WorldTJ R' g' m') : NodeDb R' m' db lim := by
  obtain ⟨v, kind, rep, hok, h8, hlv, hfz⟩ := h
  have hfr : ∀ a, TabFoot db v a → m' a = m a := by
    intro a ha
    obtain ⟨w, hw⟩ := hfz a ha
    have r1 : Rd m a w := hW.cell hw
    have r2 : Rd m' a w := hW'.cell (hle.Cn _ _ hw)
    unfold Rd at r1 r2
    rw [r1, r2]
  refine ⟨v, kind, rep, hok.frame h8 hfr, h8, fun i h1 h2 hk w hr => ?_, fun a ha => ?_⟩
  · have hlay := hok.wf.layout
    obtain ⟨l1, l2, l3, l4⟩ := id hlay
    have hn8 := hok.nodes8
    have hnl := hok.wf.next_le
    have hi : i ≤ v.nc.toNat := by omega
    have hfoot : TabFoot db v (nodeField v i 8) :=
      ⟨by rw [node_toNat hlay hi (by omega)]; omega,
        Or.inr (by rw [node_toNat hlay hi (by omega)]; constructor <;> omega)⟩
    unfold Rd at hr
    rw [hfr _ hfoot] at hr
    exact (hlv i h1 h2 hk w hr).mono hle
  · obtain ⟨w, hw⟩ := hfz a ha
    exact ⟨w, hle.Cn _ _ hw⟩

set_option maxHeartbeats 8000000 in
/-- `nodedb_lookup`: state unchanged; a found slice ends at or below `lim`. -/
theorem nodedb_lookup_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "nodedb_lookup" E.functions = some (parameters, body))
    (R : Reg) (s : St σ) (r : Result σ) (db hp : Word) (lim : Nat)
    (hdb : s.locals "db" = some (.word db)) (hh : s.locals "hash" = some (.word hp))
    (hW : WorldTJ R s.globals s.memory) (hN : NodeDb R s.memory db lim) (h : Runs E s body r) :
    Stopped r ∨ ∃ l f p n, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word f, .word p, .word n]] ∧
      (f = 0 ∨ p.toNat + n.toNat ≤ lim) := by
  have hbody := (fun_of_index 254 hE.functions (by guest_decl_at 254) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l f p n, r = .returned l s.globals s.memory s.ffi
      [.rStruct [.word f, .word p, .word n]] ∧ (f = 0 ∨ p.toNat + n.toNat ≤ lim))) r h
  obtain ⟨v, kind, rep, hok, h8, hlv, hfz⟩ := hN
  refine WPs.decCall_ret (fun vr g m ffi hret => ?_)
  obtain ⟨hg, hm, hf', a, b, hv, hres⟩ := htabget_val_ret hE hret (t := db) (kp := hp)
    (by lk [hdb]) (by lk [hh]) hok.wf hlv
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi vr
  refine WPs.conseq (Q' := fun r => ∃ l f p n, r = .returned l s.globals s.memory s.ffi
      [.rStruct [.word f, .word p, .word n]] ∧ (f = 0 ∨ p.toNat + n.toNat ≤ lim)) ?_
    (by rintro r ⟨l, f, p, n, rfl, hk⟩; exact ⟨_, f, p, n, rfl, hk⟩)
  have hR : (updatePanValueMap s.locals "r" (.rStruct [.word a, .word b])) "r" =
      some (.rStruct [.word a, .word b]) := by lk []
  refine WPs.seqG (fun x => x = ⟨updatePanValueMap s.locals "r" (.rStruct [.word a, .word b]),
      s.globals, s.memory, s.ffi⟩ ∧ a ≠ 0) (WPs.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .equal) (of_eval (w := a)
        (by rw [eval_rField _ 0 "r" _ hR]; rfl))
      (of_eval (w := 0#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i hw0
      refine WPs.skip ⟨rfl, fun h0 => ?_⟩
      subst h0 hw0
      simp [evalPanCmp] at hcv
    · exact WPs.ret_triple (a := 0#64) (b := 0#64) (c := 0#64) (of_eval (eval_const _ _))
        (of_eval (eval_const _ _)) (of_eval (eval_const _ _)) ⟨_, _, _, _, rfl, Or.inl rfl⟩
  rintro x ⟨rfl, hnz⟩
  rcases hres with h0 | hP
  · exact absurd h0 hnz
  obtain ⟨p, n, c1, c2, hpn⟩ := hP
  refine WPs.ret_triple_load2 hE (w1 := 1#64) (of_eval (eval_const _ _))
    (fun x y p' n' hx hp' hy hn' => ?_)
  rw [eval_rField _ 1 "r" _ hR] at hx
  have ex : x = b := by simpa using hx.symm
  subst ex
  have ey : E.eval (⟨updatePanValueMap s.locals "r" (.rStruct [.word a, .word x]), s.globals,
      s.memory, s.ffi⟩ : St σ) (.op .add [.rField 1 (.var .local "r"), .const 8#64]) =
      some (.word (x + 8#64)) := by
    have e1 := eval_rField (E := E) (⟨updatePanValueMap s.locals "r"
      (.rStruct [.word a, .word x]), s.globals, s.memory, s.ffi⟩ : St σ) 1 "r" _ hR
    simp [evalF_op hE.word, evalArgs_cons, evalArgs_nil, e1, wordsProj_cons, wordsProj_nil,
      wordOp]
  rw [ey] at hy
  simp only [Option.some.injEq, PanValue.word.injEq] at hy
  subst hy
  have := (hW.cell c1).inj hp'
  subst this
  have := (hW.cell c2).inj hn'
  subst this
  exact ⟨_, _, _, _, rfl, Or.inr hpn⟩

theorem nodedblookup_spec_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {R : Reg} {db hp : Word}
    {lim : Nat} {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "nodedb_lookup" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word db)) (h2 : E.eval s e2 = some (.word hp))
    (hW : WorldTJ R s.globals s.memory) (hN : NodeDb R s.memory db lim) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ f p n : Word,
      vs = [.rStruct [.word f, .word p, .word n]] ∧ (f = 0 ∨ p.toNat + n.toNat ≤ lim) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 254 hE.functions (by guest_decl_at 254) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases nodedb_lookup_spec hE parameters body hlookup R ⟨cl, s.globals, s.memory, s.ffi⟩ _ db hp
    lim (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hW hN hrun
    with hst | ⟨l', f, p, n, heq, hk⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, f, p, n, rfl, hk⟩

end InitECandidate.Solver.GuestBound
