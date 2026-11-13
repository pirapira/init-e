import InitECandidate.Solver.GuestBound.RlpCountSpec
import InitECandidate.Solver.GuestBound.RlpSlices

/-!
# `rlp_list_to_slices` records the item chain

Entry `j` of the returned array holds the pointer `p + o` and the total `t` of
the `j`-th item of the chain found by `rlp_list_count`; the item lies inside
`[p, p + len)` (`Items.entry_le`).  Issue #30.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem Items.next {m : Word → Option (PanValue Word)} {p : Word} {o i L c : Nat}
    (h : Items m p o i) (h' : Items m p L c) (hlt : i < c) :
    ∃ t : Word, TotSpec m (p + BitVec.ofNat 64 o) t ∧ 1 ≤ t.toNat ∧
      Items m p (o + t.toNat) (i + 1) := by
  induction h' with
  | zero => omega
  | @step o1 c1 t h1 ht h1t ih =>
    by_cases hic : i = c1
    · subst hic
      have := h.fn h1
      subst this
      exact ⟨t, ht, h1t, .step h ht h1t⟩
    · exact ih (by omega)

theorem Items.mono {m : Word → Option (PanValue Word)} {p : Word} {o i L c : Nat}
    (h : Items m p o i) (h' : Items m p L c) (hle : i ≤ c) : o ≤ L := by
  induction h' with
  | zero =>
    have : i = 0 := by omega
    subst this
    cases h
    exact Nat.le_refl _
  | @step o1 c1 t h1 ht h1t ih =>
    by_cases hic : i = c1 + 1
    · subst hic
      have := h.fn (.step h1 ht h1t)
      omega
    · have := ih (by omega)
      omega

/-- Entries `0 .. i` of the slice array at `arr` describe the item chain. -/
def SlEnt (m0 m : Word → Option (PanValue Word)) (p arr : Word) (i : Nat) : Prop :=
  ∀ j, j < i → ∃ (o : Nat) (t : Word), Items m0 p o j ∧
    TotSpec m0 (p + BitVec.ofNat 64 o) t ∧ 1 ≤ t.toNat ∧
    m (arr + BitVec.ofNat 64 (16 * j)) = some (.word (p + BitVec.ofNat 64 o)) ∧
    m (arr + BitVec.ofNat 64 (16 * j + 8)) = some (.word t)

/-- An entry's item lies inside the list payload. -/
theorem Items.entry_le {m : Word → Option (PanValue Word)} {p : Word} {o j L c : Nat} {t : Word}
    (h : Items m p o j) (ht : TotSpec m (p + BitVec.ofNat 64 o) t) (h' : Items m p L c)
    (hlt : j < c) : o + t.toNat ≤ L := by
  obtain ⟨t', ht', -, hn⟩ := h.next h' hlt
  have := ht.fn ht'
  subst this
  exact hn.mono h' (by omega)

theorem rlplistcount_items_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {pv fv pw lw : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "rlp_list_count" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word pw)) (h2 : E.eval s e2 = some (.word lw))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (hlow : pw.toNat + lw.toNat + 16 ≤ fv.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧ ScrMem pv fv s.memory m ∧ ∃ c : Word, vs = [.word c] ∧
      Items s.memory pw lw.toNat c.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 113 hE.functions (by guest_decl_at 113) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases rlp_list_count_items hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    pv fv pw lw (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hp hf hfp hlow hrun
    with hst | ⟨l', m', c, heq, hk, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hk, c, rfl, hc⟩

theorem rlptotalunchecked_ret (hE : GuestEnv E) {e1 : Exp Word} {pw : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "rlp_item_total_unchecked" [e1] vs g m ffi)
    (h1 : E.eval s e1 = some (.word pw)) :
    g = s.globals ∧ ffi = s.ffi ∧ m = s.memory ∧ ∃ t : Word, vs = [.word t] ∧
      TotSpec s.memory pw t := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 114 hE.functions (by guest_decl_at 114) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases rlp_item_total_unchecked_spec hE parameters body hlookup
    ⟨cl, s.globals, s.memory, s.ffi⟩ _ pw
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hrun
    with hst | ⟨l', t, heq, ht⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, t, rfl, ht⟩

/-- Loop invariant. -/
def SlJ (G : VarName → Option (PanValue Word)) (m0 m1 : Word → Option (PanValue Word))
    (f : FfiState σ) (pw c hv0 : Word) (a : St σ) : Prop :=
  SlI G m1 f pw c hv0 a ∧ ∃ iw ow : Word, a.locals "i" = some (.word iw) ∧
    a.locals "off" = some (.word ow) ∧ Items m0 pw ow.toNat iw.toNat ∧
    SlEnt m0 a.memory pw hv0 iw.toNat

set_option maxHeartbeats 8000000 in
theorem rlp_list_to_slices_items (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_list_to_slices" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv pw lw hv0 : Word)
    (hpw : s.locals "p" = some (.word pw)) (hlen : s.locals "len" = some (.word lw))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (hh : s.globals "heap_ptr" = some (.word hv0)) (hhH : InHeap hv0)
    (hlow : pw.toNat + lw.toNat + 16 ≤ fv.toNat) (hlow2 : pw.toNat + lw.toNat + 16 ≤ hv0.toNat)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l qv m c, r = .returned l (updatePanValueMap s.globals "heap_ptr" (.word qv)) m
        s.ffi [.rStruct [.word hv0, .word c]] ∧
      hv0.toNat + 16 * c.toNat ≤ qv.toNat ∧ InHeap qv ∧ Items s.memory pw lw.toNat c.toNat ∧
      SlEnt s.memory m pw hv0 c.toNat ∧
      ∀ x : Word, (x.toNat < fv.toNat ∨ pv.toNat ≤ x.toNat) →
        (x.toNat < hv0.toNat ∨ hv0.toNat + 16 * c.toNat ≤ x.toNat) → m x = s.memory x := by
  have hbody := (fun_of_index 115 hE.functions (by guest_decl_at 115) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l qv m c,
      r = .returned l (updatePanValueMap s.globals "heap_ptr" (.word qv)) m
        s.ffi [.rStruct [.word hv0, .word c]] ∧
      hv0.toNat + 16 * c.toNat ≤ qv.toNat ∧ InHeap qv ∧ Items s.memory pw lw.toNat c.toNat ∧
      SlEnt s.memory m pw hv0 c.toNat ∧
      ∀ x : Word, (x.toNat < fv.toNat ∨ pv.toNat ≤ x.toNat) →
        (x.toNat < hv0.toNat ∨ hv0.toNat + 16 * c.toNat ≤ x.toNat) → m x = s.memory x)) r h
  refine WPs.decCall_ret (fun v g m1 ffi hret => ?_)
  obtain ⟨hg, hf', hk1, c, hv, hitc⟩ := rlplistcount_items_ret hE hret (pw := pw) (lw := lw)
    (by lk [hpw]) (by lk [hlen]) hp hf hfp hlow
  simp only [List.cons.injEq, and_true] at hv
  subst g ffi v
  try dsimp only
  refine WPs.decCall_alloc hE (nv := c * 16#64) (by ev []) hh hhH (fun qv a1 a2 => ?_)
  try dsimp only
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l m,
      r = .returned l (updatePanValueMap s.globals "heap_ptr" (.word qv)) m
        s.ffi [.rStruct [.word hv0, .word c]] ∧
      hv0.toNat + 16 * c.toNat ≤ qv.toNat ∧ SlEnt s.memory m pw hv0 c.toNat ∧
      ∀ x : Word, (x.toNat < hv0.toNat ∨ hv0.toNat + 16 * c.toNat ≤ x.toNat) → m x = m1 x) ?_
    (by
      rintro r ⟨l, m, rfl, hq, hen, hfr⟩
      exact ⟨_, qv, m, c, rfl, hq, a2, hitc, hen,
        fun x hx1 hx2 => (hfr x hx2).trans (hk1 x hx1)⟩)
  have hhv := hhH.1
  have hlwl := lw.isLt
  refine WPs.seqG (fun a => SlJ (updatePanValueMap s.globals "heap_ptr" (.word qv)) s.memory m1
      s.ffi pw c hv0 a ∧ a.locals "i" = some (.word c))
    (WPs.loopG
      (I := SlJ (updatePanValueMap s.globals "heap_ptr" (.word qv)) s.memory m1 s.ffi pw c hv0)
      ⟨⟨rfl, rfl, by lk [hpw], by lk [], by lk [], 0#64, 0#64, by lk [], by lk [],
        by simp; omega, Nat.zero_le _, fun _ _ => rfl⟩, 0#64, 0#64, by lk [], by lk [], .zero,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩
      ⟨⟨hg, hfa, hP, hC, hA, iw, ow, hi, hoff, d1, d2, hfr⟩, iw', ow', hi', hoff', hit, hen⟩
      ⟨w, cc, hcond, hw⟩
    simp only at hg hfa hP hC hA hi hoff hfr hi' hoff' hen
    rw [hi] at hi'
    rw [hoff] at hoff'
    simp only [Option.some.injEq, PanValue.word.injEq] at hi' hoff'
    subst hi' hoff'
    subst hg hfa
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := iw) (by lk [hi]))
      (of_eval (w := c) (by lk [hC])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hlt : iw.toNat < c.toNat := by
      by_contra hge
      have hl : ¬ iw < c := by rw [BitVec.lt_def]; omega
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have hmul : (iw * 16#64).toNat = 16 * iw.toNat := by
      rw [BitVec.toNat_mul, show (16#64 : Word).toNat = 16 by decide]
      omega
    have ad0 : (hv0 + iw * 16#64).toNat = hv0.toNat + 16 * iw.toNat := by
      rw [BitVec.toNat_add, hmul]
      omega
    have ad8 : (hv0 + (iw * 16#64 + 8#64)).toNat = hv0.toNat + 16 * iw.toNat + 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hmul, show (8#64 : Word).toNat = 8 by decide]
      omega
    have hole := hit.mono hitc (Nat.le_of_lt hlt)
    have epo : (pw + ow).toNat = pw.toNat + ow.toNat := by
      rw [BitVec.toNat_add]
      omega
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hf', hm, tw, hv, hts⟩ := rlptotalunchecked_ret hE hret (pw := pw + ow)
      (by ev [hP, hoff])
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    dsimp only at hts
    have hts0 : TotSpec s.memory (pw + BitVec.ofNat 64 ow.toNat) tw := by
      rw [ofNat_toNat']
      refine hts.frame (by omega) (fun j hj => byteAt_low (fun x hx => ?_))
      have e : (pw + ow + BitVec.ofNat 64 j).toNat = pw.toNat + ow.toNat + j := by
        rw [BitVec.toNat_add, epo, BitVec.toNat_ofNat]
        omega
      exact ((hfr x (Or.inl (by omega))).trans (hk1 x (Or.inl (by omega)))).symm
    obtain ⟨t', ht', ht1, hnext⟩ := hit.next hitc hlt
    have := hts0.fn ht'
    subst this
    have hnl := hnext.mono hitc (by omega)
    try dsimp only
    refine WPs.seq_store_dom hE (addr := hv0 + iw * 16#64) (w := pw + ow)
      (of_eval (by ev [hA, hi])) (of_eval (by ev [hP, hoff])) (fun hdom => ?_)
    try dsimp only
    refine WPs.seq_store_inv hE (addr := hv0 + (iw * 16#64 + 8#64)) (w := tw)
      (of_eval (by ev [hA, hi])) (of_eval (by lk [])) ?_
    try dsimp only
    refine WPs.seq_assign (old := ow) (by lk [hoff]) (of_eval (w := ow + tw) (by ev [hoff])) ?_
    try dsimp only
    refine WPs.assign (old := iw) (by lk [hi]) (of_eval (w := iw + 1#64) (by ev [hi])) ?_
    simp only [restorePanValueFfiLocal]
    have e1 : (iw + 1#64).toNat = iw.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
      omega
    have e2 : (ow + tw).toNat = ow.toNat + tw.toNat := by
      rw [BitVec.toNat_add]
      omega
    rw [ad0] at hdom
    have hfr' : ∀ x : Word, (x.toNat < hv0.toNat ∨ hv0.toNat + 16 * (iw.toNat + 1) ≤ x.toNat) →
        setCell (setCell ma (hv0 + iw * 16#64) (pw + ow)) (hv0 + (iw * 16#64 + 8#64)) tw x =
          m1 x := by
      intro x hx
      rw [setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [ad8] at this; omega),
        setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [ad0] at this; omega)]
      exact hfr x (by omega)
    refine ⟨⟨rfl, rfl,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hP],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hC],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hA],
      iw + 1#64, ow + tw,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by rw [e1]; omega, by rw [e1]; omega, by rw [e1]; exact hfr'⟩, iw + 1#64, ow + tw,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by rw [e1, e2]; exact hnext, ?_⟩
    dsimp only
    rw [e1]
    intro j hj
    have aj0 : (hv0 + BitVec.ofNat 64 (16 * j)).toNat = hv0.toNat + 16 * j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    have aj8 : (hv0 + BitVec.ofNat 64 (16 * j + 8)).toNat = hv0.toNat + 16 * j + 8 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    by_cases hji : j < iw.toNat
    · obtain ⟨o, t, h1, h2, h3, h4, h5⟩ := hen j hji
      refine ⟨o, t, h1, h2, h3, ?_, ?_⟩
      · rw [setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [ad8, aj0] at this; omega),
          setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [ad0, aj0] at this; omega)]
        exact h4
      · rw [setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [ad8, aj8] at this; omega),
          setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [ad0, aj8] at this; omega)]
        exact h5
    · have hje : j = iw.toNat := by omega
      subst hje
      have x0 : hv0 + BitVec.ofNat 64 (16 * iw.toNat) = hv0 + iw * 16#64 :=
        BitVec.eq_of_toNat_eq (by rw [aj0, ad0])
      have x8 : hv0 + BitVec.ofNat 64 (16 * iw.toNat + 8) = hv0 + (iw * 16#64 + 8#64) :=
        BitVec.eq_of_toNat_eq (by rw [aj8, ad8])
      refine ⟨ow.toNat, tw, hit, hts0, ht1, ?_, ?_⟩
      · rw [x0, setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [ad8, ad0] at this; omega),
          ofNat_toNat']
        simp [setCell]
      · rw [x8]
        simp [setCell]
  · rintro a k ⟨⟨hg, hfa, hP, hC, hA, iw, ow, hi, hoff, d1, d2, hfr⟩, hJ⟩ hcond
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := iw) (by lk [hi]))
      (of_eval (w := c) (by lk [hC])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge : ¬ iw.toNat < c.toNat := by
      intro hlt
      have hl : iw < c := by rw [BitVec.lt_def]; exact hlt
      simp [evalPanCmp, hl] at hcv
    have heq : iw = c := BitVec.eq_of_toNat_eq (by omega)
    subst heq
    exact ⟨⟨⟨hg, hfa, hP, hC, hA, iw, ow, hi, hoff, d1, d2, hfr⟩, hJ⟩, hi⟩
  · rintro a ⟨⟨⟨hg, hfa, hP, hC, hA, iw, ow, hi, hoff, d1, d2, hfr⟩, iw', ow', hi', hoff', hit,
      hen⟩, hic⟩
    have : iw = c := by
      rw [hi] at hic
      simpa using hic
    subst this
    rw [hi] at hi'
    simp only [Option.some.injEq, PanValue.word.injEq] at hi'
    subst hi'
    have hmul : (iw * 16#64).toNat = 16 * iw.toNat := by
      rw [BitVec.toNat_mul, show (16#64 : Word).toNat = 16 by decide]
      omega
    rw [hmul] at a1
    have hev : E.eval a (.rStruct [.var .local "arr", .var .local "count"]) =
        some (.rStruct [.word hv0, .word iw]) := by
      simp [evalF_rStruct, evalArgs_cons, evalArgs_nil, evalF_local, hA, hC]
    refine WPs.ret_any (v := .rStruct [.word hv0, .word iw])
      (fun y hy => by rw [hev] at hy; exact (Option.some.inj hy).symm) ?_
    exact ⟨_, a.memory, by rw [hg, hfa], a1, hen, hfr⟩

end InitECandidate.Solver.GuestBound
