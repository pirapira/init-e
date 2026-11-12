import InitECandidate.Solver.GuestBound.RlpCountFrame
import InitECandidate.Solver.GuestBound.FqSmall

/-!
# `rlp_list_to_slices` writes only its slice array

The array has `count * 16` bytes, where `count` comes from `rlp_list_count`.
Nothing bounds the length argument here (callers read it from memory), so the
product could wrap. It does not matter for runs that return: a word store
succeeds only below the end of the guest memory (`MemEnv.storeDom`), the loop
stores at `arr + 16 i` for every `i < count`, so a returning run has
`arr + 16 count` below that end and the product did not wrap.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `st a, v; rest`, with the fact that the store succeeded inside guest memory. -/
theorem WPs.seq_store_dom (hE : GuestEnv E) {a val : Exp Word} {q : Prog Word} {addr w : Word}
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : ∀ y, E.eval s val = some y → y = .word w)
    (h : addr.toNat < 33806089704 →
      WPs E ⟨s.locals, s.globals, setCell s.memory addr w, s.ffi⟩ q Q) :
    WPs E s (.seq (.store a val) q) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  obtain ⟨fuel, n, hrun⟩ := h1
  rcases store_word_inv' hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · cases r1 with
    | error l g m f => simp only at hrest; subst hrest; exact Or.inl trivial
    | _ => cases herr
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  have := hv y hy
  subst this
  obtain ⟨hm1, hdom⟩ := hm w rfl
  rw [hm1] at hrest
  exact h hdom r hrest

/-- Returning a value of any shape. -/
theorem WPs.ret_any {e : Exp Word} {v : PanValue Word}
    (he : ∀ y, E.eval s e = some y → y = v)
    (h : Q (.returned (fun _ => none) s.globals s.memory s.ffi [v])) :
    WPs E s (.return e) Q := by
  intro r hr
  rw [runs_return] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some y =>
    have := he y hv
    subst this
    rw [hv] at hr
    simp only at hr
    split at hr
    · subst hr; exact Or.inr h
    · subst hr; exact Or.inl (Stopped.err s)

theorem rlplistcount_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {pv fv pw0 lenv : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "rlp_list_count" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word pw0)) (h2 : E.eval s e2 = some (.word lenv))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧ ScrMem pv fv s.memory m ∧ ∃ c : Word, vs = [.word c] ∧
      c.toNat ≤ lenv.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 113 hE.functions (by guest_decl_at 113) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases rlp_list_count_frame hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    pv fv pw0 lenv (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hp hf hfp hrun
    with hst | ⟨l', m', c, heq, hc, hk⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hk, c, rfl, hc⟩

/-- Loop invariant: entries `0 .. i` of the array are written, nothing else. -/
def SlI (G : VarName → Option (PanValue Word)) (m1 : Word → Option (PanValue Word))
    (f : FfiState σ) (pw0 c hv0 : Word) (a : St σ) : Prop :=
  a.globals = G ∧ a.ffi = f ∧ a.locals "p" = some (.word pw0) ∧
    a.locals "count" = some (.word c) ∧ a.locals "arr" = some (.word hv0) ∧
    ∃ iw ow : Word, a.locals "i" = some (.word iw) ∧ a.locals "off" = some (.word ow) ∧
      hv0.toNat + 16 * iw.toNat < 33806089704 + 16 ∧ iw.toNat ≤ c.toNat ∧
      ∀ x : Word, (x.toNat < hv0.toNat ∨ hv0.toNat + 16 * iw.toNat ≤ x.toNat) → a.memory x = m1 x

set_option maxHeartbeats 8000000 in
theorem rlp_list_to_slices_frame (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_list_to_slices" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv pw0 lenv hv0 : Word)
    (hpw : s.locals "p" = some (.word pw0)) (hlen : s.locals "len" = some (.word lenv))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (hh : s.globals "heap_ptr" = some (.word hv0)) (hhH : InHeap hv0)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l qv m c, r = .returned l (updatePanValueMap s.globals "heap_ptr" (.word qv)) m
        s.ffi [.rStruct [.word hv0, .word c]] ∧
      hv0.toNat + 16 * c.toNat ≤ qv.toNat ∧ InHeap qv ∧ c.toNat ≤ lenv.toNat ∧
      ∀ x : Word, (x.toNat < fv.toNat ∨ pv.toNat ≤ x.toNat) →
        (x.toNat < hv0.toNat ∨ hv0.toNat + 16 * c.toNat ≤ x.toNat) → m x = s.memory x := by
  have hbody := (fun_of_index 115 hE.functions (by guest_decl_at 115) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l qv m c,
      r = .returned l (updatePanValueMap s.globals "heap_ptr" (.word qv)) m
        s.ffi [.rStruct [.word hv0, .word c]] ∧
      hv0.toNat + 16 * c.toNat ≤ qv.toNat ∧ InHeap qv ∧ c.toNat ≤ lenv.toNat ∧
      ∀ x : Word, (x.toNat < fv.toNat ∨ pv.toNat ≤ x.toNat) →
        (x.toNat < hv0.toNat ∨ hv0.toNat + 16 * c.toNat ≤ x.toNat) → m x = s.memory x)) r h
  refine WPs.decCall_ret (fun v g m1 ffi hret => ?_)
  obtain ⟨hg, hf', hk1, c, hv, hc⟩ := rlplistcount_ret hE hret (pw0 := pw0) (lenv := lenv)
    (by lk [hpw]) (by lk [hlen]) hp hf hfp
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
      hv0.toNat + 16 * c.toNat ≤ qv.toNat ∧
      ∀ x : Word, (x.toNat < hv0.toNat ∨ hv0.toNat + 16 * c.toNat ≤ x.toNat) → m x = m1 x) ?_
    (by
      rintro r ⟨l, m, rfl, hq, hfr⟩
      exact ⟨_, qv, m, c, rfl, hq, a2, hc, fun x hx1 hx2 => (hfr x hx2).trans (hk1 x hx1)⟩)
  have hhv := hhH.1
  refine WPs.seqG (fun a => SlI (updatePanValueMap s.globals "heap_ptr" (.word qv)) m1 s.ffi pw0
      c hv0 a ∧ a.locals "i" = some (.word c))
    (WPs.loopG (I := SlI (updatePanValueMap s.globals "heap_ptr" (.word qv)) m1 s.ffi pw0 c hv0)
      ⟨rfl, rfl, by lk [hpw], by lk [], by lk [], 0#64, 0#64, by lk [], by lk [],
        by simp; omega, Nat.zero_le _, fun _ _ => rfl⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hfa, hP, hC, hA, iw, ow, hi, hoff, d1, d2, hfr⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hfa hP hC hA hi hoff hfr
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
    refine WPs.decCall_word (fun tw g m ffi hret => ?_)
    obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet (keepFn_sound (quietKeeper E) hE.functions 3
      "rlp_item_total_unchecked"
      (show keepFn quietLeaf Guest.Software.guestAst 3 "rlp_item_total_unchecked" = true by
        decide +kernel)) hret
    subst g m ffi
    try dsimp only
    refine WPs.seq_store_dom hE (addr := hv0 + iw * 16#64) (w := pw0 + ow)
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
    rw [ad0] at hdom
    refine ⟨rfl, rfl,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hP],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hC],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hA],
      iw + 1#64, ow + tw,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by rw [e1]; omega, by rw [e1]; omega, fun x hx => ?_⟩
    dsimp only
    rw [e1] at hx
    rw [setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [ad8] at this; omega),
      setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [ad0] at this; omega)]
    exact hfr x (by omega)
  · rintro a k ⟨hg, hfa, hP, hC, hA, iw, ow, hi, hoff, d1, d2, hfr⟩ hcond
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := iw) (by lk [hi]))
      (of_eval (w := c) (by lk [hC])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge : ¬ iw.toNat < c.toNat := by
      intro hlt
      have hl : iw < c := by rw [BitVec.lt_def]; exact hlt
      simp [evalPanCmp, hl] at hcv
    have heq : iw = c := BitVec.eq_of_toNat_eq (by omega)
    subst heq
    exact ⟨⟨hg, hfa, hP, hC, hA, iw, ow, hi, hoff, d1, d2, hfr⟩, hi⟩
  · rintro a ⟨⟨hg, hfa, hP, hC, hA, iw, ow, hi, hoff, d1, d2, hfr⟩, hic⟩
    have : iw = c := by
      rw [hi] at hic
      simpa using hic
    subst this
    have hmul : (iw * 16#64).toNat = 16 * iw.toNat := by
      rw [BitVec.toNat_mul, show (16#64 : Word).toNat = 16 by decide]
      omega
    rw [hmul] at a1
    have hev : E.eval a (.rStruct [.var .local "arr", .var .local "count"]) =
        some (.rStruct [.word hv0, .word iw]) := by
      simp [evalF_rStruct, evalArgs_cons, evalArgs_nil, evalF_local, hA, hC]
    refine WPs.ret_any (v := .rStruct [.word hv0, .word iw])
      (fun y hy => by rw [hev] at hy; exact (Option.some.inj hy).symm) ?_
    exact ⟨_, a.memory, by rw [hg, hfa], a1, hfr⟩

end InitECandidate.Solver.GuestBound
