import InitECandidate.Solver.GuestBound.RlpItemFrame
import InitECandidate.Solver.GuestBound.ResolveStep
import InitECandidate.Solver.GuestBound.TrieResolve

/-!
# `rlp_item`: the result lies inside the input slice

`rlp_item(p, len)` returns `<kind, q, n, total>` with `p ≤ q`,
`q + n ≤ p + len`, `n ≤ total ≤ len`.  This is the first step of the pointer
provenance of witness data (issue #30).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `if c { f(…); }` for an `f` that never returns: afterwards `c` was false. -/
theorem WPs.guard_nr {c : Exp Word} {f : FunName} {args : List (Exp Word)} {q : Prog Word}
    (hf : FunNoReturn E f)
    (h : E.eval s c = some (.word 0#64) → WPs E s q Q) :
    WPs E s (.seq (.ite c (.call (some (none, none)) f args) .skip) q) Q := by
  refine WPs.seqG (fun a => a = s ∧ E.eval s c = some (.word 0#64))
    (WPs.ite_both (fun w hw => ?_)) (fun a ha => by
      obtain ⟨ha, hc⟩ := ha
      rw [ha]
      exact h hc)
  split
  · rename_i h0
    rw [h0] at hw
    exact WPs.skip ⟨rfl, hw⟩
  · exact fun r hr => Or.inl (stops_call_noReturn hf hr)

/-- An unsigned `<` that evaluated to 0. -/
theorem lower_false (hE : GuestEnv E) {a b : Exp Word} {wa wb : Word}
    (ha : E.eval s a = some (.word wa)) (hb : E.eval s b = some (.word wb))
    (hw : E.eval s (.cmp .lower a b) = some (.word 0#64)) : wb.toNat ≤ wa.toNat := by
  have := eval_cmp_inv hE (op := .lower) (of_eval ha) (of_eval hb) _ hw
  simp only [PanValue.word.injEq] at this
  by_contra hlt
  have hl : wa < wb := BitVec.lt_def.mpr (by omega)
  simp [evalPanCmp, hl] at this

/-- What `rlp_item` returns. -/
def ItemR (pv fv : Word) (s : St σ) (pw lw : Word) (r : Result σ) : Prop :=
  ∃ l m, ∃ (k q n tot : Word), r = .returned l s.globals m s.ffi
      [.rStruct [.word k, .word q, .word n, .word tot]] ∧ ScrMem pv fv s.memory m ∧
    pw.toNat ≤ q.toNat ∧ q.toNat + n.toNat ≤ pw.toNat + lw.toNat ∧ tot.toNat ≤ lw.toNat ∧
    n.toNat ≤ tot.toNat

theorem ItemR.restore {pv fv pw lw : Word} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : ItemR pv fv s pw lw r) :
    ItemR pv fv s pw lw (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, m, k, q, n, tot, rfl, hk⟩ := h
  exact ⟨_, m, k, q, n, tot, rfl, hk⟩

set_option maxHeartbeats 16000000 in
theorem rlp_item_range (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_item" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv pw lw : Word) (hpw : s.locals "p" = some (.word pw))
    (hlw : s.locals "len" = some (.word lw)) (h64 : pw.toNat + lw.toNat < 2 ^ 64)
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (h : Runs E s body r) : Stopped r ∨ ItemR pv fv s pw lw r := by
  have hbody := (fun_of_index 107 hE.functions (by guest_decl_at 107) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (ItemR pv fv s pw lw)) r h
  have hfq := rlp_fail_quiet hE
  have hnr := rlp_fail_noReturn hE
  have hrq := rlp_read_length_quiet hE
  have h1 : (1#64 : Word).toNat = 1 := rfl
  have dm : ∀ r, ItemR pv fv s pw lw r → ItemR pv fv s pw lw r := fun _ h => h
  refine WPs.guard_nr hnr (fun hc0 => ?_)
  have hl1 : 1 ≤ lw.toNat := by
    have := eval_cmp_inv hE (op := .equal) (of_eval (w := lw) (by lk [hlw]))
      (of_eval (eval_const _ 0#64)) _ hc0
    simp only [PanValue.word.injEq] at this
    by_contra hlt
    have : lw = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst this
    simp [evalPanCmp] at *
  have esub : (lw - 1#64).toNat = lw.toNat - 1 := by
    rw [BitVec.toNat_sub, h1]
    omega
  have ep1 : (pw + 1#64).toNat = pw.toNat + 1 := by
    rw [BitVec.toNat_add, h1]
    omega
  refine WPs.dec_ev (fun vb _ => WPs.conseq (Q' := ItemR pv fv s pw lw) ?_ (fun r h => h.restore))
  try dsimp only
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qp : L "p" = some (.word pw) := by rw [hLL]; lk [hpw]
  have ql : L "len" = some (.word lw) := by rw [hLL]; lk [hlw]
  clear hLL
  have elen1 : ∀ (L' : VarName → Option (PanValue Word)) (m' : Word → Option (PanValue Word)),
      L' "len" = some (.word lw) →
      E.eval ⟨L', s.globals, m', s.ffi⟩ (.op .sub [.var .local "len", .const 1#64]) =
        some (.word (lw - 1#64)) := by
    intro L' m' h
    simp [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_local, h, wordsProj_cons,
      wordsProj_nil, wordOp]
  -- a single byte below 128
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · exact WPs.ret_quad (of_eval (eval_const _ 0#64)) (of_eval (by lk [qp]))
        (of_eval (eval_const _ 1#64)) (of_eval (eval_const _ 1#64))
        ⟨_, _, 0#64, pw, 1#64, 1#64, rfl, ScrMem.refl _ _ _, Nat.le_refl _, by rw [h1]; omega,
          by rw [h1]; omega, Nat.le_refl _⟩
  intro a ha
  rw [ha]
  clear ha a
  -- short string
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.dec_ev (fun vn hvn => WPs.conseq (Q' := ItemR pv fv s pw lw) ?_ (fun r h => by
        obtain ⟨l, m, k, q, n, tot, rfl, hk⟩ := h
        exact ⟨_, m, k, q, n, tot, rfl, hk⟩))
      obtain ⟨nn, rfl⟩ := isw_op hE _ hvn
      refine WPs.guard_nr hnr (fun hc => ?_)
      have hn := lower_false hE (wb := nn) (elen1 _ _ (by lk [ql])) (by lk []) hc
      rw [esub] at hn
      refine WPs.guard2_quiet hfq ?_
      have e1n : (1#64 + nn).toNat = 1 + nn.toNat := by
        rw [BitVec.toNat_add, h1]
        omega
      exact WPs.ret_quad (a := 0#64) (b := pw + 1#64) (c := nn) (d := 1#64 + nn)
        (of_eval (eval_const _ 0#64)) (of_eval (by ev [qp])) (of_eval (by lk []))
        (of_eval (by ev []))
        ⟨_, _, 0#64, pw + 1#64, nn, 1#64 + nn, rfl, ScrMem.refl _ _ _, by omega, by omega,
          by omega, by omega⟩
  intro a ha
  rw [ha]
  clear ha a
  -- long string
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.dec_ev (fun vl hvl => WPs.conseq (Q' := ItemR pv fv s pw lw) ?_ (fun r h => by
        obtain ⟨l, m, k, q, n, tot, rfl, hk⟩ := h
        exact ⟨_, m, k, q, n, tot, rfl, hk⟩))
      obtain ⟨llw, rfl⟩ := isw_op hE _ hvl
      refine WPs.guard_nr hnr (fun hc => ?_)
      have hll := lower_false hE (wb := llw) (elen1 _ _ (by lk [ql])) (by lk []) hc
      rw [esub] at hll
      refine WPs.decCall_word (fun nn g m ffi hret =>
        WPs.conseq (Q' := ItemR pv fv s pw lw) ?_ (fun r h => h.restore))
      obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet hrq hret
      subst g m ffi
      refine WPs.guard_quiet hfq ?_
      refine WPs.guard_nr hnr (fun hc2 => ?_)
      have esub2 : (lw - 1#64 - llw).toNat = lw.toNat - 1 - llw.toNat := by
        rw [BitVec.toNat_sub, esub]
        omega
      have hn := lower_false hE (a := .op .sub [.op .sub [.var .local "len", .const 1#64],
        .var .local "ll"]) (wa := lw - 1#64 - llw) (wb := nn)
        (by simp (config := { decide := true }) [evalF_op hE.word, evalArgs_cons, evalArgs_nil,
          evalF_local, update_lookup, ql, wordsProj_cons, wordsProj_nil, wordOp])
        (by lk []) hc2
      rw [esub2] at hn
      have e1l : (1#64 + llw).toNat = 1 + llw.toNat := by
        rw [BitVec.toNat_add, h1]
        omega
      have eq : (pw + (1#64 + llw)).toNat = pw.toNat + 1 + llw.toNat := by
        rw [BitVec.toNat_add, e1l]
        omega
      have eln : (llw + nn).toNat = llw.toNat + nn.toNat := by
        rw [BitVec.toNat_add]
        omega
      have et : (1#64 + (llw + nn)).toNat = 1 + llw.toNat + nn.toNat := by
        rw [BitVec.toNat_add, h1, eln]
        omega
      exact WPs.ret_quad (a := 0#64) (b := pw + (1#64 + llw)) (c := nn) (d := 1#64 + (llw + nn))
        (of_eval (eval_const _ 0#64)) (of_eval (by ev [qp])) (of_eval (by lk []))
        (of_eval (by ev []))
        ⟨_, _, 0#64, _, nn, _, rfl, ScrMem.refl _ _ _, by omega, by omega, by omega, by omega⟩
  intro a ha
  rw [ha]
  clear ha a
  -- short list
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.dec_ev (fun vn hvn => WPs.conseq (Q' := ItemR pv fv s pw lw) ?_ (fun r h => by
        obtain ⟨l, m, k, q, n, tot, rfl, hk⟩ := h
        exact ⟨_, m, k, q, n, tot, rfl, hk⟩))
      obtain ⟨nn, rfl⟩ := isw_op hE _ hvn
      refine WPs.guard_nr hnr (fun hc => ?_)
      have hn := lower_false hE (wb := nn) (elen1 _ _ (by lk [ql])) (by lk []) hc
      rw [esub] at hn
      refine WPs.seq_call_ret (fun vs g m ffi hret => ?_)
      obtain ⟨hg, hf', hk, -⟩ := rlplistcount_ret hE hret (pw0 := pw + 1#64) (lenv := nn)
        (by ev [qp]) (by lk []) hp hf hfp
      subst g ffi
      have e1n : (1#64 + nn).toNat = 1 + nn.toNat := by
        rw [BitVec.toNat_add, h1]
        omega
      exact WPs.ret_quad (a := 1#64) (b := pw + 1#64) (c := nn) (d := 1#64 + nn)
        (of_eval (eval_const _ 1#64)) (of_eval (by ev [qp])) (of_eval (by lk []))
        (of_eval (by ev []))
        ⟨_, _, 1#64, pw + 1#64, nn, 1#64 + nn, rfl, hk, by omega, by omega, by omega, by omega⟩
  intro a ha
  rw [ha]
  clear ha a
  -- long list
  refine WPs.dec_ev (fun vl hvl => WPs.conseq (Q' := ItemR pv fv s pw lw) ?_
    (fun r h => h.restore))
  obtain ⟨llw, rfl⟩ := isw_op hE _ hvl
  refine WPs.guard_nr hnr (fun hc => ?_)
  have hll := lower_false hE (wb := llw) (elen1 _ _ (by lk [ql])) (by lk []) hc
  rw [esub] at hll
  refine WPs.decCall_word (fun nn g m ffi hret =>
    WPs.conseq (Q' := ItemR pv fv s pw lw) ?_ (fun r h => h.restore))
  obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet hrq hret
  subst g m ffi
  refine WPs.guard_quiet hfq ?_
  refine WPs.guard_nr hnr (fun hc2 => ?_)
  have esub2 : (lw - 1#64 - llw).toNat = lw.toNat - 1 - llw.toNat := by
    rw [BitVec.toNat_sub, esub]
    omega
  have hn := lower_false hE (a := .op .sub [.op .sub [.var .local "len", .const 1#64],
    .var .local "ll"]) (wa := lw - 1#64 - llw) (wb := nn)
    (by simp (config := { decide := true }) [evalF_op hE.word, evalArgs_cons, evalArgs_nil,
      evalF_local, update_lookup, ql, wordsProj_cons, wordsProj_nil, wordOp])
    (by lk []) hc2
  rw [esub2] at hn
  have e1l : (1#64 + llw).toNat = 1 + llw.toNat := by
    rw [BitVec.toNat_add, h1]
    omega
  have eq : (pw + (1#64 + llw)).toNat = pw.toNat + 1 + llw.toNat := by
    rw [BitVec.toNat_add, e1l]
    omega
  have eln : (llw + nn).toNat = llw.toNat + nn.toNat := by
    rw [BitVec.toNat_add]
    omega
  have et : (1#64 + (llw + nn)).toNat = 1 + llw.toNat + nn.toNat := by
    rw [BitVec.toNat_add, h1, eln]
    omega
  refine WPs.seq_call_ret (fun vs g m ffi hret => ?_)
  obtain ⟨hg, hf', hk, -⟩ := rlplistcount_ret hE hret (pw0 := pw + (1#64 + llw)) (lenv := nn)
    (by ev [qp]) (by lk []) hp hf hfp
  subst g ffi
  exact WPs.ret_quad (a := 1#64) (b := pw + (1#64 + llw)) (c := nn) (d := 1#64 + (llw + nn))
    (of_eval (eval_const _ 1#64)) (of_eval (by ev [qp])) (of_eval (by lk []))
    (of_eval (by ev []))
    ⟨_, _, 1#64, _, nn, _, rfl, hk, by omega, by omega, by omega, by omega⟩


section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

/-- What a returning `rlp_item` leaves, with the range of its result. -/
theorem rlpitem_range_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {pv fv pw lw : Word}
    (h : CalleeRet E s "rlp_item" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word pw)) (h2 : E.eval s e2 = some (.word lw))
    (h64 : pw.toNat + lw.toNat < 2 ^ 64)
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧ ScrMem pv fv s.memory m ∧
      ∃ k q n tot : Word, vs = [.rStruct [.word k, .word q, .word n, .word tot]] ∧
        pw.toNat ≤ q.toNat ∧ q.toNat + n.toNat ≤ pw.toNat + lw.toNat ∧
        tot.toNat ≤ lw.toNat ∧ n.toNat ≤ tot.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 107 hE.functions (by guest_decl_at 107) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases rlp_item_range hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ pv fv pw
    lw (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) h64 hp hf hfp
    hrun with hst | ⟨l', m', k, q, n, tot, heq, hk, a1, a2, a3, a4⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hk, k, q, n, tot, rfl, a1, a2, a3, a4⟩

end rets

set_option maxHeartbeats 8000000 in
/-- `rlp_decode_fully(p, len)`: the item spans the whole slice. -/
theorem rlp_decode_fully_range (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_decode_fully" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv pw lw : Word) (hpw : s.locals "p" = some (.word pw))
    (hlw : s.locals "len" = some (.word lw)) (h64 : pw.toNat + lw.toNat < 2 ^ 64)
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (h : Runs E s body r) : Stopped r ∨ ItemR pv fv s pw lw r := by
  have hbody := (fun_of_index 108 hE.functions (by guest_decl_at 108) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (ItemR pv fv s pw lw)) r h
  refine WPs.decCall_ret (fun v g m ffi hret => WPs.conseq (Q' := ItemR pv fv s pw lw) ?_
    (fun r h => h.restore))
  obtain ⟨hg, hf', hk, k, q, n, tot, hv, a1, a2, a3, a4⟩ := rlpitem_range_ret hE hret
    (pw := pw) (lw := lw) (by lk [hpw]) (by lk [hlw]) h64 hp hf hfp
  simp only [List.cons.injEq, and_true] at hv
  subst g ffi v
  refine WPs.guard_quiet (rlp_fail_quiet hE) ?_
  refine WPs.ret_ev (fun v hv => ?_)
  simp (config := { decide := true }) [evalF_local, update_lookup] at hv
  subst hv
  exact ⟨_, m, k, q, n, tot, rfl, hk, a1, a2, a3, a4⟩

end InitECandidate.Solver.GuestBound
