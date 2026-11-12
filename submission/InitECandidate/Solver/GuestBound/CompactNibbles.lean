import InitECandidate.Solver.GuestBound.KeyNibbles

/-!
# `compact_to_nibbles` writes only its fresh nibble buffer

The buffer is `alloc(2 * n)`; the nibbles go to `[out + k, out + k + 2 (n - 1))`
with `k ≤ 1`. That `2 * n` did not wrap follows from `key_to_nibbles_frame`
(a returning run stayed inside guest memory), so no bound on `n` is assumed.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Returning whatever the expression evaluates to. -/
theorem WPs.ret_ev {e : Exp Word}
    (h : ∀ v, E.eval s e = some v → Q (.returned (fun _ => none) s.globals s.memory s.ffi [v])) :
    WPs E s (.return e) Q := by
  intro r hr
  rw [runs_return] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some y =>
    rw [hv] at hr
    simp only at hr
    split at hr
    · subst hr; exact Or.inr (h y hv)
    · subst hr; exact Or.inl (Stopped.err s)

theorem keynibbles_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {kw nw ow0 : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "key_to_nibbles" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word kw)) (h2 : E.eval s e2 = some (.word nw))
    (h3 : E.eval s e3 = some (.word ow0)) (hob : ow0.toNat < 33806089704 + 16) :
    g = s.globals ∧ ffi = s.ffi ∧ ow0.toNat + 2 * nw.toNat < 33806089704 + 16 ∧
      ∀ x : Word, (x.toNat < ow0.toNat / 8 * 8 ∨ ow0.toNat + 2 * nw.toNat ≤ x.toNat) →
        m x = s.memory x := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 248 hE.functions (by guest_decl_at 248) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases key_to_nibbles_frame hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    kw nw ow0 (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hob hrun
    with hst | ⟨l', m', heq, hb, hfr⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hb, hfr⟩

set_option maxHeartbeats 8000000 in
theorem compact_to_nibbles_frame (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "compact_to_nibbles" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pw nw hv0 : Word) (hpw : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw))
    (hh : s.globals "heap_ptr" = some (.word hv0)) (hhH : InHeap hv0) (h : Runs E s body r) :
    Stopped r ∨ ∃ l qv m b c, r = .returned l (updatePanValueMap s.globals "heap_ptr" (.word qv)) m
        s.ffi [.rStruct [.word hv0, .word b, c]] ∧ InHeap qv ∧ hv0.toNat ≤ qv.toNat ∧
      ∀ x : Word, (x.toNat < hv0.toNat ∨ qv.toNat ≤ x.toNat) → m x = s.memory x := by
  have hbody := (fun_of_index 249 hE.functions (by guest_decl_at 249) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l qv m b c,
      r = .returned l (updatePanValueMap s.globals "heap_ptr" (.word qv)) m
        s.ffi [.rStruct [.word hv0, .word b, c]] ∧ InHeap qv ∧ hv0.toNat ≤ qv.toNat ∧
      ∀ x : Word, (x.toNat < hv0.toNat ∨ qv.toNat ≤ x.toNat) → m x = s.memory x)) r h
  refine WPs.seq (fun a => a = s) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip ⟨_, _, _, _, rfl, rfl⟩
    · refine WPs.call_ret (fun vs g m ffi hret => ?_)
      obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet (keepFn_sound (quietKeeper E) hE.functions 1
        "mpt_fail" (show keepFn quietLeaf Guest.Software.guestAst 1 "mpt_fail" = true by
          decide +kernel)) hret
      subst g m ffi
      exact ⟨_, _, _, _, rfl, rfl⟩
  intro a ha
  rw [ha]
  clear ha a
  refine WPs.dec_ev (fun vc0 _ => ?_)
  refine WPs.dec_ev (fun vfirst _ => ?_)
  refine WPs.dec_ev (fun vleaf _ => ?_)
  refine WPs.dec_ev (fun vodd _ => ?_)
  try dsimp only
  refine WPs.decCall_alloc hE (nv := 2#64 * nw) (by ev [hn]) hh hhH (fun qv a1 a2 => ?_)
  try dsimp only
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l m b c,
      r = .returned l (updatePanValueMap s.globals "heap_ptr" (.word qv)) m
        s.ffi [.rStruct [.word hv0, .word b, c]] ∧
      ∀ x : Word, (x.toNat < hv0.toNat ∨ qv.toNat ≤ x.toNat) → m x = s.memory x) ?_
    (by
      rintro r ⟨l, m, b, c, rfl, hfr⟩
      exact ⟨_, qv, m, b, c, rfl, a2, by omega, hfr⟩)
  generalize hL : updatePanValueMap _ "k" (PanValue.word 0#64) = L
  have L_out : L "out" = some (.word hv0) := by rw [← hL]; lk []
  have L_k : L "k" = some (.word 0#64) := by rw [← hL]; lk []
  have L_p : L "p" = some (.word pw) := by rw [← hL]; lk [hpw]
  have L_n : L "n" = some (.word nw) := by rw [← hL]; lk [hn]
  have hal := hhH.2
  have hend := hhH.1
  refine WPs.seq (fun a => a.globals = updatePanValueMap s.globals "heap_ptr" (.word qv) ∧
      a.ffi = s.ffi ∧ a.locals "out" = some (.word hv0) ∧ a.locals "p" = some (.word pw) ∧
      a.locals "n" = some (.word nw) ∧
      (∃ kw : Word, a.locals "k" = some (.word kw) ∧ kw.toNat ≤ 1) ∧
      ∀ x : Word, x.toNat ≠ hv0.toNat → a.memory x = s.memory x)
    (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip ⟨_, _, _, _, rfl, rfl, rfl, L_out, L_p, L_n, ⟨0#64, L_k, by decide⟩,
        fun _ _ => rfl⟩
    · refine WPs.seq_storeByte_fr hE (addr := hv0) (of_eval (by lk [L_out])) (fun m1 _ hf1 => ?_)
      refine WPs.assign (old := 0#64) L_k (of_eval (w := 1#64) (eval_const _ _)) ?_
      refine ⟨_, _, _, _, rfl, rfl, rfl, by lk [L_out], by lk [L_p], by lk [L_n],
        ⟨1#64, by lk [], by decide⟩, fun x hx => hf1 x (by omega)⟩
  rintro ⟨la, ga, ma, fa⟩ ⟨hg, hfa, hO, hP, hN, ⟨kw, hK, hk1⟩, hfr⟩
  simp only at hg hfa hO hP hN hK hfr
  subst hg hfa
  have hok : (hv0 + kw).toNat = hv0.toNat + kw.toNat := by
    rw [BitVec.toNat_add]
    omega
  refine WPs.seq_call_ret (fun vs g m2 ffi hret => ?_)
  obtain ⟨hg, hf', hb, hfr2⟩ := keynibbles_ret hE hret (kw := pw + 1#64) (nw := nw - 1#64)
    (ow0 := hv0 + kw) (by ev [hP]) (by ev [hN]) (by ev [hO, hK]) (by rw [hok]; omega)
  subst g ffi
  rw [hok] at hb hfr2
  refine WPs.ret_ev (fun v hv => ?_)
  rw [evalF_rStruct] at hv
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, hO] at hv
  cases h2 : E.eval ⟨la, updatePanValueMap s.globals "heap_ptr" (.word qv), m2, s.ffi⟩
      (.op .add [.var .local "k", .panOp .mul [.const 2#64,
        .op .sub [.var .local "n", .const 1#64]]]) with
  | none => rw [h2] at hv; simp at hv
  | some v2 =>
    obtain ⟨_, _, b, -, -, -, rfl⟩ := eval_op2_inv hE.word h2
    rw [h2] at hv
    cases h3 : la "is_leaf" with
    | none => rw [h3] at hv; simp at hv
    | some v3 =>
      rw [h3] at hv
      simp at hv
      subst hv
      refine ⟨_, m2, b, v3, rfl, fun x hx => ?_⟩
      have hsub : (nw - 1#64).toNat = (2 ^ 64 - 1 + nw.toNat) % 2 ^ 64 := by
        rw [BitVec.toNat_sub, show (1#64 : Word).toNat = 1 by decide]
      have hmul : (2#64 * nw).toNat = 2 * nw.toNat % 2 ^ 64 := by
        rw [BitVec.toNat_mul, show (2#64 : Word).toNat = 2 by decide]
      have hnl := nw.isLt
      rw [hmul] at a1
      rw [hfr2 x (by omega)]
      exact hfr x (by omega)

end InitECandidate.Solver.GuestBound
