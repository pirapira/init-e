import InitECandidate.Solver.GuestBound.RlpHdrSpec
import InitECandidate.Solver.GuestBound.RlpCountFrame

/-!
# `rlp_item_total` agrees with `TotSpec`

The checked total of an item is the `TotSpec` total, fits in the given length,
and only free scratch memory changes (the nested-list validation).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- What a returning `rlp_item_header` leaves. -/
theorem rlphdr_tot_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {pw lw : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "rlp_item_header" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word pw)) (h2 : E.eval s e2 = some (.word lw)) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ h0 h1' k : Word,
      vs = [.rStruct [.word h0, .word h1', .word k]] ∧ TotSpec s.memory pw (h0 + h1') ∧
      h0.toNat + h1'.toNat ≤ lw.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 109 hE.functions (by guest_decl_at 109) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases rlp_item_header_tot hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ pw lw
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hrun
    with hst | ⟨l', h0, h1', k, heq, ht, hb⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, h0, h1', k, rfl, ht, hb⟩

/-- What `rlp_item_total` returns. -/
def TotQ (pv fv : Word) (s : St σ) (pw lw : Word) (r : Result σ) : Prop :=
  ∃ l m t, r = .returned l s.globals m s.ffi [.word t] ∧ TotSpec s.memory pw t ∧
    t.toNat ≤ lw.toNat ∧ ScrMem pv fv s.memory m

set_option maxHeartbeats 8000000 in
theorem rlp_item_total_tot (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_item_total" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv pw lw : Word) (hpw : s.locals "p" = some (.word pw))
    (hlen : s.locals "len" = some (.word lw))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (h : Runs E s body r) : Stopped r ∨ TotQ pv fv s pw lw r := by
  have hbody := (fun_of_index 112 hE.functions (by guest_decl_at 112) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (TotQ pv fv s pw lw)) r h
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf', a, b, c, hv, ht, hb⟩ := rlphdr_tot_ret hE hret (pw := pw) (lw := lw)
    (by lk [hpw]) (by lk [hlen])
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  try dsimp only
  refine WPs.seq (fun st => ∃ m, st = ⟨updatePanValueMap s.locals "h"
      (.rStruct [.word a, .word b, .word c]), s.globals, m, s.ffi⟩ ∧ ScrMem pv fv s.memory m)
    (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip ⟨_, _, _, _, rfl, _, rfl, ScrMem.refl _ _ _⟩
    · refine WPs.call_ret (fun vs g m ffi hret => ?_)
      obtain ⟨hg, hf', hk⟩ := rlpvalidate_ret hE hret (pw0 := pw + a)
        (by ev [hpw, evalF_rField]) hp hf hfp
      subst g ffi
      exact ⟨_, _, _, _, rfl, m, rfl, hk⟩
  · rintro _ ⟨m, rfl, hk⟩
    refine WPs.ret (w := a + b) (of_eval (by ev [evalF_rField])) ?_
    simp only [restorePanValueFfiLocal]
    have : (a + b).toNat ≤ a.toNat + b.toNat := by
      rw [BitVec.toNat_add]
      exact Nat.mod_le _ _
    exact ⟨_, m, a + b, rfl, ht, by omega, hk⟩

/-- What a returning `rlp_item_total` leaves. -/
theorem rlptotal_tot_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {pv fv pw lw : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "rlp_item_total" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word pw)) (h2 : E.eval s e2 = some (.word lw))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧ ∃ t : Word, vs = [.word t] ∧ TotSpec s.memory pw t ∧
      t.toNat ≤ lw.toNat ∧ ScrMem pv fv s.memory m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 112 hE.functions (by guest_decl_at 112) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases rlp_item_total_tot hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ pv fv
    pw lw (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hp hf hfp hrun
    with hst | ⟨l', m', t, heq, ht, hb, hk⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, t, rfl, ht, hb, hk⟩

end InitECandidate.Solver.GuestBound
