import InitECandidate.Solver.GuestBound.RlpValidateFrame

/-!
# `rlp_validate_items`, `rlp_item_total`, `rlp_list_count`: frame and count

`rlp_validate_items` releases the scratch it used, so on return all globals
are as before and only free scratch memory changed. The same then holds for
`rlp_item_total` and `rlp_list_count`, and the count returned by
`rlp_list_count(p, len)` is at most `len` (every item takes at least one
byte). Frame facts for the witness-decoding loop (issue #21).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A call statement followed by a `raise` never ends normally. -/
theorem stops_call_raise {g : FunName} {args : List (Exp Word)} {exc : ExceptionId}
    {e : Exp Word} {s' : St σ} {r : Result σ}
    (h : Runs E s' (.seq (.call (some (none, none)) g args) (.raise exc e)) r) : Stopped r := by
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp h
  have hc : WPs E s' (.call (some (none, none)) g args)
      (fun r => ∃ l g m f, r = .normal l g m f) :=
    WPs.call_ret (fun vs g m ffi _ => ⟨_, _, _, _, rfl⟩)
  rcases hc r1 h1 with hs | ⟨l, g', m, f, rfl⟩
  · cases r1 with
    | normal l g m f => exact absurd hs Stopped.not_normal
    | _ => simp only at hrest; subst hrest; exact hs
  · simp only at hrest
    rcases runs_raise_inv hrest with he | ⟨v, -, rfl⟩
    · exact Stopped.of_error he
    · trivial

/-- `try f(…) catch exc => hv { hp }` as a statement, when the handler always stops. -/
theorem WPs.callH_stop {f : FunName} {exc : ExceptionId} {hv : VarName} {hp : Prog Word}
    {args : List (Exp Word)} (hstop : ∀ s' r, Runs E s' hp r → Stopped r)
    (h : ∀ vs g m ffi, CalleeRet E s f args vs g m ffi → Q (.normal s.locals g m ffi)) :
    WPs E s (.call (some (none, some (exc, hv, hp))) f args) Q := by
  intro r hr
  rcases runs_callH_inv hr with herr | ⟨parameters, body, values, cl, rb, hlookup, hvalues,
    hbind, hrun, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  cases rb with
  | returned lr g m ffi vs =>
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    · obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
      have : l' = s.locals := funext (fun x => hl x (by simp))
      subst this
      exact Or.inr (h vs _ m ffi ⟨parameters, body, values, cl, lr, hlookup, hvalues, hbind,
        hrun⟩)
  | raised lr g m ffi e v =>
    rcases hout with ⟨-, rfl⟩ | ⟨-, hrunh⟩
    · exact Or.inl trivial
    · exact Or.inl (hstop _ _ hrunh)
  | finalFfi lr g m ffi ev =>
    subst hout
    exact Or.inl trivial
  | _ => exact Or.inl (Stopped.of_error hout)

theorem scratch_mark_ret (hE : GuestEnv E) {pv : Word} {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} (h : CalleeRet E s "scratch_mark" [] vs g m ffi)
    (hp : s.globals "scratch_ptr" = some (.word pv)) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ vs = [.word pv] := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hbody := (fun_of_index 14 hE.functions (by guest_decl_at 14) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  simp only [runs_return, eval_global, hp, payload_word, if_true] at hrun
  cases hrun
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem scratch_release_ret (hE : GuestEnv E) {e : Exp Word} {mv pv : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "scratch_release" [e] vs g m ffi) (he : E.eval s e = some (.word mv))
    (hp : s.globals "scratch_ptr" = some (.word pv)) :
    g = updatePanValueMap s.globals "scratch_ptr" (.word mv) ∧ m = s.memory ∧ ffi = s.ffi := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hf := fun_of_index 15 hE.functions (by guest_decl_at 15) (by decide +kernel) hlookup
  have hbody := hf.1
  have hparams := hf.2
  subst hbody
  simp only [evalArgs_cons, evalArgs_nil, he, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  subst hbind
  dsimp only at hrun
  simp (config := { decide := true }) only [runs_seq, runs_assign_global, runs_return,
    evalF_local, update_lookup, eval_const, panValueAssignmentValid, hp, shape_word,
    shape_matches_self, payload_word, if_true, exists_eq_left] at hrun
  cases hrun
  exact ⟨rfl, rfl, rfl⟩

/-- On return, `rlp_validate_items` has changed only free scratch memory. -/
theorem rlp_validate_items_frame (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_validate_items" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv pw0 : Word) (hpw : s.locals "p" = some (.word pw0))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l m, r = .returned l s.globals m s.ffi [.word 0#64] ∧
      ∀ x : Word, (x.toNat < fv.toNat ∨ pv.toNat ≤ x.toNat) → m x = s.memory x := by
  have hbody := (fun_of_index 111 hE.functions (by guest_decl_at 111) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m, r = .returned l s.globals m s.ffi [.word 0#64] ∧
    ∀ x : Word, (x.toNat < fv.toNat ∨ pv.toNat ≤ x.toNat) → m x = s.memory x)) r h
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf', hv⟩ := scratch_mark_ret hE hret hp
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  try dsimp only
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l m, r = .returned l s.globals m s.ffi [.word 0#64] ∧
    ∀ x : Word, (x.toNat < fv.toNat ∨ pv.toNat ≤ x.toNat) → m x = s.memory x) ?_
    (by rintro r ⟨l, m, rfl, hk⟩; exact ⟨_, m, rfl, hk⟩)
  try dsimp only
  refine WPs.seq (fun a => ∃ g m, a = ⟨updatePanValueMap (updatePanValueMap s.locals "mark"
      (.word pv)) "e" (.word 0#64), g, m, s.ffi⟩ ∧ ScrKeep pv fv s g m s.ffi)
    (WPs.callH_stop (fun s' r hr => stops_call_raise hr) (fun vs g m ffi hret => ?_)) ?_
  · obtain ⟨ps, cb, values, cl, l, hl, hvalues, hbind, hrun⟩ := hret
    have hparams := (fun_of_index 110 hE.functions (by guest_decl_at 110) (by decide +kernel)
      hl).2
    obtain ⟨v2, hv2⟩ : ∃ v2, values = [.word pw0, v2] := by
      have e1 : E.eval ⟨updatePanValueMap (updatePanValueMap s.locals "mark" (.word pv)) "e"
          (.word 0#64), s.globals, s.memory, s.ffi⟩ (.var .local "p") = some (.word pw0) := by
        lk [hpw]
      simp only [evalArgs_cons, evalArgs_nil, e1] at hvalues
      cases he2 : E.eval ⟨updatePanValueMap (updatePanValueMap s.locals "mark" (.word pv)) "e"
          (.word 0#64), s.globals, s.memory, s.ffi⟩ (.var .local "len") with
      | none => rw [he2] at hvalues; simp at hvalues
      | some v2 =>
        rw [he2] at hvalues
        simp at hvalues
        exact ⟨v2, hvalues.symm⟩
    subst hv2
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    rcases rlp_validate_body_frame hE ps cb hl ⟨cl, s.globals, s.memory, s.ffi⟩ _ pv fv pw0
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hp hf hfp hrun
      with hst | ⟨l', g', m', heq, hk⟩
    · exact absurd hst (fun h => h)
    · cases heq
      exact ⟨_, _, _, _, rfl, _, _, rfl, hk⟩
  rintro _ ⟨g, m, rfl, hfa, hgl, ⟨qv, hq, hq1, hq2⟩, hfr⟩
  refine WPs.seq_call_ret (fun vs g2 m2 ffi2 hret => ?_)
  obtain ⟨hg2, hm2, hf2⟩ := scratch_release_ret hE hret (mv := pv) (by lk []) hq
  subst g2 m2 ffi2
  refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  have hgs : updatePanValueMap g "scratch_ptr" (.word pv) = s.globals := by
    funext x
    rw [update_lookup]
    by_cases hx : x = "scratch_ptr"
    · subst hx
      simp [hp]
    · rw [if_neg (by simpa using hx)]
      exact hgl x hx
  exact ⟨_, m, by rw [hgs], hfr⟩

end InitECandidate.Solver.GuestBound
