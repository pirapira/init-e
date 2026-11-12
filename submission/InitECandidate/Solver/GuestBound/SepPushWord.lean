import InitECandidate.Solver.GuestBound.SepBinop

/-!
# Handlers that push one loaded word

`stack_push_word` wraps `stack_push`. `pushLoad_framed` covers every handler of
the shape `charge_gas(G); stack_push_word(lds 1 a); pc_add(1); return 0`,
whatever the address `a` is: the value pushed does not matter here.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The outcome of `stack_push` does not depend on the locals of the result. -/
theorem StackPushPost.ret_congr {ffi ffi' : FfiState σ} {e sp cap base pv fv : Word}
    {l l' g g' : VarName → Option (PanValue Word)} {m m' : Word → Option (PanValue Word)}
    {vs : List (PanValue Word)} {R : Assn} {st : St σ}
    (h : (StackPushPost ffi e sp cap base pv fv (.returned l g m ffi' vs) ⋆ R).holds st) :
    (StackPushPost ffi e sp cap base pv fv (.returned l' g' m' ffi' [.word 0#64]) ⋆ R).holds
      st := by
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨hlt, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    exact Assn.holds_or_right (Assn.holds_or_left
      (Assn.holds_pure_intro ⟨hlt, _, _, _, rfl⟩ hk))
  · obtain ⟨qv, h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨nc, h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨⟨hok, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    exact Assn.holds_or_right (Assn.holds_or_right (Assn.holdsV_ex.mpr ⟨qv,
      Assn.holdsV_ex.mpr ⟨nc, Assn.holds_pure_intro ⟨hok, _, _, _, rfl⟩ hk⟩⟩))

theorem StackPushPost.raise_congr {ffi ffi' : FfiState σ} {e sp cap base pv fv : Word}
    {l l' g g' : VarName → Option (PanValue Word)} {m m' : Word → Option (PanValue Word)}
    {exc : ExceptionId} {v : PanValue Word} {R : Assn} {st : St σ}
    (h : (StackPushPost ffi e sp cap base pv fv (.raised l g m ffi' exc v) ⋆ R).holds st) :
    (StackPushPost ffi e sp cap base pv fv (.raised l' g' m' ffi' exc v) ⋆ R).holds st := by
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨hsc, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf hx hv
    subst hf hx hv
    exact Assn.holds_or_left (Assn.holds_pure_intro ⟨hsc, _, _, _, rfl⟩ hk)
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  · obtain ⟨qv, h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨nc, h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC

/-- `stack_push_word(w)` behaves as `stack_push`. -/
theorem stack_push_word_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "stack_push_word" E.functions = some (parameters, body))
    (s : St σ) (e sp cap base pv fv w : Word) (hw : s.locals "w" = some (.word w))
    (ok : StackOk sp cap base pv fv) :
    WPFt E s body (StackW e sp cap base pv fv) (StackPushPost s.ffi e sp cap base pv fv) := by
  have hbody := (fun_of_index 455 hE.functions (by guest_decl_at 455) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  dsimp only
  refine WPr.seq_call_framedT hR (stack_push_hc hE (w0 := w) (w1 := 0#64) (w2 := 0#64)
    (w3 := 0#64) (by simp [evalArgs_cons, evalArgs_nil, evalF_rStruct, evalF_local, eval_const,
      hw]) e sp cap base pv fv ok) (by trap_tac) ?_ ?_
  · intro l g m ffi vs h
    exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
      (Or.inr (StackPushPost.ret_congr (Assn.holds_congr rfl rfl h)))
  · intro l g m ffi exc v _ h
    exact Or.inr (StackPushPost.raise_congr (Assn.holds_congr rfl rfl h))

/-- The value of a one-element argument list. -/
theorem evalArgs1_inv {a : Exp Word} {values : List (PanValue Word)}
    (h : E.evalArgs s [a] = some values) : ∃ v, E.eval s a = some v ∧ values = [v] := by
  simp only [evalArgs_cons, evalArgs_nil] at h
  cases h1 : E.eval s a with
  | none => rw [h1] at h; simp at h
  | some v =>
    rw [h1] at h
    simp at h
    exact ⟨v, rfl, h.symm⟩

/-- `stack_push_word(lds 1 a)` at a call site. -/
theorem stack_push_word_hc (hE : GuestEnv E) (a : Exp Word) (e sp cap base pv fv : Word)
    (ok : StackOk sp cap base pv fv) :
    ∀ parameters cbody values cl,
      lookupPanFunction "stack_push_word" E.functions = some (parameters, cbody) →
      E.evalArgs s [.load .one a] = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (StackW e sp cap base pv fv)
        (StackPushPost s.ffi e sp cap base pv fv) := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 455 hE.functions (by guest_decl_at 455) (by decide +kernel)
    hlk).2
  obtain ⟨v, hv, rfl⟩ := evalArgs1_inv hvalues
  obtain ⟨addr, w, -, rfl, -⟩ := eval_load_one hE.mem hv
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact stack_push_word_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e sp cap
    base pv fv w (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) ok

/-- The body shared by the handlers that push one loaded word. -/
def pushLoadBody (G : Word) (a : Exp Word) : Prog Word :=
  .seq (.call (some (none, none)) "charge_gas" [.const G])
    (.seq (.call (some (none, none)) "stack_push_word" [.load .one a])
      (.seq (.call (some (none, none)) "pc_add" [.const 1#64]) (.return (.const 0#64))))

/-- What such a handler leaves: out of gas; stack overflow after the charge;
pushed in place; or pushed after the stack moved to `qv` with `nc` slots. -/
def PushPost (ffi : FfiState σ) (e sp cap base pv fv gl used pc G : Word) (r : Result σ) :
    Assn :=
  Assn.or
    (⌜gl < G ∧ ∃ l g m, r = .raised l g m ffi "EvmErr" (.word 4#64)⌝ ⋆
      OpW e sp cap base pv fv gl used pc)
    (Assn.or
      (⌜(¬ gl < G ∧ sp.toNat = cap.toNat) ∧
          ∃ l g m, r = .raised l g m ffi "EvmErr" (.word 3#64)⌝ ⋆
        OpW e sp cap base pv fv (gl - G) (used + G) pc)
      (Assn.or
        (⌜(¬ gl < G ∧ sp.toNat < cap.toNat) ∧ ∃ l g m, r = .returned l g m ffi [.word 0#64]⌝ ⋆
          OpW e (sp + 1#64) cap base pv fv (gl - G) (used + G) (pc + 1#64))
        (Assn.ex fun qv : Word => Assn.ex fun nc : Word =>
          ⌜(¬ gl < G ∧ StackOk (sp + 1#64) nc qv qv fv ∧
              qv.toNat + 32 * nc.toNat ≤ pv.toNat ∧ sp.toNat = cap.toNat) ∧
            ∃ l g m, r = .returned l g m ffi [.word 0#64]⌝ ⋆
          (OpW e (sp + 1#64) nc qv qv fv (gl - G) (used + G) (pc + 1#64) ⋆
            Assn.Range (qv + 32#64 * nc) pv ⋆ Assn.Range base (base + 32#64 * cap)))))

set_option maxHeartbeats 1000000 in
theorem pushLoad_framed (hE : GuestEnv E) (G : Word) (a : Exp Word)
    (s : St σ) (e sp cap base pv fv gl used pc : Word) (ok : StackOk sp cap base pv fv) :
    WPFt E s (pushLoadBody G a) (OpW e sp cap base pv fv gl used pc)
      (PushPost s.ffi e sp cap base pv fv gl used pc G) := by
  intro R hR
  unfold pushLoadBody
  refine WPr.seq_call_framedT (Assn.holds_focus (OpW_gas ..) hR)
    (fun p b v cl a1 a2 a3 => (charge_gas_hc hE (a := G)
      (by simp [evalArgs_cons, evalArgs_nil, eval_const]) e gl used p b v cl a1 a2 a3).toT)
    (by trap_tac) ?_ ?_
  rotate_left
  · intro l g m ffi exc v _ h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨hlt, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      exact Or.inr (Assn.holds_or_left (Assn.holds_pure_intro ⟨hlt, _, _, _, rfl⟩
        (Assn.holds_unfocus (OpW_gas ..) (Assn.holds_congr rfl rfl hk))))
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
  intro l g m ffi vs h
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  obtain ⟨⟨hge, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
  injection hC with _ _ _ hf _
  subst hf
  have hO1 := Assn.holds_unfocus (OpW_gas e sp cap base pv fv (gl - G) (used + G) pc) hk
  refine WPr.seq_call_framedT (Assn.holds_focus (OpW_stack ..) hO1)
    (stack_push_word_hc hE a e sp cap base pv fv ok) (by trap_tac) ?_ ?_
  rotate_left
  · intro l2 g2 m2 ffi2 exc v _ h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨hsc, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      exact Or.inr (Assn.holds_or_right (Assn.holds_or_left
        (Assn.holds_pure_intro ⟨⟨hge, hsc⟩, _, _, _, rfl⟩
          (Assn.holds_unfocus (OpW_stack ..) (Assn.holds_congr rfl rfl hk)))))
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    · obtain ⟨qv, h⟩ := Assn.holdsV_ex.mp h
      obtain ⟨nc, h⟩ := Assn.holdsV_ex.mp h
      obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
  intro l2 g2 m2 ffi2 vs2 h
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  rcases Assn.holds_or_elim h with h | h
  · -- pushed in place
    obtain ⟨⟨hlt, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    have hO2 := Assn.holds_unfocus
      (OpW_stack e (sp + 1#64) cap base pv fv (gl - G) (used + G) pc) hk
    refine WPr.seq_call_framedT (Assn.holds_focus (OpW_pc ..) hO2)
      (fun p b v cl a1 a2 a3 => (pc_add_hc hE (n := 1#64)
        (by simp [evalArgs_cons, evalArgs_nil, eval_const]) e pc p b v cl a1 a2 a3).toT)
      (by trap_tac) ?_ ?_
    rotate_left
    · intro l3 g3 m3 ffi3 exc v _ h
      obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    intro l3 g3 m3 ffi3 vs3 h
    obtain ⟨⟨_, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
    exact Or.inr (Assn.holds_or_right (Assn.holds_or_right (Assn.holds_or_left
      (Assn.holds_pure_intro ⟨⟨hge, hlt⟩, _, _, _, rfl⟩
        (Assn.holds_unfocus (OpW_pc ..) (Assn.holds_congr rfl rfl hk))))))
  · -- pushed after the stack moved
    obtain ⟨qv, h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨nc, h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨⟨hok, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    have hO2 : (OpW e (sp + 1#64) nc qv qv fv (gl - G) (used + G) pc ⋆
        (Assn.Range (qv + 32#64 * nc) pv ⋆ Assn.Range base (base + 32#64 * cap)) ⋆ R).holds
        (⟨s.locals, g2, m2, s.ffi⟩ : St σ) :=
      Assn.holds_perm hk (by rw [OpW_stack]; ac_rfl)
    refine WPr.seq_call_framedT (Assn.holds_focus (OpW_pc ..) hO2)
      (fun p b v cl a1 a2 a3 => (pc_add_hc hE (n := 1#64)
        (by simp [evalArgs_cons, evalArgs_nil, eval_const]) e pc p b v cl a1 a2 a3).toT)
      (by trap_tac) ?_ ?_
    rotate_left
    · intro l3 g3 m3 ffi3 exc v _ h
      obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    intro l3 g3 m3 ffi3 vs3 h
    obtain ⟨⟨_, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
    have hO3 := Assn.holds_unfocus
      (OpW_pc e (sp + 1#64) nc qv qv fv (gl - G) (used + G) (pc + 1#64))
      (Assn.holds_congr (s' := (⟨fun _ => none, g3, m3, s.ffi⟩ : St σ)) rfl rfl hk)
    exact Or.inr (Assn.holds_or_right (Assn.holds_or_right (Assn.holds_or_right
      (Assn.holdsV_ex.mpr ⟨qv, Assn.holdsV_ex.mpr ⟨nc,
        Assn.holds_pure_intro ⟨⟨hge, hok.1, hok.2.1, hok.2.2⟩, _, _, _, rfl⟩
          (Assn.holds_assoc_l
            (P := OpW e (sp + 1#64) nc qv qv fv (gl - G) (used + G) (pc + 1#64)) hO3)⟩⟩))))

/-- `stack_push_bool(b)` behaves as `stack_push`, whatever `b` is. -/
theorem stack_push_bool_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "stack_push_bool" E.functions = some (parameters, body))
    (s : St σ) (e sp cap base pv fv : Word) (ok : StackOk sp cap base pv fv) :
    WPFt E s body (StackW e sp cap base pv fv) (StackPushPost s.ffi e sp cap base pv fv) := by
  have hbody := (fun_of_index 456 hE.functions (by guest_decl_at 456) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  dsimp only
  refine WPr.seq (fun s' => ∃ l g m ffi vs, s' = ⟨s.locals, g, m, ffi⟩ ∧
      (StackPushPost s.ffi e sp cap base pv fv (.returned l g m ffi vs) ⋆ R).holds s')
    (WPr.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPr.call_framedT hR (stack_push_hc hE (w0 := 0#64) (w1 := 0#64) (w2 := 0#64)
        (w3 := 0#64) (by simp [evalArgs_cons, evalArgs_nil, evalF_rStruct, eval_const])
        e sp cap base pv fv ok) (by trap_tac) (fun l g m ffi vs h => ⟨l, g, m, ffi, vs, rfl, h⟩)
        (fun l g m ffi exc v _ h =>
          Or.inr (StackPushPost.raise_congr (Assn.holds_congr rfl rfl h)))
    · exact WPr.call_framedT hR (stack_push_hc hE (w0 := 1#64) (w1 := 0#64) (w2 := 0#64)
        (w3 := 0#64) (by simp [evalArgs_cons, evalArgs_nil, evalF_rStruct, eval_const])
        e sp cap base pv fv ok) (by trap_tac) (fun l g m ffi vs h => ⟨l, g, m, ffi, vs, rfl, h⟩)
        (fun l g m ffi exc v _ h =>
          Or.inr (StackPushPost.raise_congr (Assn.holds_congr rfl rfl h)))
  · rintro _ ⟨l, g, m, ffi, vs, rfl, h⟩
    exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
      (Or.inr (StackPushPost.ret_congr (Assn.holds_congr rfl rfl h)))

/-- `stack_push_bool` pushes a one-word result. -/
theorem pushesR_stack_push_bool (hE : GuestEnv E) : PushesR E .one "stack_push_bool" := by
  intro st v _ _ e sp cap base pv fv ok parameters cbody values cl hlk _ _
  exact stack_push_bool_framed hE parameters cbody hlk ⟨cl, st.globals, st.memory, st.ffi⟩ e sp
    cap base pv fv ok

/-- A comparison handler: the one-word result is pushed with `stack_push_bool`. -/
theorem cmpop_framed (hE : GuestEnv E) {f : FunName} (G : Word)
    (hq : FunKeeps (quietKeeper E) f) (hr : FunRaises E (fun _ => false) f)
    (s : St σ) (e sp cap base pv fv gl used pc : Word) (ok : StackOk sp cap base pv fv) :
    WPFt E s (binopBodyG .one f "stack_push_bool" G) (OpW e sp cap base pv fv gl used pc)
      (BinopPost s.ffi e sp cap base pv fv gl used pc G) :=
  binopG_framed hE G hq hr (pushesR_stack_push_bool hE) s e sp cap base pv fv gl used pc ok

end InitECandidate.Solver.GuestBound
