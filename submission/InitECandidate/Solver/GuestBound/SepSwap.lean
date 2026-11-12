import InitECandidate.Solver.GuestBound.SepFrameOp2

/-!
# `stack_swap_positions` and the swap opcodes
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

set_option maxHeartbeats 2000000 in
/-- `stack_swap_positions(i, j)` with both positions on the stack: the stack
buffer is rewritten in place; nothing else changes. -/
theorem swap_positions_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "stack_swap_positions" E.functions = some (parameters, body))
    (s : St σ) (e sp cap b hiw i j : Word) {Rest R : Assn}
    (hi : s.locals "i" = some (.word i)) (hj : s.locals "j" = some (.word j))
    (h : ((Assn.Range b hiw ⋆ .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word sp ⋆
      .mem (e + 232#64) ↦ .word cap ⋆ .mem (e + 8#64) ↦ .word b ⋆ Rest) ⋆ R).holds s)
    (hil : i.toNat < sp.toNat) (hjl : j.toNat < sp.toNat) (hsp : sp.toNat ≤ cap.toNat)
    (hcap : cap.toNat ≤ 1024) (hhi : hiw.toNat = b.toNat + 32 * cap.toNat)
    (hb : b.toNat + 32 * cap.toNat ≤ 2 ^ 62) :
    WPr E s body (fun r => ∃ l g m, r = .returned l g m s.ffi [.word 0#64] ∧
      ((Assn.Range b hiw ⋆ .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word sp ⋆
        .mem (e + 232#64) ↦ .word cap ⋆ .mem (e + 8#64) ↦ .word b ⋆ Rest) ⋆ R).holds r.st) := by
  have hbody := (fun_of_index 516 hE.functions (by guest_decl_at 516) (by decide +kernel)
    hlookup).1
  subst hbody
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at h (by look)
  refine WPr.dec_ev (fun v hv => ?_)
  have e1 := eval_load_at hE (addr := e + 16#64) (of_eval (by ev [eval_global, hev])) h (by look)
    v hv
  subst e1
  refine WPr.dec_ev (fun v hv => ?_)
  have h2 := Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "sp" (.word sp), s.globals,
    s.memory, s.ffi⟩ : St σ)) rfl rfl h
  have e2 := eval_load_at hE (addr := e + 8#64) (of_eval (by ev [eval_global, hev])) h2 (by look)
    v hv
  subst e2
  refine WPr.dec_ev (fun v hv => ?_)
  have e3 : v = .word (b + (sp - 1#64 - i) * 32#64) := of_eval (by ev [hi]) v hv
  subst e3
  refine WPr.dec_ev (fun v hv => ?_)
  have e4 : v = .word (b + (sp - 1#64 - j) * 32#64) := of_eval (by ev [hj]) v hv
  subst e4
  refine WPr.dec_ev (fun va hva => ?_)
  obtain ⟨a0, a1, a2, a3, rfl⟩ := arg4_load hE _ va hva
  refine WPr.dec_ev (fun vb hvb => ?_)
  obtain ⟨b0, b1, b2, b3, rfl⟩ := arg4_load hE _ vb hvb
  have pa0 : (b + (sp - 1#64 - i) * 32#64).toNat = b.toNat + 32 * (sp.toNat - 1 - i.toNat) := by
    bv_omega
  have pa1 : (b + (sp - 1#64 - i) * 32#64 + 8#64).toNat =
      b.toNat + 32 * (sp.toNat - 1 - i.toNat) + 8 := by bv_omega
  have pa2 : (b + (sp - 1#64 - i) * 32#64 + 8#64 + 8#64).toNat =
      b.toNat + 32 * (sp.toNat - 1 - i.toNat) + 16 := by bv_omega
  have pa3 : (b + (sp - 1#64 - i) * 32#64 + 8#64 + 8#64 + 8#64).toNat =
      b.toNat + 32 * (sp.toNat - 1 - i.toNat) + 24 := by bv_omega
  have pb0 : (b + (sp - 1#64 - j) * 32#64).toNat = b.toNat + 32 * (sp.toNat - 1 - j.toNat) := by
    bv_omega
  have pb1 : (b + (sp - 1#64 - j) * 32#64 + 8#64).toNat =
      b.toNat + 32 * (sp.toNat - 1 - j.toNat) + 8 := by bv_omega
  have pb2 : (b + (sp - 1#64 - j) * 32#64 + 8#64 + 8#64).toNat =
      b.toNat + 32 * (sp.toNat - 1 - j.toNat) + 16 := by bv_omega
  have pb3 : (b + (sp - 1#64 - j) * 32#64 + 8#64 + 8#64 + 8#64).toNat =
      b.toNat + 32 * (sp.toNat - 1 - j.toNat) + 24 := by bv_omega
  refine WPr.seq_store4_at hE (Assn.holds_congr rfl rfl h) (addr := b + (sp - 1#64 - i) * 32#64)
    (w0 := b0) (w1 := b1) (w2 := b2) (w3 := b3)
    (of_eval (by lk [])) (fun y hy => by rw [evalF_local] at hy; simpa [update_lookup] using hy.symm)
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega))) (fun m1 h1 => ?_)
  refine WPr.seq_store4_at hE h1 (addr := b + (sp - 1#64 - j) * 32#64)
    (w0 := a0) (w1 := a1) (w2 := a2) (w3 := a3)
    (of_eval (by lk [])) (fun y hy => by rw [evalF_local] at hy; simpa [update_lookup] using hy.symm)
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega))) (fun m2 h2 => ?_)
  exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
    ⟨_, _, _, rfl, Assn.holds_congr rfl rfl h2⟩

/-- A comparison that evaluated to 0: both sides are words. -/
theorem cmp_zero_inv (hE : GuestEnv E) {op : Cmp} {a b : Exp Word}
    (h : E.eval s (.cmp op a b) = some (.word 0#64)) :
    ∃ x y, E.eval s a = some (.word x) ∧ E.eval s b = some (.word y) ∧
      evalPanCmp op x y = 0#64 := by
  rw [evalF_cmp hE.word] at h
  cases ha : E.eval s a with
  | none => rw [ha] at h; cases h
  | some va =>
    cases hb : E.eval s b with
    | none => rw [ha, hb] at h; cases va <;> cases h
    | some vb =>
      rw [ha, hb] at h
      cases va with
      | word x =>
        cases vb with
        | word y =>
          simp only [Option.some.injEq, PanValue.word.injEq] at h
          exact ⟨x, y, rfl, rfl, h⟩
        | _ => cases h
      | _ => cases h

/-- `if c { P }; rest` where `P` never ends normally: the rest runs knowing `c` was false. -/
theorem WPr.seq_ite_raise {c : Exp Word} {P q : Prog Word}
    (hthen : WPr E s P (fun r1 => match r1 with
      | .normal _ _ _ _ => False
      | r1 => Q r1))
    (hrest : E.eval s c = some (.word 0#64) → WPr E s q Q) :
    WPr E s (.seq (.ite c P .skip) q) Q := by
  refine WPr.seq (fun s' => s' = s ∧ E.eval s c = some (.word 0#64))
    (WPr.ite_both (fun w hw => ?_)) (by rintro _ ⟨rfl, h0⟩; exact hrest h0)
  split
  · rename_i h0
    rw [h0] at hw
    exact WPr.skip ⟨rfl, hw⟩
  · refine WPr.conseq hthen (fun r hr => ?_)
    cases r with
    | normal l g m f => exact hr.elim
    | _ => exact hr

/-- The stack pointer cell, read under the frame invariant. -/
theorem eval_sp (hE : GuestEnv E) {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {X : OpSt} (h : (FrameOp M K e fv X ⋆ R).holds s) :
    ∀ y, E.eval s (.load .one (.op .add [.var .global "ev", .const 16#64])) = some y →
      y = .word X.sp := by
  have hf : (StackW e X.sp X.cap X.base X.pv fv ⋆ OpNoStack e X.gl X.used X.pc ⋆
      JunkW M K X.pv X.base X.cap ⋆ R).holds s :=
    Assn.holds_perm h (by unfold FrameOp OpW OpNoStack; ac_rfl)
  unfold StackW at hf
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hf (by look)
  exact eval_load_at hE (addr := e + 16#64) (of_eval (by ev [eval_global, hev])) hf (by look)

set_option maxHeartbeats 1000000 in
/-- `stack_swap_positions(i, j); rest` with both positions on the stack. -/
theorem op_swap_pos (hE : GuestEnv E) {args : List (Exp Word)} {q : Prog Word} {i j : Word}
    {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt}
    (hargs : E.evalArgs s args = some [.word i, .word j])
    (hi : i.toNat < X.sp.toNat) (hj : j.toNat < X.sp.toNat) (hok : FrameOk M K fv X)
    (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hq : ∀ g m, (FrameOp M K e fv X ⋆ R).holds (⟨s.locals, g, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, g, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "stack_swap_positions" args) q) Q := by
  have hf : (StackW e X.sp X.cap X.base X.pv fv ⋆ OpNoStack e X.gl X.used X.pc ⋆
      JunkW M K X.pv X.base X.cap ⋆ R).holds s :=
    Assn.holds_perm h (by unfold FrameOp OpW OpNoStack; ac_rfl)
  have hcap := hok.ok.cap_le
  have hbh := hok.ok.base_hi
  have hhi : (X.base + 32#64 * X.cap).toNat = X.base.toNat + 32 * X.cap.toNat := by bv_omega
  refine WPr.seq (fun s' => ∃ g m, s' = ⟨s.locals, g, m, s.ffi⟩ ∧
      (FrameOp M K e fv X ⋆ R).holds s')
    (WPr.call_spec (fun r => ∃ l g m, r = .returned l g m s.ffi [.word 0#64] ∧
      (StackW e X.sp X.cap X.base X.pv fv ⋆ OpNoStack e X.gl X.used X.pc ⋆
        JunkW M K X.pv X.base X.cap ⋆ R).holds r.st) ?_ ?_ ?_ ?_) ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 516 hE.functions (by guest_decl_at 516) (by decide +kernel)
      hlk).2
    rw [hargs] at hvalues
    cases hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    have hf' : (StackW e X.sp X.cap X.base X.pv fv ⋆ OpNoStack e X.gl X.used X.pc ⋆
        JunkW M K X.pv X.base X.cap ⋆ R).holds (⟨cl, s.globals, s.memory, s.ffi⟩ : St σ) :=
      Assn.holds_congr rfl rfl hf
    unfold StackW at hf' ⊢
    exact swap_positions_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e X.sp
      X.cap X.base (X.base + 32#64 * X.cap) i j
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hf' hi hj hok.ok.sp_le hcap hhi hbh
  · rintro l g m ffi vs ⟨l', g', m', hC, hh⟩
    injection hC with _ hg hm hf2 _
    subst hg hm hf2
    exact ⟨g, m, rfl, Assn.holds_perm (Assn.holds_congr rfl rfl hh)
      (by unfold FrameOp OpW OpNoStack; ac_rfl)⟩
  · rintro l g m ffi exc v ⟨_, _, _, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨_, _, _, hC, -⟩
    cases hC
  · rintro _ ⟨g, m, rfl, hh⟩
    exact hq g m hh

/-- `op_swap(item)`. -/
theorem op_swap_frame (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_swap" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt)
    (hok : FrameOk M K fv X0) (h : (FrameOp M K e fv X0 ⋆ R).holds s) :
    WPr E s body (HandlerQ M K e fv R s.ffi X0) := by
  have hbody := (fun_of_index 517 hE.functions (by guest_decl_at 517) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine op_charge hE 3#64 hok hp h AcceptsH.refl.abort (fun g m hok hp h => ?_)
  refine WPr.seq_ite_raise ?_ (fun h0 => ?_)
  · exact op_raise hok hp h (AcceptsH.refl.mid (Rm := fun _ => False)).abort
  obtain ⟨it, y, hit, hy, hc⟩ := cmp_zero_inv hE h0
  have hy' := eval_sp hE h _ hy
  simp only [PanValue.word.injEq] at hy'
  subst hy'
  rw [evalF_local] at hit
  dsimp only at hit
  have hlt : it.toNat < (X0.sp).toNat := by
    by_contra hn
    have : ¬ it < X0.sp := fun hlt => hn (BitVec.lt_def.mp hlt)
    simp [evalPanCmp, this] at hc
  refine op_swap_pos hE (i := 0#64) (j := it)
    (X := { X0 with gl := X0.gl - 3#64, used := X0.used + 3#64 })
    (by simp [evalArgs_cons, evalArgs_nil, eval_const, evalF_local, hit]) (by simp; omega) hlt
    hok h (fun g m h => ?_)
  refine op_pc_add hE (d := 1#64)
    (by simp [evalArgs_cons, evalArgs_nil, eval_const]) hok hp h
    AcceptsH.refl.abort (fun g m hok hp h => ?_)
  exact op_return hok hp (by decide) h AcceptsH.refl

/-- The low byte, in the form the evaluator produces for `v & 255`. -/
theorem and_255 (v : BitVec 64) :
    (AndOp.and v (AndOp.and 255#64 (~~~(0 : BitVec 64)))).toNat = v.toNat % 256 := by
  have hmask : AndOp.and 255#64 (~~~(0 : BitVec 64)) = 255#64 := by decide
  rw [hmask]
  show (v &&& 255#64).toNat = v.toNat % 256
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod v.toNat 8

/-- `decode_single(x)`: a byte, or `EvmErr 10`; nothing changes. -/
theorem decode_single_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "decode_single" E.functions = some (parameters, body))
    (c : St σ) (x : Word) (hx : c.locals "x" = some (.word x)) :
    WPr E c body (fun r =>
      (∃ l w, r = .returned l c.globals c.memory c.ffi [.word w] ∧ w.toNat < 256) ∨
        ∃ l, r = .raised l c.globals c.memory c.ffi "EvmErr" (.word 10#64)) := by
  have hbody := (fun_of_index 519 hE.functions (by guest_decl_at 519) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.seq (fun s' => s' = c) (WPr.ite_both (fun w hw => ?_)) ?_
  · split
    · exact WPr.skip rfl
    · refine WPr.ret (w := AndOp.and (x + 145#64) (AndOp.and 255#64 (~~~(0 : BitVec 64))))
        (of_eval (by ev [hx])) ?_
      exact Or.inl ⟨_, _, rfl, by rw [and_255]; omega⟩
  rintro _ rfl
  refine WPr.seq (fun _ => False) (WPr.raise (fun v hv => ?_)) (fun _ h => h.elim)
  rw [eval_const] at hv
  cases hv
  exact Or.inr ⟨_, rfl⟩

/-- `var x = decode_single(a); rest` under the frame invariant. -/
theorem op_decode_single (hE : GuestEnv E) {x : VarName} {a : Exp Word} {body : Prog Word}
    {w : Word} {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt} {n : Nat}
    (ha : E.evalArgs s [a] = some [.word w]) (hok : FrameOk M K fv X) (hp : Adv X X0 n)
    (h : (FrameOp M K e fv X ⋆ R).holds s) (hab : AcceptsAbort M K e fv R s.ffi X0 Q)
    (hk : ∀ v : Word, v.toNat < 256 → (FrameOp M K e fv X ⋆ R).holds
        (⟨updatePanValueMap s.locals x (.word v), s.globals, s.memory, s.ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x (.word v), s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x .one "decode_single" [a] body) Q := by
  refine WPr.decCall_spec (fun r =>
      (∃ l w, r = .returned l s.globals s.memory s.ffi [.word w] ∧ w.toNat < 256) ∨
        ∃ l, r = .raised l s.globals s.memory s.ffi "EvmErr" (.word 10#64)) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 519 hE.functions (by guest_decl_at 519) (by decide +kernel)
      hlk).2
    rw [ha] at hvalues
    cases hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact decode_single_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ w
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  · rintro l g m ffi v (⟨l', w', hC, hw⟩ | ⟨_, hC⟩)
    · injection hC with _ hg hm hf hv
      subst hg hm hf
      cases hv
      exact hk w' hw (Assn.holds_congr rfl rfl h)
    · cases hC
  · rintro l g m ffi exc v (⟨_, _, hC, _⟩ | ⟨l', hC⟩)
    · cases hC
    · injection hC with _ hg hm hf hx hv
      subst hg hm hf hx hv
      exact hab _ (Or.inr ⟨X, n, hok, hp, Assn.holds_congr rfl rfl h, _, _, _, _, rfl⟩)
  · rintro l g m ffi ev (⟨_, _, hC, _⟩ | ⟨_, hC⟩) <;> cases hC

set_option maxHeartbeats 1000000 in
/-- `op_swapn`. -/
theorem op_swapn_frame (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_swapn" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt)
    (hok : FrameOk M K fv X0) (h : (FrameOp M K e fv X0 ⋆ R).holds s) :
    WPr E s body (HandlerQ M K e fv R s.ffi X0) := by
  have hbody := (fun_of_index 521 hE.functions (by guest_decl_at 521) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine op_charge hE 3#64 hok hp h AcceptsH.refl.abort (fun g m hok hp h => ?_)
  refine op_quiet (keepFn_sound (quietKeeper E) hE.functions 6 "code_imm"
      (show keepFn quietLeaf Guest.Software.guestAst 6 "code_imm" = true by decide +kernel))
    (raiseFn_sound _ hE.functions 6 "code_imm"
      (show raiseFn (fun _ => false) Guest.Software.guestAst 6 "code_imm" = true by
        decide +kernel))
    h AcceptsH.refl.abort (fun vimm hsh_imm h => ?_)
  obtain ⟨imm, rfl⟩ := word_of_shape_one hsh_imm
  refine op_decode_single hE (w := imm)
    (by simp [evalArgs_cons, evalArgs_nil, evalF_local, update_lookup]) hok hp h
    AcceptsH.refl.restore.abort (fun nv hnv h => ?_)
  refine WPr.seq_ite_raise ?_ (fun h0 => ?_)
  · exact op_raise hok hp h (AcceptsH.refl.restore.restore.mid (Rm := fun _ => False)).abort
  obtain ⟨y, n1, hy, hn1, hc⟩ := cmp_zero_inv hE h0
  have hy' := eval_sp hE h _ hy
  simp only [PanValue.word.injEq] at hy'
  subst hy'
  have hn1' : n1 = nv + 1#64 := by
    have := of_eval (w := nv + 1#64) (by ev []) _ hn1
    simpa using this
  subst hn1'
  have hlt : nv.toNat < (X0.sp).toNat := by
    have hge : ¬ X0.sp < nv + 1#64 := lower_zero hc
    have h1 : (nv + 1#64).toNat = nv.toNat + 1 := by bv_omega
    have : ¬ (X0.sp).toNat < (nv + 1#64).toNat := fun hl => hge (BitVec.lt_def.mpr hl)
    omega
  refine op_swap_pos hE (i := 0#64) (j := nv)
    (X := { X0 with gl := X0.gl - 3#64, used := X0.used + 3#64 })
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_const,
      evalF_local, update_lookup]) (by simp; omega) hlt hok h (fun g m h => ?_)
  refine op_pc_add hE (d := 2#64)
    (by simp [evalArgs_cons, evalArgs_nil, eval_const]) hok hp h
    AcceptsH.refl.restore.restore.abort (fun g m hok hp h => ?_)
  exact op_return hok hp (by decide) h AcceptsH.refl.restore.restore

/-- `code_imm()`: a byte; nothing changes. -/
theorem code_imm_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "code_imm" E.functions = some (parameters, body))
    (c : St σ) :
    WPr E c body (fun r => ∃ l w, r = .returned l c.globals c.memory c.ffi [.word w] ∧
      w.toNat < 256) := by
  have hbody := (fun_of_index 518 hE.functions (by guest_decl_at 518) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.dec_ev (fun v hv => ?_)
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap c.locals "pc" v, c.globals, c.memory,
    c.ffi⟩) (WPr.ite_both (fun w hw => ?_)) ?_
  · split
    · exact WPr.skip rfl
    · refine WPr.ret_any (fun y hy => ?_)
      obtain ⟨addr, cell, -, -, hyv⟩ := eval_loadByte hE.mem hy
      rw [hE.bytes] at hyv
      have hlt := gb_lt addr cell
      change (RiscV.panRiscVGetByte 8#64 addr cell).toNat < 256 at hlt
      generalize RiscV.panRiscVGetByte 8#64 addr cell = bv at hyv hlt
      subst hyv
      simp only [restorePanValueFfiLocal]
      exact ⟨_, bv, rfl, hlt⟩
  · rintro _ rfl
    refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, _, rfl, by decide⟩

/-- `var x = code_imm(); rest` under the frame invariant. -/
theorem op_code_imm (hE : GuestEnv E) {x : VarName} {body : Prog Word}
    {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt}
    (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hk : ∀ v : Word, v.toNat < 256 → (FrameOp M K e fv X ⋆ R).holds
        (⟨updatePanValueMap s.locals x (.word v), s.globals, s.memory, s.ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x (.word v), s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x .one "code_imm" [] body) Q := by
  refine WPr.decCall_spec (fun r => ∃ l w, r = .returned l s.globals s.memory s.ffi [.word w] ∧
      w.toNat < 256) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk _ _
    exact code_imm_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩
  · rintro l g m ffi v ⟨l', w', hC, hw⟩
    injection hC with _ hg hm hf hv
    subst hg hm hf
    cases hv
    exact hk w' hw (Assn.holds_congr rfl rfl h)
  · rintro l g m ffi exc v ⟨_, _, hC, _⟩
    cases hC
  · rintro l g m ffi ev ⟨_, _, hC, _⟩
    cases hC

/-- `max(a, b)` returns the larger word and changes nothing. -/
theorem max_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "max" E.functions = some (parameters, body))
    (c : St σ) (a b : Word) (ha : c.locals "a" = some (.word a))
    (hb : c.locals "b" = some (.word b)) :
    WPr E c body (fun r => ∃ l, r = .returned l c.globals c.memory c.ffi
      [.word (if b < a then a else b)]) := by
  have hbody := (fun_of_index 32 hE.functions (by guest_decl_at 32) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.seq (fun s' => s' = c ∧ ¬ b < a) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := b) (by lk [hb]))
      (of_eval (w := a) (by lk [ha])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      exact WPr.skip ⟨rfl, lower_zero hcv.symm⟩
    · rename_i h0
      have hlt : b < a := by
        by_contra hlt
        exact h0 (by rw [hcv]; simp [evalPanCmp, hlt])
      refine WPr.ret (w := a) (of_eval (by lk [ha])) ?_
      exact ⟨_, by rw [if_pos hlt]⟩
  rintro _ ⟨rfl, hge⟩
  refine WPr.ret (w := b) (of_eval (by lk [hb])) ?_
  exact ⟨_, by rw [if_neg hge]⟩

theorem and_15 (v : BitVec 64) :
    (AndOp.and v (AndOp.and 15#64 18446744073709551615#64)).toNat = v.toNat % 16 := by
  have hmask : AndOp.and 15#64 18446744073709551615#64 = 15#64 := by decide
  rw [hmask]
  show (v &&& 15#64).toNat = v.toNat % 16
  rw [BitVec.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod v.toNat 4

set_option maxHeartbeats 2000000 in
/-- `op_exchange`. -/
theorem op_exchange_frame (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_exchange" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt)
    (hok : FrameOk M K fv X0) (h : (FrameOp M K e fv X0 ⋆ R).holds s) :
    WPr E s body (HandlerQ M K e fv R s.ffi X0) := by
  have hbody := (fun_of_index 522 hE.functions (by guest_decl_at 522) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine op_charge hE 3#64 hok hp h AcceptsH.refl.abort (fun g m hok hp h => ?_)
  refine op_code_imm hE h (fun imm himm h => ?_)
  refine WPr.seq_ite_skip ?_ ?_
  · exact op_raise hok hp h AcceptsH.refl.restore.mid.abort
  refine op_dec_ev h (fun vk hk h => ?_)
  simp (config := { decide := true }) [evalF_op hE.word, evalArgs_cons, evalArgs_nil,
    evalF_local, update_lookup, wordsProj_cons, wordsProj_nil, wordOp, eval_const] at hk
  subst hk
  refine op_dec_ev h (fun vq hq h => ?_)
  simp (config := { decide := true }) [evalF_shift hE.word, evalF_local, update_lookup,
    eval_const, RiscV.panRiscVShift] at hq
  refine op_dec_ev h (fun vr hr h => ?_)
  simp (config := { decide := true }) [evalF_op hE.word, evalArgs_cons, evalArgs_nil,
    evalF_local, update_lookup, wordsProj_cons, wordsProj_nil, wordOp, eval_const] at hr
  have hk256 : (imm ^^^ 143#64).toNat < 256 := by
    rw [BitVec.toNat_xor]
    exact Nat.xor_lt_two_pow (n := 8) himm (by decide)
  obtain ⟨qv, hqv, hq16⟩ : ∃ qv : Word, vq = .word qv ∧ qv.toNat < 16 := by
    refine ⟨_, hq.symm, ?_⟩
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have e16 : (2 : Nat) ^ 4 = 16 := rfl
    rw [e16]
    omega
  obtain ⟨rv, hrv, hr16⟩ : ∃ rv : Word, vr = .word rv ∧ rv.toNat < 16 := by
    refine ⟨_, hr.symm, ?_⟩
    rw [and_15]
    omega
  subst hqv hrv
  clear hq hr
  refine op_dec_ev h (fun vn hn h => ?_)
  rw [eval_const] at hn
  cases hn
  refine op_dec_ev h (fun vm hm h => ?_)
  rw [eval_const] at hm
  cases hm
  refine WPr.seq (fun s' => ∃ nv mv : Word, s'.locals "n" = some (.word nv) ∧
      s'.locals "m" = some (.word mv) ∧ s'.globals = g ∧ s'.memory = m ∧ s'.ffi = s.ffi ∧
      nv.toNat ≤ 16 ∧ mv.toNat ≤ 29)
    (WPr.ite_both (fun w hw => ?_)) ?_
  · split
    · refine WPr.seq_assign_local (old := 0#64) (w := rv + 1#64)
        (by simp (config := { decide := true }) [update_lookup]) (of_eval (by ev [])) ?_
      refine WPr.assign_local (old := 0#64) (w := 29#64 - qv)
        (by simp (config := { decide := true }) [update_lookup]) (of_eval (by ev [])) ?_
      exact ⟨rv + 1#64, 29#64 - qv, by simp (config := { decide := true }) [update_lookup],
        by simp (config := { decide := true }) [update_lookup], rfl, rfl, rfl, by bv_omega,
        by bv_omega⟩
    · refine WPr.seq_assign_local (old := 0#64) (w := qv + 1#64)
        (by simp (config := { decide := true }) [update_lookup]) (of_eval (by ev [])) ?_
      refine WPr.assign_local (old := 0#64) (w := rv + 1#64)
        (by simp (config := { decide := true }) [update_lookup]) (of_eval (by ev [])) ?_
      exact ⟨qv + 1#64, rv + 1#64, by simp (config := { decide := true }) [update_lookup],
        by simp (config := { decide := true }) [update_lookup], rfl, rfl, rfl, by bv_omega,
        by bv_omega⟩
  rintro ⟨L, g', m', f'⟩ ⟨nv, mv, Ln, Lm, hg', hm', hf', hnv, hmv⟩
  dsimp only at Ln Lm hg' hm' hf'
  subst g' m' f'
  have h1 := Assn.holds_congr (s' := (⟨L, g, m, s.ffi⟩ : St σ)) rfl rfl h
  refine WPr.decCall_spec (fun r => ∃ l, r = .returned l g m s.ffi
      [.word (if mv < nv then nv else mv)]) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 32 hE.functions (by guest_decl_at 32) (by decide +kernel)
      hlk).2
    have hvals : values = [.word nv, .word mv] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local, Ln,
        Lm] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact max_runs hE parameters cbody hlk ⟨cl, g, m, s.ffi⟩ nv mv
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  rotate_left
  · rintro l g2 m2 ffi exc v ⟨_, hC⟩
    cases hC
  · rintro l g2 m2 ffi ev ⟨_, hC⟩
    cases hC
  rintro l g2 m2 ffi v ⟨l', hC⟩
  injection hC with _ hg2 hm2 hf2 hv
  subst g2 m2 ffi
  cases hv
  obtain ⟨mx, hmx⟩ : ∃ mx : Word, mx = (if mv < nv then nv else mv) := ⟨_, rfl⟩
  rw [← hmx]
  have hmxb : nv.toNat ≤ mx.toNat ∧ mv.toNat ≤ mx.toNat ∧ mx.toNat ≤ 29 := by
    rw [hmx]
    split
    · rename_i hlt
      have := BitVec.lt_def.mp hlt
      omega
    · rename_i hge
      have : ¬ mv.toNat < nv.toNat := fun hl => hge (BitVec.lt_def.mpr hl)
      omega
  have h2 := Assn.holds_congr (s' := (⟨updatePanValueMap L "mx" (.word mx), g, m, s.ffi⟩ :
    St σ)) rfl rfl h1
  refine WPr.seq_ite_raise ?_ (fun h0 => ?_)
  · exact op_raise hok hp h2 (AcceptsH.refl.restore.restore.restore.restore.restore.restore.restore.mid
      (Rm := fun _ => False)).abort
  obtain ⟨y, n1, hy, hn1, hc⟩ := cmp_zero_inv hE h0
  have hy' := eval_sp hE h2 _ hy
  simp only [PanValue.word.injEq] at hy'
  subst hy'
  have hn1' : n1 = mx + 1#64 := by
    have := of_eval (w := mx + 1#64) (by ev []) _ hn1
    simpa using this
  subst hn1'
  have hlt : mx.toNat < (X0.sp).toNat := by
    have hge : ¬ X0.sp < mx + 1#64 := lower_zero hc
    have h1' : (mx + 1#64).toNat = mx.toNat + 1 := by bv_omega
    have : ¬ (X0.sp).toNat < (mx + 1#64).toNat := fun hl => hge (BitVec.lt_def.mpr hl)
    omega
  refine op_swap_pos hE (i := nv) (j := mv)
    (X := { X0 with gl := X0.gl - 3#64, used := X0.used + 3#64 })
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, Ln, Lm]) (by simp; omega) (by simp; omega) hok h2 (fun g m h => ?_)
  refine op_pc_add hE (d := 2#64)
    (by simp [evalArgs_cons, evalArgs_nil, eval_const]) hok hp h
    AcceptsH.refl.restore.restore.restore.restore.restore.restore.restore.abort
    (fun g m hok hp h => ?_)
  exact op_return hok hp (by decide) h
    AcceptsH.refl.restore.restore.restore.restore.restore.restore.restore

/-- `op_clz`. -/
theorem op_clz_frame (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_clz" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt)
    (hok : FrameOk M K fv X0) (h : (FrameOp M K e fv X0 ⋆ R).holds s) :
    WPr E s body (HandlerQ M K e fv R s.ffi X0) := by
  have hbody := (fun_of_index 500 hE.functions (by guest_decl_at 500) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine op_pop_sh hE hok hp h AcceptsH.refl.abort (fun _ g m hsh_x hok hp h => ?_)
  refine op_charge hE 5#64 hok hp h AcceptsH.refl.restore.abort (fun g m hok hp h => ?_)
  refine op_quiet (keepFn_sound (quietKeeper E) hE.functions 6 "u256_bit_length"
      (show keepFn quietLeaf Guest.Software.guestAst 6 "u256_bit_length" = true by
        decide +kernel))
    (raiseFn_sound _ hE.functions 6 "u256_bit_length"
      (show raiseFn (fun _ => false) Guest.Software.guestAst 6 "u256_bit_length" = true by
        decide +kernel))
    h AcceptsH.refl.restore.abort (fun _ hsh_bl h => ?_)
  refine op_push hok hp h AcceptsH.refl.restore.restore.abort
    (stack_push_word_any_hc hE (fun v hv => eval_op_word hE hv) e _ _ _ _ fv hok.ok)
    (fun _ g m hok hp h => ?_)
  refine op_pc_add hE (d := 1#64)
    (by simp [evalArgs_cons, evalArgs_nil, eval_const]) hok hp h
    AcceptsH.refl.restore.restore.abort (fun g m hok hp h => ?_)
  exact op_return hok hp (by decide) h AcceptsH.refl.restore.restore

end InitECandidate.Solver.GuestBound
