import InitECandidate.Solver.GuestBound.SepFrameOp

/-!
# More step rules under the frame invariant

Guards that raise `EvmErr`, conditionals whose taken branch ends the handler,
pops that remember the shape of the popped value, pushes of computed values,
and a store to the program counter.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `WPr.decCall_framedT`, with the shape check on the bound value. -/
theorem WPr.decCall_framedTS {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} {P F : Assn} {Qc : Result σ → Assn} (hpre : (P ⋆ F).holds s)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody P Qc)
    (htrap : ∀ r, Trap r → Q r)
    (hret : ∀ l g m ffi v, panShapeMatches (panValueShape E.structs v) sh = true →
      (Qc (.returned l g m ffi [v]) ⋆ F).holds
        (⟨updatePanValueMap s.locals x v, g, m, ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r')))
    (hraise : ∀ l g m ffi exc v, exc ≠ "TrapErr" → (Qc (.raised l g m ffi exc v) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.raised (fun _ => none) g m ffi exc v)) :
    WPr E s (.decCall x sh f args body) Q := by
  refine WPr.decCall_specS (fun rb => Trap rb ∨ (Qc rb ⋆ F).holds rb.st)
    (fun parameters cbody values cl hlk hvalues hbind =>
      hc parameters cbody values cl hlk hvalues hbind F (Assn.holds_congr rfl rfl hpre))
    ?_ ?_ ?_
  · rintro l g m ffi v (ht | hC) hsh
    · exact ht.elim
    · exact hret l g m ffi v hsh (Assn.holds_congr rfl rfl hC)
  · rintro l g m ffi exc v (ht | hC)
    · exact htrap _ ht
    · by_cases he : exc = "TrapErr"
      · exact htrap _ he
      · exact hraise l g m ffi exc v he (Assn.holds_congr rfl rfl hC)
  · intro l g m ffi ev _
    exact htrap _ trivial

/-- `var x = stack_pop(); rest`, remembering the shape of the popped value. -/
theorem op_pop_sh (hE : GuestEnv E) {x : VarName} {sh : Shape} {body : Prog Word} {M : Word}
    {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt} {n : Nat}
    (hok : FrameOk M K fv X) (hp : Adv X X0 n) (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hab : AcceptsAbort M K e fv R s.ffi X0 Q)
    (hq : ∀ v g m, panShapeMatches (panValueShape E.structs v) sh = true →
      FrameOk M K fv { X with sp := X.sp - 1#64 } →
      Adv { X with sp := X.sp - 1#64 } X0 n →
      (FrameOp M K e fv { X with sp := X.sp - 1#64 } ⋆ R).holds
        (⟨updatePanValueMap s.locals x v, g, m, s.ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x v, g, m, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x sh "stack_pop" [] body) Q := by
  refine WPr.decCall_framedTS (Assn.holds_focus (OpW_sp ..) (Assn.holds_assoc_r h))
    (fun p b v cl a1 a2 a3 => (stack_pop_hc hE e X.sp p b v cl a1 a2 a3).toT)
    (fun r ht => hab r (Or.inl ht)) ?_ ?_
  · intro l g m ffi v hsh hh
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC
    obtain ⟨⟨hne, _, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
    injection hC with _ _ _ hf _
    subst hf
    have hsp : (X.sp - 1#64).toNat ≤ X.cap.toNat := by
      have := hok.ok.sp_le
      have : X.sp.toNat ≠ 0 := fun h0 => hne (by bv_omega)
      have : (X.sp - 1#64).toNat = X.sp.toNat - 1 := by bv_omega
      omega
    exact hq v g m hsh ⟨⟨hok.ok.cap_pos, hok.ok.cap_le, hsp, hok.ok.base_al, hok.ok.base_hi,
      hok.ok.fp, hok.ok.pv_hi⟩, hok.pb, hok.bM, hok.Kpv, hok.Kst⟩ hp
      (Assn.holds_assoc_l (P := OpW e (X.sp - 1#64) X.cap X.base X.pv fv X.gl X.used X.pc)
        (Assn.holds_unfocus (OpW_sp ..) hk))
  · intro l g m ffi exc v _ hh
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      exact hab _ (Or.inr ⟨X, n, hok, hp, Assn.holds_assoc_l
        (Assn.holds_unfocus (OpW_sp ..) (Assn.holds_congr rfl rfl hk)), _, _, _, _, rfl⟩)
    · obtain ⟨⟨-, _, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC

/-- `raise EvmErr k` under the frame invariant is an abort. -/
theorem op_raise {k : Word} {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {X0 X : OpSt} {n : Nat} (hok : FrameOk M K fv X) (hp : Adv X X0 n)
    (h : (FrameOp M K e fv X ⋆ R).holds s) (hab : AcceptsAbort M K e fv R s.ffi X0 Q) :
    WPr E s (.raise "EvmErr" (.const k)) Q := by
  refine WPr.raise (fun v hv => ?_)
  rw [eval_const] at hv
  cases hv
  exact hab _ (Or.inr ⟨X, n, hok, hp, Assn.holds_congr rfl rfl h, _, _, _, _, rfl⟩)

/-- A handler outcome is never `.normal`, so it passes through a sequence. -/
theorem AcceptsH.mid {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {ffi : FfiState σ} {X0 : OpSt} {Rm : St σ → Prop} (h : AcceptsH M K e fv R ffi X0 Q) :
    AcceptsH M K e fv R ffi X0 (fun r => match r with
      | .normal l g m f => Rm ⟨l, g, m, f⟩
      | r => Q r) := by
  intro r hr
  cases r with
  | normal l g m f =>
    rcases hr with (ht | ⟨_, _, _, _, _, _, _, _, _, hC⟩) | ⟨_, _, _, _, _, _, _, _, _, hC⟩
    · exact ht.elim
    · cases hC
    · cases hC
  | _ => exact h _ hr

/-- Any value of an operator expression is a word. -/
theorem eval_op_word (hE : GuestEnv E) {o : BinOp} {es : List (Exp Word)} {y : PanValue Word}
    (h : E.eval s (.op o es) = some y) : ∃ w, y = .word w := by
  rw [evalF_op hE.word] at h
  split at h
  · split at h
    · simp only [Option.map_eq_some_iff] at h
      obtain ⟨w, -, rfl⟩ := h
      exact ⟨w, rfl⟩
    · cases h
  · cases h

/-- A struct of four operator expressions has a four-word value. -/
theorem arg4_ops (hE : GuestEnv E) (o0 o1 o2 o3 : BinOp) (l0 l1 l2 l3 : List (Exp Word)) :
    ∀ v, E.eval s (.rStruct [.op o0 l0, .op o1 l1, .op o2 l2, .op o3 l3]) = some v →
      ∃ w0 w1 w2 w3 : Word, v = .rStruct [.word w0, .word w1, .word w2, .word w3] := by
  intro v hv
  rw [evalF_rStruct] at hv
  simp only [evalArgs_cons, evalArgs_nil] at hv
  cases h0 : E.eval s (.op o0 l0) with
  | none => rw [h0] at hv; simp at hv
  | some v0 =>
    cases h1 : E.eval s (.op o1 l1) with
    | none => rw [h0, h1] at hv; simp at hv
    | some v1 =>
      cases h2 : E.eval s (.op o2 l2) with
      | none => rw [h0, h1, h2] at hv; simp at hv
      | some v2 =>
        cases h3 : E.eval s (.op o3 l3) with
        | none => rw [h0, h1, h2, h3] at hv; simp at hv
        | some v3 =>
          obtain ⟨w0, rfl⟩ := eval_op_word hE h0
          obtain ⟨w1, rfl⟩ := eval_op_word hE h1
          obtain ⟨w2, rfl⟩ := eval_op_word hE h2
          obtain ⟨w3, rfl⟩ := eval_op_word hE h3
          rw [h0, h1, h2, h3] at hv
          simp at hv
          exact ⟨w0, w1, w2, w3, hv.symm⟩

/-- `stack_push_word(a)` at a call site, when any value of `a` is a word. -/
theorem stack_push_word_any_hc (hE : GuestEnv E) {a : Exp Word}
    (harg : ∀ v, E.eval s a = some v → ∃ w : Word, v = .word w)
    (e sp cap base pv fv : Word) (ok : StackOk sp cap base pv fv) :
    ∀ parameters cbody values cl,
      lookupPanFunction "stack_push_word" E.functions = some (parameters, cbody) →
      E.evalArgs s [a] = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (StackW e sp cap base pv fv)
        (StackPushPost s.ffi e sp cap base pv fv) := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 455 hE.functions (by guest_decl_at 455) (by decide +kernel)
    hlk).2
  obtain ⟨v, hv, rfl⟩ := evalArgs1_inv hvalues
  obtain ⟨w, rfl⟩ := harg v hv
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact stack_push_word_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e sp cap
    base pv fv w (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) ok

/-- A local whose value has the one-word shape. -/
theorem arg1_shape {x : VarName} {v : PanValue Word} (hx : s.locals x = some v)
    (hsh : panShapeMatches (panValueShape E.structs v) .one = true) :
    ∀ v', E.eval s (.var .local x) = some v' → ∃ w : Word, v' = .word w := by
  obtain ⟨w, rfl⟩ := word_of_shape_one hsh
  intro v' hv'
  rw [evalF_local, hx] at hv'
  exact ⟨w, (Option.some.inj hv').symm⟩

/-- `f(args); rest` for a callee that changes nothing and raises at most `EvmErr`. -/
theorem op_call_raise {f : FunName} {args : List (Exp Word)} {q : Prog Word} {M : Word}
    {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt} {n : Nat}
    (hq : FunKeeps (quietKeeper E) f) (hr : FunRaises E (fun x => x == "EvmErr") f)
    (hok : FrameOk M K fv X) (hp : Adv X X0 n) (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hab : AcceptsAbort M K e fv R s.ffi X0 Q) (hk : WPr E s q Q) :
    WPr E s (.seq (.call (some (none, none)) f args) q) Q := by
  refine WPr.seq (fun s' => s' = s) (WPr.call_spec (fun rb => RaiseIn (fun x => x == "EvmErr") rb ∧
    rb.st.globals = s.globals ∧ rb.st.memory = s.memory ∧ rb.st.ffi = s.ffi) ?_ ?_ ?_ ?_)
    (by rintro _ rfl; exact hk)
  · intro parameters cbody values cl hlk _ _ r hr'
    rcases hr parameters cbody hlk _ r hr' with he | hra
    · exact Or.inl he
    · obtain ⟨fuel, n', hrun⟩ := hr'
      exact Or.inr ⟨hra, hq parameters cbody hlk fuel ⟨cl, s.globals, s.memory, s.ffi⟩ r n' hrun⟩
  · rintro l g m ffi vs ⟨-, hg, hm, hf⟩
    dsimp only [PanValueFfiControlResult.st] at hg hm hf
    subst hg hm hf
    rfl
  · rintro l g m ffi exc v ⟨hra, hg, hm, hf⟩
    dsimp only [PanValueFfiControlResult.st] at hg hm hf
    subst hg hm hf
    have hx : exc = "EvmErr" := by simpa [RaiseIn] using hra
    subst hx
    exact hab _ (Or.inr ⟨X, n, hok, hp, Assn.holds_congr rfl rfl h, _, _, _, _, rfl⟩)
  · intro l g m ffi ev _
    exact hab _ (Or.inl trivial)

/-- `var x = f(args); rest` for a callee that changes nothing and raises at most `EvmErr`. -/
theorem op_quiet_raise {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt}
    {n : Nat} (hq : FunKeeps (quietKeeper E) f) (hr : FunRaises E (fun x => x == "EvmErr") f)
    (hok : FrameOk M K fv X) (hp : Adv X X0 n) (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hab : AcceptsAbort M K e fv R s.ffi X0 Q)
    (hk : ∀ v, panShapeMatches (panValueShape E.structs v) sh = true →
      (FrameOp M K e fv X ⋆ R).holds
        (⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x sh f args body) Q := by
  refine WPr.decCall_specS (fun rb => RaiseIn (fun x => x == "EvmErr") rb ∧
    rb.st.globals = s.globals ∧ rb.st.memory = s.memory ∧ rb.st.ffi = s.ffi) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk _ _ r hr'
    rcases hr parameters cbody hlk _ r hr' with he | hra
    · exact Or.inl he
    · obtain ⟨fuel, n', hrun⟩ := hr'
      exact Or.inr ⟨hra, hq parameters cbody hlk fuel ⟨cl, s.globals, s.memory, s.ffi⟩ r n' hrun⟩
  · rintro l g m ffi v ⟨-, hg, hm, hf⟩ hsh
    dsimp only [PanValueFfiControlResult.st] at hg hm hf
    subst hg hm hf
    exact hk v hsh (Assn.holds_congr rfl rfl h)
  · rintro l g m ffi exc v ⟨hra, hg, hm, hf⟩
    dsimp only [PanValueFfiControlResult.st] at hg hm hf
    subst hg hm hf
    have hx : exc = "EvmErr" := by simpa [RaiseIn] using hra
    subst hx
    exact hab _ (Or.inr ⟨X, n, hok, hp, Assn.holds_congr rfl rfl h, _, _, _, _, rfl⟩)
  · intro l g m ffi ev _
    exact hab _ (Or.inl trivial)

/-- `st a, v; rest` into an owned cell, for whatever word `v` is. -/
theorem WPr.seq_store_at_ex (hE : GuestEnv E) {a val : Exp Word} {q : Prog Word} {addr : Word}
    {A : Assn} {A' : Word → Assn} {R : Assn} (h : (A ⋆ R).holds s)
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : ∀ y, E.eval s val = some y → ∃ w : Word, y = .word w)
    (hstep : ∀ w : Word, Step (.mem addr) (.word w) A (A' w))
    (hq : ∀ w m, (A' w ⋆ R).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.store a val) q) Q := by
  refine WPr.seq (fun s' => ∃ w m, s' = ⟨s.locals, s.globals, m, s.ffi⟩ ∧ (A' w ⋆ R).holds s')
    ?_ ?_
  · intro r hr
    obtain ⟨fuel, n, hrun⟩ := hr
    rcases store_word_inv hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
    · exact Or.inl herr
    have := ha _ ha'
    simp only [PanValue.word.injEq] at this
    subst this
    obtain ⟨w, rfl⟩ := hv y hy
    have hm' := hm w rfl
    subst hm'
    exact Or.inr ⟨w, _, rfl, hstep w _ _ _ (upd_setCell s addr' w s.locals s.ffi) h⟩
  · rintro _ ⟨w, m, rfl, hm⟩
    exact hq w m hm

/-- `st ev + 0, v; rest`: a store to the program counter. -/
theorem op_set_pc (hE : GuestEnv E) {val : Exp Word} {q : Prog Word} {M : Word}
    {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt} {n : Nat}
    (hv : ∀ y, E.eval s val = some y → ∃ w : Word, y = .word w)
    (hok : FrameOk M K fv X) (hp : Adv X X0 n) (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hq : ∀ w m, FrameOk M K fv { X with pc := w } → Adv { X with pc := w } X0 n →
      (FrameOp M K e fv { X with pc := w } ⋆ R).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.store (.op .add [.var .global "ev", .const 0#64]) val) q) Q := by
  have hf := Assn.holds_focus (OpW_pc ..) (Assn.holds_assoc_r h)
  have hf' : ((.glob "ev" ↦ .word e ⋆ .mem e ↦ .word X.pc) ⋆
      OpNoPc e X.sp X.cap X.base X.pv fv X.gl X.used ⋆ JunkW M K X.pv X.base X.cap ⋆ R).holds s :=
    hf
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hf' (by look)
  refine WPr.seq_store_at_ex hE hf' (addr := e)
    (A' := fun w => .glob "ev" ↦ .word e ⋆ .mem e ↦ .word w)
    (of_eval (by ev [eval_global, hev])) hv (fun w => by step) (fun w m hm => ?_)
  have hm' : (PcCell e w ⋆ OpNoPc e X.sp X.cap X.base X.pv fv X.gl X.used ⋆
      JunkW M K X.pv X.base X.cap ⋆ R).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) := hm
  exact hq w m ⟨hok.ok, hok.pb, hok.bM, hok.Kpv, hok.Kst⟩ hp
    (Assn.holds_assoc_l (P := OpW e X.sp X.cap X.base X.pv fv X.gl X.used w)
      (Assn.holds_unfocus (OpW_pc ..) hm'))

/-- A field of a local holding a four-word value is a word. -/
theorem arg1_rfield4 {x : VarName} {v : PanValue Word} (i : Nat) (hi : i < 4)
    (hx : s.locals x = some v)
    (hsh : panShapeMatches (panValueShape E.structs v) (.comb [.one, .one, .one, .one]) = true) :
    ∀ y, E.eval s (.rField i (.var .local x)) = some y → ∃ w : Word, y = .word w := by
  obtain ⟨w0, w1, w2, w3, rfl⟩ := struct4_of_shape hsh
  intro y hy
  rw [evalF_rField, evalF_local, hx] at hy
  simp only at hy
  interval_cases i <;> simp at hy <;> exact ⟨_, hy.symm⟩

/-- The state is `s`. -/
def IsState (s s' : St σ) : Prop := s' = s

/-- `if c { P }; rest`, where `P` either leaves the state alone or ends the function. -/
theorem WPr.seq_ite_skip {c : Exp Word} {P q : Prog Word}
    (hthen : WPr E s P (fun r1 => match r1 with
      | .normal l g m f => IsState s ⟨l, g, m, f⟩
      | r1 => Q r1))
    (hrest : WPr E s q Q) : WPr E s (.seq (.ite c P .skip) q) Q := by
  refine WPr.seq (IsState s) (WPr.ite_both (fun w _ => ?_)) (by rintro _ rfl; exact hrest)
  split
  · exact WPr.skip rfl
  · exact hthen

/-- `var x = e; rest` under the frame invariant, remembering how `x` was computed. -/
theorem op_dec_ev {x : VarName} {sh : Shape} {ex : Exp Word} {body : Prog Word} {M : Word}
    {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt}
    (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hk : ∀ v, E.eval s ex = some v → (FrameOp M K e fv X ⋆ R).holds
        (⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.dec x sh ex body) Q :=
  WPr.dec_ev (fun v hv => hk v hv (Assn.holds_congr rfl rfl h))

/-- A local known to hold a four-word value. -/
theorem arg4_ex {x : VarName} {v : PanValue Word} (hx : s.locals x = some v)
    (hv : ∃ w0 w1 w2 w3 : Word, v = .rStruct [.word w0, .word w1, .word w2, .word w3]) :
    ∀ v', E.eval s (.var .local x) = some v' →
      ∃ w0 w1 w2 w3 : Word, v' = .rStruct [.word w0, .word w1, .word w2, .word w3] := by
  obtain ⟨w0, w1, w2, w3, rfl⟩ := hv
  exact arg4_local hx

end InitECandidate.Solver.GuestBound
