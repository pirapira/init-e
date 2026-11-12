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

end InitECandidate.Solver.GuestBound
