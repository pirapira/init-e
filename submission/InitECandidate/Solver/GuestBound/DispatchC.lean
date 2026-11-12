import InitECandidate.Solver.GuestBound.SepChain

/-!
# Dispatch on a chain: handlers that may push a frame

Most handlers stay in their frame (`HandlerSpecM`). The six call/create
opcodes may start a child frame. `PushD` is that outcome: the running frame
`F` became a suspended frame `F'` of the same identity, with a child `c`
linked on top of it, the world index may have changed (tables in `D` stay
live), and child plus parent hold at least one unit of gas less than `F` did.

`HandlerSpecPush` is the statement to prove for those six handlers;
`op_dispatch_chain` is the dispatcher with both kinds of leaves.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {ι : Type}

/-- The opcodes that may start a child frame. -/
def callOps : List FunName :=
  ["op_create", "op_create2", "op_call", "op_callcode", "op_delegatecall", "op_staticcall"]

/-- A child frame was pushed on `F`. -/
def PushD (W : ι → Assn) (D : ι → Word → Prop) (i : ι) (F : Fr) (R : Assn) (st : St σ) : Prop :=
  ∃ (i' : ι) (F' c : Fr), F'.M = F.M ∧ F'.K = F.K ∧ F'.e = F.e ∧ F'.C = F.C ∧ F'.A = F.A ∧
    F'.Y.mem = F.Y.mem ∧ F'.Z.cc = F.Z.cc ∧ F'.Z.msg = F.Z.msg ∧ F'.Z.ee = F.Z.ee ∧
    F'.Ok (D i') ∧ c.Ok (D i') ∧ Link c F' ∧ (∀ t, D i t → D i' t) ∧
    c.gas + F'.gas + 1 ≤ F.gas ∧ (c.full ⋆ F'.susp ⋆ W i' ⋆ R).holds st

theorem PushD.congr {W : ι → Assn} {D : ι → Word → Prop} {i : ι} {F : Fr} {R : Assn}
    {st st' : St σ} (h : PushD W D i F R st) (hg : st'.globals = st.globals)
    (hm : st'.memory = st.memory) : PushD W D i F R st' := by
  obtain ⟨i', F', c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hh⟩ := h
  exact ⟨i', F', c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    Assn.holds_congr hg hm hh⟩

/-- What the rest of the running frame's assertion is, seen from a handler. -/
def frameRest (W : ι → Assn) (i : ι) (F : Fr) (R : Assn) : Assn :=
  ExcExtraM F.e F.Z ⋆ RecCells F.Z.cc F.C ⋆ AccCells F.e F.A ⋆ W i ⋆ R

/-- The outcome of a handler on a chain: it stayed in its frame, or it pushed a child. -/
def HandlerQC (W : ι → Assn) (D : ι → Word → Prop) (i : ι) (F : Fr) (R : Assn)
    (ffi : FfiState σ) (r : Result σ) : Prop :=
  HandlerQM F.M F.K F.e F.Y.mem (frameRest W i F R) ffi F.X r ∨
    ∃ l g m, r = .returned l g m ffi [.word 0#64] ∧ PushD W D i F R ⟨l, g, m, ffi⟩

/-- A handler that may push a child frame. -/
def HandlerSpecPush (E : Env σ) (W : ι → Assn) (D : ι → Word → Prop) (f : FunName) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    ∀ (s : St σ) (i : ι) (F : Fr) (R : Assn), F.Ok (D i) → F.X.gl.toNat < 2 ^ 64 - 1 →
      (F.full ⋆ W i ⋆ R).holds s → WPr E s body (HandlerQC W D i F R s.ffi)

/-- The frame's assertion, split the way single-frame handlers see it. -/
theorem holds_frameRest {W : ι → Assn} {i : ι} {F : Fr} {R : Assn} {s : St σ}
    (h : (F.full ⋆ W i ⋆ R).holds s) :
    (FrameOp F.M F.K F.e F.fv F.X ⋆ MemExtra F.e F.Y ⋆ frameRest W i F R).holds s :=
  Assn.holds_perm h (by unfold Fr.full frameRest; ac_rfl)

/-- A leaf of the dispatcher for a handler that may push a frame. -/
theorem handler_leafC {W : ι → Assn} {D : ι → Word → Prop} {f : FunName}
    (hf : HandlerSpecPush E W D f) (args : List (Exp Word)) (s : St σ) (i : ι) (F : Fr)
    (R : Assn) (hok : F.Ok (D i)) (hgl : F.X.gl.toNat < 2 ^ 64 - 1)
    (h : (F.full ⋆ W i ⋆ R).holds s) :
    WPr E s (.seq (.call (some (none, none)) f args) (.return (.const 0#64)))
      (HandlerQC W D i F R s.ffi) := by
  refine WPr.seq (fun s' => ∃ g m, s' = ⟨s.locals, g, m, s.ffi⟩ ∧
      ((∃ fv' X Y n, FrameOk F.M F.K fv' X ∧ MBufOk Y fv' ∧ Y.mem = F.Y.mem ∧ Adv X F.X n ∧
        (0 < n ∨ Y.run = 0#64) ∧
        (FrameOp F.M F.K F.e fv' X ⋆ MemExtra F.e Y ⋆ frameRest W i F R).holds s') ∨
        PushD W D i F R s'))
    (WPr.call_spec (HandlerQC W D i F R s.ffi)
      (fun parameters body _ cl hlk _ _ =>
        hf parameters body hlk ⟨cl, s.globals, s.memory, s.ffi⟩ i F R hok hgl
          (Assn.holds_congr rfl rfl h)) ?_ ?_ ?_) ?_
  · rintro l g m ffi vs (((ht | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) |
      ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hn, hh, _, _, _, hC⟩) | ⟨l', g', m', hC, hpd⟩)
    · exact ht.elim
    · cases hC
    · injection hC with _ _ _ hf' _
      subst hf'
      exact ⟨g, m, rfl, Or.inl ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hn,
        Assn.holds_congr rfl rfl hh⟩⟩
    · injection hC with _ hg hm hf' _
      subst hg hm hf'
      exact ⟨g, m, rfl, Or.inr (hpd.congr rfl rfl)⟩
  · rintro l g m ffi exc v (((ht | ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hh, _, _, _, _, hC⟩) |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) | ⟨_, _, _, hC, _⟩)
    · exact Or.inl (Or.inl (Or.inl ht))
    · injection hC with _ _ _ hf' hx hv
      subst hf' hx hv
      exact Or.inl (Or.inl (Or.inr ⟨fv', X, Y, n, hokX, hYX, hmX, hp,
        Assn.holds_congr rfl rfl hh, _, _, _, _, rfl⟩))
    · cases hC
    · cases hC
  · intro l g m ffi ev _
    exact Or.inl (Or.inl (Or.inl trivial))
  · rintro _ ⟨g, m, rfl, hcase⟩
    refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
    rcases hcase with ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hn, hh⟩ | hpd
    · exact Or.inl (Or.inr ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hn, Assn.holds_congr rfl rfl hh,
        _, _, _, rfl⟩)
    · exact Or.inr ⟨_, _, _, rfl, hpd.congr rfl rfl⟩

/-- The dispatcher on a chain. -/
theorem op_dispatch_chain (hE : GuestEnv E) {W : ι → Assn} {D : ι → Word → Prop}
    (hrest : ∀ f, f ∈ restOpsM → f ∉ callOps → HandlerSpecM E f)
    (hcall : ∀ f, f ∈ callOps → HandlerSpecPush E W D f)
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_dispatch" E.functions = some (parameters, body))
    (s : St σ) (i : ι) (F : Fr) (R : Assn) (hok : F.Ok (D i))
    (hgl : F.X.gl.toNat < 2 ^ 64 - 1) (h : (F.full ⋆ W i ⋆ R).holds s) :
    WPr E s body (fun r => match r with
      | .normal l g m f => (⟨l, g, m, f⟩ : St σ) = s
      | r => HandlerQC W D i F R s.ffi r) := by
  have hbody := (fun_of_index 577 hE.functions (by guest_decl_at 577) (by decide +kernel)
    hlookup).1
  subst hbody
  have hfr := holds_frameRest h
  have hall : ∀ f, (provedOps ++ restOps).contains f = true → f ∉ callOps →
      HandlerSpecM E f := by
    intro f hf hnc
    rcases List.mem_append.mp (List.contains_iff_mem.mp hf) with h1 | h2
    · exact handlers_provedM hE f (List.mem_append_left _ h1)
    · by_cases hm : memOps.contains f = true
      · exact handlers_provedM hE f (List.mem_append_right _ (List.contains_iff_mem.mp hm))
      · exact hrest f (List.mem_filter.mpr ⟨h2, by simpa using hm⟩) hnc
  refine tree_sound (ok := fun f => (provedOps ++ restOps).contains f) (P := fun a => a = s)
    (Q := HandlerQC W D i F R s.ffi) ?_ ?_ ?_ _ (by decide +kernel) s rfl
  · rintro f args hf _ rfl
    by_cases hc : f ∈ callOps
    · exact handler_leafC (hcall f hc) args _ i F R hok hgl h
    · exact WPr.conseq (handler_leafM (hall f hf hc) args _ F.M F.K F.e F.fv
        (frameRest W i F R) F.X F.Y hok.ok hok.buf hgl hfr) (fun r hr => Or.inl hr)
  · rintro _ k rfl
    exact Or.inl (Or.inl (Or.inr ⟨F.fv, F.X, F.Y, 0, hok.ok, hok.buf, rfl,
      ⟨Nat.le_refl _, Nat.le_refl _⟩, Assn.holds_congr rfl rfl hfr, _, _, _, _, rfl⟩))
  · rintro l g m f (((ht | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) | ⟨_, _, _, hC, _⟩)
    · exact ht.elim
    · cases hC
    · cases hC
    · cases hC

end InitECandidate.Solver.GuestBound
