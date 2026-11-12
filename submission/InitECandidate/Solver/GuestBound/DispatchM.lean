import InitECandidate.Solver.GuestBound.SepReturn
import InitECandidate.Solver.GuestBound.DispatchOps

/-!
# Handlers and dispatcher leaves at the memory level

`HandlerSpecM` is the handler statement with the memory buffer in the
invariant. Every stack-level handler theorem lifts to it (`HandlerSpec.toM`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A handler, at the level of the frame with its memory buffer. -/
def HandlerSpecM (E : Env σ) (f : FunName) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    ∀ (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt) (Y0 : MemSt),
      FrameOk M K fv X0 → MBufOk Y0 fv → X0.gl.toNat < 2 ^ 64 - 1 →
      (FrameOp M K e fv X0 ⋆ MemExtra e Y0 ⋆ R).holds s →
      WPr E s body (HandlerQM M K e Y0.mem R s.ffi X0)

theorem HandlerSpec.toM {f : FunName} (h : HandlerSpec E f) : HandlerSpecM E f :=
  fun p b hl s M K e fv R X0 Y0 hok hY _ hh =>
    WPr.conseq (h p b hl s M K e fv (MemExtra e Y0 ⋆ R) X0 hok hh) (fun _ hr => hr.toM hY rfl)

theorem op_mload_specM (hE : GuestEnv E) : HandlerSpecM E "op_mload" :=
  fun p b hl s M K e fv R X0 Y0 hok hY hgl hh =>
    op_mload_frameM hE p b hl s M K e fv R X0 Y0 hok hY hgl hh

theorem op_mstore_specM (hE : GuestEnv E) : HandlerSpecM E "op_mstore" :=
  fun p b hl s M K e fv R X0 Y0 hok hY hgl hh =>
    op_mstore_frameM hE p b hl s M K e fv R X0 Y0 hok hY hgl hh

theorem op_mstore8_specM (hE : GuestEnv E) : HandlerSpecM E "op_mstore8" :=
  fun p b hl s M K e fv R X0 Y0 hok hY hgl hh =>
    op_mstore8_frameM hE p b hl s M K e fv R X0 Y0 hok hY hgl hh

theorem op_stop_specM (hE : GuestEnv E) : HandlerSpecM E "op_stop" :=
  fun p b hl s M K e fv R X0 Y0 hok hY _ hh =>
    op_stop_frameM hE p b hl s M K e fv R X0 Y0 hok hY hh

theorem op_return_specM (hE : GuestEnv E) : HandlerSpecM E "op_return" :=
  fun p b hl s M K e fv R X0 Y0 hok hY hgl hh =>
    op_return_frameM hE p b hl s M K e fv R X0 Y0 hok hY hgl hh

theorem op_revert_specM (hE : GuestEnv E) : HandlerSpecM E "op_revert" :=
  fun p b hl s M K e fv R X0 Y0 hok hY hgl hh =>
    op_revert_frameM hE p b hl s M K e fv R X0 Y0 hok hY hgl hh

/-- A leaf of the dispatcher, from the handler's memory-level theorem. -/
theorem handler_leafM {f : FunName} (hf : HandlerSpecM E f) (args : List (Exp Word))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt) (Y0 : MemSt)
    (hok : FrameOk M K fv X0) (hY : MBufOk Y0 fv) (hgl : X0.gl.toNat < 2 ^ 64 - 1)
    (h : (FrameOp M K e fv X0 ⋆ MemExtra e Y0 ⋆ R).holds s) :
    WPr E s (.seq (.call (some (none, none)) f args) (.return (.const 0#64)))
      (HandlerQM M K e Y0.mem R s.ffi X0) := by
  refine WPr.seq (fun s' => ∃ g m fv' X Y n, s' = ⟨s.locals, g, m, s.ffi⟩ ∧ FrameOk M K fv' X ∧
      MBufOk Y fv' ∧ Y.mem = Y0.mem ∧ Adv X X0 n ∧ (0 < n ∨ Y.run = 0#64) ∧
      (FrameOp M K e fv' X ⋆ MemExtra e Y ⋆ R).holds s')
    (WPr.call_spec (HandlerQM M K e Y0.mem R s.ffi X0)
      (fun parameters body _ cl hlk _ _ =>
        hf parameters body hlk ⟨cl, s.globals, s.memory, s.ffi⟩ M K e fv R X0 Y0 hok hY hgl
          (Assn.holds_congr rfl rfl h)) ?_ ?_ ?_) ?_
  · rintro l g m ffi vs ((ht | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) |
      ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hn, hh, _, _, _, hC⟩)
    · exact ht.elim
    · cases hC
    · injection hC with _ _ _ hf' _
      subst hf'
      exact ⟨g, m, fv', X, Y, n, rfl, hokX, hYX, hmX, hp, hn, Assn.holds_congr rfl rfl hh⟩
  · rintro l g m ffi exc v ((ht | ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hh, _, _, _, _, hC⟩) |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩)
    · exact Or.inl (Or.inl ht)
    · injection hC with _ _ _ hf' hx hv
      subst hf' hx hv
      exact Or.inl (Or.inr ⟨fv', X, Y, n, hokX, hYX, hmX, hp, Assn.holds_congr rfl rfl hh,
        _, _, _, _, rfl⟩)
    · cases hC
  · intro l g m ffi ev _
    exact Or.inl (Or.inl trivial)
  · rintro _ ⟨g, m, fv', X, Y, n, rfl, hokX, hYX, hmX, hp, hn, hh⟩
    exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
      (Or.inr ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hn, Assn.holds_congr rfl rfl hh, _, _, _, rfl⟩)

/-- The handlers proved by hand at the memory level. -/
def memOps : List FunName := ["op_mload", "op_mstore", "op_mstore8", "op_stop", "op_return", "op_revert"]

/-- The handlers still to be proved, at the memory level. -/
def restOpsM : List FunName := restOps.filter (fun f => !memOps.contains f)

theorem handlers_provedM (hE : GuestEnv E) :
    ∀ f, f ∈ provedOps ++ memOps → HandlerSpecM E f := by
  intro f hf
  rcases List.mem_append.mp hf with h1 | h2
  · exact (handlers_proved hE f h1).toM
  · simp only [memOps, List.mem_cons, List.not_mem_nil, or_false] at h2
    rcases h2 with rfl | rfl | rfl | rfl | rfl | rfl
    · exact op_mload_specM hE
    · exact op_mstore_specM hE
    · exact op_mstore8_specM hE
    · exact op_stop_specM hE
    · exact op_return_specM hE
    · exact op_revert_specM hE

/-- The dispatcher at the memory level. -/
theorem op_dispatch_frameM (hE : GuestEnv E) (hrest : ∀ f, f ∈ restOpsM → HandlerSpecM E f)
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_dispatch" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt) (Y0 : MemSt)
    (hok : FrameOk M K fv X0) (hY : MBufOk Y0 fv) (hgl : X0.gl.toNat < 2 ^ 64 - 1)
    (h : (FrameOp M K e fv X0 ⋆ MemExtra e Y0 ⋆ R).holds s) :
    WPr E s body (fun r => match r with
      | .normal l g m f => (⟨l, g, m, f⟩ : St σ) = s
      | r => HandlerQM M K e Y0.mem R s.ffi X0 r) := by
  have hbody := (fun_of_index 577 hE.functions (by guest_decl_at 577) (by decide +kernel)
    hlookup).1
  subst hbody
  have hall : ∀ f, (provedOps ++ restOps).contains f = true → HandlerSpecM E f := by
    intro f hf
    rcases List.mem_append.mp (List.contains_iff_mem.mp hf) with h1 | h2
    · exact handlers_provedM hE f (List.mem_append_left _ h1)
    · by_cases hm : memOps.contains f = true
      · exact handlers_provedM hE f (List.mem_append_right _ (List.contains_iff_mem.mp hm))
      · exact hrest f (List.mem_filter.mpr ⟨h2, by simpa using hm⟩)
  refine tree_sound (ok := fun f => (provedOps ++ restOps).contains f) (P := fun a => a = s)
    (Q := HandlerQM M K e Y0.mem R s.ffi X0) ?_ ?_ ?_ _ (by decide +kernel) s rfl
  · rintro f args hf _ rfl
    exact handler_leafM (hall f hf) args _ M K e fv R X0 Y0 hok hY hgl h
  · rintro _ k rfl
    exact Or.inl (Or.inr ⟨fv, X0, Y0, 0, hok, hY, rfl, ⟨Nat.le_refl _, Nat.le_refl _⟩,
      Assn.holds_congr rfl rfl h, _, _, _, _, rfl⟩)
  · rintro l g m f ((ht | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩)
    · exact ht.elim
    · cases hC
    · cases hC

end InitECandidate.Solver.GuestBound
