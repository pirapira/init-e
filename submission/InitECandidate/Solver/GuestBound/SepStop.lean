import InitECandidate.Solver.GuestBound.SepMstore

/-!
# `op_stop`

It clears the running flag and advances the program counter. It charges no
gas; its progress is the cleared flag.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `ev`, from the frame's assertion. -/
theorem holds_ev {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt} {Y : MemSt}
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s) :
    s.globals "ev" = some (.word e) := by
  have h' := Assn.holds_assoc_r (Assn.holds_focus (FrameM_cmw M K e fv X Y)
    (Assn.holds_assoc_l (P := FrameOp M K e fv X) h))
  unfold MemW at h'
  exact Assn.glob_at h' (by look)

/-- `st ev + 104, 0; rest`: clear the running flag. -/
theorem op_clear_run (hE : GuestEnv E) {q : Prog Word} {M : Word} {K : Word → Prop}
    {e fv : Word} {R : Assn} {X : OpSt} {Y : MemSt}
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s)
    (hq : ∀ m, (FrameOp M K e fv X ⋆ MemExtra e { Y with run := 0#64 } ⋆ R).holds
        (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) → WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.store (.op .add [.var .global "ev", .const 104#64]) (.const 0#64)) q) Q := by
  have hev := holds_ev h
  have h2 : (MemTail e Y ⋆ (Assn.Range Y.mem (Y.mem + Y.cap) ⋆ FrameOp M K e fv X) ⋆ R).holds s :=
    Assn.holds_perm h (by unfold MemExtra; ac_rfl)
  unfold MemTail at h2
  refine WPr.seq_store_at hE h2 (addr := e + 104#64) (w := 0#64)
    (of_eval (by ev [eval_global, hev])) (of_eval (eval_const _ _)) (by step) (fun m hm => ?_)
  have hm' : (MemTail e { Y with run := 0#64 } ⋆ (Assn.Range Y.mem (Y.mem + Y.cap) ⋆
      FrameOp M K e fv X) ⋆ R).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) := hm
  exact hq m (Assn.holds_perm hm' (by unfold MemExtra; ac_rfl))

/-- `return 0` at the end of a handler that cleared the running flag. -/
theorem op_return_stopped {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {X0 X : OpSt} {Y : MemSt} {n : Nat} (hok : FrameOk M K fv X) (hY : MBufOk Y fv)
    (hp : Adv X X0 n) (hrun : Y.run = 0#64)
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s) {mem0 : Word}
    (hQ : AcceptsM M K e mem0 R s.ffi X0 Q) (hm : Y.mem = mem0 := by rfl) :
    WPr E s (.return (.const 0#64)) Q :=
  WPr.ret (w := 0#64) (of_eval (eval_const _ _))
    (hQ _ (Or.inr ⟨fv, X, Y, n, hok, hY, hm, hp, Or.inr hrun, Assn.holds_congr rfl rfl h,
      _, _, _, rfl⟩))

theorem op_stop_frameM (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_stop" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt) (Y0 : MemSt)
    (hok : FrameOk M K fv X0) (hY : MBufOk Y0 fv)
    (h : (FrameOp M K e fv X0 ⋆ MemExtra e Y0 ⋆ R).holds s) :
    WPr E s body (HandlerQM M K e Y0.mem R s.ffi X0) := by
  have hbody := (fun_of_index 502 hE.functions (by guest_decl_at 502) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hY' : MBufOk { Y0 with run := 0#64 } fv := ⟨hY.mal, hY.cal, hY.l32, hY.lc, hY.top⟩
  refine op_clear_run hE h (fun m h1 => ?_)
  refine op_pc_add hE (d := 1#64)
    (by simp [evalArgs_cons, evalArgs_nil, eval_const]) hok hp h1
    (AcceptsM.refl.toH hY').abort (fun g m2 hok hp h2 => ?_)
  exact op_return_stopped hok hY' hp rfl h2 AcceptsM.refl

end InitECandidate.Solver.GuestBound
