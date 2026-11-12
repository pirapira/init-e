import InitECandidate.Solver.GuestBound.SepFrameOp2

/-!
# `frame_exception` as a framed specification

The handler of `EvmErr` in the interpreter loop: spilled state gas returns to
gas left; unless the error is a revert (code 1) all gas left is burnt and the
return data is cleared; the error code is recorded and the continuation's
exception flag is set, so the next iteration ends the frame.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- What `frame_exception` owns. -/
def ExcW (e gl sgl sp msg r0 used code rd rl cc fl ee : Word) : Assn :=
  .glob "ev" ↦ .word e ⋆ .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 72#64) ↦ .word sgl ⋆
    .mem (e + 192#64) ↦ .word sp ⋆ .mem (e + 112#64) ↦ .word msg ⋆
    .mem (msg + 48#64) ↦ .word r0 ⋆ .mem (e + 184#64) ↦ .word used ⋆
    .mem (e + 160#64) ↦ .word code ⋆ .mem (e + 120#64) ↦ .word rd ⋆
    .mem (e + 128#64) ↦ .word rl ⋆ .glob "cur_cont" ↦ .word cc ⋆
    .mem (cc + 32#64) ↦ .word fl ⋆ .glob "evm_empty" ↦ .word ee

/-- `ExcW` without the state-gas cells. -/
def ExcRestS (e used code rd rl cc fl ee : Word) : Assn :=
  .mem (e + 184#64) ↦ .word used ⋆ .mem (e + 160#64) ↦ .word code ⋆
    .mem (e + 120#64) ↦ .word rd ⋆ .mem (e + 128#64) ↦ .word rl ⋆
    .glob "cur_cont" ↦ .word cc ⋆ .mem (cc + 32#64) ↦ .word fl ⋆ .glob "evm_empty" ↦ .word ee

/-- `ExcW` without the cells `frame_halt` touches. -/
def ExcRestH (e sgl sp msg r0 rd rl cc fl ee : Word) : Assn :=
  .mem (e + 72#64) ↦ .word sgl ⋆ .mem (e + 192#64) ↦ .word sp ⋆
    .mem (e + 112#64) ↦ .word msg ⋆ .mem (msg + 48#64) ↦ .word r0 ⋆
    .mem (e + 120#64) ↦ .word rd ⋆ .mem (e + 128#64) ↦ .word rl ⋆
    .glob "cur_cont" ↦ .word cc ⋆ .mem (cc + 32#64) ↦ .word fl ⋆ .glob "evm_empty" ↦ .word ee

theorem ExcW_state (e gl sgl sp msg r0 used code rd rl cc fl ee : Word) :
    ExcW e gl sgl sp msg r0 used code rd rl cc fl ee =
      (StateGas e gl sgl sp msg r0 ⋆ ExcRestS e used code rd rl cc fl ee) := by
  unfold ExcW StateGas ExcRestS; ac_rfl

theorem ExcW_halt (e gl sgl sp msg r0 used code rd rl cc fl ee : Word) :
    ExcW e gl sgl sp msg r0 used code rd rl cc fl ee =
      (HaltCells e gl used code ⋆ ExcRestH e sgl sp msg r0 rd rl cc fl ee) := by
  unfold ExcW HaltCells ExcRestH; ac_rfl

/-- `refill_frame_state_gas()` at a call site. -/
theorem refill_hc (hE : GuestEnv E) (e gl sgl sp msg r0 : Word) :
    ∀ parameters cbody values cl,
      lookupPanFunction "refill_frame_state_gas" E.functions = some (parameters, cbody) →
      E.evalArgs s [] = some values →
      bindPanValueParameters parameters values = some cl →
      WPFr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (StateGas e gl sgl sp msg r0)
        (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
          StateGas e (gl + sp) r0 0#64 msg r0) :=
  fun parameters cbody _ cl hlk _ _ =>
    refill_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e gl sgl sp msg r0

/-- `frame_halt(e)` at a call site where the argument evaluates to `err`. -/
theorem frame_halt_hc (hE : GuestEnv E) {args : List (Exp Word)} {err : Word}
    (hargs : E.evalArgs s args = some [.word err]) (e gl used code : Word) :
    ∀ parameters cbody values cl,
      lookupPanFunction "frame_halt" E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (HaltCells e gl used code)
        (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
          HaltCells e 0#64 (used + gl) err) := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 586 hE.functions (by guest_decl_at 586) (by decide +kernel)
    hlk).2
  rw [hargs] at hvalues
  cases hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact frame_halt_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e gl used
    code err (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])

set_option maxHeartbeats 1000000 in
/-- `frame_exception(err)`. -/
theorem frame_exception_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "frame_exception" E.functions = some (parameters, body))
    (s : St σ) (e gl sgl sp msg r0 used code rd rl cc fl ee : Word) (v : PanValue Word)
    (hv : s.locals "err" = some v) :
    WPFr E s body (ExcW e gl sgl sp msg r0 used code rd rl cc fl ee)
      (fun r => Assn.ex fun err : Word =>
        ⌜v = .word err ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        ExcW e (if err = 1#64 then gl + sp else 0#64) r0 0#64 msg r0
          (if err = 1#64 then used else used + (gl + sp)) err
          (if err = 1#64 then rd else ee) (if err = 1#64 then rl else 0#64) cc 1#64 ee) := by
  have hbody := (fun_of_index 579 hE.functions (by guest_decl_at 579) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  dsimp only
  refine WPr.seq_call_framed (Assn.holds_focus (ExcW_state ..) hR)
    (refill_hc hE e gl sgl sp msg r0) ?_ ?_ ?_
  rotate_left
  · intro l g m ffi exc v h
    obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  · intro l g m ffi ev h
    obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  intro l g m ffi vs h
  obtain ⟨⟨_, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
  injection hC with _ _ _ hf _
  subst hf
  have h1 := Assn.holds_unfocus
    (ExcW_state e (gl + sp) r0 0#64 msg r0 used code rd rl cc fl ee) hk
  refine WPr.seq (fun s' => ∃ g2 m2 err, v = .word err ∧ s' = ⟨s.locals, g2, m2, s.ffi⟩ ∧
      (ExcW e (if err = 1#64 then gl + sp else 0#64) r0 0#64 msg r0
        (if err = 1#64 then used else used + (gl + sp)) err
        (if err = 1#64 then rd else ee) (if err = 1#64 then rl else 0#64) cc fl ee ⋆ R).holds s')
    (WPr.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨err, rfl⟩ : ∃ err : Word, v = .word err := by
      rw [evalF_cmp hE.word, evalF_local] at hw
      simp only [hv] at hw
      cases v with
      | word x => exact ⟨x, rfl⟩
      | _ => simp at hw
    have herr := hv
    have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := err) (by lk [herr]))
      (of_eval (w := 1#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · -- a revert: only the code is recorded
      rename_i hz
      have e1 : err = 1#64 := by
        by_contra hne
        rw [hz] at hcv
        simp [evalPanCmp, hne] at hcv
      have h1u := h1
      unfold ExcW at h1u
      have hev : g "ev" = some (.word e) := Assn.glob_at h1u (by look)
      refine WPr.store_at hE h1u (addr := e + 160#64) (w := err)
        (of_eval (by ev [eval_global, hev])) (of_eval (by lk [herr])) (by step)
        (fun m3 hm => ⟨_, m3, err, rfl, rfl, ?_⟩)
      simp only [e1, ↓reduceIte]
      rw [e1] at hm
      exact hm
    · -- any other error: burn the gas, clear the return data
      rename_i hnz
      have hne : err ≠ 1#64 := by
        intro e1
        exact hnz (by rw [hcv, e1]; simp [evalPanCmp])
      refine WPr.seq_call_framed (Assn.holds_focus (ExcW_halt ..) h1)
        (frame_halt_hc hE (err := err) (by simp [evalArgs_cons, evalArgs_nil, eval_local, herr])
          e (gl + sp) used code) ?_ ?_ ?_
      rotate_left
      · intro l2 g2 m2 ffi2 exc v h
        obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
        cases hC
      · intro l2 g2 m2 ffi2 ev h
        obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
        cases hC
      intro l2 g2 m2 ffi2 vs2 h
      obtain ⟨⟨_, _, _, hC⟩, hk2⟩ := Assn.holds_pure_elim h
      injection hC with _ _ _ hf _
      subst hf
      have h2 := Assn.holds_unfocus
        (ExcW_halt e 0#64 r0 0#64 msg r0 (used + (gl + sp)) err rd rl cc fl ee) hk2
      unfold ExcW at h2
      have hev : g2 "ev" = some (.word e) := Assn.glob_at h2 (by look)
      have hee : g2 "evm_empty" = some (.word ee) := Assn.glob_at h2 (by look)
      refine WPr.seq_store_at hE h2 (addr := e + 120#64) (w := ee)
        (of_eval (by ev [eval_global, hev])) (of_eval (by rw [eval_global]; exact hee)) (by step)
        (fun m4 h4 => ?_)
      refine WPr.store_at hE h4 (addr := e + 128#64) (w := 0#64)
        (of_eval (by ev [eval_global, hev])) (of_eval (eval_const _ _)) (by step)
        (fun m5 h5 => ⟨_, m5, err, rfl, rfl, ?_⟩)
      simp only [hne, ↓reduceIte]
      exact h5
  rintro _ ⟨g2, m2, err, rfl, rfl, h3⟩
  unfold ExcW at h3
  have hcc : g2 "cur_cont" = some (.word cc) := Assn.glob_at h3 (by look)
  refine WPr.seq_store_at hE h3 (addr := cc + 32#64) (w := 1#64)
    (of_eval (by ev [eval_global, hcc])) (of_eval (eval_const _ _)) (by step) (fun m6 h6 => ?_)
  exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
    (Assn.holdsV_ex.mpr ⟨err, Assn.holds_pure_intro ⟨rfl, _, _, _, rfl⟩
      (Assn.holds_congr rfl rfl h6)⟩)

end InitECandidate.Solver.GuestBound
