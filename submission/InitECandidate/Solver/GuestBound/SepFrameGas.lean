import InitECandidate.Solver.GuestBound.SepChargeState

/-!
# Gas moving between frames and at a halt

`frame_halt` burns the gas left of the current frame. `incorporate_child_on_error`
adds the child's gas left, reservoir and gas used to the current (parent) frame;
the child's spilled gas is not carried over.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The cells `frame_halt` touches: gas left, gas used, error code. -/
def HaltCells (e gl used code : Word) : Assn :=
  .glob "ev" ↦ .word e ⋆ .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 184#64) ↦ .word used ⋆
    .mem (e + 160#64) ↦ .word code

/-- `frame_halt(err)`: all gas left becomes gas used. -/
theorem frame_halt_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "frame_halt" E.functions = some (parameters, body))
    (s : St σ) (e gl used code err : Word) (herr : s.locals "err" = some (.word err)) :
    WPFr E s body (HaltCells e gl used code)
      (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        HaltCells e 0#64 (used + gl) err) := by
  have hbody := (fun_of_index 586 hE.functions (by guest_decl_at 586)
    (by decide +kernel) hlookup).1
  subst hbody
  intro R hR
  unfold HaltCells at hR
  dsimp only
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hR (by look)
  refine WPr.seq_store_at hE hR (addr := e + 184#64) (w := used + gl)
    (of_eval (by ev [eval_global, hev]))
    (eval_add2_inv hE
      (eval_load_at hE (addr := e + 184#64) (of_eval (by ev [eval_global, hev])) hR (by look))
      (eval_load_at hE (addr := e + 64#64) (of_eval (by ev [eval_global, hev])) hR (by look)))
    (by step) (fun m1 h1 => ?_)
  refine WPr.seq_store_at hE h1 (addr := e + 64#64) (w := 0#64)
    (of_eval (by ev [eval_global, hev])) (of_eval (eval_const _ _))
    (by step) (fun m2 h2 => ?_)
  refine WPr.seq_store_at hE h2 (addr := e + 160#64) (w := err)
    (of_eval (by ev [eval_global, hev])) (of_eval (by lk [herr]))
    (by step) (fun m3 h3 => ?_)
  refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  show ((⌜_⌝ ⋆ HaltCells _ _ _ _) ⋆ R).holds _
  rw [Assn.sep_assoc]
  exact Assn.holdsV_pure.mpr ⟨⟨_, _, _, rfl⟩, Assn.holds_congr rfl rfl h3⟩

/-- Gas left, reservoir and gas used of the current frame and of a child record. -/
def ParentChild (e gl sgl used c cg cs cu : Word) : Assn :=
  .glob "ev" ↦ .word e ⋆ .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 72#64) ↦ .word sgl ⋆
    .mem (e + 184#64) ↦ .word used ⋆ .mem (c + 64#64) ↦ .word cg ⋆
    .mem (c + 72#64) ↦ .word cs ⋆ .mem (c + 184#64) ↦ .word cu

/-- `incorporate_child_on_error(child)`: the child's three counters are added
to the current frame's; the child record is only read. -/
theorem incorporate_error_framed (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "incorporate_child_on_error" E.functions =
      some (parameters, body))
    (s : St σ) (e gl sgl used c cg cs cu : Word) (hc : s.locals "child" = some (.word c)) :
    WPFr E s body (ParentChild e gl sgl used c cg cs cu)
      (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        ParentChild e (gl + cg) (sgl + cs) (used + cu) c cg cs cu) := by
  have hbody := (fun_of_index 591 hE.functions (by guest_decl_at 591)
    (by decide +kernel) hlookup).1
  subst hbody
  intro R hR
  unfold ParentChild at hR
  dsimp only
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hR (by look)
  refine WPr.seq_store_at hE hR (addr := e + 64#64) (w := gl + cg)
    (of_eval (by ev [eval_global, hev]))
    (eval_add2_inv hE
      (eval_load_at hE (addr := e + 64#64) (of_eval (by ev [eval_global, hev])) hR (by look))
      (eval_load_at hE (addr := c + 64#64) (of_eval (by ev [hc])) hR (by look)))
    (by step) (fun m1 h1 => ?_)
  refine WPr.seq_store_at hE h1 (addr := e + 72#64) (w := sgl + cs)
    (of_eval (by ev [eval_global, hev]))
    (eval_add2_inv hE
      (eval_load_at hE (addr := e + 72#64) (of_eval (by ev [eval_global, hev])) h1 (by look))
      (eval_load_at hE (addr := c + 72#64) (of_eval (by ev [hc])) h1 (by look)))
    (by step) (fun m2 h2 => ?_)
  refine WPr.seq_store_at hE h2 (addr := e + 184#64) (w := used + cu)
    (of_eval (by ev [eval_global, hev]))
    (eval_add2_inv hE
      (eval_load_at hE (addr := e + 184#64) (of_eval (by ev [eval_global, hev])) h2 (by look))
      (eval_load_at hE (addr := c + 184#64) (of_eval (by ev [hc])) h2 (by look)))
    (by step) (fun m3 h3 => ?_)
  refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  show ((⌜_⌝ ⋆ ParentChild _ _ _ _ _ _ _ _) ⋆ R).holds _
  rw [Assn.sep_assoc]
  exact Assn.holdsV_pure.mpr ⟨⟨_, _, _, rfl⟩, Assn.holds_congr rfl rfl h3⟩

end InitECandidate.Solver.GuestBound
