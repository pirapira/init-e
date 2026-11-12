import InitECandidate.Solver.GuestBound.SepDom

/-!
# Ending a child frame: the arena goes back to the parent

`finish_child` ends with `scratch_release(child_mark)` and
`frame_mem_release(child_mem_mark)`. `child_teardown`: after these two calls
the child's gap and everything the child kept are the parent's free gap
(`Fr.reclaim`), and the parent is the running frame again (`Fr.full`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A call that sets one owned global to its argument and returns 0. -/
theorem WPr.seq_release (hE : GuestEnv E) {f : FunName} {x : VarName} (idx : Nat)
    (hdecl : ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
      body = .seq (.assign .global x (.var .local "m")) (.return (.const 0#64)) ∧
        parameters = ["m"])
    {e : Exp Word} {q : Prog Word} {a mk : Word} {R : Assn}
    (h : (.glob x ↦ .word a ⋆ R).holds s) (he : ∀ y, E.eval s e = some y → y = .word mk)
    (hq : ∀ g, (.glob x ↦ .word mk ⋆ R).holds (⟨s.locals, g, s.memory, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, g, s.memory, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) f [e]) q) Q := by
  refine WPr.seq (fun s' => ∃ g, s' = ⟨s.locals, g, s.memory, s.ffi⟩ ∧
      (.glob x ↦ .word mk ⋆ R).holds s')
    (WPr.call_spec (fun r => ∃ l g, r = .returned l g s.memory s.ffi [.word 0#64] ∧
      (.glob x ↦ .word mk ⋆ R).holds (⟨l, g, s.memory, s.ffi⟩ : St σ)) ?_ ?_ ?_ ?_) ?_
  · intro parameters cbody values cl hlk hvalues hbind
    obtain ⟨hb, hp⟩ := hdecl parameters cbody hlk
    subst hb
    obtain ⟨v, hv, rfl⟩ := evalArgs1_inv hvalues
    have := he v hv
    subst this
    rw [hp] at hbind
    simp [bindPanValueParameters] at hbind
    have hm : cl "m" = some (.word mk) := by
      rw [← hbind]
      simp (config := { decide := true }) [updatePanValueMap]
    refine WPr.seq_assign_global_at (s := ⟨cl, s.globals, s.memory, s.ffi⟩) (w := mk)
      (Assn.holds_congr rfl rfl h) (of_eval (by lk [hm])) Step.here (fun h' => ?_)
    exact WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ⟨_, _, rfl, Assn.holds_congr rfl rfl h'⟩
  · rintro l g m ffi vs ⟨l', g', heq, hh⟩
    injection heq with _ hg hm hf _
    subst hg hm hf
    exact ⟨_, rfl, Assn.holds_congr rfl rfl hh⟩
  · rintro l g m ffi exc v ⟨_, _, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨_, _, hC, -⟩
    cases hC
  · rintro _ ⟨g, rfl, hh⟩
    exact hq g hh

set_option maxHeartbeats 1000000 in
/-- The two releases at the end of `finish_child`: the parent `p` is the
running frame again. Before: `ev` and `cur_cont` already name the parent, the
arena pointers are still the child's, and the child's gap and suspended part
are owned. -/
theorem child_teardown (hE : GuestEnv E) {I : WInfo} {c p : Fr} {R : Assn} {q : Prog Word}
    (hokc : c.Ok I) (hl : Link c p)
    (hcm : s.locals "child_mark" = some (.word c.C.mark))
    (hcmm : s.locals "child_mem_mark" = some (.word c.C.mmark))
    (h : (.glob "scratch_ptr" ↦ .word c.X.pv ⋆ .glob "frame_mem_ptr" ↦ .word c.fv ⋆
      .glob "ev" ↦ .word p.e ⋆ .glob "cur_cont" ↦ .word p.Z.cc ⋆
      .glob "evm_empty" ↦ .word p.Z.ee ⋆ Assn.Range c.fv c.X.pv ⋆ c.susp ⋆ p.susp ⋆ R).holds s)
    (hq : ∀ g, (p.full ⋆ R).holds (⟨s.locals, g, s.memory, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, g, s.memory, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "scratch_release" [.var .local "child_mark"])
      (.seq (.call (some (none, none)) "frame_mem_release" [.var .local "child_mem_mark"]) q))
      Q := by
  refine WPr.seq_release hE 15 (fun parameters body hlk => by
      have hf := fun_of_index 15 hE.functions (by guest_decl_at 15) (by decide +kernel) hlk
      exact ⟨hf.1, hf.2⟩) (mk := c.C.mark) h (of_eval (by lk [hcm])) (fun g1 h1 => ?_)
  have h1' : (.glob "frame_mem_ptr" ↦ .word c.fv ⋆ (.glob "scratch_ptr" ↦ .word c.C.mark ⋆
      .glob "ev" ↦ .word p.e ⋆ .glob "cur_cont" ↦ .word p.Z.cc ⋆
      .glob "evm_empty" ↦ .word p.Z.ee ⋆ Assn.Range c.fv c.X.pv ⋆ c.susp ⋆ p.susp ⋆ R)).holds
      (⟨s.locals, g1, s.memory, s.ffi⟩ : St σ) := Assn.holds_perm h1 (by ac_rfl)
  refine WPr.seq_release hE 12 (fun parameters body hlk => by
      have hf := fun_of_index 12 hE.functions (by guest_decl_at 12) (by decide +kernel) hlk
      exact ⟨hf.1, hf.2⟩) (mk := c.C.mmark) h1' (of_eval (by lk [hcmm])) (fun g2 h2 => ?_)
  refine hq g2 ?_
  -- the child's region becomes the parent's gap
  have h3 : (Assn.Range c.fv c.X.pv ⋆ c.susp ⋆ (.glob "frame_mem_ptr" ↦ .word c.C.mmark ⋆
      .glob "scratch_ptr" ↦ .word c.C.mark ⋆ .glob "ev" ↦ .word p.e ⋆
      .glob "cur_cont" ↦ .word p.Z.cc ⋆ .glob "evm_empty" ↦ .word p.Z.ee ⋆ p.susp ⋆ R)).holds
      (⟨s.locals, g2, s.memory, s.ffi⟩ : St σ) := Assn.holds_perm h2 (by ac_rfl)
  have h4 := Fr.reclaim hokc hl h3
  rw [hl.mark, hl.mmark] at h4
  refine Assn.holds_perm h4 ?_
  rw [Fr.full_eq]
  unfold Fr.top
  ac_rfl

end InitECandidate.Solver.GuestBound
