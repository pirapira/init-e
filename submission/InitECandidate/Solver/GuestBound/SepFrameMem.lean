import InitECandidate.Solver.GuestBound.SepFrameOp2

/-!
# The frame-memory allocator as a framed specification

`frame_mem_alloc(n)` returns the old `frame_mem_ptr` and advances it to the
next multiple of 8 at or above `frame_mem_ptr + n`, trapping when that would
pass `scratch_ptr`. It touches no memory.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `g = e; rest` for an owned global. -/
theorem WPr.seq_assign_global_at {x : VarName} {e : Exp Word} {q : Prog Word} {w : Word}
    {A A' R : Assn} (h : (A ⋆ R).holds s) (he : ∀ y, E.eval s e = some y → y = .word w)
    (hstep : Step (.glob x) (.word w) A A')
    (hq : (A' ⋆ R).holds
        (⟨s.locals, updatePanValueMap s.globals x (.word w), s.memory, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, updatePanValueMap s.globals x (.word w), s.memory, s.ffi⟩ q Q) :
    WPr E s (.seq (.assign .global x e) q) Q := by
  refine WPr.seq (fun s' => s' = ⟨s.locals, updatePanValueMap s.globals x (.word w), s.memory,
    s.ffi⟩) ?_ (by rintro _ rfl; exact hq (Assn.setGlobal_at h hstep))
  intro r hr
  rw [runs_assign_global] at hr
  cases hy : E.eval s e with
  | none => rw [hy] at hr; simp only at hr; subst hr; exact Or.inl rfl
  | some y =>
    have := he y hy
    subst this
    rw [hy] at hr
    simp only at hr
    split at hr
    · subst hr; exact Or.inr rfl
    · subst hr; exact Or.inl rfl

set_option maxHeartbeats 1000000 in
/-- `frame_mem_alloc(n)`. -/
theorem frame_mem_alloc_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "frame_mem_alloc" E.functions = some (parameters, body))
    (s : St σ) (pv fv nv : Word) (hn : s.locals "n" = some (.word nv))
    (hfp : fv.toNat ≤ pv.toNat) (hpv : pv.toNat ≤ 2 ^ 62) :
    WPFt E s body (ArenaPtrs pv fv) (fun r => Assn.ex fun qv : Word =>
      ⌜(fv.toNat + nv.toNat ≤ qv.toNat ∧ qv.toNat ≤ pv.toNat ∧ qv.toNat % 8 = 0) ∧
        ∃ l g m, r = .returned l g m s.ffi [.word fv]⌝ ⋆ ArenaPtrs pv qv) := by
  have hbody := (fun_of_index 10 hE.functions (by guest_decl_at 10) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  unfold ArenaPtrs at hR
  dsimp only
  have hsp : s.globals "scratch_ptr" = some (.word pv) := Assn.glob_at hR (by look)
  have hfm : s.globals "frame_mem_ptr" = some (.word fv) := Assn.glob_at hR (by look)
  refine WPr.dec_ev (fun v hv => ?_)
  have hp := (of_eval (w := fv) (by rw [eval_global]; exact hfm)) v hv
  subst hp
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap s.locals "p" (.word fv), s.globals,
      s.memory, s.ffi⟩ ∧ nv.toNat ≤ pv.toNat - fv.toNat) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .lower)
      (of_eval (w := pv - fv) (by ev [eval_global, hsp]))
      (of_eval (w := nv) (by lk [hn])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      have hnl := lower_zero hcv.symm
      refine WPr.skip ⟨rfl, ?_⟩
      have : ¬ (pv - fv).toNat < nv.toNat := fun h => hnl (BitVec.lt_def.mpr h)
      have : (pv - fv).toNat = pv.toNat - fv.toNat := by bv_omega
      omega
    · refine WPr.trap_call hE (fun r hr => ?_)
      cases r <;> first
        | exact hr.elim
        | (simp only [restorePanValueFfiLocal]; exact Or.inl hr)
  rintro _ ⟨rfl, hfit⟩
  refine WPr.dec_ev (fun v hv => ?_)
  have hq := (of_eval (w := AndOp.and (fv + (nv + (7#64 + 0)))
    (AndOp.and (0#64 - 8#64) (~~~(0 : BitVec 64)))) (by ev [hn])) v hv
  subst hq
  have hm8 := and_m8 (fv + (nv + (7#64 + 0)))
  have hx : (fv + (nv + (7#64 + 0))).toNat = fv.toNat + nv.toNat + 7 := by bv_omega
  rw [hx] at hm8
  generalize hqd : (AndOp.and (fv + (nv + (7#64 + 0))) (AndOp.and (0#64 - 8#64)
    (~~~(0 : BitVec 64)))) = q at hm8 ⊢
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap (updatePanValueMap s.locals "p" (.word fv))
      "q" (.word q), s.globals, s.memory, s.ffi⟩ ∧ q.toNat ≤ pv.toNat)
    (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .lower)
      (of_eval (w := pv) (by rw [eval_global]; exact hsp))
      (of_eval (w := q) (by lk [])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      have hnl := lower_zero hcv.symm
      exact WPr.skip ⟨rfl, Nat.le_of_not_lt (fun h => hnl (BitVec.lt_def.mpr h))⟩
    · refine WPr.trap_call hE (fun r hr => ?_)
      cases r <;> first
        | exact hr.elim
        | (simp only [restorePanValueFfiLocal]; exact Or.inl hr)
  rintro _ ⟨rfl, hqp⟩
  refine WPr.seq_assign_global_at hR (w := q) (of_eval (by lk [])) (by step) (fun h' => ?_)
  refine WPr.ret (w := fv) (of_eval (by lk [])) ?_
  simp only [restorePanValueFfiLocal]
  refine Or.inr (Assn.holdsV_ex.mpr ⟨q, Assn.holds_pure_intro ⟨⟨?_, hqp, ?_⟩, _, _, _, rfl⟩
    (Assn.holds_congr rfl rfl h')⟩)
  · rw [hm8]; omega
  · rw [hm8]; omega

end InitECandidate.Solver.GuestBound
