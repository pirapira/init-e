import InitECandidate.Solver.GuestBound.SepCredit

/-!
# `charge_state_gas` as a framed specification

State gas is taken from the reservoir first. What the reservoir cannot cover is
taken from gas left and recorded as spilled, so gas left plus spilled is
unchanged. When both together are too small the call raises with nothing
changed.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `add_sat(a, b)` changes nothing and returns at most the sum. -/
theorem add_sat_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "add_sat" E.functions = some (parameters, body))
    (c : St σ) (a b : Word) (ha : c.locals "a" = some (.word a))
    (hb : c.locals "b" = some (.word b)) :
    WPr E c body (fun r => ∃ l t, r = .returned l c.globals c.memory c.ffi [.word t] ∧
      t.toNat ≤ a.toNat + b.toNat) := by
  have hbody := (fun_of_index 441 hE.functions (by guest_decl_at 441) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.dec_ev (fun v hv => ?_)
  have hs := (of_eval (w := a + b) (by ev [ha, hb])) v hv
  subst hs
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap c.locals "s" (.word (a + b)), c.globals,
      c.memory, c.ffi⟩ ∧ ¬ (a + b) < a) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := a + b) (by lk []))
      (of_eval (w := a) (by lk [ha])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      exact WPr.skip ⟨rfl, lower_zero hcv.symm⟩
    · rename_i h0
      have hlt : a + b < a := by
        by_contra hlt
        exact h0 (by rw [hcv]; simp [evalPanCmp, hlt])
      refine WPr.ret (w := 18446744073709551615#64) (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨_, _, rfl, ?_⟩
      bv_omega
  rintro _ ⟨rfl, hge⟩
  refine WPr.ret (w := a + b) (of_eval (by lk [])) ?_
  simp only [restorePanValueFfiLocal]
  refine ⟨_, _, rfl, ?_⟩
  bv_omega

/-- `charge_state_gas(amount)`: from the reservoir when it suffices; otherwise
the reservoir is emptied and the rest moves from gas left to spilled; otherwise
it raises with nothing changed. -/
theorem charge_state_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "charge_state_gas" E.functions = some (parameters, body))
    (s : St σ) (e gl sgl sp a : Word) (ha : s.locals "amount" = some (.word a)) :
    WPFr E s body (RefundGas e gl sgl sp) (fun r => Assn.or
      (⌜¬ sgl < a ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        RefundGas e gl (sgl - a) sp)
      (Assn.or
        (⌜(sgl < a ∧ (a - sgl).toNat ≤ gl.toNat) ∧
            ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
          RefundGas e (gl - (a - sgl)) 0#64 (sp + (a - sgl)))
        (⌜sgl < a ∧ ∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 4#64)⌝ ⋆
          RefundGas e gl sgl sp))) := by
  have hbody := (fun_of_index 449 hE.functions (by guest_decl_at 449) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  unfold RefundGas at hR
  dsimp only
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hR (by look)
  refine WPr.dec_ev (fun v hv => ?_)
  have hm := eval_load_at hE (addr := e + 72#64) (v := .word sgl)
    (of_eval (by ev [eval_global, hev])) hR (by look) v hv
  subst hm
  refine WPr.dec_ev (fun v hv => ?_)
  have hm := eval_load_at hE (addr := e + 64#64) (v := .word gl)
    (of_eval (by ev [eval_global, hev]))
    (Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "sgl" (.word sgl), s.globals,
      s.memory, s.ffi⟩ : St σ)) rfl rfl hR) (by look) v hv
  subst hm
  have h2 := Assn.holds_congr (s' := (⟨updatePanValueMap
    (updatePanValueMap s.locals "sgl" (.word sgl)) "gl" (.word gl), s.globals, s.memory,
    s.ffi⟩ : St σ)) rfl rfl hR
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap
      (updatePanValueMap s.locals "sgl" (.word sgl)) "gl" (.word gl), s.globals, s.memory,
      s.ffi⟩ ∧ sgl < a) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .notLower) (of_eval (w := sgl) (by lk []))
      (of_eval (w := a) (by lk [ha])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      exact WPr.skip ⟨rfl, cmp_notLower_zero hcv.symm⟩
    · rename_i h0
      have hge : ¬ sgl < a := cmp_notLower_ne (by rw [← hcv]; exact h0)
      refine WPr.seq_store_at hE h2 (addr := e + 72#64) (w := sgl - a)
        (of_eval (by ev [eval_global, hev])) (of_eval (by ev [ha]))
        (by step) (fun m1 h3 => ?_)
      refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      refine Assn.holds_or_left ?_
      rw [Assn.sep_assoc]
      exact Assn.holdsV_pure.mpr ⟨⟨hge, _, _, _, rfl⟩, Assn.holds_congr rfl rfl h3⟩
  rintro _ ⟨rfl, hlt⟩
  refine WPr.decCall_spec (fun rb => ∃ l t, rb = .returned l s.globals s.memory s.ffi
      [.word t] ∧ t.toNat ≤ sgl.toNat + gl.toNat) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 441 hE.functions (by guest_decl_at 441) (by decide +kernel)
      hlk).2
    have hvals : values = [.word sgl, .word gl] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, update_lookup]
        at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact add_sat_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ sgl gl
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  · rintro l g m ffi v ⟨l', t, hC, ht⟩
    injection hC with _ hg hm hf hv
    subst hg hm hf
    simp only [List.cons.injEq, and_true] at hv
    subst hv
    have h3 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap
      (updatePanValueMap s.locals "sgl" (.word sgl)) "gl" (.word gl)) "tot" (.word t),
      s.globals, s.memory, s.ffi⟩ : St σ)) rfl rfl hR
    refine WPr.seq (fun s' => s' = ⟨updatePanValueMap (updatePanValueMap
        (updatePanValueMap s.locals "sgl" (.word sgl)) "gl" (.word gl)) "tot" (.word t),
        s.globals, s.memory, s.ffi⟩ ∧ t < a) (WPr.ite_both (fun w hw => ?_)) ?_
    · have hcv := eval_cmp_inv hE (op := .notLower) (of_eval (w := t) (by lk []))
        (of_eval (w := a) (by lk [ha])) _ hw
      simp only [PanValue.word.injEq] at hcv
      split
      · rename_i h0
        rw [h0] at hcv
        exact WPr.skip ⟨rfl, cmp_notLower_zero hcv.symm⟩
      · rename_i h0
        have hge : ¬ t < a := cmp_notLower_ne (by rw [← hcv]; exact h0)
        have hrem : (a - sgl).toNat ≤ gl.toNat := by bv_omega
        refine WPr.dec_ev (fun v hv => ?_)
        have hr := (of_eval (w := a - sgl) (by ev [ha])) v hv
        subst hr
        have h4 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap
          (updatePanValueMap (updatePanValueMap s.locals "sgl" (.word sgl)) "gl" (.word gl))
          "tot" (.word t)) "rem" (.word (a - sgl)), s.globals, s.memory, s.ffi⟩ : St σ))
          rfl rfl hR
        refine WPr.seq_store_at hE h4 (addr := e + 72#64) (w := 0#64)
          (of_eval (by ev [eval_global, hev])) (of_eval (eval_const _ _))
          (by step) (fun m1 h5 => ?_)
        refine WPr.seq_store_at hE h5 (addr := e + 64#64) (w := gl - (a - sgl))
          (of_eval (by ev [eval_global, hev])) (of_eval (by ev []))
          (by step) (fun m2 h6 => ?_)
        refine WPr.seq_store_at hE h6 (addr := e + 192#64) (w := sp + (a - sgl))
          (of_eval (by ev [eval_global, hev]))
          (eval_add2_inv hE
            (eval_load_at hE (addr := e + 192#64) (of_eval (by ev [eval_global, hev])) h6
              (by look))
            (of_eval (by lk [])))
          (by step) (fun m3 h7 => ?_)
        refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
        simp only [restorePanValueFfiLocal]
        refine Assn.holds_or_right (Assn.holds_or_left ?_)
        rw [Assn.sep_assoc]
        exact Assn.holdsV_pure.mpr ⟨⟨⟨hlt, hrem⟩, _, _, _, rfl⟩, Assn.holds_congr rfl rfl h7⟩
    rintro _ ⟨rfl, htlt⟩
    refine WPr.seq (fun _ => False) (WPr.raise (fun v hv => ?_)) (fun _ h => h.elim)
    rw [eval_const] at hv
    cases hv
    simp only [restorePanValueFfiLocal]
    refine Assn.holds_or_right (Assn.holds_or_right ?_)
    rw [Assn.sep_assoc]
    exact Assn.holdsV_pure.mpr ⟨⟨hlt, _, _, _, rfl⟩, Assn.holds_congr rfl rfl hR⟩
  · rintro l g m ffi exc v ⟨l', t, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', t, hC, -⟩
    cases hC

end InitECandidate.Solver.GuestBound
