import InitECandidate.Solver.GuestBound.SepAt

/-!
# `credit_state_gas_refund` as a framed specification

The refund first undoes what was spilled into gas left (so gas left grows by
`min amount spilled` and spilled shrinks by the same), and the rest goes to the
state-gas reservoir. Gas left plus spilled is unchanged.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A declaring call whose callee satisfies `C` on every result other than `.error`. -/
theorem WPr.decCall_spec {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} (C : Result σ → Prop)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody C)
    (hret : ∀ l g m ffi v, C (.returned l g m ffi [v]) →
      WPr E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r')))
    (hraise : ∀ l g m ffi exc v, C (.raised l g m ffi exc v) →
      Q (.raised (fun _ => none) g m ffi exc v))
    (hffi : ∀ l g m ffi ev, C (.finalFfi l g m ffi ev) → Q (.finalFfi (fun _ => none) g m ffi ev)) :
    WPr E s (.decCall x sh f args body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl herr
  have hcal := hc parameters cbody values cl hlookup hvalues hbind rb hcallee
  cases rb with
  | returned lr g m ffi vs =>
    cases vs with
    | nil => exact hout.elim
    | cons v rest =>
      cases rest with
      | cons v' rest' => exact hout.elim
      | nil =>
        obtain ⟨r', -, hrun', rfl⟩ := hout
        rcases hcal with he | hC
        · cases he
        rcases hret lr g m ffi v hC r' hrun' with he | hq
        · exact Or.inl (isError_restore he)
        · exact Or.inr hq
  | raised lr g m ffi ex v =>
    simp only at hout
    subst hout
    rcases hcal with he | hC
    · cases he
    · exact Or.inr (hraise lr g m ffi ex v hC)
  | finalFfi lr g m ffi ev =>
    simp only at hout
    subst hout
    rcases hcal with he | hC
    · cases he
    · exact Or.inr (hffi lr g m ffi ev hC)
  | _ => exact hout.elim

/-- `min(a, b)` returns the smaller word and changes nothing. -/
theorem min_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "min" E.functions = some (parameters, body))
    (c : St σ) (a b : Word) (ha : c.locals "a" = some (.word a))
    (hb : c.locals "b" = some (.word b)) :
    WPr E c body (fun r => ∃ l, r = .returned l c.globals c.memory c.ffi
      [.word (if a < b then a else b)]) := by
  have hbody := (fun_of_index 31 hE.functions (by guest_decl_at 31) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.seq (fun s' => s' = c ∧ ¬ a < b) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := a) (by lk [ha]))
      (of_eval (w := b) (by lk [hb])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      exact WPr.skip ⟨rfl, lower_zero hcv.symm⟩
    · rename_i h0
      have hlt : a < b := by
        by_contra hlt
        exact h0 (by rw [hcv]; simp [evalPanCmp, hlt])
      refine WPr.ret (w := a) (of_eval (by lk [ha])) ?_
      exact ⟨_, by rw [if_pos hlt]⟩
  rintro _ ⟨rfl, hge⟩
  refine WPr.ret (w := b) (of_eval (by lk [hb])) ?_
  exact ⟨_, by rw [if_neg hge]⟩

/-- The gas fields that a state-gas refund touches. -/
def RefundGas (e gl sgl sp : Word) : Assn :=
  .glob "ev" ↦ .word e ⋆ .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 72#64) ↦ .word sgl ⋆
    .mem (e + 192#64) ↦ .word sp

/-- `credit_state_gas_refund(amount)`. With `f = min amount spilled`: gas left
grows by `f`, spilled shrinks by `f`, the reservoir grows by `amount - f`. -/
theorem credit_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "credit_state_gas_refund" E.functions = some (parameters, body))
    (s : St σ) (e gl sgl sp a : Word) (ha : s.locals "amount" = some (.word a)) :
    WPFr E s body (RefundGas e gl sgl sp)
      (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        RefundGas e (gl + (if a < sp then a else sp)) (sgl + (a - (if a < sp then a else sp)))
          (sp - (if a < sp then a else sp))) := by
  have hbody := (fun_of_index 450 hE.functions (by guest_decl_at 450) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  unfold RefundGas at hR
  dsimp only
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hR (by look)
  refine WPr.dec_ev (fun v hv => ?_)
  have hm := eval_load_at hE (addr := e + 192#64) (v := .word sp)
    (of_eval (by ev [eval_global, hev])) hR (by look) v hv
  subst hm
  have h1 := Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "spilled" (.word sp),
    s.globals, s.memory, s.ffi⟩ : St σ)) rfl rfl hR
  refine WPr.decCall_spec (fun rb => ∃ l, rb = .returned l s.globals s.memory s.ffi
      [.word (if a < sp then a else sp)]) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 31 hE.functions (by guest_decl_at 31) (by decide +kernel)
      hlk).2
    have hvals : values = [.word a, .word sp] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil,
        update_lookup, ha] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact min_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ a sp
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  · rintro l g m ffi v ⟨l', hC⟩
    injection hC with _ hg hm hf hv
    subst hg hm hf
    simp only [List.cons.injEq, and_true] at hv
    subst hv
    generalize hfdef : (if a < sp then a else sp) = f at *
    have h2 := Assn.holds_congr (s' := (⟨updatePanValueMap
      (updatePanValueMap s.locals "spilled" (.word sp)) "from_gl" (.word f),
      s.globals, s.memory, s.ffi⟩ : St σ)) rfl rfl hR
    refine WPr.seq_store_at hE h2 (addr := e + 64#64) (w := gl + f)
      (of_eval (by ev [eval_global, hev]))
      (eval_add2_inv hE
        (eval_load_at hE (addr := e + 64#64) (of_eval (by ev [eval_global, hev])) h2 (by look))
        (of_eval (by lk [])))
      (by step) (fun m1 h3 => ?_)
    refine WPr.seq_store_at hE h3 (addr := e + 192#64) (w := sp - f)
      (of_eval (by ev [eval_global, hev])) (of_eval (by ev []))
      (by step) (fun m2 h4 => ?_)
    refine WPr.seq_store_at hE h4 (addr := e + 72#64) (w := sgl + (a - f))
      (of_eval (by ev [eval_global, hev]))
      (eval_add2_inv hE
        (eval_load_at hE (addr := e + 72#64) (of_eval (by ev [eval_global, hev])) h4 (by look))
        (of_eval (by ev [ha])))
      (by step) (fun m3 h5 => ?_)
    refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    show ((⌜_⌝ ⋆ RefundGas _ _ _ _) ⋆ R).holds _
    rw [Assn.sep_assoc]
    exact Assn.holdsV_pure.mpr ⟨⟨_, _, _, rfl⟩, Assn.holds_congr rfl rfl h5⟩
  · rintro l g m ffi exc v ⟨l', hC⟩
    cases hC
  · rintro l g m ffi ev ⟨l', hC⟩
    cases hC

end InitECandidate.Solver.GuestBound
