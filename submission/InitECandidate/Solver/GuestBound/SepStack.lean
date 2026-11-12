import InitECandidate.Solver.GuestBound.SepBridge

/-!
# `stack_push` as a framed specification

The EVM stack of a frame is a buffer of `cap` 32-byte slots in the scratch
arena. `stack_push` stores at slot `sp`; when `sp = cap` it first allocates a
buffer of twice the size (at most 1024 slots) with `scratch_alloc`, copies the
old one, and switches to it. The old buffer and the unused tail of the
allocation stay owned: they are returned when the frame's scratch mark is
released.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem Step.left {k : Key} {w : PanValue Word} {X X' Y : Assn} (h : Step k w X X') :
    Step k w (X ⋆ Y) (X' ⋆ Y) := by
  intro V V' R hu hV
  rw [Assn.sep_assoc] at hV ⊢
  exact h V V' _ hu hV

theorem Assn.holds_assoc_r {P A R : Assn} {s : St σ} (h : ((P ⋆ A) ⋆ R).holds s) :
    (P ⋆ A ⋆ R).holds s := by
  unfold Assn.holds at h ⊢
  rw [Assn.sep_assoc] at h
  exact h

theorem Assn.holds_assoc_l {P A R : Assn} {s : St σ} (h : (P ⋆ A ⋆ R).holds s) :
    ((P ⋆ A) ⋆ R).holds s := by
  unfold Assn.holds at h ⊢
  rw [Assn.sep_assoc]
  exact h

/-- `st a, v` as a last statement, into an owned cell. -/
theorem WPr.store_at (hE : GuestEnv E) {a val : Exp Word} {addr w : Word}
    {A A' R : Assn} (h : (A ⋆ R).holds s)
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : ∀ y, E.eval s val = some y → y = .word w)
    (hstep : Step (.mem addr) (.word w) A A')
    (hq : ∀ m, (A' ⋆ R).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      Q (.normal s.locals s.globals m s.ffi)) :
    WPr E s (.store a val) Q := by
  intro r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  rcases store_word_inv hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · exact Or.inl herr
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  have := hv y hy
  subst this
  have hm' := hm w rfl
  subst hm'
  exact Or.inr (hq _ (hstep _ _ _ (upd_setCell s addr' w s.locals s.ffi) h))

/-- `x = e` as a last statement, for a word-valued local `x`. -/
theorem WPr.assign_local {x : VarName} {e : Exp Word} {old w : Word}
    (hx : s.locals x = some (.word old)) (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : Q (.normal (updatePanValueMap s.locals x (.word w)) s.globals s.memory s.ffi)) :
    WPr E s (.assign .local x e) Q := by
  intro r hr
  rw [runs_assign_local] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl rfl
  | some y =>
    have := he y hv
    subst this
    rw [hv] at hr
    simp only [panValueAssignmentValid, hx, shape_word, shape_matches_self, if_true] at hr
    subst hr
    exact Or.inr h

/-- Evaluate an expression of locals, constants and `*`. -/
macro "pan" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := { decide := true }) [evalF_panOp, evalArgs_cons, evalArgs_nil, evalF_local,
    update_lookup, evalPanOp, $hs,*])

/-- The bounds the stack of a frame and the scratch arena satisfy. -/
structure StackOk (sp cap base pv fv : Word) : Prop where
  cap_pos : 0 < cap.toNat
  cap_le : cap.toNat ≤ 1024
  sp_le : sp.toNat ≤ cap.toNat
  base_al : base.toNat % 8 = 0
  base_hi : base.toNat + 32 * cap.toNat ≤ 2 ^ 62
  fp : fv.toNat ≤ pv.toNat
  pv_hi : pv.toNat ≤ 2 ^ 62

/-- The tail of `stack_push`: store the value at slot `sp` and bump `sp`. -/
theorem stack_push_tail (hE : GuestEnv E) {a : St σ} {e sp cap b hiw w0 w1 w2 w3 : Word}
    {Rest R : Assn} (hsp : a.locals "sp" = some (.word sp))
    (hv : a.locals "v" = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (h : ((Assn.Range b hiw ⋆ .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word sp ⋆
      .mem (e + 232#64) ↦ .word cap ⋆ .mem (e + 8#64) ↦ .word b ⋆ Rest) ⋆ R).holds a)
    (hlt : sp.toNat < cap.toNat) (hcap : cap.toNat ≤ 1024)
    (hhi : hiw.toNat = b.toNat + 32 * cap.toNat) (hb : b.toNat + 32 * cap.toNat ≤ 2 ^ 62) :
    WPr E a
      (.seq (.ite (.cmp .equal (.var .local "sp") (.const 1024#64))
          (.raise "EvmErr" (.const 3#64)) .skip)
        (.seq (.store (.op .add [.load .one (.op .add [.var .global "ev", .const 8#64]),
            .panOp .mul [.var .local "sp", .const 32#64]]) (.var .local "v"))
          (.seq (.store (.op .add [.var .global "ev", .const 16#64])
              (.op .add [.var .local "sp", .const 1#64]))
            (.return (.const 0#64)))))
      (fun r => ∃ l g m, r = .returned l g m a.ffi [.word 0#64] ∧
        ((Assn.Range b hiw ⋆ .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word (sp + 1#64) ⋆
          .mem (e + 232#64) ↦ .word cap ⋆ .mem (e + 8#64) ↦ .word b ⋆ Rest) ⋆ R).holds r.st) := by
  have hev : a.globals "ev" = some (.word e) := Assn.glob_at h (by look)
  refine WPr.seq (fun s' => s' = a) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .equal) (of_eval (w := sp) (by lk [hsp]))
      (of_eval (w := 1024#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · exact WPr.skip rfl
    · rename_i h0
      have hz : sp = 1024#64 := by
        by_contra hne
        exact h0 (by rw [hcv]; simp [evalPanCmp, hne])
      subst hz
      exact absurd hlt (by simp; omega)
  rintro _ rfl
  have a0 : (b + sp * 32#64).toNat = b.toNat + 32 * sp.toNat := by bv_omega
  have a1 : (b + sp * 32#64 + 8#64).toNat = b.toNat + 32 * sp.toNat + 8 := by bv_omega
  have a2 : (b + sp * 32#64 + 8#64 + 8#64).toNat = b.toNat + 32 * sp.toNat + 16 := by bv_omega
  have a3 : (b + sp * 32#64 + 8#64 + 8#64 + 8#64).toNat = b.toNat + 32 * sp.toNat + 24 := by
    bv_omega
  refine WPr.seq_store4_at hE h (addr := b + sp * 32#64)
    (eval_add2_inv hE
      (eval_load_at hE (addr := e + 8#64) (of_eval (by ev [eval_global, hev])) h (by look))
      (of_eval (w := sp * 32#64) (by pan [hsp])))
    (fun y hy => by rw [evalF_local, hv] at hy; exact (Option.some.inj hy).symm)
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega))) (fun m1 h1 => ?_)
  refine WPr.seq_store_at hE h1 (addr := e + 16#64) (w := sp + 1#64)
    (of_eval (by ev [eval_global, hev])) (of_eval (by ev [hsp])) (by step) (fun m2 h2 => ?_)
  exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
    ⟨_, _, _, rfl, Assn.holds_congr rfl rfl h2⟩

end InitECandidate.Solver.GuestBound
