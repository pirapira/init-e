import InitECandidate.Solver.GuestBound.OffsetLoop

/-! # Iteration bound for offset-guard loops -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The guard `i + k <=+ n`, as the parser normalises it. -/
def offsetExp (n i : VarName) (k : Word) : Exp Word :=
  .cmp .notLower (.var .local n) (.op .add [.var .local i, .const k])

/-- The counter, the limit and the step of an offset guard. -/
def offsetGuard : Exp Word → Option (VarName × VarName × Word)
  | .cmp .notLower (.var .local n) (.op .add [.var .local i, .const k]) => some (i, n, k)
  | _ => none

/-- The loop is `while i + k <=+ n { straight-line body that adds k to i and keeps n }`. -/
def offsetLoop (c : Exp Word) (body : Prog Word) : Bool :=
  match offsetGuard c with
  | some (i, n, k) =>
      straight body && (effect (.upBy k) i body).normal == .step &&
        (effect .up n body).normal == .keep
  | none => false

theorem offsetGuard_eq {c : Exp Word} {i n : VarName} {k : Word}
    (h : offsetGuard c = some (i, n, k)) : c = offsetExp n i k := by
  unfold offsetGuard at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · cases h

/-- The counter after `t` steps. -/
def stepN (k : Word) : Nat → Word → Word
  | 0, w => w
  | t + 1, w => stepN k t (w + k)

theorem stepN_eq (k : Word) : ∀ (t : Nat) (w : Word), stepN k t w = w + BitVec.ofNat 64 t * k
  | 0, w => by simp [stepN]
  | t + 1, w => by
      rw [stepN, stepN_eq k t (w + k)]
      have : BitVec.ofNat 64 (t + 1) = BitVec.ofNat 64 t + 1 := by
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [this]
      ring

theorem stepN_mod (k : Word) (t : Nat) (w : Word) : stepN k (t % 2 ^ 64) w = stepN k t w := by
  rw [stepN_eq, stepN_eq]
  congr 2
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

/-- `i + k` evaluates only when `i` is a word. -/
theorem add_eval (hE : WordEnv E) {s : St σ} {i : VarName} {k : Word} {x : PanValue Word}
    (h : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord (.op .add [.var .local i, .const k]) E.memoryAccess = some x) :
    ∃ w, s.locals i = some (.word w) ∧ x = .word (w + k) := by
  obtain ⟨access, hacc, hadd, -, -⟩ := hE.access
  rw [hacc] at h
  cases hl : s.locals i with
  | none => simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hl] at h
  | some v =>
    cases v with
    | word w =>
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hl, hadd] at h
      exact ⟨w, rfl, h.symm⟩
    | _ =>
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hl, panValueWordProjection] at h

/-- When the offset guard evaluates, both variables are words, and its value
is zero exactly when the limit is below `i + k`. -/
theorem offset_guard_val (hE : WordEnv E) {s : St σ} {n i : VarName} {k v : Word} {m : Nat}
    (h : E.cond s (offsetExp n i k) = some (v, m)) :
    ∃ w N, s.locals i = some (.word w) ∧ s.locals n = some (.word N) ∧
      ((v == 0) = true ↔ N < w + k) := by
  have he := cond_eval h
  obtain ⟨a, b, hl, hr, hx⟩ := cmp_eval hE he
  simp only [evalPanValueExp] at hl
  obtain ⟨w, hw, hb⟩ := add_eval hE hr
  simp only [PanValue.word.injEq] at hb hx
  subst hb
  subst hx
  refine ⟨w, a, hw, hl, ?_⟩
  by_cases hlt : a < w + k
  · simp [evalPanCmp, hlt]
  · simp [evalPanCmp, hlt]

section loop
variable (hE : WordEnv E) {n i : VarName} {k : Word} {body : Prog Word} {b : Nat}
  (hstraight : straight body = true)
  (hstep : (effect (.upBy k) i body).normal = .step)
  (hkeep : (effect .up n body).normal = .keep)

include hE hstep hkeep in
/-- One normal body run adds `k` to the counter and keeps the limit. -/
theorem offset_body {fuel : Nat} {s : St σ} {l g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {f : FfiState σ} {nb : Nat} {w N : Word}
    (hrun : E.run fuel s body = some (.normal l g m f, nb))
    (hw : s.locals i = some (.word w)) (hN : s.locals n = some (.word N)) :
    l i = some (.word (w + k)) ∧ l n = some (.word N) := by
  have p₁ := effect_sound hE (.upBy k) i fuel body s _ nb hrun
  have p₂ := effect_sound hE .up n fuel body s _ nb hrun
  simp only [PostR] at p₁ p₂
  rw [hstep] at p₁
  rw [hkeep] at p₂
  exact ⟨p₁ w hw, p₂ N hN⟩

include hE hstraight hstep hkeep in
/-- If the guard becomes false after `t` more steps, the loop takes at most
`t + 1` iterations. -/
theorem offset_bounded (hbody : Costs E body b) :
    ∀ (fuel t : Nat) (s : St σ) (w N : Word) (r : Result σ) (steps : Nat),
      s.locals i = some (.word w) → s.locals n = some (.word N) →
      N < stepN k t w + k →
      E.run fuel s (.while (offsetExp n i k) body) = some (r, steps) → r.isError = false →
      steps ≤ (t + 1) * (panValueExpStepCost (offsetExp n i k) + b + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro t s w N r steps _ _ _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro t s w N r steps hw hN hlt hrun hne
    have hpos : panValueExpStepCost (offsetExp n i k) + b + 1 ≤
        (t + 1) * (panValueExpStepCost (offsetExp n i k) + b + 1) :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory (offsetExp n i k) E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact Bool.noConfusion hne
    | some pair =>
      obtain ⟨v, kc⟩ := pair
      rw [hcond] at hrun
      have hkc : kc ≤ panValueExpStepCost (offsetExp n i k) :=
        condCost (E := E) (fun _ => True) _ s v kc trivial hcond
      obtain ⟨w', N', hw', hN', hiff⟩ := offset_guard_val hE hcond
      rw [hw] at hw'
      rw [hN] at hN'
      simp only [Option.some.injEq, PanValue.word.injEq] at hw' hN'
      subst hw' hN'
      simp only [Option.elim_some] at hrun
      by_cases hv : (v == 0) = true
      · rw [if_pos hv] at hrun
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      · rw [if_neg hv] at hrun
        have hge : ¬ N < w + k := fun h => hv (hiff.mpr h)
        cases t with
        | zero => exact absurd hlt hge
        | succ t =>
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi body (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            have pb := straight_sound fuel body s rb nb hstraight hb
            cases rb with
            | normal l g m f =>
              have hnb : nb ≤ b := (hbody fuel s _ nb trivial hb rfl).1
              obtain ⟨hl, hln⟩ := offset_body hE hstep hkeep hb hw hN
              simp only [Option.bind_eq_bind, Option.bind_some] at hrun
              cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                  E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f
                  (.while (offsetExp n i k) body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
              | none => rw [hloop] at hrun; simp at hrun
              | some pair =>
                obtain ⟨rl, nl⟩ := pair
                rw [hloop] at hrun
                simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                  Prod.mk.injEq] at hrun
                obtain ⟨rfl, rfl⟩ := hrun
                have hnl := ih t ⟨l, g, m, f⟩ (w + k) N rl nl hl hln hlt hloop hne
                have hsucc : (t + 1 + 1) * (panValueExpStepCost (offsetExp n i k) + b + 1) =
                    (t + 1) * (panValueExpStepCost (offsetExp n i k) + b + 1) +
                      (panValueExpStepCost (offsetExp n i k) + b + 1) := Nat.succ_mul _ _
                omega
            | error l g m f =>
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact Bool.noConfusion hne
            | _ => exact absurd pb (by simp [PanValueFfiControlResult.plain])

include hE hstraight hstep hkeep in
/-- If the guard never becomes false, the loop returns only `.error`. -/
theorem offset_never :
    ∀ (fuel : Nat) (s : St σ) (w N : Word) (r : Result σ) (steps : Nat),
      s.locals i = some (.word w) → s.locals n = some (.word N) →
      (∀ t, ¬ N < stepN k t w + k) →
      E.run fuel s (.while (offsetExp n i k) body) = some (r, steps) → r.isError = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro s w N r steps _ _ _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro s w N r steps hw hN hall hrun
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory (offsetExp n i k) E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      rfl
    | some pair =>
      obtain ⟨v, kc⟩ := pair
      rw [hcond] at hrun
      obtain ⟨w', N', hw', hN', hiff⟩ := offset_guard_val hE hcond
      rw [hw] at hw'
      rw [hN] at hN'
      simp only [Option.some.injEq, PanValue.word.injEq] at hw' hN'
      subst hw' hN'
      simp only [Option.elim_some] at hrun
      have hv : ¬ (v == 0) = true := fun h => hall 0 (hiff.mp h)
      rw [if_neg hv] at hrun
      cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
          s.memory s.ffi body (memoryAccess := E.memoryAccess)
          (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
      | none => rw [hb] at hrun; simp at hrun
      | some pair =>
        obtain ⟨rb, nb⟩ := pair
        rw [hb] at hrun
        have pb := straight_sound fuel body s rb nb hstraight hb
        cases rb with
        | normal l g m f =>
          obtain ⟨hl, hln⟩ := offset_body hE hstep hkeep hb hw hN
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f
              (.while (offsetExp n i k) body) (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hloop] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rl, nl⟩ := pair
            rw [hloop] at hrun
            simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih ⟨l, g, m, f⟩ (w + k) N rl nl hl hln (fun t => hall (t + 1)) hloop
        | error l g m f =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
            Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          rfl
        | _ => exact absurd pb (by simp [PanValueFfiControlResult.plain])

end loop

/-- An offset-guard loop costs at most `2^64` iterations of its guard and body. -/
theorem offsetLoop_costs (hE : WordEnv E) (c : Exp Word) (body : Prog Word) (b : Nat)
    (hcheck : offsetLoop c body = true) (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  unfold offsetLoop at hcheck
  split at hcheck
  · rename_i i n k hg
    have hc := offsetGuard_eq hg
    subst hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
    obtain ⟨⟨hstraight, hstep⟩, hkeep⟩ := hcheck
    unfold Costs Triple
    intro fuel s r steps _ hrun hne
    refine ⟨?_, trivial⟩
    rw [← stepCost_eq]
    by_cases hwords : ∃ w N, s.locals i = some (.word w) ∧ s.locals n = some (.word N)
    · obtain ⟨w, N, hw, hN⟩ := hwords
      by_cases ht : ∃ t, N < stepN k t w + k
      · obtain ⟨t, ht⟩ := ht
        have hmod : N < stepN k (t % 2 ^ 64) w + k := by rw [stepN_mod]; exact ht
        have hle := offset_bounded hE hstraight hstep hkeep hbody fuel (t % 2 ^ 64) s w N r steps
          hw hN hmod hrun hne
        have hlt : t % 2 ^ 64 + 1 ≤ 2 ^ 64 := Nat.mod_lt _ (by decide)
        exact Nat.le_trans hle (Nat.mul_le_mul_right _ hlt)
      · have herr := offset_never hE hstraight hstep hkeep fuel s w N r steps hw hN
          (fun t h => ht ⟨t, h⟩) hrun
        rw [herr] at hne
        cases hne
    · cases fuel with
      | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
      | succ fuel =>
        simp only [Env.run] at hrun
        rw [evalPanValueFfiProgSteps] at hrun
        cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
            s.locals s.globals s.memory (offsetExp n i k) E.memoryAccess with
        | none =>
          rw [hcond] at hrun
          simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact Bool.noConfusion hne
        | some pair =>
          obtain ⟨v, kc⟩ := pair
          obtain ⟨w, N, hw, hN, -⟩ := offset_guard_val hE hcond
          exact absurd ⟨w, N, hw, hN⟩ hwords
  · cases hcheck

end InitECandidate.Solver.GuestBound
