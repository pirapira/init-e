import InitECandidate.Solver.GuestBound.WalkLoop

/-! # Iteration bound for walk loops -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A guard that compares the local `n` directly, so it evaluates only when `n` is a word. -/
def walkGuard : Exp Word → Option VarName
  | .cmp _ (.var .local n) _ => some n
  | .cmp _ _ (.var .local n) => some n
  | _ => none

/-- The loop walks one local through words, changing nothing else. -/
def walkLoop (c : Exp Word) (body : Prog Word) : Bool :=
  match walkGuard c with
  | some n => walkOk n body
  | none => false

theorem walk_guard_word (hE : WordEnv E) {c : Exp Word} {n : VarName}
    (hg : walkGuard c = some n) {s : St σ} {v : Word} {k : Nat}
    (h : E.cond s c = some (v, k)) : ∃ w, s.locals n = some (.word w) := by
  have he := cond_eval h
  unfold walkGuard at hg
  split at hg
  · simp only [Option.some.injEq] at hg
    subst hg
    obtain ⟨a, b, hl, -, -⟩ := cmp_eval hE he
    simp only [evalPanValueExp] at hl
    exact ⟨a, hl⟩
  · simp only [Option.some.injEq] at hg
    subst hg
    obtain ⟨a, b, -, hr, -⟩ := cmp_eval hE he
    simp only [evalPanValueExp] at hr
    exact ⟨b, hr⟩
  · cases hg

/-- Words inject into `Fin (2^64)`. -/
theorem word_toFin_injective :
    Function.Injective (fun w : Word => (⟨w.toNat, w.isLt⟩ : Fin (2 ^ 64))) :=
  fun _ _ hab => BitVec.eq_of_toNat_eq (by simpa using congrArg Fin.val hab)

noncomputable instance wordFintype : Fintype Word :=
  Fintype.ofInjective _ word_toFin_injective

theorem word_card : Fintype.card Word ≤ 2 ^ 64 := by
  have h := Fintype.card_le_of_injective _ word_toFin_injective
  simpa using h

section core
variable (hE : WordEnv E) {c : Exp Word} {body : Prog Word} {n : VarName} {b : Nat}
  (hg : walkGuard c = some n) (hw : walkOk n body = true) (hbody : Costs E body b)
  (base : St σ)

/-- The state with the word `w` in `n` and everything else as in `base`. -/
def stOf (base : St σ) (n : VarName) (w : Word) : St σ :=
  ⟨updatePanValueMap base.locals n (.word w), base.globals, base.memory, base.ffi⟩

/-- `s` is `base` except possibly at the local `n`. -/
def Agree (base : St σ) (n : VarName) (s : St σ) : Prop :=
  s.globals = base.globals ∧ s.memory = base.memory ∧ s.ffi = base.ffi ∧
    ∀ x, x ≠ n → s.locals x = base.locals x

theorem agree_eq {base s : St σ} {n : VarName} {w : Word} (ha : Agree base n s)
    (hn : s.locals n = some (.word w)) : s = stOf base n w := by
  obtain ⟨hg, hm, hf, hl⟩ := ha
  cases s with
  | mk locals globals memory ffi =>
    simp only at hg hm hf hl hn
    subst hg hm hf
    have hlocals : locals = updatePanValueMap base.locals n (.word w) := by
      funext x
      by_cases hx : x = n
      · subst hx
        rw [hn]
        simp [updatePanValueMap]
      · have hx' : (x == n) = false := by simpa using hx
        rw [hl x hx]
        simp [updatePanValueMap, hx']
    rw [hlocals]
    rfl

include hE hg hw hbody in
/-- With the words in `V` already visited by longer runs, the loop still has
at most `2^64 - |V|` iterations left. -/
theorem walk_core (r : Result σ) (hne : r.isError = false) :
    ∀ (fuel : Nat) (V : Finset Word) (s : St σ) (m : Nat),
      Agree base n s → E.run fuel s (.while c body) = some (r, m) →
      (∀ v ∈ V, ∃ fuel' m', fuel ≤ fuel' ∧ m < m' ∧
        E.run fuel' (stOf base n v) (.while c body) = some (r, m')) →
      m + V.card * (panValueExpStepCost c + b + 1) ≤
        2 ^ 64 * (panValueExpStepCost c + b + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro V s m _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro V s m hagree hrun0 hV
    have hrun := hrun0
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory c E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact Bool.noConfusion hne
    | some pair =>
      obtain ⟨v, kc⟩ := pair
      rw [hcond] at hrun
      have hkc : kc ≤ panValueExpStepCost c :=
        condCost (E := E) (fun _ => True) c s v kc trivial hcond
      obtain ⟨w, hsw⟩ := walk_guard_word hE hg hcond
      have hs : s = stOf base n w := agree_eq hagree hsw
      have hwV : w ∉ V := by
        intro hmem
        obtain ⟨fuel', m', hfuel, hlt, hrun'⟩ := hV w hmem
        have hsame := run_mono hfuel hrun0
        rw [hs, hrun'] at hsame
        simp only [Option.some.injEq, Prod.mk.injEq] at hsame
        omega
      have hcard : V.card + 1 ≤ 2 ^ 64 :=
        Nat.le_trans (Finset.card_lt_univ_of_notMem hwV) word_card
      have hroom : V.card * (panValueExpStepCost c + b + 1) + (panValueExpStepCost c + b + 1) ≤
          2 ^ 64 * (panValueExpStepCost c + b + 1) := by
        rw [← Nat.succ_mul]
        exact Nat.mul_le_mul_right _ hcard
      simp only [Option.elim_some] at hrun
      by_cases hv : (v == 0) = true
      · rw [if_pos hv] at hrun
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      · rw [if_neg hv] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi body (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at hrun
          have again : ∀ l g mem f, nb ≤ b → Agree base n ⟨l, g, mem, f⟩ →
              (do
                let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                  E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                  l g mem f (.while c body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                pure (loopResult, kc + nb + loopSteps + 1)) = some (r, m) →
              m + V.card * (panValueExpStepCost c + b + 1) ≤
                2 ^ 64 * (panValueExpStepCost c + b + 1) := by
            intro l g mem f hnb hagree' hrun
            cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g mem f
                (.while c body) (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                (memoryHandler := E.memoryHandler) with
            | none => rw [hloop] at hrun; simp at hrun
            | some pair =>
              obtain ⟨rl, nl⟩ := pair
              rw [hloop] at hrun
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              have hV' : ∀ v ∈ insert w V, ∃ fuel' m', fuel ≤ fuel' ∧ nl < m' ∧
                  E.run fuel' (stOf base n v) (.while c body) = some (rl, m') := by
                intro v hv
                rcases Finset.mem_insert.mp hv with rfl | hv
                · exact ⟨fuel + 1, _, Nat.le_succ _, by omega, hs ▸ hrun0⟩
                · obtain ⟨fuel', m', hfuel, hlt, hrun'⟩ := hV v hv
                  exact ⟨fuel', m', by omega, by omega, hrun'⟩
              have hih := ih (insert w V) ⟨l, g, mem, f⟩ nl hagree' hloop hV'
              rw [Finset.card_insert_of_notMem hwV, Nat.succ_mul] at hih
              omega
          have walk := walk_sound n fuel body s rb nb hw hb
          cases rb with
          | normal l g mem f =>
            have hnb : nb ≤ b := (hbody fuel s _ nb trivial hb rfl).1
            simp only [Walk] at walk
            obtain ⟨h1, h2, h3, h4⟩ := walk
            exact again l g mem f hnb ⟨h1.trans hagree.1, h2.trans hagree.2.1,
              h3.trans hagree.2.2.1, fun x hx => (h4 x hx).trans (hagree.2.2.2 x hx)⟩ hrun
          | continued l g mem f =>
            have hnb : nb ≤ b := (hbody fuel s _ nb trivial hb rfl).1
            simp only [Walk] at walk
            obtain ⟨h1, h2, h3, h4⟩ := walk
            exact again l g mem f hnb ⟨h1.trans hagree.1, h2.trans hagree.2.1,
              h3.trans hagree.2.2.1, fun x hx => (h4 x hx).trans (hagree.2.2.2 x hx)⟩ hrun
          | broke l g mem f =>
            have hnb : nb ≤ b := (hbody fuel s _ nb trivial hb rfl).1
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            omega
          | _ =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            have hnb : nb ≤ b := (hbody fuel s _ nb trivial hb hne).1
            omega

end core

/-- A walk loop costs at most `2^64` iterations of its guard and body. -/
theorem walkLoop_costs (hE : WordEnv E) (c : Exp Word) (body : Prog Word) (b : Nat)
    (hcheck : walkLoop c body = true) (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  unfold walkLoop at hcheck
  split at hcheck
  · rename_i n hg
    unfold Costs Triple
    intro fuel s r m _ hrun hne
    refine ⟨?_, trivial⟩
    rw [← stepCost_eq]
    have h := walk_core hE hg hcheck hbody s r hne fuel ∅ s m
      ⟨rfl, rfl, rfl, fun _ _ => rfl⟩ hrun (by intro v hv; simp at hv)
    simpa using h
  · cases hcheck

end InitECandidate.Solver.GuestBound
