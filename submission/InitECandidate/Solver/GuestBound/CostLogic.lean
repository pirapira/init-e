import Flapjack.PanValueFfiSemantics
import Flapjack.RiscV.Model

/-!
# Cost triples for the stepped Pancake evaluator

A quantitative partial-correctness Hoare logic over
`Flapjack.evalPanValueFfiProgSteps`. `Triple E P p B Q` says: every run of `p`
from a state satisfying `P` that returns a result returns a step count of at
most `B` and a result satisfying `Q`. It does not claim termination or memory
safety. See pirapira/init-e#2 for the plan this module starts.

The step count is the index `B`; allocation and other resources are state, so
they are bounded through `Q` with the same rules.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

abbrev Word := Flapjack.RiscV.Word 64

/-- The fixed parameters of the stepped evaluator. -/
structure Env (σ : Type) where
  context : PanValueFfiContext Word
  primitive : PanPrimitiveHandler Word
  handler : PanValueStatefulFfiHandler Word σ
  structs : StructContext
  functions : List (FunName × List VarName × Prog Word)
  baseAddress : Word
  topAddress : Word
  bytesInWord : Word
  memoryAccess : Option (PanValueMemoryAccess Word)
  contracts : Option PanValueCallContracts
  memoryHandler : Option (PanValueMemoryFfiHandler Word σ)

/-- The mutable part of an evaluator configuration. -/
structure St (σ : Type) where
  locals : VarName → Option (PanValue Word)
  globals : VarName → Option (PanValue Word)
  memory : Word → Option (PanValue Word)
  ffi : FfiState σ

abbrev Result (σ : Type) := PanValueFfiControlResult Word σ

/-- The state a control result carries. -/
def Result.st {σ : Type} : Result σ → St σ
  | .normal l g m f | .error l g m f | .returned l g m f _ | .raised l g m f _ _
  | .broke l g m f | .continued l g m f | .finalFfi l g m f _ => ⟨l, g, m, f⟩

/-- The result is the evaluator's `.error` outcome (a failing source semantics). -/
def _root_.Flapjack.PanValueFfiControlResult.isError {σ : Type} : Result σ → Bool
  | .error _ _ _ _ => true
  | _ => false

namespace Env
variable {σ : Type} (E : Env σ)

/-- `evalPanValueFfiProgSteps` at the environment's parameters. -/
def run (fuel : Nat) (s : St σ) (p : Prog Word) : Option (Result σ × Nat) :=
  evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs E.functions
    E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi p
    (memoryAccess := E.memoryAccess) (contracts := E.contracts)
    (memoryHandler := E.memoryHandler)

/-- Counted evaluation of an `if`/`while` condition. -/
def cond (s : St σ) (c : Exp Word) : Option (Word × Nat) :=
  panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
    s.locals s.globals s.memory c E.memoryAccess

end Env

/-- Every run of `p` from a `P`-state that returns a result other than `.error`
takes at most `B` steps and ends in `Q`. An `.error` result is a failing source
semantics, which the challenge does not cover, so such runs are left unbounded. -/
def Triple {σ : Type} (E : Env σ) (P : St σ → Prop) (p : Prog Word) (B : Nat)
    (Q : Result σ → Prop) : Prop :=
  ∀ fuel s r n, P s → E.run fuel s p = some (r, n) → r.isError = false → n ≤ B ∧ Q r

/-- An unconditional step bound. -/
def Costs {σ : Type} (E : Env σ) (p : Prog Word) (B : Nat) : Prop :=
  Triple E (fun _ => True) p B (fun _ => True)

/-- `c` takes at most `e` counted expression steps in every `P`-state. -/
def CondCost {σ : Type} (E : Env σ) (P : St σ → Prop) (c : Exp Word) (e : Nat) : Prop :=
  ∀ s v k, P s → E.cond s c = some (v, k) → k ≤ e

/-- The loop or branch condition evaluates to a nonzero word in `s`. -/
def CondTrue {σ : Type} (E : Env σ) (s : St σ) (c : Exp Word) : Prop :=
  ∃ v k, E.cond s c = some (v, k) ∧ (v == 0) = false

variable {σ : Type} {E : Env σ}

theorem Triple.consequence {P P' : St σ → Prop} {Q Q' : Result σ → Prop} {p : Prog Word}
    {B B' : Nat} (h : Triple E P p B Q) (pre : ∀ s, P' s → P s) (bound : B ≤ B')
    (post : ∀ r, Q r → Q' r) : Triple E P' p B' Q' := by
  unfold Triple
  intro fuel s r n hP hrun hne
  obtain ⟨hn, hQ⟩ := h fuel s r n (pre s hP) hrun hne
  exact ⟨Nat.le_trans hn bound, post r hQ⟩

theorem Triple.skip {P : St σ → Prop} :
    Triple E P .skip 1 (fun r => ∃ s, P s ∧ r = .normal s.locals s.globals s.memory s.ffi) := by
  unfold Triple
  intro fuel s r n hP hrun _
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run, evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    exact ⟨Nat.le_refl _, s, hP, rfl⟩

/-- Sequencing: `first` either ends normally in a `Mid`-state, from which
`second` runs, or its abrupt result already satisfies `Q`. -/
theorem Triple.seq {P Mid : St σ → Prop} {Q : Result σ → Prop} {first second : Prog Word}
    {B₁ B₂ : Nat}
    (h₁ : Triple E P first B₁ (fun r =>
      match r with
      | .normal l g m f => Mid ⟨l, g, m, f⟩
      | r => Q r))
    (h₂ : Triple E Mid second B₂ Q) :
    Triple E P (.seq first second) (B₁ + B₂ + 1) Q := by
  unfold Triple
  intro fuel s r n hP hrun hne
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hfirst : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
        E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
        s.ffi first (memoryAccess := E.memoryAccess) (contracts := E.contracts)
        (memoryHandler := E.memoryHandler) with
    | none => rw [hfirst] at hrun; simp at hrun
    | some firstPair =>
      obtain ⟨r₁, n₁⟩ := firstPair
      rw [hfirst] at hrun
      cases r₁ with
      | normal l g m f =>
        obtain ⟨hn₁, hQ₁⟩ := h₁ fuel s _ n₁ hP hfirst rfl
        simp only [Option.bind_eq_bind, Option.bind_some] at hrun
        cases hsecond : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f second
            (memoryAccess := E.memoryAccess) (contracts := E.contracts)
            (memoryHandler := E.memoryHandler) with
        | none => rw [hsecond] at hrun; simp at hrun
        | some secondPair =>
          obtain ⟨r₂, n₂⟩ := secondPair
          rw [hsecond] at hrun
          simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨hn₂, hQ₂⟩ := h₂ fuel ⟨l, g, m, f⟩ r₂ n₂ hQ₁ hsecond hne
          exact ⟨by omega, hQ₂⟩
      | _ =>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        obtain ⟨hn₁, hQ₁⟩ := h₁ fuel s _ n₁ hP hfirst hne
        exact ⟨by omega, hQ₁⟩

/-- Conditional. A condition that does not evaluate to a word yields `.error`,
which is not covered. -/
theorem Triple.ite {P : St σ → Prop} {Q : Result σ → Prop} {c : Exp Word}
    {thenBranch elseBranch : Prog Word} {e B₁ B₂ : Nat}
    (hc : CondCost E P c e)
    (h₁ : Triple E P thenBranch B₁ Q) (h₂ : Triple E P elseBranch B₂ Q) :
    Triple E P (.ite c thenBranch elseBranch) (e + max B₁ B₂ + 1) Q := by
  unfold Triple
  intro fuel s r n hP hrun hne
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory c E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      cases hne
    | some pair =>
      obtain ⟨v, k⟩ := pair
      rw [hcond] at hrun
      have hk : k ≤ e := hc s v k hP hcond
      simp only [Option.elim_some] at hrun
      by_cases hv : (v != 0) = true
      · rw [if_pos hv] at hrun
        cases hbranch : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi thenBranch (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hbranch] at hrun; simp at hrun
        | some branchPair =>
          obtain ⟨r₁, n₁⟩ := branchPair
          rw [hbranch] at hrun
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨hn₁, hQ⟩ := h₁ fuel s r₁ n₁ hP hbranch hne
          exact ⟨by omega, hQ⟩
      · rw [if_neg hv] at hrun
        cases hbranch : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi elseBranch (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hbranch] at hrun; simp at hrun
        | some branchPair =>
          obtain ⟨r₂, n₂⟩ := branchPair
          rw [hbranch] at hrun
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨hn₂, hQ⟩ := h₂ fuel s r₂ n₂ hP hbranch hne
          exact ⟨by omega, hQ⟩

/-- What one loop-body run must establish: an iteration that reaches the loop
head again re-establishes the invariant with a smaller variant; `break` leaves
the loop normally; any other result leaves it with that result. -/
def loopBodyPost (I : St σ → Prop) (μ : St σ → Nat) (k : Nat) (Q : Result σ → Prop) :
    Result σ → Prop
  | .normal l g m f | .continued l g m f => I ⟨l, g, m, f⟩ ∧ μ ⟨l, g, m, f⟩ < k
  | .broke l g m f => Q (.normal l g m f)
  | r => Q r

/-- The while rule, with the bound stated in the variant of the entry state. -/
theorem while_steps {I : St σ → Prop} {μ : St σ → Nat} {Q : Result σ → Prop}
    {c : Exp Word} {body : Prog Word} {e b : Nat}
    (hc : CondCost E I c e)
    (hexit : ∀ s, I s → Q (.normal s.locals s.globals s.memory s.ffi))
    (hbody : ∀ k, Triple E (fun s => I s ∧ μ s = k ∧ CondTrue E s c) body b
      (loopBodyPost I μ k Q)) :
    ∀ (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat), I s →
      Env.run E fuel s (.while c body) = some (r, n) → r.isError = false →
      n ≤ (μ s + 1) * (e + b + 1) ∧ Q r := by
  intro fuel
  induction fuel with
  | zero =>
    intro s r n _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro s r n hI hrun hne
    have hpos : e + b + 1 ≤ (μ s + 1) * (e + b + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory c E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      cases hne
    | some pair =>
      obtain ⟨v, k⟩ := pair
      rw [hcond] at hrun
      have hk : k ≤ e := hc s v k hI hcond
      simp only [Option.elim_some] at hrun
      by_cases hv : (v == 0) = true
      · rw [if_pos hv] at hrun
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨by omega, hexit s hI⟩
      · rw [if_neg hv] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi body (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some bodyPair =>
          obtain ⟨rb, nb⟩ := bodyPair
          rw [hb] at hrun
          have hpre : I s ∧ μ s = μ s ∧ CondTrue E s c := ⟨hI, rfl, v, k, hcond, by simpa using hv⟩
          have again : ∀ l g m f, nb ≤ b → I ⟨l, g, m, f⟩ → μ ⟨l, g, m, f⟩ < μ s →
              ∀ (r : Result σ) (n : Nat), (do
                let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                  E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                  l g m f (.while c body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                pure (loopResult, k + nb + loopSteps + 1)) = some (r, n) →
              r.isError = false →
              n ≤ (μ s + 1) * (e + b + 1) ∧ Q r := by
            intro l g m f hnb hI' hμ r n hrun hne
            cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f
                (.while c body) (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                (memoryHandler := E.memoryHandler) with
            | none => rw [hloop] at hrun; simp at hrun
            | some loopPair =>
              obtain ⟨rl, nl⟩ := loopPair
              rw [hloop] at hrun
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              obtain ⟨hnl, hQ⟩ := ih ⟨l, g, m, f⟩ rl nl hI' hloop hne
              refine ⟨?_, hQ⟩
              have step : (μ (⟨l, g, m, f⟩ : St σ) + 1) * (e + b + 1) + (e + b + 1) ≤
                  (μ s + 1) * (e + b + 1) := by
                rw [← Nat.succ_mul]
                exact Nat.mul_le_mul_right _ (by omega)
              omega
          cases rb with
          | normal l g m f =>
            obtain ⟨hnb, hpost⟩ := hbody (μ s) fuel s _ nb hpre hb rfl
            exact again l g m f hnb hpost.1 hpost.2 r n hrun hne
          | continued l g m f =>
            obtain ⟨hnb, hpost⟩ := hbody (μ s) fuel s _ nb hpre hb rfl
            exact again l g m f hnb hpost.1 hpost.2 r n hrun hne
          | broke l g m f =>
            obtain ⟨hnb, hpost⟩ := hbody (μ s) fuel s _ nb hpre hb rfl
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            exact ⟨by omega, hpost⟩
          | _ =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            obtain ⟨hnb, hpost⟩ := hbody (μ s) fuel s _ nb hpre hb hne
            exact ⟨by omega, hpost⟩

/-- The while rule as a triple: a loop entered with variant at most `M`
takes at most `(M + 1) * (e + b + 1)` steps. -/
theorem Triple.while {I : St σ → Prop} {μ : St σ → Nat} {Q : Result σ → Prop}
    {c : Exp Word} {body : Prog Word} {e b : Nat} (M : Nat)
    (hc : CondCost E I c e)
    (hexit : ∀ s, I s → Q (.normal s.locals s.globals s.memory s.ffi))
    (hbody : ∀ k, Triple E (fun s => I s ∧ μ s = k ∧ CondTrue E s c) body b
      (loopBodyPost I μ k Q)) :
    Triple E (fun s => I s ∧ μ s ≤ M) (.while c body) ((M + 1) * (e + b + 1)) Q := by
  unfold Triple
  intro fuel s r n hP hrun hne
  obtain ⟨hn, hQ⟩ := while_steps hc hexit hbody fuel s r n hP.1 hrun hne
  exact ⟨Nat.le_trans hn (Nat.mul_le_mul_right _ (by omega)), hQ⟩

/-- Crude loop bound: a 64-bit variant gives at most `2^64` iterations. -/
theorem Triple.while_word {I : St σ → Prop} {w : St σ → Word} {Q : Result σ → Prop}
    {c : Exp Word} {body : Prog Word} {e b : Nat}
    (hc : CondCost E I c e)
    (hexit : ∀ s, I s → Q (.normal s.locals s.globals s.memory s.ffi))
    (hbody : ∀ k, Triple E (fun s => I s ∧ (w s).toNat = k ∧ CondTrue E s c) body b
      (loopBodyPost I (fun s => (w s).toNat) k Q)) :
    Triple E I (.while c body) (2 ^ 64 * (e + b + 1)) Q := by
  have h := Triple.while (μ := fun s => (w s).toNat) (2 ^ 64 - 1) hc hexit hbody
  exact h.consequence (fun s hI => ⟨hI, by have := (w s).isLt; omega⟩) (Nat.le_refl _)
    (fun _ hQ => hQ)

end InitECandidate.Solver.GuestBound
