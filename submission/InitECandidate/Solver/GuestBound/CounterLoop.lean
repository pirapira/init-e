import InitECandidate.Solver.GuestBound.EffectSound
import InitECandidate.Solver.GuestBound.ExpCostEval

/-!
# Iteration bound for counter loops

A loop accepted by `counterLoop` performs at most `2^64` iterations in any
returning run: the guard keeps the counter away from the end of its range and
every iteration moves it by exactly one.
-/

set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A quantity that strictly decreases with each step while the guard holds. -/
def measure : Kind → Word → Nat
  | .upU, w => 2 ^ 64 - 1 - w.toNat
  | .upS, w => 2 ^ 64 - 1 - (w.toNat + 2 ^ 63) % 2 ^ 64
  | .down, w => w.toNat

/-- The loop variant: the measure of the counter, when it is a word. -/
def counterVariant (kind : Kind) (i : VarName) (s : St σ) : Nat :=
  match s.locals i with
  | some (.word w) => measure kind w
  | _ => 0

theorem measure_lt (kind : Kind) (w : Word) : measure kind w < 2 ^ 64 := by
  have := w.isLt
  cases kind <;> simp only [measure] <;> omega

/-- A condition that evaluates yields a word. -/
theorem cond_eval {s : St σ} {c : Exp Word} {v : Word} {k : Nat}
    (h : E.cond s c = some (v, k)) :
    evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord c E.memoryAccess = some (.word v) := by
  simp only [Env.cond, panValueIteCondition, evalPanValueExpCounted] at h
  cases he : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord c E.memoryAccess with
  | none => rw [he] at h; simp at h
  | some value =>
    rw [he] at h
    cases value <;> simp at h
    rw [h.1]

/-- A comparison evaluates both sides to words and compares them. -/
theorem cmp_eval (hE : WordEnv E) {s : St σ} {operator : Cmp} {left right : Exp Word}
    {x : PanValue Word}
    (h : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord (.cmp operator left right) E.memoryAccess = some x) :
    ∃ a b,
      evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord left E.memoryAccess = some (.word a) ∧
      evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord right E.memoryAccess = some (.word b) ∧
      x = .word (evalPanCmp operator a b) := by
  obtain ⟨access, hacc, -, -, hcmp⟩ := hE.access
  rw [hacc] at h ⊢
  rw [evalPanValueExp] at h
  simp only [Option.bind_eq_bind] at h
  cases hl : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord left (some access) with
  | none => rw [hl] at h; simp at h
  | some lv =>
    rw [hl] at h
    simp only [Option.bind_some] at h
    cases hr : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord right (some access) with
    | none => rw [hr] at h; simp at h
    | some rv =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      cases lv <;> cases rv <;> simp at h
      rename_i a b
      exact ⟨a, b, rfl, rfl, by rw [← h, hcmp]⟩

/-- While the guard holds, the counter is a word and one step decreases its measure. -/
theorem guard_step (hE : WordEnv E) {c : Exp Word} {kind : Kind} {i : VarName}
    (hk : guardKind c = some (kind, i)) {s : St σ} (hc : CondTrue E s c) :
    ∃ w, s.locals i = some (.word w) ∧
      measure kind (stepWord kind.mode w) < measure kind w := by
  obtain ⟨v, k, hcond, hv⟩ := hc
  have he := cond_eval hcond
  unfold guardKind at hk
  split at hk
  · -- i <+ e
    simp only [Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    obtain ⟨a, b, hl, -, hx⟩ := cmp_eval hE he
    simp only [evalPanValueExp] at hl
    simp only [PanValue.word.injEq] at hx
    subst hx
    refine ⟨a, hl, ?_⟩
    have hlt : a < b := by
      by_cases hab : a < b
      · exact hab
      · simp [evalPanCmp, hab] at hv
    have := BitVec.lt_def.mp hlt
    have hb := b.isLt
    simp only [measure, Kind.mode, stepWord, BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]
    omega
  · -- i < e
    simp only [Option.some.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    obtain ⟨a, b, hl, -, hx⟩ := cmp_eval hE he
    simp only [evalPanValueExp] at hl
    simp only [PanValue.word.injEq] at hx
    subst hx
    refine ⟨a, hl, ?_⟩
    have hlt : RiscV.signedLess a b = true := by
      by_cases hab : RiscV.signedLess a b = true
      · exact hab
      · simp [evalPanCmp, hab] at hv
    have ha := a.isLt
    have hb := b.isLt
    simp only [RiscV.signedLess] at hlt
    simp only [measure, Kind.mode, stepWord, BitVec.toNat_add, show (1 : Word).toNat = 1 from rfl]
    split at hlt
    · split at hlt
      · have := of_decide_eq_true hlt
        omega
      · cases hlt
    · split at hlt
      · omega
      · have := of_decide_eq_true hlt
        omega
  · -- 0 <+ i
    split at hk
    · rename_i hk0
      simp only [Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      simp only [beq_iff_eq] at hk0
      subst hk0
      obtain ⟨a, b, hl, hr, hx⟩ := cmp_eval hE he
      simp only [evalPanValueExp] at hl hr
      simp only [Option.some.injEq, PanValue.word.injEq] at hl
      subst hl
      simp only [PanValue.word.injEq] at hx
      subst hx
      refine ⟨b, hr, ?_⟩
      have hlt : (0 : Word) < b := by
        simp only [evalPanCmp] at hv
        split at hv
        · rename_i h
          simpa using h
        · simp at hv
      have := BitVec.lt_def.mp hlt
      have hb := b.isLt
      simp only [measure, Kind.mode, stepWord, BitVec.toNat_sub, show (1 : Word).toNat = 1 from rfl,
        show (0 : Word).toNat = 0 from rfl] at this ⊢
      omega
    · cases hk
  · -- 0 < i
    split at hk
    · rename_i hk0
      simp only [Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      simp only [beq_iff_eq] at hk0
      subst hk0
      obtain ⟨a, b, hl, hr, hx⟩ := cmp_eval hE he
      simp only [evalPanValueExp] at hl hr
      simp only [Option.some.injEq, PanValue.word.injEq] at hl
      subst hl
      simp only [PanValue.word.injEq] at hx
      subst hx
      refine ⟨b, hr, ?_⟩
      have hlt : RiscV.signedLess (0 : Word) b = true := by
        simp only [evalPanCmp] at hv
        split at hv
        · rename_i h
          simpa using h
        · simp at hv
      have hb := b.isLt
      simp only [RiscV.signedLess, show (0 : Word).toNat = 0 from rfl] at hlt
      simp only [measure, Kind.mode, stepWord, BitVec.toNat_sub, show (1 : Word).toNat = 1 from rfl,
        show (0 : Word).toNat = 0 from rfl]
      split at hlt
      · split at hlt
        · have := of_decide_eq_true hlt
          omega
        · cases hlt
      · omega
    · cases hk
  · -- i != 0
    split at hk
    · rename_i hk0
      simp only [Option.some.injEq, Prod.mk.injEq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      simp only [beq_iff_eq] at hk0
      subst hk0
      obtain ⟨a, b, hl, hr, hx⟩ := cmp_eval hE he
      simp only [evalPanValueExp] at hl hr
      simp only [Option.some.injEq, PanValue.word.injEq] at hr
      subst hr
      simp only [PanValue.word.injEq] at hx
      subst hx
      refine ⟨a, hl, ?_⟩
      have hne : a ≠ 0 := by
        intro h0
        simp [evalPanCmp, h0] at hv
      have hpos : 0 < a.toNat := by
        rcases Nat.eq_zero_or_pos a.toNat with h0 | h0
        · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0)) hne
        · exact h0
      have ha := a.isLt
      simp only [measure, Kind.mode, stepWord, BitVec.toNat_sub, show (1 : Word).toNat = 1 from rfl,
        show (0 : Word).toNat = 0 from rfl]
      omega
    · cases hk
  · cases hk

/-- A loop whose guard keeps a local counter in a range where one step
decreases a measure below `2^64`, and whose body steps the counter exactly once
on every way back to the loop head, takes at most `2^64` iterations. -/
theorem variant_loop_costs (hE : WordEnv E) (c : Exp Word) (body : Prog Word) (b : Nat)
    (mode : Mode) (i : VarName) (meas : Word → Nat) (hmeas : ∀ w, meas w < 2 ^ 64)
    (hguard : ∀ s : St σ, CondTrue E s c →
      ∃ w, s.locals i = some (.word w) ∧ meas (stepWord mode w) < meas w)
    (hback : stepsBack (effect mode i body) = true) (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  let μ : St σ → Nat := fun s =>
    match s.locals i with
    | some (.word w) => meas w
    | _ => 0
  have hw := Triple.while (E := E) (I := fun _ => True) (μ := μ)
    (Q := fun _ => True) (c := c) (body := body) (e := expCost c) (b := b) (2 ^ 64 - 1)
    (by rw [← stepCost_eq]; exact condCost _ c) (fun _ _ => trivial)
    (by
      intro k fuel s r n hP hrun hne
      obtain ⟨-, hμ, hc⟩ := hP
      refine ⟨(hbody fuel s r n trivial hrun hne).1, ?_⟩
      obtain ⟨w, hw, hlt⟩ := hguard s hc
      have post := effect_sound hE mode i fuel body s r n hrun
      simp only [stepsBack, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hback
      have hk' : μ s = meas w := by
        simp [μ, hw]
      cases r with
      | normal l g m f =>
        simp only [PostR] at post
        simp only [loopBodyPost, true_and]
        rcases hback.1 with he | he
        · rw [he] at post
          have := post w hw
          simp only [μ, this]
          omega
        · rw [he] at post
          exact post.elim
      | continued l g m f =>
        simp only [PostR] at post
        simp only [loopBodyPost, true_and]
        rcases hback.2 with he | he
        · rw [he] at post
          have := post w hw
          simp only [μ, this]
          omega
        · rw [he] at post
          exact post.elim
      | _ => simp only [loopBodyPost])
  have hpre : ∀ s : St σ, True → True ∧ μ s ≤ 2 ^ 64 - 1 := by
    intro s _
    refine ⟨trivial, ?_⟩
    simp only [μ]
    split
    · rename_i w _
      have := hmeas w
      omega
    · omega
  exact hw.consequence hpre (by omega) (fun _ h => h)

/-- A counter loop costs at most `2^64` iterations of its guard and body. -/
theorem counterLoop_costs (hE : WordEnv E) (c : Exp Word) (body : Prog Word) (b : Nat)
    (hcheck : counterLoop c body = true) (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  unfold counterLoop at hcheck
  split at hcheck
  · rename_i kind i hk
    exact variant_loop_costs hE c body b kind.mode i (measure kind) (measure_lt kind)
      (fun _ hc => guard_step hE hk hc) hcheck hbody
  · cases hcheck

/-! ### Counters with a literal bound and a constant step -/

/-- `while i <+ C` or `while i < C` with a literal `C`: the bound, and whether it is signed. -/
def constGuard : Exp Word → Option (VarName × Word × Bool)
  | .cmp .lower (.var .local i) (.const bound) => some (i, bound, false)
  | .cmp .less (.var .local i) (.const bound) => some (i, bound, true)
  | _ => none

/-- A step `k ≥ 1` from below the bound cannot overflow. -/
def constFits (bound k : Word) (signed : Bool) : Bool :=
  decide (1 ≤ k.toNat) &&
    (if signed then decide (bound.toNat + k.toNat ≤ 2 ^ 63)
     else decide (bound.toNat + k.toNat ≤ 2 ^ 64))

/-- The loop is `while i < C { …; i = i + k }` with literals that cannot overflow. -/
def constLoop (step : Option (VarName × Word)) (c : Exp Word) (body : Prog Word) : Bool :=
  match step with
  | some (j, k) =>
      match constGuard c with
      | some (i, bound, signed) =>
          i == j && constFits bound k signed && stepsBack (effect (.upBy k) i body)
      | none => false
  | none => false

/-- A constant-bound counter loop costs at most `2^64` iterations of its guard and body. -/
theorem constLoop_costs (hE : WordEnv E) (step : Option (VarName × Word)) (c : Exp Word)
    (body : Prog Word) (b : Nat) (hcheck : constLoop step c body = true)
    (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  unfold constLoop at hcheck
  split at hcheck
  · rename_i j k
    split at hcheck
    case h_2 => cases hcheck
    rename_i i bound signed hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
    obtain ⟨⟨rfl, hfits⟩, hback⟩ := hcheck
    simp only [constFits, Bool.and_eq_true, decide_eq_true_eq] at hfits
    obtain ⟨hk1, hfit⟩ := hfits
    unfold constGuard at hg
    split at hg
    · -- unsigned
      rename_i iv bv
      simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl, rfl⟩ := hg
      simp only [Bool.false_eq_true, if_false, decide_eq_true_eq] at hfit
      refine variant_loop_costs hE _ body b (.upBy k) _ (measure .upU) (measure_lt .upU) ?_
        hback hbody
      intro s hc
      obtain ⟨v, kc, hcond, hv⟩ := hc
      obtain ⟨a, b', hl, hr, hx⟩ := cmp_eval hE (cond_eval hcond)
      simp only [evalPanValueExp] at hl hr
      simp only [Option.some.injEq, PanValue.word.injEq] at hr
      subst hr
      simp only [PanValue.word.injEq] at hx
      subst hx
      refine ⟨a, hl, ?_⟩
      have hlt : a < bv := by
        simp only [evalPanCmp] at hv
        split at hv
        · rename_i h
          simpa using h
        · simp at hv
      have := BitVec.lt_def.mp hlt
      have ha := a.isLt
      have hkk := k.isLt
      simp only [measure, stepWord, BitVec.toNat_add]
      omega
    · -- signed
      rename_i iv bv
      simp only [Option.some.injEq, Prod.mk.injEq] at hg
      obtain ⟨rfl, rfl, rfl⟩ := hg
      simp only [if_true, decide_eq_true_eq] at hfit
      refine variant_loop_costs hE _ body b (.upBy k) _ (measure .upS) (measure_lt .upS) ?_
        hback hbody
      intro s hc
      obtain ⟨v, kc, hcond, hv⟩ := hc
      obtain ⟨a, b', hl, hr, hx⟩ := cmp_eval hE (cond_eval hcond)
      simp only [evalPanValueExp] at hl hr
      simp only [Option.some.injEq, PanValue.word.injEq] at hr
      subst hr
      simp only [PanValue.word.injEq] at hx
      subst hx
      refine ⟨a, hl, ?_⟩
      have hlt : RiscV.signedLess a bv = true := by
        simp only [evalPanCmp] at hv
        split at hv
        · rename_i h
          simpa using h
        · simp at hv
      have ha := a.isLt
      have hb := bv.isLt
      have hkk := k.isLt
      simp only [RiscV.signedLess] at hlt
      simp only [measure, stepWord, BitVec.toNat_add]
      split at hlt
      · split at hlt
        · have := of_decide_eq_true hlt
          omega
        · cases hlt
      · split at hlt
        · omega
        · have := of_decide_eq_true hlt
          omega
    · cases hg
  · cases hcheck

end InitECandidate.Solver.GuestBound
