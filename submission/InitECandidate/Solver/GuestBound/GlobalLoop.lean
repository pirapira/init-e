import InitECandidate.Solver.GuestBound.Keepers
import InitECandidate.Solver.GuestBound.CounterLoop

/-!
# Loops counting a global down

`while snap <+ g { g = g - 1; rest }` where nothing in `rest` or its call tree
writes the global `g` (`state_restore`). The guard keeps `g` above zero and
each iteration decreases it by one.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A run of `first; second` is a run of `first` followed, if it ends normally, by `second`. -/
theorem seq_run_inv {fuel : Nat} {s : St σ} {first second : Prog Word} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.seq first second) = some (r, n)) :
    ∃ fuel' r₁ n₁, E.run fuel' s first = some (r₁, n₁) ∧
      match r₁ with
      | .normal l g m f => ∃ n₂, E.run fuel' ⟨l, g, m, f⟩ second = some (r, n₂)
      | _ => r = r₁ := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    cases h₁ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
        E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
        s.ffi first (memoryAccess := E.memoryAccess) (contracts := E.contracts)
        (memoryHandler := E.memoryHandler) with
    | none => rw [h₁] at h; simp at h
    | some pair =>
      obtain ⟨r₁, n₁⟩ := pair
      rw [h₁] at h
      refine ⟨fuel, r₁, n₁, h₁, ?_⟩
      cases r₁ with
      | normal l g m f =>
        simp only [Option.bind_eq_bind, Option.bind_some] at h
        cases h₂ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f second
            (memoryAccess := E.memoryAccess) (contracts := E.contracts)
            (memoryHandler := E.memoryHandler) with
        | none => rw [h₂] at h; simp at h
        | some pair₂ =>
          obtain ⟨r₂, n₂⟩ := pair₂
          rw [h₂] at h
          simp only [Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact ⟨n₂, h₂⟩
      | _ =>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at h
        exact h.1.symm

/-- `g = g - 1` on a global word either fails or stores the decremented word. -/
theorem dec_global_inv (hE : WordEnv E) {fuel : Nat} {s : St σ} {g : VarName} {w : Word}
    {r : Result σ} {n : Nat} (hg : s.globals g = some (.word w))
    (h : E.run fuel s (.assign .global g (.op .sub [.var .global g, .const 1])) = some (r, n)) :
    r.isError = true ∨ ∃ globals, r = .normal s.locals globals s.memory s.ffi ∧
      globals g = some (.word (w - 1)) := by
  obtain ⟨access, hacc, -, hsub, -⟩ := hE.access
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueAssignGlobalResult, evalPanValueExpCounted] at h
    have hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord (.op .sub [.var .global g, .const 1]) E.memoryAccess =
        some (.word (w - 1)) := by
      rw [hacc]
      simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hg, hsub]
    rw [hv] at h
    simp only [Option.map_some] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inr ⟨_, rfl, by simp [updatePanValueMap]⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inl rfl

/-- The loop is `while e <+ g { g = g - 1; rest }` with `rest` not writing the global `g`. -/
def globalCounterLoop (decls : List (Decl Word)) (depth : Nat) (c : Exp Word)
    (body : Prog Word) : Bool :=
  match c, body with
  | .cmp .lower _ (.var .global g),
      .seq (.assign .global g' (.op .sub [.var .global g'', .const k])) rest =>
      g == g' && g == g'' && k == 1 &&
        keepWith (globalLeaf g) (keepFn (globalLeaf g) decls depth) rest
  | _, _ => false

/-- A global down-counter loop costs at most `2^64` iterations of its guard and body. -/
theorem globalCounterLoop_costs (hE : WordEnv E) {decls : List (Decl Word)}
    (hfrom : FunctionsFrom E.functions decls) (depth : Nat) (c : Exp Word) (body : Prog Word)
    (b : Nat) (hcheck : globalCounterLoop decls depth c body = true) (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  unfold globalCounterLoop at hcheck
  split at hcheck
  · rename_i left g g' g'' k rest
    simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hkeep⟩ := hcheck
    let μ : St σ → Nat := fun s =>
      match s.globals g with
      | some (.word w) => w.toNat
      | _ => 0
    have hw := Triple.while (E := E) (I := fun _ => True) (μ := μ) (Q := fun _ => True)
      (c := .cmp .lower left (.var .global g))
      (body := .seq (.assign .global g (.op .sub [.var .global g, .const 1])) rest)
      (e := expCost (.cmp .lower left (.var .global g))) (b := b) (2 ^ 64 - 1)
      (by rw [← stepCost_eq]; exact condCost _ _) (fun _ _ => trivial)
      (by
        intro k fuel s r n hP hrun hne
        obtain ⟨-, hμ, hc⟩ := hP
        refine ⟨(hbody fuel s r n trivial hrun hne).1, ?_⟩
        obtain ⟨v, kc, hcond, hv⟩ := hc
        obtain ⟨a, w, -, hr, hx⟩ := cmp_eval hE (cond_eval hcond)
        simp only [evalPanValueExp] at hr
        simp only [PanValue.word.injEq] at hx
        subst hx
        have hlt : a < w := by
          simp only [evalPanCmp] at hv
          split at hv
          · rename_i h
            simpa using h
          · simp at hv
        have hpos : 0 < w.toNat := by
          have := BitVec.lt_def.mp hlt
          omega
        have hμs : μ s = w.toNat := by simp [μ, hr]
        obtain ⟨fuel', r₁, n₁, h₁, h₂⟩ := seq_run_inv hrun
        rcases dec_global_inv hE hr h₁ with herr | ⟨globals, rfl, hglobals⟩
        · cases r₁ with
          | error l gl m f =>
            simp only at h₂
            subst h₂
            exact Bool.noConfusion hne
          | _ => cases herr
        · simp only at h₂
          obtain ⟨n₂, h₂⟩ := h₂
          have hrel := keepWith_sound (globalKeeper E g) _
            (keepFn_sound (globalKeeper E g) hfrom depth) fuel' rest
            ⟨s.locals, globals, s.memory, s.ffi⟩ r n₂ hkeep h₂
          have hg' : r.st.globals g = some (.word (w - 1)) := hrel.trans hglobals
          have hsub : (w - 1).toNat = w.toNat - 1 := by
            have hwlt := w.isLt
            simp only [BitVec.toNat_sub, show (1 : Word).toNat = 1 from rfl]
            omega
          cases r with
          | normal l gl m f =>
            simp only [loopBodyPost, true_and]
            have : gl g = some (.word (w - 1)) := hg'
            simp only [μ, this, hsub]
            omega
          | continued l gl m f =>
            simp only [loopBodyPost, true_and]
            have : gl g = some (.word (w - 1)) := hg'
            simp only [μ, this, hsub]
            omega
          | _ => simp only [loopBodyPost])
    have hpre : ∀ s : St σ, True → True ∧ μ s ≤ 2 ^ 64 - 1 := by
      intro s _
      refine ⟨trivial, ?_⟩
      simp only [μ]
      split
      · rename_i w _
        have := w.isLt
        omega
      · omega
    exact hw.consequence hpre (by omega) (fun _ h => h)
  · cases hcheck

end InitECandidate.Solver.GuestBound
