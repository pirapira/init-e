import InitECandidate.Solver.GuestBound.SymEval

/-!
# Halving loops

`while 1 < i { var h = i >>> 1; var j = e; P; i = h }` where `P` keeps `h`
and cannot `continue` (`merkleize`). The guard gives `i ≥ 2`, so `i` strictly
decreases.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A local assignment fails or stores the value of its expression. -/
theorem assign_local_inv {fuel : Nat} {s : St σ} {x : VarName} {e : Exp Word}
    {r : Result σ} {n : Nat} (h : E.run fuel s (.assign .local x e) = some (r, n)) :
    r.isError = true ∨ ∃ v, E.eval s e = some v ∧
      r = .normal (updatePanValueMap s.locals x v) s.globals s.memory s.ffi := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run] at h
    rw [evalPanValueFfiProgSteps] at h
    simp only [panValueAssignLocalResult, evalPanValueExpCounted] at h
    cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord e E.memoryAccess with
    | none =>
      rw [hv] at h
      simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inl rfl
    | some v =>
      rw [hv] at h
      simp only [Option.map_some] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inr ⟨v, hv, rfl⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inl rfl

/-- A logical right shift by one of a word-valued local. -/
theorem eval_lsr1 (hE : WordEnv E) {s : St σ} {i : VarName} {w : Word}
    (hi : s.locals i = some (.word w)) :
    E.eval s (.shift .lsr (.var .local i) (.const 1)) = some (.word (w >>> (1 : Nat))) := by
  obtain ⟨access, hacc, -, -, -⟩ := hE.access
  have hshift := hE.shift access hacc
  simp only [Env.eval]
  rw [hacc]
  simp [evalPanValueExp, hi, hshift, RiscV.panRiscVShift]

/-- The loop is `while 1 < i { var h = i >>> 1; var j = e; P; i = h }`. -/
def halvingLoop (c : Exp Word) (body : Prog Word) : Bool :=
  match c, body with
  | .cmp .less (.const one) (.var .local i),
      .dec h .one (.shift .lsr (.var .local i') (.const k))
        (.dec j _ _ (.seq inner (.assign .local i'' (.var .local h')))) =>
      one == 1 && k == 1 && i == i' && i == i'' && h == h' && h != i && j != h && j != i &&
        (effect .up h inner).normal == .keep && (effect .up h inner).continued == .unreach
  | _, _ => false

/-- A halving loop costs at most `2^64` iterations of its guard and body. -/
theorem halvingLoop_costs (hE : WordEnv E) (c : Exp Word) (body : Prog Word) (b : Nat)
    (hcheck : halvingLoop c body = true) (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  unfold halvingLoop at hcheck
  split at hcheck
  · rename_i one i h i' k j shj ej inner i'' h'
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hhi⟩, hjh⟩, hji⟩, hkeep⟩, hcont⟩ := hcheck
    let μ : St σ → Nat := fun s =>
      match s.locals i with
      | some (.word w) => w.toNat
      | _ => 0
    have hw := Triple.while (E := E) (I := fun _ => True) (μ := μ) (Q := fun _ => True)
      (c := .cmp .less (.const 1) (.var .local i))
      (body := .dec h .one (.shift .lsr (.var .local i) (.const 1))
        (.dec j shj ej (.seq inner (.assign .local i (.var .local h)))))
      (e := expCost (.cmp .less (.const 1) (.var .local i))) (b := b) (2 ^ 64 - 1)
      (by rw [← stepCost_eq]; exact condCost _ _) (fun _ _ => trivial)
      (by
        intro k fuel s r n hP hrun hne
        obtain ⟨-, hμ, hc⟩ := hP
        refine ⟨(hbody fuel s r n trivial hrun hne).1, ?_⟩
        obtain ⟨v, kc, hcond, hv⟩ := hc
        obtain ⟨a, w, hl, hr, hx⟩ := cmp_eval hE (cond_eval hcond)
        simp only [evalPanValueExp] at hl hr
        simp only [Option.some.injEq, PanValue.word.injEq] at hl
        subst hl
        simp only [PanValue.word.injEq] at hx
        subst hx
        have hlt : RiscV.signedLess (1 : Word) w = true := by
          simp only [evalPanCmp] at hv
          split at hv
          · rename_i hh
            simpa using hh
          · simp at hv
        have hwlt := w.isLt
        have hge : 2 ≤ w.toNat := by
          simp only [RiscV.signedLess, show (1 : Word).toNat = 1 from rfl] at hlt
          split at hlt
          · split at hlt
            · have := of_decide_eq_true hlt
              omega
            · cases hlt
          · omega
        have hhalf : (w >>> (1 : Nat)).toNat < w.toNat := by
          have hdiv : w.toNat >>> 1 = w.toNat / 2 := by simp [Nat.shiftRight_eq_div_pow]
          simp only [BitVec.toNat_ushiftRight, hdiv]
          omega
        have hμs : μ s = w.toNat := by simp [μ, hr]
        -- declaration of `h`
        rcases dec_run_inv hrun with herr | ⟨fuel₁, vh, r₁, n₁, hvh, -, hrun₁, rfl⟩
        · rw [herr] at hne; cases hne
        rw [eval_lsr1 hE hr] at hvh
        simp only [Option.some.injEq] at hvh
        subst hvh
        -- declaration of `j`
        rcases dec_run_inv hrun₁ with herr | ⟨fuel₂, vj, r₂, n₂, -, -, hrun₂, rfl⟩
        · cases r₁ with
          | error l g m f => exact Bool.noConfusion hne
          | _ => cases herr
        -- `inner; i = h`
        obtain ⟨fuel₃, r₃, n₃, hrun₃, hrest⟩ := seq_run_inv hrun₂
        have hhj : (h == j) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun hh => hjh hh.symm
        have hih : (i == h) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun hh => hhi hh.symm
        have hij : (i == j) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          exact fun hh => hji hh.symm
        have hsh : (updatePanValueMap (updatePanValueMap s.locals h (.word (w >>> (1 : Nat)))) j vj) h =
            some (.word (w >>> (1 : Nat))) := by
          simp [updatePanValueMap, hhj]
        have post := effect_sound hE .up h fuel₃ inner
          ⟨updatePanValueMap (updatePanValueMap s.locals h (.word (w >>> (1 : Nat)))) j vj, s.globals,
            s.memory, s.ffi⟩ r₃ n₃ hrun₃
        cases r₃ with
        | normal l g m f =>
          simp only [PostR] at post
          rw [hkeep] at post
          have hlh : l h = some (.word (w >>> (1 : Nat))) := post _ hsh
          simp only at hrest
          obtain ⟨n₄, hrun₄⟩ := hrest
          rcases assign_local_inv hrun₄ with herr | ⟨va, hva, rfl⟩
          · cases r₂ with
            | error l' g' m' f' => exact Bool.noConfusion hne
            | _ => cases herr
          simp only [eval_local] at hva
          rw [hlh] at hva
          simp only [Option.some.injEq] at hva
          subst hva
          simp only [restorePanValueFfiLocal, loopBodyPost, true_and]
          have hfinal : restorePanValueLocal (restorePanValueLocal
              (updatePanValueMap l i (.word (w >>> (1 : Nat)))) j
                ((updatePanValueMap s.locals h (.word (w >>> (1 : Nat)))) j)) h (s.locals h) i =
              some (.word (w >>> (1 : Nat))) := by
            simp [restorePanValueLocal, updatePanValueMap, hih, hij]
          simp only [μ, hfinal]
          omega
        | continued l g m f =>
          simp only [PostR] at post
          rw [hcont] at post
          exact post.elim
        | broke l g m f =>
          simp only at hrest
          subst hrest
          simp only [restorePanValueFfiLocal, loopBodyPost]
        | error l g m f =>
          simp only at hrest
          subst hrest
          exact Bool.noConfusion hne
        | returned l g m f vs =>
          simp only at hrest
          subst hrest
          simp only [restorePanValueFfiLocal, loopBodyPost]
        | raised l g m f ex va =>
          simp only at hrest
          subst hrest
          simp only [restorePanValueFfiLocal, loopBodyPost]
        | finalFfi l g m f ev =>
          simp only at hrest
          subst hrest
          simp only [restorePanValueFfiLocal, loopBodyPost])
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
