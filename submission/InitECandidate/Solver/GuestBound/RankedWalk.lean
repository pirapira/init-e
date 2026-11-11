import InitECandidate.Solver.GuestBound.WalkMBound

/-!
# Ranked walk loops

A loop in which every iteration either changes only a few locals (in the sense
of `WalkM`) or strictly decreases a rank of the globals. Within a phase of
constant rank the no-revisit argument of `walkM_core` applies; a decrease
starts a new phase. With ranks below `R` the loop takes at most
`R * walkIters m` iterations.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- One iteration walked the locals in `M` or decreased the rank. -/
def StepPost (M : List VarName) (rank : (VarName → Option (PanValue Word)) → Nat) (s : St σ) :
    Result σ → Prop
  | .normal l g m f | .continued l g m f =>
      WalkM M s (.normal l g m f : Result σ) ∨ rank g < rank s.globals
  | _ => True

section core
variable (M : List VarName) (rank : (VarName → Option (PanValue Word)) → Nat)
  {c : Exp Word} {body : Prog Word} {b : Nat}
  (hstep : ∀ fuel (s : St σ) r n, E.run fuel s body = some (r, n) → StepPost M rank s r)
  (hbody : Costs E body b)

include hstep hbody in
theorem rankedWalk_core (r : Result σ) (hne : r.isError = false) :
    ∀ (ρ fuel : Nat) (base : St σ) (V : Finset (Code M)) (s : St σ) (m : Nat),
      rank s.globals ≤ ρ → OkM M base s → E.run fuel s (.while c body) = some (r, m) →
      (∀ code ∈ V, ∃ s' fuel' m', OkM M base s' ∧ enc M base s' = code ∧ fuel ≤ fuel' ∧
        m < m' ∧ E.run fuel' s' (.while c body) = some (r, m')) →
      m + V.card * (panValueExpStepCost c + b + 1) ≤
        (ρ + 1) * (walkIters M.length * (panValueExpStepCost c + b + 1)) := by
  intro ρ
  induction ρ using Nat.strongRecOn with
  | _ ρ outer =>
  intro fuel
  induction fuel with
  | zero =>
    intro base V s m _ _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro base V s m hrank hok hrun0 hV
    have hrun := hrun0
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    have hnotV : enc M base s ∉ V := by
      intro hmem
      obtain ⟨s', fuel', m', hok', henc, hfuel, hlt, hrun'⟩ := hV _ hmem
      have hs : s' = s := enc_inj M base hok' hok henc
      have hsame := run_mono hfuel hrun0
      rw [hs] at hrun'
      rw [hrun'] at hsame
      simp only [Option.some.injEq, Prod.mk.injEq] at hsame
      omega
    have hcard : V.card + 1 ≤ walkIters M.length :=
      Nat.le_trans (Finset.card_lt_univ_of_notMem hnotV) (code_card M)
    have hroom : V.card * (panValueExpStepCost c + b + 1) + (panValueExpStepCost c + b + 1) ≤
        walkIters M.length * (panValueExpStepCost c + b + 1) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hcard
    have hmul : (ρ + 1) * (walkIters M.length * (panValueExpStepCost c + b + 1)) =
        ρ * (walkIters M.length * (panValueExpStepCost c + b + 1)) +
          walkIters M.length * (panValueExpStepCost c + b + 1) := Nat.succ_mul _ _
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
          have again : ∀ l g mem f, nb ≤ b →
              (WalkM M s (.normal l g mem f : Result σ) ∨ rank g < rank s.globals) →
              (do
                let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                  E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                  l g mem f (.while c body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                pure (loopResult, kc + nb + loopSteps + 1)) = some (r, m) →
              m + V.card * (panValueExpStepCost c + b + 1) ≤
                (ρ + 1) * (walkIters M.length * (panValueExpStepCost c + b + 1)) := by
            intro l g mem f hnb hpost hrun
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
              rcases hpost with hwalk | hdec
              · -- a pure step: stay in the phase
                obtain ⟨h1, h2, h3, h4, h5⟩ := hwalk
                obtain ⟨hg, hm, hf, hl, hvals⟩ := hok
                have hok' : OkM M base ⟨l, g, mem, f⟩ := by
                  refine ⟨h1.trans hg, h2.trans hm, h3.trans hf,
                    fun x hx => (h4 x hx).trans (hl x hx), ?_⟩
                  intro x hx
                  rcases h5 x hx with hword | ⟨y, hy, hxy⟩
                  · exact Or.inl hword
                  · rcases hvals y hy with hword | ⟨z, hz, hyz⟩
                    · exact Or.inl (by show IsWordVal (l x); rw [hxy]; exact hword)
                    · exact Or.inr ⟨z, hz, hxy.trans hyz⟩
                have hV' : ∀ code ∈ insert (enc M base s) V, ∃ s' fuel' m', OkM M base s' ∧
                    enc M base s' = code ∧ fuel ≤ fuel' ∧ nl < m' ∧
                    E.run fuel' s' (.while c body) = some (rl, m') := by
                  intro code hcode
                  rcases Finset.mem_insert.mp hcode with rfl | hcode
                  · exact ⟨s, fuel + 1, _, ⟨hg, hm, hf, hl, hvals⟩, rfl, Nat.le_succ _, by omega,
                      hrun0⟩
                  · obtain ⟨s', fuel', m', hok'', henc, hfuel, hlt, hrun'⟩ := hV code hcode
                    exact ⟨s', fuel', m', hok'', henc, by omega, by omega, hrun'⟩
                have hrank' : rank g ≤ ρ := by
                  have : g = s.globals := h1
                  rw [this]; exact hrank
                have hih := ih base (insert (enc M base s) V) ⟨l, g, mem, f⟩ nl hrank' hok'
                  hloop hV'
                rw [Finset.card_insert_of_notMem hnotV, Nat.succ_mul] at hih
                omega
              · -- the rank decreased: a new phase from the new state
                have hlt : rank g < ρ := Nat.lt_of_lt_of_le hdec hrank
                have hnew := outer (rank g) hlt fuel ⟨l, g, mem, f⟩ ∅ ⟨l, g, mem, f⟩ nl
                  (Nat.le_refl _) ⟨rfl, rfl, rfl, fun _ _ => rfl, fun x hx => Or.inr ⟨x, hx, rfl⟩⟩
                  hloop (by intro code hcode; simp at hcode)
                simp only [Finset.card_empty, Nat.zero_mul, Nat.add_zero] at hnew
                have hle : (rank g + 1) * (walkIters M.length * (panValueExpStepCost c + b + 1)) ≤
                    ρ * (walkIters M.length * (panValueExpStepCost c + b + 1)) :=
                  Nat.mul_le_mul_right _ hlt
                omega
          have post := hstep fuel s rb nb hb
          cases rb with
          | normal l g mem f =>
            have hnb : nb ≤ b := (hbody fuel s _ nb trivial hb rfl).1
            exact again l g mem f hnb post hrun
          | continued l g mem f =>
            have hnb : nb ≤ b := (hbody fuel s _ nb trivial hb rfl).1
            exact again l g mem f hnb post hrun
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

/-- A ranked walk loop with ranks below `R` costs at most `R * walkIters m`
iterations of its guard and body. -/
theorem rankedWalk_costs (M : List VarName) (rank : (VarName → Option (PanValue Word)) → Nat)
    (R : Nat) (hR : ∀ g, rank g < R) (c : Exp Word) (body : Prog Word) (b : Nat)
    (hstep : ∀ fuel (s : St σ) r n, E.run fuel s body = some (r, n) → StepPost M rank s r)
    (hbody : Costs E body b) :
    Costs E (.while c body) (R * walkIters M.length * (expCost c + b + 1)) := by
  unfold Costs Triple
  intro fuel s r m _ hrun hne
  refine ⟨?_, trivial⟩
  rw [← stepCost_eq]
  have hok : OkM M s s := ⟨rfl, rfl, rfl, fun _ _ => rfl, fun x hx => Or.inr ⟨x, hx, rfl⟩⟩
  have h := rankedWalk_core M rank hstep hbody r hne (rank s.globals) fuel s ∅ s m
    (Nat.le_refl _) hok hrun (by intro code hcode; simp at hcode)
  simp only [Finset.card_empty, Nat.zero_mul, Nat.add_zero] at h
  have hle : rank s.globals + 1 ≤ R := hR s.globals
  calc m ≤ (rank s.globals + 1) * (walkIters M.length * (panValueExpStepCost c + b + 1)) := h
    _ ≤ R * (walkIters M.length * (panValueExpStepCost c + b + 1)) :=
        Nat.mul_le_mul_right _ hle
    _ = R * walkIters M.length * (panValueExpStepCost c + b + 1) := (Nat.mul_assoc _ _ _).symm

end InitECandidate.Solver.GuestBound
