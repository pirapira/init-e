import InitECandidate.Solver.GuestBound.CounterSound

/-! # `effect` is sound for the stepped evaluator -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The step expression evaluates to the stepped word. -/
theorem eval_isStep (hE : WordEnv E) {mode : Mode} {i : VarName} {value : Exp Word}
    (hstep : isStep mode i value = true) (s : St σ) (w : Word)
    (hw : s.locals i = some (.word w)) :
    evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord value E.memoryAccess = some (.word (stepWord mode w)) := by
  obtain ⟨access, hacc, hadd, hsub, -⟩ := hE.access
  unfold isStep at hstep
  split at hstep
  · rename_i name k
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hstep
    obtain ⟨rfl, hmode⟩ := hstep
    rw [hacc]
    rcases hmode with ⟨rfl, rfl⟩ | rfl
    · simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hw, hadd, stepWord]
    · simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hw, hadd, stepWord]
  · rename_i name k
    simp only [Bool.and_eq_true, beq_iff_eq] at hstep
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hstep
    rw [hacc]
    simp [evalPanValueExp, evalPanValueExp.evalPanValueExps, hw, hsub, stepWord]
  · cases hstep

/-- Assigning a call result leaves the tracked local alone unless it is the destination. -/
theorem assign_keeps {i : VarName} {structs : StructContext}
    {locals globals locals' globals' : VarName → Option (PanValue Word)}
    {destination : Option (VarKind × VarName)} {values : List (PanValue Word)}
    (hdest : (destination == some (VarKind.local, i)) = false)
    (h : assignPanValueCallResult locals globals destination values (structs := structs) =
      some (locals', globals')) :
    locals' i = locals i := by
  unfold assignPanValueCallResult at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
  · rename_i name value
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      have hne : (i == name) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq] at hdest ⊢
        intro heq
        exact hdest (by rw [heq])
      simp [updatePanValueMap, hne]
    · simp at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
    · simp at h
  · simp at h

/-- A call that returns normally keeps the tracked local, as `effect` says. -/
theorem call_normal_post {mode : Mode} {i : VarName} {structs : StructContext}
    {locals globals locals' globals' : VarName → Option (PanValue Word)}
    {destination : Option (VarKind × VarName)} {values : List (PanValue Word)}
    (handlerInfo : Option (ExceptionId × VarName × Prog Word)) (f : FunName)
    (arguments : List (Exp Word)) (memory : Word → Option (PanValue Word)) (ffi : FfiState σ)
    (h : assignPanValueCallResult locals globals destination values (structs := structs) =
      some (locals', globals')) :
    PostR mode i (locals i) (effect mode i (.call (some (destination, handlerInfo)) f arguments))
      (.normal locals' globals' memory ffi : Result σ) := by
  by_cases hdest : (destination == some (VarKind.local, i)) = true
  · cases handlerInfo with
    | none => simp only [effect, hdest, if_true]; exact PostR.bad _
    | some triple =>
      obtain ⟨exception, handlerVar, handlerProgram⟩ := triple
      simp only [effect, hdest, Bool.or_true, if_true]
      exact PostR.bad _
  · have hdest' : (destination == some (VarKind.local, i)) = false := by simpa using hdest
    have hkeep := assign_keeps hdest' h
    cases handlerInfo with
    | none =>
      simp only [effect, hdest', PostR, Effs.keep, Post]
      exact fun w hw => by rw [hkeep]; exact hw
    | some triple =>
      obtain ⟨exception, handlerVar, handlerProgram⟩ := triple
      by_cases hvar : (handlerVar == i) = true
      · simp only [effect, hvar, Bool.true_or, if_true]; exact PostR.bad _
      · simp only [effect, hvar, hdest', Bool.or_self, PostR]
        refine Post.join_left _ ?_
        simp only [Post]
        exact fun w hw => by rw [hkeep]; exact hw

/-- A handler's result has the effect `effect` assigns to the call. -/
theorem call_handler_post {mode : Mode} {i : VarName}
    {locals : VarName → Option (PanValue Word)} {value : PanValue Word}
    (destination : Option (VarKind × VarName)) (exception : ExceptionId) {handlerVar : VarName}
    {handlerProgram : Prog Word} (f : FunName) (arguments : List (Exp Word)) {r : Result σ}
    (h : PostR mode i (updatePanValueMap locals handlerVar value i)
      (effect mode i handlerProgram) r) :
    PostR mode i (locals i)
      (effect mode i (.call (some (destination, some (exception, handlerVar, handlerProgram)))
        f arguments)) r := by
  by_cases hbad : (handlerVar == i || destination == some (VarKind.local, i)) = true
  · simp only [effect, hbad, if_true]; exact PostR.bad _
  · simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hbad
    obtain ⟨hvar, hdest⟩ := hbad
    have hin : (i == handlerVar) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq] at hvar ⊢
      exact fun heq => hvar heq.symm
    have hsame : updatePanValueMap locals handlerVar value i = locals i := by
      simp [updatePanValueMap, hin]
    rw [hsame] at h
    simp only [effect, hvar, hdest, Bool.or_self]
    cases r <;> simp only [PostR] at h ⊢
    · exact Post.join_right _ h
    · exact h
    · exact h

set_option hygiene false in
/-- Finish a leaf whose normal result keeps the locals. -/
local macro "keep_leaf" helper:ident : tactic => `(tactic| (
  rw [evalPanValueFfiProgSteps] at hrun
  simp only [$helper:ident] at hrun
  repeat' split at hrun
  all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
  all_goals (obtain ⟨rfl, -⟩ := hrun)
  all_goals (simp only [effect, PostR, Effs.keep, Post])
  all_goals (try (exact fun _ hw => hw))))

set_option maxHeartbeats 1000000 in
/-- On every exit, the tracked local has changed as `effect` says. -/
theorem effect_sound (hE : WordEnv E) (mode : Mode) (i : VarName) :
    ∀ (fuel : Nat) (p : Prog Word) (s : St σ) (r : Result σ) (n : Nat),
      E.run fuel s p = some (r, n) → PostR mode i (s.locals i) (effect mode i p) r := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel sih =>
  cases fuel with
  | zero =>
    intro p s r n hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    have ih := sih fuel (Nat.lt_succ_self fuel)
    intro p s r n hrun
    simp only [Env.run] at hrun
    cases p with
    | skip =>
      simp only [evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      simp only [effect, PostR, Effs.keep, Post]
      exact fun _ hw => hw
    | tick =>
      simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      simp only [effect, PostR, Effs.keep, Post]
      exact fun _ hw => hw
    | annot key text =>
      simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      simp only [effect, PostR, Effs.keep, Post]
      exact fun _ hw => hw
    | «break» =>
      simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      simp only [effect, PostR, Post]
      exact fun _ hw => hw
    | «continue» =>
      simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      simp only [effect, PostR, Post]
      exact fun _ hw => hw
    | store address value => keep_leaf panValueStoreResult
    | store32 address value => keep_leaf panValueStore32Result
    | storeByte address value => keep_leaf panValueStoreByteResult
    | shMemStore size address value => keep_leaf panValueShMemStoreResult
    | «return» value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueReturnResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [PostR])
    | raise exception value =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueRaiseResult] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [PostR])
    | extCall function configuration configurationLength array arrayLength =>
      obtain ⟨access, hacc, -⟩ := hE.access
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [panValueFfiExtCallSteps, hE.noMemoryHandler, hacc] at hrun
      repeat' split at hrun
      all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq, Option.pure_def] at hrun))
      all_goals (obtain ⟨rfl, -⟩ := hrun)
      all_goals (simp only [effect, PostR, Effs.keep, Post])
      all_goals (try (exact fun _ hw => hw))
    | assign kind name value =>
      cases kind with
      | global =>
        rw [evalPanValueFfiProgSteps] at hrun
        simp only [panValueAssignGlobalResult] at hrun
        repeat' split at hrun
        all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
        all_goals (obtain ⟨rfl, -⟩ := hrun)
        all_goals (simp only [effect, PostR, Effs.keep, Post])
        all_goals (try (exact fun _ hw => hw))
      | «local» =>
        rw [evalPanValueFfiProgSteps] at hrun
        simp only [panValueAssignLocalResult, evalPanValueExpCounted] at hrun
        cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
            E.topAddress E.bytesInWord value E.memoryAccess with
        | none =>
          rw [hv] at hrun
          simp only [Option.map_none, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [PostR]
        | some evaluated =>
          rw [hv] at hrun
          simp only [Option.map_some] at hrun
          split at hrun
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            by_cases hname : (name == i) = true
            · have hni : name = i := by simpa using hname
              subst hni
              by_cases hstep : isStep mode name value = true
              · simp only [effect, hname, hstep, if_true, PostR, Post]
                intro w hw
                have := eval_isStep hE hstep s w hw
                rw [hv] at this
                simp only [Option.some.injEq] at this
                simp [updatePanValueMap, this]
              · simp only [effect, hname, hstep, if_true, PostR, Effs.bad, Post]
                simp
            · have hin : (i == name) = false := by
                simp only [beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true] at hname ⊢
                exact fun h => hname h.symm
              simp only [effect, hname, PostR, Effs.keep, Post]
              intro w hw
              simp [updatePanValueMap, hin, hw]
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            simp only [PostR]
    | primitive name operator arguments =>
      rw [evalPanValueFfiProgSteps] at hrun
      by_cases hname : (name == i) = true
      · simp only [effect, hname, if_true]
        exact PostR.bad r
      · have hin : (i == name) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true] at hname ⊢
          exact fun h => hname h.symm
        simp only [panValuePrimitiveResult] at hrun
        repeat' split at hrun
        all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
        all_goals (obtain ⟨rfl, -⟩ := hrun)
        all_goals (simp only [effect, hname, PostR, Effs.keep, Post])
        all_goals (try (exact fun w hw => by simp [updatePanValueMap, hin, hw]))
    | shMemLoad size kind name address =>
      rw [evalPanValueFfiProgSteps] at hrun
      cases kind with
      | global =>
        simp only [panValueShMemLoadResult] at hrun
        repeat' split at hrun
        all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
        all_goals (obtain ⟨rfl, -⟩ := hrun)
        all_goals (simp only [effect, PostR, Effs.keep, Post])
        all_goals (try (exact fun _ hw => hw))
      | «local» =>
        by_cases hname : (name == i) = true
        · simp only [effect, hname, if_true]
          exact PostR.bad r
        · have hin : (i == name) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true] at hname ⊢
            exact fun h => hname h.symm
          simp only [panValueShMemLoadResult] at hrun
          repeat' split at hrun
          all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
          all_goals (obtain ⟨rfl, -⟩ := hrun)
          all_goals (simp only [effect, hname, PostR, Effs.keep, Post])
          all_goals (try (exact fun w hw => by simp [updatePanValueMap, hin, hw]))
    | seq first second =>
      rw [evalPanValueFfiProgSteps] at hrun
      cases h₁ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi first (memoryAccess := E.memoryAccess) (contracts := E.contracts)
          (memoryHandler := E.memoryHandler) with
      | none => rw [h₁] at hrun; simp at hrun
      | some pair =>
        obtain ⟨r₁, n₁⟩ := pair
        rw [h₁] at hrun
        have p₁ := ih first s r₁ n₁ h₁
        simp only [effect]
        cases r₁ with
        | normal l g m f =>
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases h₂ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f second
              (memoryAccess := E.memoryAccess) (contracts := E.contracts)
              (memoryHandler := E.memoryHandler) with
          | none => rw [h₂] at hrun; simp at hrun
          | some pair₂ =>
            obtain ⟨r₂, n₂⟩ := pair₂
            rw [h₂] at hrun
            simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            have p₂ := ih second ⟨l, g, m, f⟩ r₂ n₂ h₂
            exact PostR.seq_second p₁ p₂
        | continued l g m f =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact Post.join_left _ p₁
        | broke l g m f =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact Post.join_left _ p₁
        | _ =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [PostR]
    | ite condition thenBranch elseBranch =>
      rw [evalPanValueFfiProgSteps] at hrun
      simp only [effect]
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [PostR]
      | some pair =>
        obtain ⟨c, k⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hc : (c != 0) = true
        · rw [if_pos hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi thenBranch (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact PostR.join_left _ (ih thenBranch s rb nb hb)
        · rw [if_neg hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi elseBranch (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact PostR.join_right _ (ih elseBranch s rb nb hb)
    | «while» condition body =>
      by_cases hq : ((effect mode i body).normal.quiet && (effect mode i body).continued.quiet &&
          (effect mode i body).broke.quiet) = true
      · have heff : effect mode i (.while condition body) = Effs.keep := by
          simp only [effect, hq, if_true]
        rw [heff]
        simp only [Bool.and_eq_true] at hq
        obtain ⟨⟨hqn, hqc⟩, hqb⟩ := hq
        rw [evalPanValueFfiProgSteps] at hrun
        cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
            s.locals s.globals s.memory condition E.memoryAccess with
        | none =>
          rw [hcond] at hrun
          simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          simp only [PostR]
        | some pair =>
          obtain ⟨c, k⟩ := pair
          rw [hcond] at hrun
          simp only [Option.elim_some] at hrun
          by_cases hc : (c == 0) = true
          · rw [if_pos hc] at hrun
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            simp only [PostR, Effs.keep, Post]
            exact fun _ hw => hw
          · rw [if_neg hc] at hrun
            cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
                s.memory s.ffi body (memoryAccess := E.memoryAccess)
                (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
            | none => rw [hb] at hrun; simp at hrun
            | some pair =>
              obtain ⟨rb, nb⟩ := pair
              rw [hb] at hrun
              have pb := ih body s rb nb hb
              have again : ∀ l g m f,
                  (∀ w, s.locals i = some (.word w) → l i = some (.word w)) →
                  ∀ r n, (do
                    let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                      E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord
                      fuel l g m f (.while condition body) (memoryAccess := E.memoryAccess)
                      (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                    pure (loopResult, k + nb + loopSteps + 1)) = some (r, n) →
                  PostR mode i (s.locals i) Effs.keep r := by
                intro l g m f hl r n hrun
                cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler
                    E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f
                    (.while condition body) (memoryAccess := E.memoryAccess)
                    (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
                | none => rw [hloop] at hrun; simp at hrun
                | some pair =>
                  obtain ⟨rl, nl⟩ := pair
                  rw [hloop] at hrun
                  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                    Option.some.injEq, Prod.mk.injEq] at hrun
                  obtain ⟨rfl, -⟩ := hrun
                  have pl := ih (.while condition body) ⟨l, g, m, f⟩ rl nl hloop
                  rw [heff] at pl
                  cases rl <;> simp only [PostR, Effs.keep, Post] at pl ⊢
                  exact fun w hw => pl w (hl w hw)
              cases rb with
              | normal l g m f =>
                exact again l g m f (Post.of_quiet hqn pb) r n hrun
              | continued l g m f =>
                exact again l g m f (Post.of_quiet hqc pb) r n hrun
              | broke l g m f =>
                simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                  Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                simp only [PostR, Effs.keep, Post]
                exact Post.of_quiet hqb pb
              | _ =>
                simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                  Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                simp only [PostR]
      · have heff : effect mode i (.while condition body) = Effs.bad := by
          simp only [effect, hq]
          simp
        rw [heff]
        exact PostR.bad r
    | dec name shape value body =>
      rw [evalPanValueFfiProgSteps] at hrun
      cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory value E.memoryAccess shape with
      | none =>
        rw [hacc] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        simp only [PostR]
      | some accepted =>
        rw [hacc] at hrun
        simp only [Option.elim_some] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel
            (updatePanValueMap s.locals name accepted.1) s.globals s.memory s.ffi body
            (memoryAccess := E.memoryAccess) (contracts := E.contracts)
            (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at hrun
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          have pb := ih body ⟨updatePanValueMap s.locals name accepted.1, s.globals, s.memory,
            s.ffi⟩ rb nb hb
          by_cases hname : (name == i) = true
          · have hni : name = i := by simpa using hname
            subst hni
            simp only [effect, hname, if_true]
            exact PostR.restore_same pb
          · have hin : (i == name) = false := by
              simp only [beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true] at hname ⊢
              exact fun h => hname h.symm
            simp only [effect, hname]
            have hsame : updatePanValueMap s.locals name accepted.1 i = s.locals i := by
              simp [updatePanValueMap, hin]
            simp only [hsame] at pb
            exact PostR.restore_other hin pb
    | decCall name shape function arguments body =>
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi none function arguments (memoryAccess := E.memoryAccess)
          (contracts := E.contracts) (memoryHandler := E.memoryHandler)
          (preserveReturnLocals := true) with
      | none => rw [hcall] at hrun; simp at hrun
      | some pair =>
        obtain ⟨rc, nc⟩ := pair
        rw [hcall] at hrun
        simp only [Option.bind_eq_bind, Option.bind_some] at hrun
        split at hrun
        · split at hrun
          · rename_i returnedLocals g m ffi value _
            cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                (updatePanValueMap s.locals name value) g m ffi body
                (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                (memoryHandler := E.memoryHandler) with
            | none => rw [hb] at hrun; simp at hrun
            | some pair =>
              obtain ⟨rb, nb⟩ := pair
              rw [hb] at hrun
              simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              have pb := ih body ⟨updatePanValueMap s.locals name value, g, m, ffi⟩ rb nb hb
              by_cases hname : (name == i) = true
              · have hni : name = i := by simpa using hname
                subst hni
                simp only [effect, hname, if_true]
                exact PostR.restore_same pb
              · have hin : (i == name) = false := by
                  simp only [beq_eq_false_iff_ne, ne_eq, Bool.not_eq_true] at hname ⊢
                  exact fun h => hname h.symm
                simp only [effect, hname]
                have hsame : updatePanValueMap s.locals name value i = s.locals i := by
                  simp [updatePanValueMap, hin]
                simp only [hsame] at pb
                exact PostR.restore_other hin pb
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            simp only [PostR]
        all_goals first
          | (simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
             obtain ⟨rfl, -⟩ := hrun
             simp only [PostR])
          | (simp at hrun)
    | call info function arguments =>
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi info function arguments (memoryAccess := E.memoryAccess)
          (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
      | none => rw [hcall] at hrun; simp at hrun
      | some pair =>
        obtain ⟨rc, nc⟩ := pair
        rw [hcall] at hrun
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        cases fuel with
        | zero => simp [evalPanValueFfiCallSteps] at hcall
        | succ k =>
          have ihk := sih k (by omega)
          rw [evalPanValueFfiCallSteps] at hcall
          cases hargs : panValueCallArguments E.structs E.baseAddress E.topAddress
              E.bytesInWord s.locals s.globals s.memory arguments E.memoryAccess with
          | none =>
            rw [hargs] at hcall
            simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hcall
            obtain ⟨rfl, -⟩ := hcall
            simp only [PostR]
          | some argumentPair =>
            obtain ⟨values, argumentSteps⟩ := argumentPair
            rw [hargs] at hcall
            simp only [Option.elim_some] at hcall
            cases htarget : panValueCallTarget E.structs E.contracts function E.functions
                values with
            | none =>
              rw [htarget] at hcall
              simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hcall
              obtain ⟨rfl, -⟩ := hcall
              simp only [PostR]
            | some callTarget =>
              obtain ⟨body, calleeLocals⟩ := callTarget
              rw [htarget] at hcall
              simp only [Option.elim_some] at hcall
              cases hbody : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                  E.functions E.baseAddress E.topAddress E.bytesInWord k calleeLocals s.globals
                  s.memory s.ffi body (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
              | none => rw [hbody] at hcall; simp at hcall
              | some bodyPair =>
                obtain ⟨rb, nb⟩ := bodyPair
                rw [hbody] at hcall
                simp only [Option.bind_eq_bind, Option.bind_some] at hcall
                cases rb with
                | returned l g m ffi returned =>
                  simp only at hcall
                  split at hcall
                  · cases info with
                    | none =>
                      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hcall
                      obtain ⟨rfl, -⟩ := hcall
                      simp only [PostR]
                    | some infoPair =>
                      obtain ⟨destination, handlerInfo⟩ := infoPair
                      simp only at hcall
                      cases hassign : assignPanValueCallResult s.locals g destination returned
                          (structs := E.structs) with
                      | none => rw [hassign] at hcall; simp at hcall
                      | some assigned =>
                        obtain ⟨locals', globals'⟩ := assigned
                        rw [hassign] at hcall
                        simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                          Prod.mk.injEq] at hcall
                        obtain ⟨rfl, -⟩ := hcall
                        exact call_normal_post handlerInfo function arguments m ffi hassign
                  · simp only [Option.some.injEq, Prod.mk.injEq] at hcall
                    obtain ⟨rfl, -⟩ := hcall
                    simp only [PostR]
                | raised l g m ffi exception value =>
                  simp only at hcall
                  split at hcall
                  · cases info with
                    | none =>
                      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hcall
                      obtain ⟨rfl, -⟩ := hcall
                      simp only [PostR]
                    | some infoPair =>
                      obtain ⟨destination, handlerInfo⟩ := infoPair
                      cases handlerInfo with
                      | none =>
                        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hcall
                        obtain ⟨rfl, -⟩ := hcall
                        simp only [PostR]
                      | some triple =>
                        obtain ⟨caught, handlerVar, handlerProgram⟩ := triple
                        simp only at hcall
                        split at hcall
                        · split at hcall
                          · cases hh : evalPanValueFfiProgSteps E.context E.primitive E.handler
                                E.structs E.functions E.baseAddress E.topAddress E.bytesInWord k
                                (updatePanValueMap s.locals handlerVar value) g m ffi
                                handlerProgram (memoryAccess := E.memoryAccess)
                                (contracts := E.contracts)
                                (memoryHandler := E.memoryHandler) with
                            | none => rw [hh] at hcall; simp at hcall
                            | some handlerPair =>
                              obtain ⟨rh, nh⟩ := handlerPair
                              rw [hh] at hcall
                              simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                                Prod.mk.injEq] at hcall
                              obtain ⟨rfl, -⟩ := hcall
                              have ph := ihk handlerProgram
                                ⟨updatePanValueMap s.locals handlerVar value, g, m, ffi⟩ rh nh hh
                              exact call_handler_post destination caught function arguments ph
                          · simp at hcall
                        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hcall
                          obtain ⟨rfl, -⟩ := hcall
                          simp only [PostR]
                  · simp at hcall
                | _ =>
                  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hcall
                  obtain ⟨rfl, -⟩ := hcall
                  simp only [PostR]

end InitECandidate.Solver.GuestBound
