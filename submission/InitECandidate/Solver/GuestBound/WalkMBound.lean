import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import InitECandidate.Solver.GuestBound.WalkM

/-!
# Iteration bound for loops that change only a few locals

If a loop body satisfies `walkOkM M`, each loop-head state is determined by a
code in `Fin m → Word ⊕ Fin m` (`m = M.length`): every tracked local holds a
word or one of the `m` entry values. A returning run cannot visit the same
state twice, so it takes at most `(2^64 + m)^m` iterations.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The locals a statement assigns, without duplicates, added to `acc`. -/
def assignedInto : Prog Word → List VarName → List VarName
  | .assign .local name _, acc => if acc.contains name then acc else name :: acc
  | .seq first second, acc => assignedInto second (assignedInto first acc)
  | .ite _ thenBranch elseBranch, acc => assignedInto elseBranch (assignedInto thenBranch acc)
  | .dec _ _ _ body, acc => assignedInto body acc
  | .decCall _ _ _ _ body, acc => assignedInto body acc
  | _, acc => acc

/-- The locals a loop body assigns. -/
def assignedLocals (body : Prog Word) : List VarName := assignedInto body []

/-- The loop body changes only the locals it assigns, by word expressions or each other. -/
def walkMLoop (callee : FunName → Bool) (body : Prog Word) : Bool :=
  walkOkM callee (assignedLocals body) body

/-- Iteration bound for `m` tracked locals. -/
def walkIters (m : Nat) : Nat := (2 ^ 64 + m) ^ m

section core
variable (M : List VarName) (base : St σ)

/-- Codes of loop-head states. -/
abbrev Code (M : List VarName) := Fin M.length → Word ⊕ Fin M.length

noncomputable instance (M : List VarName) : Fintype (Code M) := inferInstance

theorem code_card (M : List VarName) : Fintype.card (Code M) ≤ walkIters M.length := by
  have h : Fintype.card (Code M) = (Fintype.card Word + M.length) ^ M.length := by
    show Fintype.card (Fin M.length → Word ⊕ Fin M.length) = _
    rw [Fintype.card_fun, Fintype.card_sum, Fintype.card_fin]
  rw [h]
  exact Nat.pow_le_pow_left (Nat.add_le_add_right word_card _) _

/-- `s` agrees with `base` outside `M`, and each local in `M` holds a word or
an entry value of a local in `M`. -/
def OkM (M : List VarName) (base s : St σ) : Prop :=
  s.globals = base.globals ∧ s.memory = base.memory ∧ s.ffi = base.ffi ∧
    (∀ x, x ∉ M → s.locals x = base.locals x) ∧
    (∀ x, x ∈ M → IsWordVal (s.locals x) ∨ ∃ y, y ∈ M ∧ s.locals x = base.locals y)

open Classical in
/-- The code of one value: its word, or the position of an entry value equal to it. -/
noncomputable def encVal (M : List VarName) (base : St σ) (v : Option (PanValue Word)) :
    Word ⊕ Fin M.length :=
  if h : ∃ w, v = some (.word w) then .inl (Classical.choose h)
  else if h' : ∃ j : Fin M.length, base.locals (M.get j) = v then .inr (Classical.choose h')
  else .inl 0

/-- The code of a state. -/
noncomputable def enc (M : List VarName) (base s : St σ) : Code M :=
  fun j => encVal M base (s.locals (M.get j))

theorem encVal_inj {v v' : Option (PanValue Word)}
    (hv : IsWordVal v ∨ ∃ j : Fin M.length, base.locals (M.get j) = v)
    (hv' : IsWordVal v' ∨ ∃ j : Fin M.length, base.locals (M.get j) = v')
    (h : encVal M base v = encVal M base v') : v = v' := by
  unfold encVal at h
  by_cases hw : ∃ w, v = some (.word w)
  · by_cases hw' : ∃ w, v' = some (.word w)
    · rw [dif_pos hw, dif_pos hw'] at h
      have h1 := Classical.choose_spec hw
      have h2 := Classical.choose_spec hw'
      simp only [Sum.inl.injEq] at h
      rw [h1, h2, h]
    · rw [dif_pos hw, dif_neg hw'] at h
      have hb : ∃ j : Fin M.length, base.locals (M.get j) = v' := by
        rcases hv' with h' | h'
        · exact absurd h' hw'
        · exact h'
      rw [dif_pos hb] at h
      cases h
  · have hb : ∃ j : Fin M.length, base.locals (M.get j) = v := by
      rcases hv with h' | h'
      · exact absurd h' hw
      · exact h'
    by_cases hw' : ∃ w, v' = some (.word w)
    · rw [dif_neg hw, dif_pos hb, dif_pos hw'] at h
      cases h
    · have hb' : ∃ j : Fin M.length, base.locals (M.get j) = v' := by
        rcases hv' with h' | h'
        · exact absurd h' hw'
        · exact h'
      rw [dif_neg hw, dif_pos hb, dif_neg hw', dif_pos hb'] at h
      have h1 := Classical.choose_spec hb
      have h2 := Classical.choose_spec hb'
      simp only [Sum.inr.injEq] at h
      rw [← h1, ← h2, h]

theorem okM_allowed {s : St σ} (hs : OkM M base s) (j : Fin M.length) :
    IsWordVal (s.locals (M.get j)) ∨
      ∃ j' : Fin M.length, base.locals (M.get j') = s.locals (M.get j) := by
  rcases hs.2.2.2.2 (M.get j) (List.get_mem M j) with hw | ⟨y, hy, hxy⟩
  · exact Or.inl hw
  · obtain ⟨j', hj'⟩ := List.get_of_mem hy
    exact Or.inr ⟨j', by rw [hj', hxy]⟩

/-- States with the same code are equal. -/
theorem enc_inj {s s' : St σ} (hs : OkM M base s) (hs' : OkM M base s')
    (h : enc M base s = enc M base s') : s = s' := by
  have hlocals : s.locals = s'.locals := by
    funext x
    by_cases hx : x ∈ M
    · obtain ⟨j, rfl⟩ := List.get_of_mem hx
      exact encVal_inj M base (okM_allowed M base hs j) (okM_allowed M base hs' j)
        (congrFun h j)
    · rw [hs.2.2.2.1 x hx, hs'.2.2.2.1 x hx]
  cases s with
  | mk l g mem f =>
    cases s' with
    | mk l' g' mem' f' =>
      simp only at hlocals
      obtain ⟨hg, hm, hf, -, -⟩ := hs
      obtain ⟨hg', hm', hf', -, -⟩ := hs'
      simp only at hg hm hf hg' hm' hf'
      rw [hlocals, hg, hm, hf, hg', hm', hf']

variable (hE : WordEnv E) {c : Exp Word} {body : Prog Word} {b : Nat}
  {callee : FunName → Bool} (hcallee : ∀ f, callee f = true → FunKeeps (quietKeeper E) f)
  (hw : walkOkM callee M body = true) (hbody : Costs E body b)

include hE hcallee hw hbody in
/-- With the codes in `V` already visited by longer runs, the loop has at most
`walkIters m - |V|` iterations left. -/
theorem walkM_core (r : Result σ) (hne : r.isError = false) :
    ∀ (fuel : Nat) (V : Finset (Code M)) (s : St σ) (m : Nat),
      OkM M base s → E.run fuel s (.while c body) = some (r, m) →
      (∀ code ∈ V, ∃ s' fuel' m', OkM M base s' ∧ enc M base s' = code ∧ fuel ≤ fuel' ∧
        m < m' ∧ E.run fuel' s' (.while c body) = some (r, m')) →
      m + V.card * (panValueExpStepCost c + b + 1) ≤
        walkIters M.length * (panValueExpStepCost c + b + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro V s m _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro V s m hok hrun0 hV
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
          have again : ∀ l g mem f, nb ≤ b → OkM M base ⟨l, g, mem, f⟩ →
              (do
                let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                  E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                  l g mem f (.while c body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                pure (loopResult, kc + nb + loopSteps + 1)) = some (r, m) →
              m + V.card * (panValueExpStepCost c + b + 1) ≤
                walkIters M.length * (panValueExpStepCost c + b + 1) := by
            intro l g mem f hnb hok' hrun
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
              have hV' : ∀ code ∈ insert (enc M base s) V, ∃ s' fuel' m', OkM M base s' ∧
                  enc M base s' = code ∧ fuel ≤ fuel' ∧ nl < m' ∧
                  E.run fuel' s' (.while c body) = some (rl, m') := by
                intro code hcode
                rcases Finset.mem_insert.mp hcode with rfl | hcode
                · exact ⟨s, fuel + 1, _, hok, rfl, Nat.le_succ _, by omega, hrun0⟩
                · obtain ⟨s', fuel', m', hok'', henc, hfuel, hlt, hrun'⟩ := hV code hcode
                  exact ⟨s', fuel', m', hok'', henc, by omega, by omega, hrun'⟩
              have hih := ih (insert (enc M base s) V) ⟨l, g, mem, f⟩ nl hok' hloop hV'
              rw [Finset.card_insert_of_notMem hnotV, Nat.succ_mul] at hih
              omega
          have walk := walkM_sound hE callee hcallee M fuel body s rb nb hw hb
          have step : ∀ l g mem f, WalkM M s (.normal l g mem f : Result σ) →
              OkM M base ⟨l, g, mem, f⟩ := by
            intro l g mem f hwalk
            obtain ⟨h1, h2, h3, h4, h5⟩ := hwalk
            obtain ⟨hg, hm, hf, hl, hvals⟩ := hok
            refine ⟨h1.trans hg, h2.trans hm, h3.trans hf,
              fun x hx => (h4 x hx).trans (hl x hx), ?_⟩
            intro x hx
            rcases h5 x hx with hword | ⟨y, hy, hxy⟩
            · exact Or.inl hword
            · rcases hvals y hy with hword | ⟨z, hz, hyz⟩
              · exact Or.inl (by show IsWordVal (l x); rw [hxy]; exact hword)
              · exact Or.inr ⟨z, hz, hxy.trans hyz⟩
          cases rb with
          | normal l g mem f =>
            have hnb : nb ≤ b := (hbody fuel s _ nb trivial hb rfl).1
            exact again l g mem f hnb (step l g mem f walk) hrun
          | continued l g mem f =>
            have hnb : nb ≤ b := (hbody fuel s _ nb trivial hb rfl).1
            exact again l g mem f hnb (step l g mem f walk) hrun
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

/-- A loop that changes only `m` locals, by word expressions or each other,
costs at most `(2^64 + m)^m` iterations of its guard and body. -/
theorem walkMLoop_costs (hE : WordEnv E) (callee : FunName → Bool)
    (hcallee : ∀ f, callee f = true → FunKeeps (quietKeeper E) f) (c : Exp Word)
    (body : Prog Word) (b : Nat)
    (hcheck : walkMLoop callee body = true) (hbody : Costs E body b) :
    Costs E (.while c body)
      (walkIters (assignedLocals body).length * (expCost c + b + 1)) := by
  unfold Costs Triple
  intro fuel s r m _ hrun hne
  refine ⟨?_, trivial⟩
  rw [← stepCost_eq]
  have hok : OkM (assignedLocals body) s s :=
    ⟨rfl, rfl, rfl, fun _ _ => rfl, fun x hx => Or.inr ⟨x, hx, rfl⟩⟩
  have h := walkM_core (assignedLocals body) s hE hcallee hcheck hbody r hne fuel ∅ s m hok hrun
    (by intro code hcode; simp at hcode)
  simpa using h

end InitECandidate.Solver.GuestBound
