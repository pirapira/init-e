import InitECandidate.Solver.GuestBound.RlpHeader

/-!
# Specification of `rlp_item_total`

When `rlp_item_total(p, len)` returns `t`, then `1 ≤ t ≤ len`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem headerVals_inv {len : Word} {values : List (PanValue Word)} (h : headerVals len values) :
    ∃ a b c, values = [.rStruct [.word a, .word b, c]] ∧ 1 ≤ a.toNat + b.toNat ∧
      a.toNat + b.toNat ≤ len.toNat := by
  unfold headerVals at h
  split at h
  · rename_i a b c
    exact ⟨a, b, c, rfl, h⟩
  · exact h.elim

/-- Two arguments evaluate separately. -/
theorem evalArgs2_inv {s : St σ} {e₁ e₂ : Exp Word} {values : List (PanValue Word)}
    (h : E.evalArgs s [e₁, e₂] = some values) :
    ∃ v₁ v₂, E.eval s e₁ = some v₁ ∧ E.eval s e₂ = some v₂ ∧ values = [v₁, v₂] := by
  simp only [Env.evalArgs, Env.eval] at h ⊢
  cases h₁ : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord e₁ E.memoryAccess with
  | none => simp [evalPanValueExps, evalPanValueExp.evalPanValueExps, h₁] at h
  | some v₁ =>
    cases h₂ : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord e₂ E.memoryAccess with
    | none => simp [evalPanValueExps, evalPanValueExp.evalPanValueExps, h₁, h₂] at h
    | some v₂ =>
      simp [evalPanValueExps, evalPanValueExp.evalPanValueExps, h₁, h₂] at h
      exact ⟨v₁, v₂, rfl, rfl, h.symm⟩

/-- Binding two parameters. -/
theorem bind2 {x y : VarName} {v₁ v₂ : PanValue Word}
    {locals : VarName → Option (PanValue Word)}
    (h : bindPanValueParameters [x, y] [v₁, v₂] = some locals) : locals y = some v₂ := by
  simp [bindPanValueParameters] at h
  rw [← h]
  simp [updatePanValueMap]

/-- A field of a struct-valued local. -/
theorem eval_rField (s : St σ) (i : Nat) (h : VarName) (fields : List (PanValue Word))
    (hh : s.locals h = some (.rStruct fields)) :
    E.eval s (.rField i (.var .local h)) = fields[i]? := by
  simp [Env.eval, evalPanValueExp, hh]

theorem nodest_of_error {r : Result σ} {locals : VarName → Option (PanValue Word)}
    (herr : r.isError = true) :
    r.leaves = false ∧ ∀ l g m ffi, r = .normal l g m ffi → l = locals := by
  cases r with
  | error l g m ffi => exact ⟨rfl, fun _ _ _ _ h => by cases h⟩
  | _ => cases herr

/-- A call without a destination does not return from, break or continue the
caller, and leaves its locals alone when it finishes normally. -/
theorem call_nodest_inv {f : FunName} {fuel : Nat} {s : St σ} {arguments : List (Exp Word)}
    {r : Result σ} {n : Nat}
    (h : E.run fuel s (.call (some (none, none)) f arguments) = some (r, n)) :
    r.leaves = false ∧ ∀ l g m ffi, r = .normal l g m ffi → l = s.locals := by
  rcases call_run_inv (some none) h with herr | ⟨fuel', parameters, body, values, calleeLocals,
    rb, nb, -, -, -, -, hout⟩
  · exact nodest_of_error herr
  · cases rb with
    | returned l g m ffi values' =>
      simp only [CallOutcome] at hout
      rcases hout with herr | ⟨l', g', hassign, rfl⟩
      · exact nodest_of_error herr
      · refine ⟨rfl, ?_⟩
        intro l'' g'' m'' ffi'' heq
        simp only [PanValueFfiControlResult.normal.injEq] at heq
        obtain ⟨rfl, -, -, -⟩ := heq
        unfold assignPanValueCallResult at hassign
        split at hassign <;> simp_all
    | raised l g m ffi exception value =>
      simp only [CallOutcome] at hout
      subst hout
      exact ⟨rfl, fun _ _ _ _ h => by cases h⟩
    | finalFfi l g m ffi event =>
      simp only [CallOutcome] at hout
      subst hout
      exact ⟨rfl, fun _ _ _ _ h => by cases h⟩
    | _ =>
      simp only [CallOutcome] at hout
      exact nodest_of_error hout

/-- The returned values are one word `t` with `1 ≤ t ≤ len`. -/
def totalVals (len : Word) : List (PanValue Word) → Prop
  | [.word t] => 1 ≤ t.toNat ∧ t.toNat ≤ len.toNat
  | _ => False

/-- A returned total `t` satisfies `1 ≤ t ≤ len`. -/
def TotalPost (len : Word) : Result σ → Prop
  | .returned _ _ _ _ values => totalVals len values
  | _ => True

theorem TotalPost.of_not_returned {len : Word} {r : Result σ} (h : r.leaves = false) :
    TotalPost len r := by
  cases r <;> trivial

theorem TotalPost.of_error {len : Word} {r : Result σ} (h : r.isError = true) :
    TotalPost len r := by
  cases r <;> trivial

theorem TotalPost.restore {len : Word} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : TotalPost len r) : TotalPost len (restorePanValueFfiLocal x old r) := by
  cases r <;> exact h

/-- `rlp_item_total(p, len)` returns `t` with `1 ≤ t ≤ len`. -/
theorem rlp_item_total_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_item_total" E.functions = some (parameters, body))
    (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (lenv : Word)
    (hrun : E.run fuel s body = some (r, n)) (hlen : s.locals "len" = some (.word lenv)) :
    TotalPost lenv r := by
  have hbody := (fun_of_index 112 hE.functions (by guest_decl_at 112) (by decide +kernel)
    hlookup).1
  subst hbody
  rcases decCall_run_inv hrun with herr | ⟨f1, params', calleeBody, values, calleeLocals, rb, nb,
    hlookup', hvalues, hbind, hcallee, hout⟩
  · exact TotalPost.of_error herr
  have hparams := (fun_of_index 109 hE.functions (by guest_decl_at 109) (by decide +kernel)
    hlookup').2
  obtain ⟨v₁, v₂, -, hv₂, rfl⟩ := evalArgs2_inv hvalues
  simp only [eval_local] at hv₂
  rw [hlen] at hv₂
  simp only [Option.some.injEq] at hv₂
  subst hv₂
  rw [hparams] at hbind
  have hclen : calleeLocals "len" = some (.word lenv) := bind2 hbind
  have hspec := rlp_item_header_spec hE params' calleeBody hlookup' f1
    ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb nb lenv hcallee hclen
  cases rb with
  | returned l g m ffi values' =>
    obtain ⟨a, b, c, rfl, hge, hle⟩ := headerVals_inv hspec
    obtain ⟨f2, r', n', -, hrun', rfl⟩ := hout
    refine TotalPost.restore ?_
    have hh : (updatePanValueMap s.locals "h" (PanValue.rStruct [.word a, .word b, c])) "h" =
        some (.rStruct [.word a, .word b, c]) := by simp [updatePanValueMap]
    obtain ⟨f3, r₁, n₁, h₁, hrest⟩ := seq_run_inv hrun'
    -- the conditional call keeps the locals or does not return
    have hite : r₁.leaves = false ∧ ∀ l₁ g₁ m₁ ffi₁, r₁ = .normal l₁ g₁ m₁ ffi₁ →
        l₁ = updatePanValueMap s.locals "h" (PanValue.rStruct [.word a, .word b, c]) := by
      rcases ite_run_inv h₁ with herr | ⟨f4, v, n'', -, hbranch⟩
      · exact nodest_of_error herr
      · rcases hbranch with ⟨-, hcall⟩ | ⟨-, hskip⟩
        · exact call_nodest_inv hcall
        · have hs := skip_inv hskip
          subst hs
          exact ⟨rfl, fun _ _ _ _ h => by
            simp only [PanValueFfiControlResult.normal.injEq] at h
            exact h.1.symm⟩
    cases r₁ with
    | normal l₁ g₁ m₁ ffi₁ =>
      have hl₁ := hite.2 l₁ g₁ m₁ ffi₁ rfl
      subst hl₁
      simp only at hrest
      obtain ⟨n₂, hrun₂⟩ := hrest
      rcases return_inv hrun₂ with herr | ⟨v, hv, rfl⟩
      · exact TotalPost.of_error herr
      obtain ⟨va, vb, hva, hvb, rfl⟩ := eval_add hE.word hv
      rw [eval_rField _ 0 "h" _ hh] at hva
      rw [eval_rField _ 1 "h" _ hh] at hvb
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq,
        PanValue.word.injEq] at hva hvb
      subst hva hvb
      show 1 ≤ (a + b).toNat ∧ (a + b).toNat ≤ lenv.toNat
      have hlt := lenv.isLt
      have hadd : (a + b).toNat = a.toNat + b.toNat := by
        rw [BitVec.toNat_add]
        omega
      omega
    | _ =>
      simp only at hrest
      subst hrest
      exact TotalPost.of_not_returned hite.1
  | raised l g m ffi exception value =>
    simp only at hout
    subst hout
    trivial
  | finalFfi l g m ffi event =>
    simp only at hout
    subst hout
    trivial
  | _ => exact hout.elim

end InitECandidate.Solver.GuestBound
