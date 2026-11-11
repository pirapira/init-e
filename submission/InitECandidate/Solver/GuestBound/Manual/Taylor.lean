import InitECandidate.Solver.GuestBound.U256Zero
import InitECandidate.Solver.GuestBound.Manual.BlsInv

/-!
# `taylor_exponential`

The loop `while nz == 0 { …; di = u256_from_word(i) * den; acc = p / di;
i = i + 1; nz = u256_is_zero(acc) }` has no guard on `i`, but when `i` is 0 at
the start of an iteration, `di` is 0, the division by zero returns 0 and `nz`
becomes 1. So the loop runs at most `2^64 + 1` times from any state.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A call assigning to the local `y`, whose callee is known to end in `.error`
or return `v` without changing the rest of the state. -/
theorem callAssign_of_spec {f : FunName} {y : VarName} {arguments : List (Exp Word)}
    {s : St σ} {r : Result σ} {v : PanValue Word}
    (hspec : ∀ parameters body values calleeLocals rb,
      lookupPanFunction f E.functions = some (parameters, body) →
      E.evalArgs s arguments = some values →
      bindPanValueParameters parameters values = some calleeLocals →
      Runs E ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body rb →
      rb.isError = true ∨ ∃ l, rb = .returned l s.globals s.memory s.ffi [v])
    (h : Runs E s (.call (some (some (.local, y), none)) f arguments) r) :
    r.isError = true ∨ r = .normal (updatePanValueMap s.locals y v) s.globals s.memory s.ffi := by
  rcases runs_call_inv (some (some (.local, y))) h with herr | ⟨parameters, body, values,
    calleeLocals, rb, hlookup, hvalues, hbind, hcallee, hout⟩
  · exact Or.inl herr
  rcases hspec parameters body values calleeLocals rb hlookup hvalues hbind hcallee with herr |
    ⟨l, rfl⟩
  · cases rb with
    | error l g m f =>
      simp only [CallOutcome] at hout
      exact Or.inl hout
    | _ => cases herr
  · simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl herr
    simp only [assignPanValueCallResult] at hassign
    split at hassign
    · simp only [Option.some.injEq, Prod.mk.injEq] at hassign
      obtain ⟨rfl, rfl⟩ := hassign
      exact Or.inr rfl
    · cases hassign

/-- `if c { trap_with(…); }` leaves the state alone or does not end normally. -/
theorem trapIte_runs (hE : GuestEnv E) {c : Exp Word} {arguments : List (Exp Word)} {s : St σ}
    {r : Result σ} :
    Runs E s (.ite c (.call (some (none, none)) "trap_with" arguments) .skip) r →
    match r with
    | .normal l g m f => l = s.locals ∧ g = s.globals ∧ m = s.memory ∧ f = s.ffi
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  intro h
  rw [runs_ite] at h
  split at h
  · split at h
    · rw [runs_skip] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl⟩
    · obtain ⟨fuel, n, hrun⟩ := h
      have hnr := call_noReturn (trap_with_noReturn hE) (some none) hrun
      cases r with
      | normal l g m f => cases hnr.2
      | continued l g m f => cases hnr.1
      | broke l g m f => cases hnr.1
      | _ => trivial
  · subst h
    simp [St.err]

/-- The end of the loop body, after `di = u256_from_word(i)`. -/
def tayTail : Prog Word :=
  .seq (.call (some (some (.local, "di"), none)) "u256_mul" [.var .local "di", .var .local "den"])
    (.seq (.call (some (some (.local, "acc"), none)) "u256_div"
        [.var .local "p", .var .local "di"])
      (.seq (.assign .local "i" (.op .add [.var .local "i", .const (BitVec.ofNat 64 1)]))
        (.call (some (some (.local, "nz"), none)) "u256_is_zero" [.var .local "acc"])))

/-- What a run of the tail guarantees: `i` is incremented, only `di`, `acc`,
`i`, `nz` change, and from `i = 0` the flag `nz` is set. -/
def TayPost (iw : Word) (s : St σ) : Result σ → Prop
  | .normal l _ _ _ =>
      l "i" = some (.word (iw + 1)) ∧ (iw = 0 → l "nz" = some (.word 1)) ∧
        ∀ z, z ≠ "di" → z ≠ "acc" → z ≠ "i" → z ≠ "nz" → l z = s.locals z
  | .continued _ _ _ _ | .broke _ _ _ _ => False
  | _ => True

theorem TayPost.of_error {iw : Word} {s : St σ} {r : Result σ} (h : r.isError = true) :
    TayPost iw s r := by
  cases r <;> first | trivial | cases h

set_option maxHeartbeats 2000000 in
/-- The tail from `i = 0`: `di`, `acc` become zero and `nz` becomes 1. -/
theorem tayTail_zero (hE : GuestEnv E) {dw : Word} {s : St σ} {r : Result σ}
    (hi : s.locals "i" = some (.word 0))
    (hden : s.locals "den" = some (.rStruct [.word dw, .word 0, .word 0, .word 0]))
    (hdi : s.locals "di" = some zero4) (h : Runs E s tayTail r) : TayPost 0 s r := by
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp h
  rcases callAssign_of_spec (v := zero4) (by
      intro parameters body values calleeLocals rb hlookup hvalues hbind hcallee
      have hparams := (fun_of_index 60 hE.functions (by guest_decl_at 60) (by decide +kernel)
        hlookup).2
      simp only [evalArgs_cons, evalArgs_nil, evalF_local, hdi, hden, Option.map_some,
        Option.some.injEq] at hvalues
      subst hvalues
      rw [hparams] at hbind
      simp [bindPanValueParameters] at hbind
      exact u256_mul_zero hE parameters body hlookup ⟨calleeLocals, s.globals, s.memory, s.ffi⟩
        rb dw
        (by rw [← hbind]; simp [updatePanValueMap]) (by rw [← hbind]; simp [updatePanValueMap])
        hcallee) h₁ with herr | rfl
  · cases r₁ with
    | error l g m f =>
      simp only at hrest
      subst hrest
      trivial
    | _ => cases herr
  simp only at hrest
  obtain ⟨r₂, h₂, hrest₂⟩ := runs_seq.mp hrest
  rcases callAssign_of_spec (v := zero4) (by
      intro parameters body values calleeLocals rb hlookup hvalues hbind hcallee
      have hparams := (fun_of_index 70 hE.functions (by guest_decl_at 70) (by decide +kernel)
        hlookup).2
      simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local,
        update_lookup, beq_self_eq_true, if_true, if_false, Option.map_some] at hvalues
      cases hp : s.locals "p" with
      | none => rw [hp] at hvalues; cases hvalues
      | some pv =>
        rw [hp] at hvalues
        simp only [Option.some.injEq] at hvalues
        subst hvalues
        rw [hparams] at hbind
        simp [bindPanValueParameters] at hbind
        exact u256_div_zero hE parameters body hlookup
          ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb
          (by rw [← hbind]; simp [updatePanValueMap]) hcallee) h₂ with herr | rfl
  · cases r₂ with
    | error l g m f =>
      simp only at hrest₂
      subst hrest₂
      trivial
    | _ => cases herr
  simp only at hrest₂
  obtain ⟨r₃, h₃, hrest₃⟩ := runs_seq.mp hrest₂
  rw [runs_assign_local] at h₃
  simp (config := { decide := true }) only [evalF_op hE.word, evalArgs_cons, evalArgs_nil,
    evalF_local, eval_const, update_lookup, if_false, hi, wordsProj_cons, wordsProj_nil, wordOp,
    List.foldr, Option.map_some] at h₃
  split at h₃
  swap
  · subst h₃
    simp only [St.err] at hrest₃
    subst hrest₃
    trivial
  subst h₃
  simp only at hrest₃
  rcases callAssign_of_spec (v := PanValue.word 1) (by
      intro parameters body values calleeLocals rb hlookup hvalues hbind hcallee
      have hparams := (fun_of_index 42 hE.functions (by guest_decl_at 42) (by decide +kernel)
        hlookup).2
      simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local,
        update_lookup, beq_self_eq_true, if_true, if_false, Option.map_some,
        Option.some.injEq] at hvalues
      subst hvalues
      rw [hparams] at hbind
      simp [bindPanValueParameters] at hbind
      exact Or.inr ⟨_, u256_is_zero_zero hE parameters body hlookup
        ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb
        (by rw [← hbind]; simp [updatePanValueMap]) hcallee⟩) hrest₃ with herr | rfl
  · exact TayPost.of_error herr
  refine ⟨?_, fun _ => ?_, ?_⟩
  · simp (config := { decide := true }) [update_lookup]
  · simp (config := { decide := true }) [update_lookup]
  · intro z h1 h2 h3 h4
    simp [update_lookup, h1, h2, h3, h4]

end InitECandidate.Solver.GuestBound
