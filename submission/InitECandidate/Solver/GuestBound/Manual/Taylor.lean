import InitECandidate.Solver.GuestBound.U256Zero
import InitECandidate.Solver.GuestBound.Manual.BlsInv
import InitECandidate.Solver.GuestBound.TripleCall

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

/-- The tail increments `i` and changes only `di`, `acc`, `i`, `nz`. -/
theorem tayTail_frame (hE : GuestEnv E) {iw : Word} {s : St σ} {r : Result σ}
    (hi : s.locals "i" = some (.word iw)) :
    Runs E s tayTail r →
    match r with
    | .normal l _ _ _ => l "i" = some (.word (iw + 1)) ∧
        ∀ z, z ≠ "di" → z ≠ "acc" → z ≠ "i" → z ≠ "nz" → l z = s.locals z
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  intro h
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp h
  have f1 := call_local_frame h₁
  cases r₁ with
  | normal l1 g1 m1 ff1 =>
    simp only at f1 hrest
    obtain ⟨r₂, h₂, hrest₂⟩ := runs_seq.mp hrest
    have f2 := call_local_frame h₂
    cases r₂ with
    | normal l2 g2 m2 ff2 =>
      simp only at f2 hrest₂
      obtain ⟨r₃, h₃, hrest₃⟩ := runs_seq.mp hrest₂
      rw [runs_assign_local] at h₃
      have hi2 : l2 "i" = some (.word iw) := by
        rw [f2 "i" (by decide), f1 "i" (by decide)]
        exact hi
      simp only [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_local, eval_const, hi2,
        wordsProj_cons, wordsProj_nil, wordOp, List.foldr, Option.map_some] at h₃
      split at h₃
      · subst h₃
        simp only at hrest₃
        have f4 := call_local_frame hrest₃
        cases r with
        | normal l g m f =>
          simp only at f4
          refine ⟨?_, ?_⟩
          · rw [f4 "i" (by decide)]
            simp [update_lookup]
          · intro z h1 h2 h3 h4
            have h3' : (z == "i") = false := by simpa using h3
            rw [f4 z h4]
            simp only [update_lookup, h3', Bool.false_eq_true, if_false]
            rw [f2 z h2, f1 z h1]
        | continued l g m f => exact f4.elim
        | broke l g m f => exact f4.elim
        | _ => trivial
      · subst h₃
        simp only [St.err] at hrest₃
        subst hrest₃
        trivial
    | continued l2 g2 m2 ff2 => exact f2.elim
    | broke l2 g2 m2 ff2 => exact f2.elim
    | _ =>
      simp only at hrest₂
      subst hrest₂
      trivial
  | continued l1 g1 m1 ff1 => exact f1.elim
  | broke l1 g1 m1 ff1 => exact f1.elim
  | _ =>
    simp only at hrest
    subst hrest
    trivial

/-- The tail of the loop body. -/
theorem tayTail_runs (hE : GuestEnv E) {iw dw : Word} {s : St σ} {r : Result σ}
    (hi : s.locals "i" = some (.word iw))
    (hden : s.locals "den" = some (.rStruct [.word dw, .word 0, .word 0, .word 0]))
    (hdi : s.locals "di" = some (.rStruct [.word iw, .word 0, .word 0, .word 0]))
    (h : Runs E s tayTail r) : TayPost iw s r := by
  by_cases hz : iw = 0
  · subst hz
    exact tayTail_zero hE hi hden hdi h
  · have hf := tayTail_frame hE hi h
    cases r with
    | normal l g m f => exact ⟨hf.1, fun h0 => absurd h0 hz, hf.2⟩
    | continued l g m f => exact hf.elim
    | broke l g m f => exact hf.elim
    | _ => trivial

/-- The body of the loop of `taylor_exponential`. -/
def tayBody : Prog Word :=
  .seq (.call (some (some (.local, "out"), none)) "u256_add"
      [.var .local "out", .var .local "acc"])
    (.decCall "prod" (.comb [.one, .one, .one, .one, .one, .one, .one, .one]) "u256_mul_full"
      [.var .local "acc", .var .local "num"]
      (.seq
        (.ite (.cmp .notEqual (.op .or [.rField 4 (.var .local "prod"),
            .rField 5 (.var .local "prod"), .rField 6 (.var .local "prod"),
            .rField 7 (.var .local "prod")]) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) "trap_with" [.const (BitVec.ofNat 64 3)]) .skip)
        (.dec "p" (.comb [.one, .one, .one, .one])
          (.rStruct [.rField 0 (.var .local "prod"), .rField 1 (.var .local "prod"),
            .rField 2 (.var .local "prod"), .rField 3 (.var .local "prod")])
          (.decCall "di" (.comb [.one, .one, .one, .one]) "u256_from_word" [.var .local "i"]
            tayTail))))

/-- What one loop iteration guarantees. -/
def TayBodyPost (iw : Word) (dv : Option (PanValue Word)) : Result σ → Prop
  | .normal l _ _ _ =>
      l "i" = some (.word (iw + 1)) ∧ l "den" = dv ∧ (iw = 0 → l "nz" = some (.word 1))
  | .continued _ _ _ _ | .broke _ _ _ _ => False
  | _ => True

theorem TayBodyPost.of_error {iw : Word} {dv : Option (PanValue Word)} {r : Result σ}
    (h : r.isError = true) : TayBodyPost iw dv r := by
  cases r <;> first | trivial | cases h

theorem restore_err (x : VarName) (old : Option (PanValue Word)) (r : Result σ) :
    (restorePanValueFfiLocal x old r).isError = r.isError := by
  cases r <;> rfl

set_option maxHeartbeats 2000000 in
/-- One loop iteration increments `i`, keeps `den`, and from `i = 0` sets `nz`. -/
theorem tayBody_runs (hE : GuestEnv E) {iw dw : Word} {s : St σ} {r : Result σ}
    (hi : s.locals "i" = some (.word iw))
    (hden : s.locals "den" = some (.rStruct [.word dw, .word 0, .word 0, .word 0])) :
    Runs E s tayBody r → TayBodyPost iw (s.locals "den") r := by
  intro h
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp h
  have f1 := call_local_frame h₁
  cases r₁ with
  | normal l1 g1 m1 ff1 =>
    simp only at f1 hrest
    have hi1 : l1 "i" = some (.word iw) := by rw [f1 "i" (by decide)]; exact hi
    have hden1 : l1 "den" = s.locals "den" := f1 "den" (by decide)
    rcases runs_decCall_inv hrest with herr | ⟨parameters, cbody, values, cl, rb, -, -, -, -,
      hout⟩
    · exact TayBodyPost.of_error herr
    cases rb with
    | returned lr g m ffi vs =>
      cases vs with
      | nil => exact hout.elim
      | cons v rest =>
        cases rest with
        | cons v' rest' => exact hout.elim
        | nil =>
          obtain ⟨r', -, hrun', rfl⟩ := hout
          obtain ⟨r₂, h₂, hrest₂⟩ := runs_seq.mp hrun'
          have ft := trapIte_runs hE h₂
          cases r₂ with
          | normal l2 g2 m2 ff2 =>
            obtain ⟨rfl, rfl, rfl, rfl⟩ := ft
            simp only at hrest₂
            rw [runs_dec] at hrest₂
            split at hrest₂
            · split at hrest₂
              · rename_i pv _ _
                obtain ⟨rb3, hrun3, rfl⟩ := hrest₂
                rcases runs_decCall_inv hrun3 with herr | ⟨params4, body4, values4, cl4, rb4,
                  hlookup4, hvalues4, hbind4, hcallee4, hout4⟩
                · exact TayBodyPost.of_error (by rw [restore_err, restore_err]; exact herr)
                have hparams4 := (fun_of_index 39 hE.functions (by guest_decl_at 39)
                  (by decide +kernel) hlookup4).2
                simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil,
                  evalF_local, update_lookup, if_false, hi1, Option.map_some,
                  Option.some.injEq] at hvalues4
                subst hvalues4
                rw [hparams4] at hbind4
                simp [bindPanValueParameters] at hbind4
                have hspec := u256_from_word_spec hE params4 body4 hlookup4 _ rb4 iw
                  (by rw [← hbind4]; simp [updatePanValueMap]) hcallee4
                subst hspec
                obtain ⟨r5, -, hrun5, rfl⟩ := hout4
                have ht := tayTail_runs hE (iw := iw) (dw := dw)
                  (by simp (config := { decide := true }) only [update_lookup, if_false]
                      exact hi1)
                  (by simp (config := { decide := true }) only [update_lookup, if_false]
                      rw [hden1]; exact hden)
                  (by simp (config := { decide := true }) only [update_lookup, if_true]) hrun5
                cases r5 with
                | normal l5 g5 m5 ff5 =>
                  obtain ⟨hi5, hnz5, hfr5⟩ := ht
                  simp only [restorePanValueFfiLocal]
                  refine ⟨?_, ?_, fun h0 => ?_⟩
                  · simp (config := { decide := true }) only [restorePanValueLocal, if_false]
                    exact hi5
                  · simp (config := { decide := true }) only [restorePanValueLocal, if_false]
                    rw [hfr5 "den" (by decide) (by decide) (by decide) (by decide)]
                    simp (config := { decide := true }) only [update_lookup, if_false]
                    exact hden1
                  · simp (config := { decide := true }) only [restorePanValueLocal, if_false]
                    exact hnz5 h0
                | continued l5 g5 m5 ff5 => exact ht.elim
                | broke l5 g5 m5 ff5 => exact ht.elim
                | _ => simp only [restorePanValueFfiLocal, TayBodyPost]
              · subst hrest₂
                simp only [St.err, restorePanValueFfiLocal, TayBodyPost]
            · subst hrest₂
              simp only [St.err, restorePanValueFfiLocal, TayBodyPost]
          | continued l2 g2 m2 ff2 => exact ft.elim
          | broke l2 g2 m2 ff2 => exact ft.elim
          | _ =>
            simp only at hrest₂
            subst hrest₂
            simp only [restorePanValueFfiLocal, TayBodyPost]
    | raised lr g m ffi ex v =>
      simp only at hout
      subst hout
      trivial
    | finalFfi lr g m ffi ev =>
      simp only at hout
      subst hout
      trivial
    | _ => exact hout.elim
  | continued l1 g1 m1 ff1 => exact f1.elim
  | broke l1 g1 m1 ff1 => exact f1.elim
  | _ =>
    simp only at hrest
    subst hrest
    trivial

/-- `u256_from_word` on any value. -/
theorem u256_from_word_any (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_from_word" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (wv : PanValue Word) (hw : s.locals "w" = some wv)
    (h : Runs E s body r) :
    r.isError = true ∨ r = .returned (fun _ => none) s.globals s.memory s.ffi
      [.rStruct [wv, .word 0, .word 0, .word 0]] := by
  have hbody := (fun_of_index 39 hE.functions (by guest_decl_at 39) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp only [runs_return, evalF_rStruct, evalF_local, eval_const, evalArgs_cons, evalArgs_nil,
    hw, Option.map_some] at h
  split at h
  · exact Or.inr h
  · subst h
    exact Or.inl rfl

/-- `den` is a one-limb number. -/
def DenOk (s : St σ) : Prop :=
  ∃ dw : Word, s.locals "den" = some (.rStruct [.word dw, .word 0, .word 0, .word 0])

theorem DenOk.update_other {s : St σ} {x : VarName} {v : PanValue Word}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {f : FfiState σ} (h : DenOk s) (hx : (("den" : VarName) == x) = false) :
    DenOk ⟨updatePanValueMap s.locals x v, g, m, f⟩ := by
  obtain ⟨dw, hd⟩ := h
  exact ⟨dw, by simp [updatePanValueMap, hx, hd]⟩

/-- Loop-head states: `i` is a word and `den` a one-limb number. -/
def TayInv (s : St σ) : Prop :=
  ∃ iw dw : Word, s.locals "i" = some (.word iw) ∧
    s.locals "den" = some (.rStruct [.word dw, .word 0, .word 0, .word 0])

theorem TayInv.update_other {s : St σ} {x : VarName} {v : PanValue Word}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {f : FfiState σ} (h : TayInv s) (hi : (("i" : VarName) == x) = false)
    (hd : (("den" : VarName) == x) = false) :
    TayInv ⟨updatePanValueMap s.locals x v, g, m, f⟩ := by
  obtain ⟨iw, dw, h1, h2⟩ := h
  exact ⟨iw, dw, by simp [updatePanValueMap, hi, h1], by simp [updatePanValueMap, hd, h2]⟩

/-- Iterations left before `i` wraps to 0. -/
def tayDist (i : Word) : Nat := if i = 0 then 0 else 2 ^ 64 - i.toNat

theorem tayDist_succ {i : Word} (hi : i ≠ 0) : tayDist (i + 1) < tayDist i := by
  have hlt := i.isLt
  have hne : i.toNat ≠ 0 := fun h => hi (BitVec.eq_of_toNat_eq h)
  unfold tayDist
  rw [if_neg hi]
  split
  · omega
  · rename_i h1
    have hsum : (i + 1).toNat = (i.toNat + 1) % 2 ^ 64 := by simp [BitVec.toNat_add]
    have hne1 : (i + 1).toNat ≠ 0 := fun h => h1 (BitVec.eq_of_toNat_eq h)
    omega

theorem tayDist_le (i : Word) : tayDist i + 1 ≤ 18446744073709551616 := by
  have hlt := i.isLt
  unfold tayDist
  split
  · omega
  · rename_i h
    have hne : i.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq h0)
    omega

/-- The loop variant: iterations until the wrap while `nz` is clear. -/
def tayMu (s : St σ) : Nat :=
  match s.locals "nz", s.locals "i" with
  | some (.word z), some (.word i) => if z = 0 then tayDist i + 1 else 0
  | _, _ => 0

/-- The guard `nz == 0`. -/
def tayGuard : Exp Word := .cmp .equal (.var .local "nz") (.const (BitVec.ofNat 64 0))

/-- The loop runs at most `2^64 + 1` times. -/
theorem tayLoop (hE : GuestEnv E) {b : Nat} (hb : Costs E tayBody b) :
    Triple E TayInv (.while tayGuard tayBody)
      ((18446744073709551616 + 1) * (panValueExpStepCost tayGuard + b + 1))
      (fun r => match r with
        | .normal _ _ _ _ => True
        | _ => True) := by
  refine (Triple.while (I := TayInv) (μ := tayMu) (Q := fun _ => True)
    (e := panValueExpStepCost tayGuard) (b := b) 18446744073709551616 (condCost _ _)
    (fun _ _ => trivial) ?_).consequence ?_ (Nat.le_refl _) (fun r _ => by cases r <;> trivial)
  · intro k
    refine Triple.of_costs hb ?_
    intro fuel s r n hP hrun hne
    obtain ⟨⟨iw, dw, hi, hden⟩, hμ, v, kc, hcond, hv⟩ := hP
    have heval := cond_of_eval hcond
    simp only [tayGuard, evalF_cmp hE.word, evalF_local, eval_const] at heval
    have hnz : s.locals "nz" = some (.word 0) := by
      cases hz : s.locals "nz" with
      | none => rw [hz] at heval; cases heval
      | some z =>
        rw [hz] at heval
        cases z with
        | word zw =>
          simp only [Option.some.injEq, PanValue.word.injEq] at heval
          by_cases hzw : zw = 0
          · rw [hzw]
          · subst heval
            simp [evalPanCmp] at hv
            exact absurd hv hzw
        | _ => cases heval
    have hμs : tayMu s = tayDist iw + 1 := by simp [tayMu, hnz, hi]
    have hp := tayBody_runs hE hi hden (Runs.of_run hrun)
    cases r with
    | normal l g m f =>
      obtain ⟨hi', hden', hnz'⟩ := hp
      refine ⟨⟨iw + 1, dw, hi', hden'.trans hden⟩, ?_⟩
      show tayMu ⟨l, g, m, f⟩ < k
      rw [← hμ, hμs]
      unfold tayMu
      simp only [hi']
      cases hl : l "nz" with
      | none => simp
      | some z' =>
        cases z' with
        | word zw' =>
          simp only
          by_cases hz' : zw' = 0
          · rw [if_pos hz']
            have hiw : iw ≠ 0 := by
              intro h0
              have h1 := hnz' h0
              rw [hl] at h1
              simp only [Option.some.injEq, PanValue.word.injEq] at h1
              rw [h1] at hz'
              simp at hz'
            have := tayDist_succ hiw
            omega
          · rw [if_neg hz']
            omega
        | _ => simp
    | continued l g m f => exact hp.elim
    | broke l g m f => exact hp.elim
    | _ => trivial
  · intro s hI
    refine ⟨hI, ?_⟩
    unfold tayMu
    split
    · rename_i z i _ _
      have := i.isLt
      split
      · exact tayDist_le i
      · omega
    · omega

end InitECandidate.Solver.GuestBound
