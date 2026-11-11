import InitECandidate.Solver.GuestBound.Limbs
import InitECandidate.Solver.GuestBound.WhileExit
import InitECandidate.Solver.GuestBound.TripleRules
import InitECandidate.Solver.GuestBound.Calm

/-!
# `bls_fp_inv_raw`: binary extended Euclid on 384-bit numbers

Call lemmas for the loop bodies: the locals `u` and `v` hold records of six
words throughout, halving calls halve the represented number, and the other
calls leave `u` and `v` alone.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The local `x` holds six words representing `n`. -/
def SixVal (x : VarName) (n : Nat) (l : VarName → Option (PanValue Word)) : Prop :=
  ∃ w0 w1 w2 w3 w4 w5 : Word,
    l x = some (.rStruct [.word w0, .word w1, .word w2, .word w3, .word w4, .word w5]) ∧
    limbsVal [w0, w1, w2, w3, w4, w5] = n

theorem SixVal.update_other {x y : VarName} {n : Nat} {l : VarName → Option (PanValue Word)}
    {v : PanValue Word} (h : SixVal x n l) (hxy : (x == y) = false) :
    SixVal x n (updatePanValueMap l y v) := by
  obtain ⟨w0, w1, w2, w3, w4, w5, hl, hn⟩ := h
  exact ⟨w0, w1, w2, w3, w4, w5, by simp [updatePanValueMap, hxy, hl], hn⟩

/-- A call assigning its result to the local `y` ends in `.error`, ends the
enclosing run, or updates `y` only. -/
theorem call_local_frame {f : FunName} {y : VarName} {s : St σ} {arguments : List (Exp Word)}
    {r : Result σ}
    (h : Runs E s (.call (some (some (.local, y), none)) f arguments) r) :
    match r with
    | .normal l _ _ _ => ∀ x, x ≠ y → l x = s.locals x
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  rcases runs_call_inv (some (some (.local, y))) h with herr | ⟨parameters, body, values,
    calleeLocals, rb, -, -, -, -, hout⟩
  · cases r <;> trivial
  · cases rb with
    | returned l g m ffi values' =>
      simp only [CallOutcome] at hout
      rcases hout with herr | ⟨l', g', hassign, rfl⟩
      · cases r <;> trivial
      · obtain ⟨-, hframe, -⟩ := assignResult_frame (structs := E.structs) (M := [y])
          (by simp [destIn]) hassign
        intro x hx
        exact hframe x (by simpa using hx)
    | raised l g m ffi exception value =>
      simp only [CallOutcome] at hout
      subst hout
      trivial
    | finalFfi l g m ffi event =>
      simp only [CallOutcome] at hout
      subst hout
      trivial
    | _ =>
      simp only [CallOutcome] at hout
      cases r <;> trivial

/-- `x = bls_fp_shr1(x)` on a six-word local halves the number it represents. -/
theorem call_shr1 (hE : GuestEnv E) {x : VarName} {n : Nat} {s : St σ} {r : Result σ}
    (hx : SixVal x n s.locals)
    (h : Runs E s (.call (some (some (.local, x), none)) "bls_fp_shr1" [.var .local x]) r) :
    r.isError = true ∨ ∃ l, r = .normal l s.globals s.memory s.ffi ∧ SixVal x (n / 2) l ∧
      ∀ y, y ≠ x → l y = s.locals y := by
  obtain ⟨w0, w1, w2, w3, w4, w5, hl, hn⟩ := hx
  rcases runs_call_inv (some (some (.local, x))) h with herr | ⟨parameters, body, values,
    calleeLocals, rb, hlookup, hvalues, hbind, hcallee, hout⟩
  · exact Or.inl herr
  have hparams := (fun_of_index 710 hE.functions (by guest_decl_at 710) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, hl, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  have hcl : calleeLocals "x" =
      some (.rStruct [.word w0, .word w1, .word w2, .word w3, .word w4, .word w5]) := by
    simp [bindPanValueParameters] at hbind
    rw [← hbind]
    simp [updatePanValueMap]
  obtain ⟨d0, d1, d2, d3, d4, d5, rfl, hd⟩ := bls_fp_shr1_spec hE parameters body hlookup
    ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb w0 w1 w2 w3 w4 w5 hcl hcallee
  simp only [CallOutcome] at hout
  rcases hout with herr | ⟨l', g', hassign, rfl⟩
  · exact Or.inl herr
  simp only [assignPanValueCallResult] at hassign
  split at hassign
  · simp only [Option.some.injEq, Prod.mk.injEq] at hassign
    obtain ⟨rfl, rfl⟩ := hassign
    refine Or.inr ⟨_, rfl, ⟨d0, d1, d2, d3, d4, d5, by simp [updatePanValueMap], ?_⟩, ?_⟩
    · rw [hd, hn]
    · intro y hy
      have : (y == x) = false := by simpa using hy
      simp [updatePanValueMap, this]
  · cases hassign

/-- The low bit of a word, in the form the evaluator produces for `w & 1`. -/
theorem low_bit (w : BitVec 64) :
    (AndOp.and w (AndOp.and (1#64) (~~~(0 : BitVec 64)))).toNat = w.toNat % 2 := by
  have h : (w &&& (1#64 &&& ~~~(0 : BitVec 64))) = w &&& 1#64 := by bv_decide
  show (w &&& (1#64 &&& ~~~(0 : BitVec 64))).toNat = _
  rw [h, BitVec.toNat_and]
  simp [Nat.and_one_is_mod]

/-- The guard `(x.0 & 1) == 0` of the halving loops. -/
def evenGuard (x : VarName) : Exp Word :=
  .cmp .equal (.op .and [.rField 0 (.var .local x), .const (BitVec.ofNat 64 1)])
    (.const (BitVec.ofNat 64 0))

/-- The halving-loop guard is nonzero exactly when the low limb is even. -/
theorem evenGuard_eval (hE : GuestEnv E) {x : VarName} {s : St σ} {w0 w1 w2 w3 w4 w5 : Word}
    (hl : s.locals x = some (.rStruct [.word w0, .word w1, .word w2, .word w3, .word w4,
      .word w5])) {g : Word} (h : E.eval s (evenGuard x) = some (.word g)) :
    g = 0 ↔ w0.toNat % 2 = 1 := by
  simp only [evenGuard, evalF_cmp hE.word, evalF_op hE.word, evalF_rField, evalF_local,
    eval_const, evalArgs_cons, evalArgs_nil, hl, wordsProj_cons, wordsProj_nil, wordOp,
    List.foldr, Option.map_some, List.getElem?_cons_zero, Option.some.injEq,
    PanValue.word.injEq] at h
  subst h
  have hlow := low_bit w0
  generalize (AndOp.and w0 (AndOp.and (1#64) (~~~(0 : BitVec 64))) : BitVec 64) = A at hlow ⊢
  by_cases hz : A = 0#64
  · have h0 : w0.toNat % 2 = 0 := by rw [← hlow, hz]; rfl
    simp [evalPanCmp, hz, h0]
  · have h1 : w0.toNat % 2 ≠ 0 := by
      intro h0
      apply hz
      apply BitVec.eq_of_toNat_eq
      rw [hlow, h0]
      rfl
    have h1' : w0.toNat % 2 = 1 := by omega
    simp [evalPanCmp, hz, h1']

/-- The number held by a six-word local, or 0. -/
def sixNat (x : VarName) (l : VarName → Option (PanValue Word)) : Nat :=
  match l x with
  | some (.rStruct [.word w0, .word w1, .word w2, .word w3, .word w4, .word w5]) =>
      limbsVal [w0, w1, w2, w3, w4, w5]
  | _ => 0

theorem SixVal.sixNat_eq {x : VarName} {n : Nat} {l : VarName → Option (PanValue Word)}
    (h : SixVal x n l) : sixNat x l = n := by
  obtain ⟨w0, w1, w2, w3, w4, w5, hl, hn⟩ := h
  simp [sixNat, hl, hn]

theorem SixVal.lt {x : VarName} {n : Nat} {l : VarName → Option (PanValue Word)}
    (h : SixVal x n l) : n < 2 ^ 384 := by
  obtain ⟨w0, w1, w2, w3, w4, w5, -, hn⟩ := h
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt; have := w4.isLt
  have := w5.isLt
  simp only [limbsVal] at hn
  omega

/-- A call to a calm function assigning to the local `y` ends in `.error` or
normally, having changed `y` only among the locals. -/
theorem call_calm_local {f : FunName} (hf : FunCalm E f) {y : VarName} {s : St σ}
    {arguments : List (Exp Word)} {r : Result σ}
    (h : Runs E s (.call (some (some (.local, y), none)) f arguments) r) :
    r.isError = true ∨ ∃ l g m ffi, r = .normal l g m ffi ∧ ∀ z, z ≠ y → l z = s.locals z := by
  rcases runs_call_inv (some (some (.local, y))) h with herr | ⟨parameters, body, values,
    calleeLocals, rb, hlookup, -, -, ⟨fuel, n, hcallee⟩, hout⟩
  · exact Or.inl herr
  have hcalm := hf parameters body hlookup fuel _ rb n hcallee
  cases rb with
  | returned l g m ffi values' =>
    simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl herr
    · obtain ⟨-, hframe, -⟩ := assignResult_frame (structs := E.structs) (M := [y])
        (by simp [destIn]) hassign
      exact Or.inr ⟨l', g', m, ffi, rfl, fun z hz => hframe z (by simpa using hz)⟩
  | raised l g m ffi exception value => cases hcalm
  | finalFfi l g m ffi event => cases hcalm
  | _ =>
    simp only [CallOutcome] at hout
    exact Or.inl hout

/-- The body of a halving loop: halve `x`, adjust `y`. -/
def halveBody (x y : VarName) : Prog Word :=
  .seq (.call (some (some (.local, x), none)) "bls_fp_shr1" [.var .local x])
    (.call (some (some (.local, y), none)) "bls_fp_half_can" [.var .local y])

/-- One halving step: `x` halves, and only `x` and `y` change. -/
theorem halveBody_runs (hE : GuestEnv E) (hcalm : FunCalm E "bls_fp_half_can") {x y : VarName}
    (hxy : x ≠ y) {n : Nat} {s : St σ} {r : Result σ} (hx : SixVal x n s.locals)
    (h : Runs E s (halveBody x y) r) :
    r.isError = true ∨ ∃ l g m f, r = .normal l g m f ∧ SixVal x (n / 2) l ∧
      ∀ z, z ≠ x → z ≠ y → l z = s.locals z := by
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp h
  rcases call_shr1 hE hx h₁ with herr | ⟨l1, rfl, hsix, hframe⟩
  · cases r₁ with
    | error l g m f =>
      simp only at hrest
      subst hrest
      exact Or.inl rfl
    | _ => cases herr
  simp only at hrest
  rcases call_calm_local hcalm hrest with herr | ⟨l, g, m, f, rfl, hframe'⟩
  · exact Or.inl herr
  refine Or.inr ⟨l, g, m, f, rfl, ?_, ?_⟩
  · obtain ⟨w0, w1, w2, w3, w4, w5, hl, hn⟩ := hsix
    exact ⟨w0, w1, w2, w3, w4, w5, by rw [hframe' x hxy]; exact hl, hn⟩
  · intro z hzx hzy
    rw [hframe' z hzy]
    exact hframe z hzx

theorem limbs_parity (w0 w1 w2 w3 w4 w5 : Word) :
    limbsVal [w0, w1, w2, w3, w4, w5] % 2 = w0.toNat % 2 := by
  simp only [limbsVal]
  omega

/-- A halving loop: from a nonzero value it stops within 384 iterations at an
odd value no larger; from zero it never returns. -/
theorem halve_loop (hE : GuestEnv E) (hcalm : FunCalm E "bls_fp_half_can") {x y : VarName}
    (hxy : x ≠ y) (F : (VarName → Option (PanValue Word)) → Prop)
    (hF : ∀ l l', (∀ z, z ≠ x → z ≠ y → l' z = l z) → F l → F l') (n b : Nat)
    (hb : Costs E (halveBody x y) b) :
    Triple E (fun s => SixVal x n s.locals ∧ F s.locals)
      (.while (evenGuard x) (halveBody x y))
      (384 * (panValueExpStepCost (evenGuard x) + b + 1))
      (fun r => match r with
        | .normal l _ _ _ => ∃ n', n' ≤ n ∧ n' % 2 = 1 ∧ SixVal x n' l ∧ F l
        | .continued _ _ _ _ | .broke _ _ _ _ => False
        | _ => True) := by
  by_cases hn : n = 0
  · subst hn
    intro fuel s r m hP hrun hne
    have herr := while_never (E := E) (Z := fun s => SixVal x 0 s.locals) (c := evenGuard x)
      (body := halveBody x y)
      (by
        intro s hZ v k hcond
        obtain ⟨w0, w1, w2, w3, w4, w5, hl, hval⟩ := hZ
        have hpar := limbs_parity w0 w1 w2 w3 w4 w5
        have hiff := evenGuard_eval hE hl (cond_of_eval hcond)
        have hv : v ≠ 0 := by
          intro hv0
          have := hiff.mp hv0
          omega
        simpa using hv)
      (by
        intro fuel s r n hZ hrun
        rcases halveBody_runs hE hcalm hxy hZ (Runs.of_run hrun) with herr |
          ⟨l, g, m, f, rfl, hsix, -⟩
        · exact Or.inl herr
        · exact Or.inr ⟨l, g, m, f, rfl, hsix⟩)
      fuel s r m hP.1 hrun
    rw [herr] at hne
    cases hne
  · refine (Triple.while_exit
      (I := fun s => ∃ n', n' ≤ n ∧ n' ≠ 0 ∧ SixVal x n' s.locals ∧ F s.locals)
      (μ := fun s => Nat.log2 (sixNat x s.locals))
      (Q := fun r => match r with
        | .normal l _ _ _ => ∃ n', n' ≤ n ∧ n' % 2 = 1 ∧ SixVal x n' l ∧ F l
        | .continued _ _ _ _ | .broke _ _ _ _ => False
        | _ => True)
      (e := panValueExpStepCost (evenGuard x)) (b := b) 383 (condCost _ _) ?_ ?_).consequence
      ?_ (Nat.le_refl _) (fun _ h => h)
    · intro s hI hexit
      obtain ⟨n', hle, -, hsix, hFs⟩ := hI
      obtain ⟨k, hcond⟩ := hexit
      obtain ⟨w0, w1, w2, w3, w4, w5, hl, hval⟩ := hsix
      have hodd := (evenGuard_eval hE hl (cond_of_eval hcond)).mp rfl
      have hpar := limbs_parity w0 w1 w2 w3 w4 w5
      exact ⟨n', hle, by omega, ⟨w0, w1, w2, w3, w4, w5, hl, hval⟩, hFs⟩
    · intro k
      refine Triple.of_costs hb ?_
      intro fuel s r m hP hrun hner
      obtain ⟨⟨n', hle, hne0, hsix, hFs⟩, hμ, v, kc, hcond, hv⟩ := hP
      have hnat := hsix.sixNat_eq
      have heven : n' % 2 = 0 := by
        obtain ⟨w0, w1, w2, w3, w4, w5, hl, hval⟩ := hsix
        have hiff := evenGuard_eval hE hl (cond_of_eval hcond)
        have hpar := limbs_parity w0 w1 w2 w3 w4 w5
        have hv0 : v ≠ 0 := by simpa using hv
        have : ¬ w0.toNat % 2 = 1 := fun h1 => hv0 (hiff.mpr h1)
        omega
      rcases halveBody_runs hE hcalm hxy hsix (Runs.of_run hrun) with herr |
        ⟨l, g, m', f, rfl, hsix', hframe⟩
      · rw [herr] at hner
        cases hner
      · have hnat' := hsix'.sixNat_eq
        refine ⟨⟨n' / 2, by omega, by omega, hsix', hF _ _ hframe hFs⟩, ?_⟩
        show Nat.log2 (sixNat x l) < k
        rw [hnat', ← hμ, hnat]
        have h2 : 2 ≤ n' := by omega
        rw [Nat.log2_def n', if_pos h2]
        omega
    · intro s hP
      obtain ⟨hsix, hFs⟩ := hP
      refine ⟨⟨n, Nat.le_refl _, hn, hsix, hFs⟩, ?_⟩
      show Nat.log2 (sixNat x s.locals) ≤ 383
      rw [hsix.sixNat_eq]
      have := (Nat.log2_lt hn (k := 384)).mpr hsix.lt
      omega

/-- One subtraction branch of the outer loop: `var d = sub_raw(a, b); a = <d.0 … d.5>;
xa = fp_sub(xa, xb)`. -/
def subBranch (a b d xa xb : VarName) : Prog Word :=
  .decCall d (.comb [.one, .one, .one, .one, .one, .one, .one]) "bls_fp_sub_raw"
    [.var .local a, .var .local b]
    (.seq
      (.assign .local a (.rStruct [.rField 0 (.var .local d), .rField 1 (.var .local d),
        .rField 2 (.var .local d), .rField 3 (.var .local d), .rField 4 (.var .local d),
        .rField 5 (.var .local d)]))
      (.call (some (some (.local, xa), none)) "bls_fp_sub" [.var .local xa, .var .local xb]))

set_option maxHeartbeats 1000000 in
/-- The subtraction branch replaces `a` by `a - b` and otherwise changes only `xa`. -/
theorem subBranch_runs (hE : GuestEnv E) {a b d xa xb : VarName} (hab : (b == a) = false)
    (had : (a == d) = false) (hbd : (b == d) = false) (haxa : (a == xa) = false)
    {A B : Nat} {s : St σ} {r : Result σ} (ha : SixVal a A s.locals) (hb : SixVal b B s.locals)
    (hle : B ≤ A) (h : Runs E s (subBranch a b d xa xb) r) :
    match r with
    | .normal l _ _ _ => SixVal a (A - B) l ∧ ∀ z, z ≠ a → z ≠ xa → l z = s.locals z
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  obtain ⟨a0, a1, a2, a3, a4, a5, hla, hA⟩ := ha
  obtain ⟨b0, b1, b2, b3, b4, b5, hlb, hB⟩ := hb
  rcases runs_decCall_inv h with herr | ⟨parameters, body, values, calleeLocals, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · cases r <;> trivial
  have hparams := (fun_of_index 701 hE.functions (by guest_decl_at 701) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, hla, hlb, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hca : calleeLocals "a" =
      some (.rStruct [.word a0, .word a1, .word a2, .word a3, .word a4, .word a5]) := by
    rw [← hbind]
    simp [updatePanValueMap]
  have hcb : calleeLocals "b" =
      some (.rStruct [.word b0, .word b1, .word b2, .word b3, .word b4, .word b5]) := by
    rw [← hbind]
    simp [updatePanValueMap]
  obtain ⟨cl, d0, d1, d2, d3, d4, d5, d6, rfl, hd⟩ := bls_fp_sub_raw_spec hE parameters body
    hlookup ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5
    hca hcb (by rw [hA, hB]; exact hle) hcallee
  obtain ⟨r', -, hrun', rfl⟩ := hout
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp hrun'
  rw [runs_assign_local] at h₁
  simp (config := { decide := true }) only [evalF_rStruct, evalF_rField, evalF_local,
    evalArgs_cons, evalArgs_nil, update_lookup, beq_self_eq_true, if_true, Option.map_some,
    List.getElem?_cons_zero, List.getElem?_cons_succ] at h₁
  split at h₁
  · subst h₁
    simp only at hrest
    have hframe := call_local_frame hrest
    cases r' with
    | normal l g m f =>
      simp only at hframe
      simp only [restorePanValueFfiLocal]
      have hxa : a ≠ xa := by simpa using haxa
      refine ⟨⟨d0, d1, d2, d3, d4, d5, ?_, ?_⟩, ?_⟩
      · simp only [restorePanValueLocal, had, Bool.false_eq_true, if_false]
        rw [hframe a hxa]
        simp [updatePanValueMap]
      · rw [hd, hA, hB]
      · intro z hza hzxa
        by_cases hzd : z = d
        · subst hzd
          simp [restorePanValueLocal]
        · have hzd' : (z == d) = false := by simpa using hzd
          have hza' : (z == a) = false := by simpa using hza
          simp only [restorePanValueLocal, hzd', Bool.false_eq_true, if_false]
          rw [hframe z hzxa]
          simp [updatePanValueMap, hzd', hza']
    | continued l g m f => exact hframe.elim
    | broke l g m f => exact hframe.elim
    | _ => simp only [restorePanValueFfiLocal]
  · subst h₁
    simp only [St.err] at hrest
    subst hrest
    simp only [restorePanValueFfiLocal]

/-- The end of the outer loop body: compare `u` and `v`, subtract the smaller. -/
def cmpTail : Prog Word :=
  .decCall "ult" .one "bls_fp_lt_raw" [.var .local "u", .var .local "v"]
    (.ite (.cmp .equal (.var .local "ult") (.const (BitVec.ofNat 64 0)))
      (subBranch "u" "v" "d" "x1" "x2") (subBranch "v" "u" "e" "x2" "x1"))

set_option maxHeartbeats 1000000 in
/-- With `u` and `v` positive, the tail decreases `u + v`. -/
theorem cmpTail_runs (hE : GuestEnv E) {U V : Nat} {s : St σ} {r : Result σ}
    (hu : SixVal "u" U s.locals) (hv : SixVal "v" V s.locals) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (h : Runs E s cmpTail r) :
    match r with
    | .normal l _ _ _ => ∃ U' V', SixVal "u" U' l ∧ SixVal "v" V' l ∧ U' + V' < U + V
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  obtain ⟨u0, u1, u2, u3, u4, u5, hlu, hUv⟩ := id hu
  obtain ⟨v0, v1, v2, v3, v4, v5, hlv, hVv⟩ := id hv
  rcases runs_decCall_inv h with herr | ⟨parameters, body, values, calleeLocals, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · cases r <;> trivial
  have hparams := (fun_of_index 699 hE.functions (by guest_decl_at 699) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, hlu, hlv, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hca : calleeLocals "a" =
      some (.rStruct [.word u0, .word u1, .word u2, .word u3, .word u4, .word u5]) := by
    rw [← hbind]
    simp [updatePanValueMap]
  have hcb : calleeLocals "b" =
      some (.rStruct [.word v0, .word v1, .word v2, .word v3, .word v4, .word v5]) := by
    rw [← hbind]
    simp [updatePanValueMap]
  have hspec := bls_fp_lt_raw_spec hE parameters body hlookup
    ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb u0 u1 u2 u3 u4 u5 v0 v1 v2 v3 v4 v5 hca hcb
    hcallee
  subst hspec
  obtain ⟨r', -, hrun', rfl⟩ := hout
  rw [hUv, hVv] at hrun'
  have hu' : ∀ c : Word, SixVal "u" U (updatePanValueMap s.locals "ult" (PanValue.word c)) :=
    fun c => hu.update_other (by decide)
  have hv' : ∀ c : Word, SixVal "v" V (updatePanValueMap s.locals "ult" (PanValue.word c)) :=
    fun c => hv.update_other (by decide)
  rw [runs_ite] at hrun'
  simp only [evalF_cmp hE.word, evalF_local, eval_const, update_lookup, beq_self_eq_true,
    if_true] at hrun'
  by_cases hlt : U < V
  · simp only [hlt, if_true, evalPanCmp] at hrun'
    have hbr := subBranch_runs hE (a := "v") (b := "u") (d := "e") (xa := "x2") (xb := "x1")
      (by decide) (by decide) (by decide) (by decide)
      (s := ⟨updatePanValueMap s.locals "ult" (PanValue.word 1#64), s.globals, s.memory, s.ffi⟩)
      (hv' _) (hu' _) (Nat.le_of_lt hlt) hrun'
    cases r' with
    | normal l g m f =>
      obtain ⟨hsix, hframe⟩ := hbr
      simp only [restorePanValueFfiLocal]
      refine ⟨U, V - U, ?_, ?_, by omega⟩
      · obtain ⟨w0, w1, w2, w3, w4, w5, hl, hn⟩ := hu' 1
        refine ⟨w0, w1, w2, w3, w4, w5, ?_, hn⟩
        simp only [restorePanValueLocal, show (("u" : String) == "ult") = false from by decide,
          Bool.false_eq_true, if_false]
        rw [hframe "u" (by decide) (by decide)]
        exact hl
      · obtain ⟨w0, w1, w2, w3, w4, w5, hl, hn⟩ := hsix
        exact ⟨w0, w1, w2, w3, w4, w5, by
          simp only [restorePanValueLocal, show (("v" : String) == "ult") = false from by decide,
            Bool.false_eq_true, if_false]
          exact hl, hn⟩
    | continued l g m f => exact hbr.elim
    | broke l g m f => exact hbr.elim
    | _ => simp only [restorePanValueFfiLocal]
  · simp only [hlt, if_false, evalPanCmp] at hrun'
    have hbr := subBranch_runs hE (a := "u") (b := "v") (d := "d") (xa := "x1") (xb := "x2")
      (by decide) (by decide) (by decide) (by decide)
      (s := ⟨updatePanValueMap s.locals "ult" (PanValue.word 0#64), s.globals, s.memory, s.ffi⟩)
      (hu' _) (hv' _) (Nat.le_of_not_lt hlt) hrun'
    cases r' with
    | normal l g m f =>
      obtain ⟨hsix, hframe⟩ := hbr
      simp only [restorePanValueFfiLocal]
      refine ⟨U - V, V, ?_, ?_, by omega⟩
      · obtain ⟨w0, w1, w2, w3, w4, w5, hl, hn⟩ := hsix
        exact ⟨w0, w1, w2, w3, w4, w5, by
          simp only [restorePanValueLocal, show (("u" : String) == "ult") = false from by decide,
            Bool.false_eq_true, if_false]
          exact hl, hn⟩
      · obtain ⟨w0, w1, w2, w3, w4, w5, hl, hn⟩ := hv' 0
        refine ⟨w0, w1, w2, w3, w4, w5, ?_, hn⟩
        simp only [restorePanValueLocal, show (("v" : String) == "ult") = false from by decide,
          Bool.false_eq_true, if_false]
        rw [hframe "v" (by decide) (by decide)]
        exact hl
    | continued l g m f => exact hbr.elim
    | broke l g m f => exact hbr.elim
    | _ => simp only [restorePanValueFfiLocal]

/-- `if c { if c2 { return e; } }` either leaves the state alone or does not end normally. -/
theorem retIte_runs {c c2 e : Exp Word} {s : St σ} {r : Result σ} :
    Runs E s (.ite c (.ite c2 (.return e) .skip) .skip) r →
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
    · rw [runs_ite] at h
      split at h
      · split at h
        · rw [runs_skip] at h
          subst h
          exact ⟨rfl, rfl, rfl, rfl⟩
        · rw [runs_return] at h
          cases he : E.eval s e with
          | none =>
            rw [he] at h
            subst h
            simp [St.err]
          | some v =>
            rw [he] at h
            simp only at h
            split at h <;> (subst h; simp [St.err])
      · subst h
        simp [St.err]
  · subst h
    simp [St.err]

/-- `if (x.1 | … | x.5) == 0 { if x.0 == 1 { return y; } }`. -/
abbrev retCheck (x y : VarName) : Prog Word :=
  .ite (.cmp .equal (.op .or [.rField 1 (.var .local x), .rField 2 (.var .local x),
      .rField 3 (.var .local x), .rField 4 (.var .local x), .rField 5 (.var .local x)])
      (.const (BitVec.ofNat 64 0)))
    (.ite (.cmp .equal (.rField 0 (.var .local x)) (.const (BitVec.ofNat 64 1)))
      (.return (.var .local y)) .skip)
    .skip

/-- The body of the outer loop of `bls_fp_inv_raw`. -/
def outerBody : Prog Word :=
  .seq (retCheck "u" "x1")
    (.seq (retCheck "v" "x2")
      (.seq (.while (evenGuard "u") (halveBody "u" "x1"))
        (.seq (.while (evenGuard "v") (halveBody "v" "x2")) cmpTail)))

/-- Loop-head states of the outer loop: `u` and `v` hold six words. -/
def OuterInv (s : St σ) : Prop := ∃ U V, SixVal "u" U s.locals ∧ SixVal "v" V s.locals

/-- The outer measure: the sum of the two numbers. -/
def outerMu (s : St σ) : Nat := sixNat "u" s.locals + sixNat "v" s.locals

theorem sixVal_frame {x : VarName} {n : Nat} {l l' : VarName → Option (PanValue Word)}
    (h : SixVal x n l) (hx : l' x = l x) : SixVal x n l' := by
  obtain ⟨w0, w1, w2, w3, w4, w5, hl, hn⟩ := h
  exact ⟨w0, w1, w2, w3, w4, w5, by rw [hx]; exact hl, hn⟩

/-- One outer iteration decreases `u + v`. -/
theorem outerBody_triple (hE : GuestEnv E) (hcalm : FunCalm E "bls_fp_half_can") (k : Nat)
    {br bh bt : Nat} (hr1 : Costs E (retCheck "u" "x1") br) (hr2 : Costs E (retCheck "v" "x2") br)
    (hh1 : Costs E (halveBody "u" "x1") bh) (hh2 : Costs E (halveBody "v" "x2") bh)
    (ht : Costs E cmpTail bt) :
    Triple E (fun s => OuterInv s ∧ outerMu s = k) outerBody
      (br + (br + (384 * (panValueExpStepCost (evenGuard "u") + bh + 1) +
        (384 * (panValueExpStepCost (evenGuard "v") + bh + 1) + bt + 1) + 1) + 1) + 1)
      (loopBodyPost OuterInv outerMu k (fun _ => True)) := by
  have key : ∀ U V, U + V = k →
      Triple E (fun s => SixVal "u" U s.locals ∧ SixVal "v" V s.locals) outerBody
        (br + (br + (384 * (panValueExpStepCost (evenGuard "u") + bh + 1) +
          (384 * (panValueExpStepCost (evenGuard "v") + bh + 1) + bt + 1) + 1) + 1) + 1)
        (loopBodyPost OuterInv outerMu k (fun _ => True)) := by
    intro U V hk
    have keep : ∀ (c : Nat) (p : Prog Word), Costs E p c →
        (∀ (s : St σ) (r : Result σ), Runs E s p r →
          match r with
          | .normal l g m f => l = s.locals ∧ g = s.globals ∧ m = s.memory ∧ f = s.ffi
          | .continued _ _ _ _ | .broke _ _ _ _ => False
          | _ => True) →
        Triple E (fun s => SixVal "u" U s.locals ∧ SixVal "v" V s.locals) p c
          (fun r => match r with
            | .normal l g m f => SixVal "u" U l ∧ SixVal "v" V l
            | r => loopBodyPost OuterInv outerMu k (fun _ => True) r) := by
      intro c p hc hruns
      refine Triple.of_costs hc ?_
      intro fuel s r n hP hrun hne
      have := hruns s r (Runs.of_run hrun)
      cases r with
      | normal l g m f =>
        obtain ⟨rfl, -, -, -⟩ := this
        exact hP
      | continued l g m f => exact this.elim
      | broke l g m f => exact this.elim
      | _ => trivial
    refine Triple.seq (Mid := fun s => SixVal "u" U s.locals ∧ SixVal "v" V s.locals)
      (keep br _ hr1 (fun s r h => retIte_runs h))
      (Triple.seq (Mid := fun s => SixVal "u" U s.locals ∧ SixVal "v" V s.locals)
        (keep br _ hr2 (fun s r h => retIte_runs h)) (Triple.seq
        (Mid := fun s => ∃ U1, U1 ≤ U ∧ U1 % 2 = 1 ∧ SixVal "u" U1 s.locals ∧
          SixVal "v" V s.locals) ?_ (Triple.seq
        (Mid := fun s => ∃ U1 V1, U1 ≤ U ∧ U1 % 2 = 1 ∧ V1 ≤ V ∧ V1 % 2 = 1 ∧
          SixVal "u" U1 s.locals ∧ SixVal "v" V1 s.locals) ?_ ?_)))
    · refine (halve_loop hE hcalm (x := "u") (y := "x1") (by decide)
        (fun l => SixVal "v" V l)
        (fun l l' hframe h => sixVal_frame h (hframe "v" (by decide) (by decide))) U bh
        hh1).consequence (fun _ h => h) (Nat.le_refl _) ?_
      intro r hr
      cases r with
      | normal l g m f =>
        obtain ⟨U1, hle, hodd, hsix, hv⟩ := hr
        exact ⟨U1, hle, hodd, hsix, hv⟩
      | continued l g m f => exact hr.elim
      | broke l g m f => exact hr.elim
      | _ => trivial
    · refine (halve_loop hE hcalm (x := "v") (y := "x2") (by decide)
        (fun l => ∃ U1, U1 ≤ U ∧ U1 % 2 = 1 ∧ SixVal "u" U1 l)
        (fun l l' hframe h => by
          obtain ⟨U1, hle, hodd, hsix⟩ := h
          exact ⟨U1, hle, hodd, sixVal_frame hsix (hframe "u" (by decide) (by decide))⟩) V bh
        hh2).consequence ?_ (Nat.le_refl _) ?_
      · intro s h
        obtain ⟨U1, hle, hodd, hsix, hv⟩ := h
        exact ⟨hv, U1, hle, hodd, hsix⟩
      · intro r hr
        cases r with
        | normal l g m f =>
          obtain ⟨V1, hle, hodd, hsix, U1, hle', hodd', hsix'⟩ := hr
          exact ⟨U1, V1, hle', hodd', hle, hodd, hsix', hsix⟩
        | continued l g m f => exact hr.elim
        | broke l g m f => exact hr.elim
        | _ => trivial
    · refine Triple.of_costs ht ?_
      intro fuel s r n hP hrun hne
      obtain ⟨U1, V1, hle, hodd, hle', hodd', hu, hv⟩ := hP
      have := cmpTail_runs hE hu hv (by omega) (by omega) (Runs.of_run hrun)
      cases r with
      | normal l g m f =>
        obtain ⟨U', V', hu', hv', hlt⟩ := this
        refine ⟨⟨U', V', hu', hv'⟩, ?_⟩
        show sixNat "u" l + sixNat "v" l < k
        rw [hu'.sixNat_eq, hv'.sixNat_eq]
        omega
      | continued l g m f => exact this.elim
      | broke l g m f => exact this.elim
      | _ => trivial
  intro fuel s r n hP hrun hne
  obtain ⟨⟨U, V, hu, hv⟩, hμ⟩ := hP
  exact key U V (by rw [← hμ]; show U + V = sixNat "u" s.locals + sixNat "v" s.locals
                    rw [hu.sixNat_eq, hv.sixNat_eq]) fuel s r n ⟨hu, hv⟩ hrun hne

/-- A value whose shape is six words is a record of six words. -/
theorem six_of_shape {structs : StructContext} {v : PanValue Word}
    (h : panShapeMatches (panValueShape structs v)
      (.comb [.one, .one, .one, .one, .one, .one]) = true) :
    ∃ w0 w1 w2 w3 w4 w5 : Word,
      v = .rStruct [.word w0, .word w1, .word w2, .word w3, .word w4, .word w5] := by
  obtain ⟨ws, rfl, hlen⟩ := panValueShape_matches_word_record_inv structs v
    [(0 : Word), 0, 0, 0, 0, 0] h
  match ws, hlen with
  | [w0, w1, w2, w3, w4, w5], _ => exact ⟨w0, w1, w2, w3, w4, w5, rfl⟩

theorem sixVal_of_shape {structs : StructContext} {v : PanValue Word} {x : VarName}
    {l : VarName → Option (PanValue Word)}
    (h : panShapeMatches (panValueShape structs v)
      (.comb [.one, .one, .one, .one, .one, .one]) = true) :
    ∃ n, SixVal x n (updatePanValueMap l x v) := by
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ := six_of_shape h
  exact ⟨_, w0, w1, w2, w3, w4, w5, by simp [updatePanValueMap], rfl⟩

/-- Close a cost inequality between closed expression costs. -/
macro "cost_le'" : tactic => `(tactic| (
  simp only [stepCost_eq, stepsCost_eq, expCost, expsCost, evenGuard]
  omega))

namespace Manual

set_option maxHeartbeats 2000000 in
theorem «bls_fp_inv_raw».cost (hE : GuestEnv E) {Z S H L R B : Nat}
    (hz : FunCost E "bls_fp_is_zero" Z) (hs : FunCost E "bls_fp_shr1" S)
    (hh : FunCost E "bls_fp_half_can" H) (hl : FunCost E "bls_fp_lt_raw" L)
    (hr : FunCost E "bls_fp_sub_raw" R) (hb : FunCost E "bls_fp_sub" B) :
    FunCost E "bls_fp_inv_raw"
      (Z + (78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 + 1) * (768 * (S + H) + L + R + B + 20004) + 200) := by
  have hcalm : FunCalm E "bls_fp_half_can" :=
    calmFn_sound hE.functions calmDepth "bls_fp_half_can" (by decide +kernel)
  have hpow : (2 : Nat) ^ 384 * 2 = 78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 := by decide +kernel
  have hr1 : Costs E (retCheck "u" "x1") 64 :=
    (X.ite σ E _ _ _ _ _ (X.ite σ E _ _ _ _ _ (X.ret σ E _) (X.skip σ E))
      (X.skip σ E)).consequence (fun _ h => h) (by cost_le') (fun _ h => h)
  have hr2 : Costs E (retCheck "v" "x2") 64 :=
    (X.ite σ E _ _ _ _ _ (X.ite σ E _ _ _ _ _ (X.ret σ E _) (X.skip σ E))
      (X.skip σ E)).consequence (fun _ h => h) (by cost_le') (fun _ h => h)
  have hh1 : Costs E (halveBody "u" "x1") (S + H + 16) :=
    (X.seq σ E _ _ _ _ (X.callDest σ E _ _ _ _ hs) (X.callDest σ E _ _ _ _ hh)).consequence
      (fun _ h => h) (by cost_le') (fun _ h => h)
  have hh2 : Costs E (halveBody "v" "x2") (S + H + 16) :=
    (X.seq σ E _ _ _ _ (X.callDest σ E _ _ _ _ hs) (X.callDest σ E _ _ _ _ hh)).consequence
      (fun _ h => h) (by cost_le') (fun _ h => h)
  have hbr : ∀ a b d xa xb : VarName, Costs E (subBranch a b d xa xb) (R + B + 48) := by
    intro a b d xa xb
    exact (X.decCall σ E _ _ _ _ _ _ _ hr (X.seq σ E _ _ _ _ (X.assign σ E _ _ _)
      (X.callDest σ E _ _ _ _ hb))).consequence (fun _ h => h) (by cost_le') (fun _ h => h)
  have ht : Costs E cmpTail (L + R + B + 128) :=
    (X.decCall σ E _ _ _ _ _ _ _ hl (X.ite σ E _ _ _ _ _ (hbr _ _ _ _ _)
      (hbr _ _ _ _ _))).consequence (fun _ h => h) (by cost_le') (fun _ h => h)
  have hloop : Triple E OuterInv (.while (.const (BitVec.ofNat 64 1)) outerBody)
      ((78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 + 1) * (768 * (S + H) + L + R + B + 20004))
      (fun r => match r with
        | .normal _ _ _ _ => True
        | _ => True) := by
    refine (Triple.while (I := OuterInv) (μ := outerMu) (Q := fun _ => True)
      (e := panValueExpStepCost (Exp.const (BitVec.ofNat 64 1) : Exp Word))
      78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 (condCost _ _) (fun _ _ => trivial)
      (fun k => (outerBody_triple hE hcalm k hr1 hr2 hh1 hh2 ht).consequence
        (fun s h => ⟨h.1, h.2.1⟩) (Nat.le_refl _) (fun _ h => h))).consequence ?_ ?_
      (fun r _ => by cases r <;> trivial)
    · intro s hI
      refine ⟨hI, ?_⟩
      obtain ⟨U, V, hu, hv⟩ := hI
      show sixNat "u" s.locals + sixNat "v" s.locals ≤ 78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632
      rw [hu.sixNat_eq, hv.sixNat_eq]
      have := hu.lt
      have := hv.lt
      omega
    · apply Nat.mul_le_mul_left
      cost_le'
  refine FunCost.mono (funCost_of_index 712 hE.functions (by guest_decl_at 712)
    (by decide +kernel) (B := Z + (78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 + 1) * (768 * (S + H) + L + R + B + 20004) + 200) ?_)
    (Nat.le_refl _)
  reduce_body
  refine (Triple.decCall (C := (78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 + 1) * (768 * (S + H) + L + R + B + 20004) + 180)
    (P' := fun _ => True) _ _ _ hz (fun _ _ _ _ _ _ _ => trivial) ?_).consequence
    (fun _ h => h) (by cost_le') (fun _ h => h)
  refine (Triple.seq (B₁ := 40) (B₂ := (78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 + 1) * (768 * (S + H) + L + R + B + 20004) + 130)
    (Mid := fun _ => True) (Q := fun _ => True) ?_ ?_).consequence (fun _ h => h) (by omega)
    (fun _ h => h)
  · exact ((X.ite σ E _ _ _ _ _ (X.ret σ E _) (X.skip σ E)).consequence (fun _ h => h)
      (by cost_le') (fun _ h => h)).consequence (fun _ h => h) (Nat.le_refl _)
      (fun r _ => by cases r <;> trivial)
  refine (Triple.dec (B := (78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 + 1) * (768 * (S + H) + L + R + B + 20004) + 120)
    (P' := fun s => ∃ U, SixVal "u" U s.locals) _ _ _
    (fun s v _ _ hshape => sixVal_of_shape hshape) ?_).consequence (fun _ h => h)
    (by cost_le') (fun _ h => h)
  refine (Triple.dec (B := (78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 + 1) * (768 * (S + H) + L + R + B + 20004) + 90)
    (P' := OuterInv) _ _ _ ?_ ?_).consequence (fun _ h => h) (by cost_le') (fun _ h => h)
  · intro s v hP _ hshape
    obtain ⟨U, hu⟩ := hP
    obtain ⟨V, hv⟩ := sixVal_of_shape (x := "v") (l := s.locals) hshape
    exact ⟨U, V, hu.update_other (by decide), hv⟩
  refine (Triple.dec (B := (78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 + 1) * (768 * (S + H) + L + R + B + 20004) + 60)
    (P' := OuterInv) _ _ _ ?_ ?_).consequence (fun _ h => h) (by cost_le') (fun _ h => h)
  · intro s v hP _ _
    obtain ⟨U, V, hu, hv⟩ := hP
    exact ⟨U, V, hu.update_other (by decide), hv.update_other (by decide)⟩
  refine (Triple.dec (B := (78804012392788958424558080200287227610159478540930893335896586808491443542994421222828532509769831281613255980613632 + 1) * (768 * (S + H) + L + R + B + 20004) + 30)
    (P' := OuterInv) _ _ _ ?_ ?_).consequence (fun _ h => h) (by cost_le') (fun _ h => h)
  · intro s v hP _ _
    obtain ⟨U, V, hu, hv⟩ := hP
    exact ⟨U, V, hu.update_other (by decide), hv.update_other (by decide)⟩
  exact (Triple.seq (Mid := fun _ => True) (Q := fun _ => True) hloop (X.ret σ E _)).consequence
    (fun _ h => h) (by cost_le') (fun _ h => h)

end Manual
end InitECandidate.Solver.GuestBound
