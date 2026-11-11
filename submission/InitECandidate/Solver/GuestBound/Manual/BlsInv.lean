import InitECandidate.Solver.GuestBound.Limbs
import InitECandidate.Solver.GuestBound.WhileExit
import InitECandidate.Solver.GuestBound.TripleRules

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

end InitECandidate.Solver.GuestBound
