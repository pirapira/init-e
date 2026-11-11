import InitECandidate.Solver.GuestBound.Manual.BlsInv
import InitECandidate.Solver.GuestBound.Limbs4

/-!
# `modinv_bin`: binary extended Euclid on 256-bit numbers

The four-limb analogue of `BlsInv.lean`. Here the halving of `u` is an inline
record expression and the subtraction result is assigned by a call.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The local `x` holds four words representing `n`. -/
def FourVal (x : VarName) (n : Nat) (l : VarName → Option (PanValue Word)) : Prop :=
  ∃ w0 w1 w2 w3 : Word,
    l x = some (.rStruct [.word w0, .word w1, .word w2, .word w3]) ∧
    limbsVal [w0, w1, w2, w3] = n

theorem FourVal.update_other {x y : VarName} {n : Nat} {l : VarName → Option (PanValue Word)}
    {v : PanValue Word} (h : FourVal x n l) (hxy : (x == y) = false) :
    FourVal x n (updatePanValueMap l y v) := by
  obtain ⟨w0, w1, w2, w3, hl, hn⟩ := h
  exact ⟨w0, w1, w2, w3, by simp [updatePanValueMap, hxy, hl], hn⟩

theorem fourVal_frame {x : VarName} {n : Nat} {l l' : VarName → Option (PanValue Word)}
    (h : FourVal x n l) (hx : l' x = l x) : FourVal x n l' := by
  obtain ⟨w0, w1, w2, w3, hl, hn⟩ := h
  exact ⟨w0, w1, w2, w3, by rw [hx]; exact hl, hn⟩

/-- The number held by a four-word local, or 0. -/
def fourNat (x : VarName) (l : VarName → Option (PanValue Word)) : Nat :=
  match l x with
  | some (.rStruct [.word w0, .word w1, .word w2, .word w3]) => limbsVal [w0, w1, w2, w3]
  | _ => 0

theorem FourVal.fourNat_eq {x : VarName} {n : Nat} {l : VarName → Option (PanValue Word)}
    (h : FourVal x n l) : fourNat x l = n := by
  obtain ⟨w0, w1, w2, w3, hl, hn⟩ := h
  simp [fourNat, hl, hn]

theorem FourVal.lt {x : VarName} {n : Nat} {l : VarName → Option (PanValue Word)}
    (h : FourVal x n l) : n < 2 ^ 256 := by
  obtain ⟨w0, w1, w2, w3, -, hn⟩ := h
  have := w0.isLt; have := w1.isLt; have := w2.isLt; have := w3.isLt
  simp only [limbsVal] at hn
  omega

theorem limbs_parity4 (w0 w1 w2 w3 : Word) :
    limbsVal [w0, w1, w2, w3] % 2 = w0.toNat % 2 := by
  simp only [limbsVal]
  omega

/-- The halving-loop guard on a four-word local. -/
theorem evenGuard_eval4 (hE : GuestEnv E) {x : VarName} {s : St σ} {w0 w1 w2 w3 : Word}
    (hl : s.locals x = some (.rStruct [.word w0, .word w1, .word w2, .word w3])) {g : Word}
    (h : E.eval s (evenGuard x) = some (.word g)) :
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

/-- `x = <(x.0 >>> 1) | (x.1 << 63), …, x.3 >>> 1>`. -/
def shrAssign (x : VarName) : Prog Word :=
  .assign .local x (.rStruct [
    .op .or [.shift .lsr (.rField 0 (.var .local x)) (.const (BitVec.ofNat 64 1)),
      .shift .lsl (.rField 1 (.var .local x)) (.const (BitVec.ofNat 64 63))],
    .op .or [.shift .lsr (.rField 1 (.var .local x)) (.const (BitVec.ofNat 64 1)),
      .shift .lsl (.rField 2 (.var .local x)) (.const (BitVec.ofNat 64 63))],
    .op .or [.shift .lsr (.rField 2 (.var .local x)) (.const (BitVec.ofNat 64 1)),
      .shift .lsl (.rField 3 (.var .local x)) (.const (BitVec.ofNat 64 63))],
    .shift .lsr (.rField 3 (.var .local x)) (.const (BitVec.ofNat 64 1))])

set_option maxHeartbeats 2000000 in
/-- The inline shift halves the number held by `x`. -/
theorem shrAssign_runs (hE : GuestEnv E) {x : VarName} {n : Nat} {s : St σ} {r : Result σ}
    (hx : FourVal x n s.locals) (h : Runs E s (shrAssign x) r) :
    r.isError = true ∨ ∃ l, r = .normal l s.globals s.memory s.ffi ∧ FourVal x (n / 2) l ∧
      ∀ y, y ≠ x → l y = s.locals y := by
  obtain ⟨w0, w1, w2, w3, hl, hn⟩ := hx
  unfold shrAssign at h
  rw [runs_assign_local] at h
  simp (config := { decide := true }) only [evalF_rStruct, evalF_rField, evalF_local,
    eval_const, evalF_op hE.word, evalF_shift hE.word, evalArgs_cons, evalArgs_nil, hl,
    Option.map_some, List.getElem?_cons_zero, List.getElem?_cons_succ, wordsProj_nil,
    wordsProj_cons, wordOp, List.foldr, RiscV.panRiscVShift, BitVec.toNat_ofNat, if_true] at h
  split at h
  · subst h
    refine Or.inr ⟨_, rfl, ⟨_, _, _, _,
      by rw [update_lookup, if_pos (beq_self_eq_true x)], ?_⟩, ?_⟩
    · have key := shrLimbs_val [w0.toNat, w1.toNat, w2.toNat, w3.toNat]
      simp only [shrLimbs, nval] at key
      rw [← hn]
      simp only [limbsVal, show (1 % 2 ^ 64 : Nat) = 1 from by decide,
        show (63 % 2 ^ 64 : Nat) = 63 from by decide, shr_limb, shr_last]
      exact key
    · intro y hy
      have : (y == x) = false := by simpa using hy
      simp [updatePanValueMap, this]
  · subst h
    exact Or.inl rfl

/-- The body of a halving loop: halve `x`, adjust `y`. -/
def halveBody4 (x y : VarName) : Prog Word :=
  .seq (shrAssign x)
    (.call (some (some (.local, y), none)) "mod_half" [.var .local y, .var .local "m"])

theorem halveBody4_runs (hE : GuestEnv E) (hcalm : FunCalm E "mod_half") {x y : VarName}
    (hxy : x ≠ y) {n : Nat} {s : St σ} {r : Result σ} (hx : FourVal x n s.locals)
    (h : Runs E s (halveBody4 x y) r) :
    r.isError = true ∨ ∃ l g m f, r = .normal l g m f ∧ FourVal x (n / 2) l ∧
      ∀ z, z ≠ x → z ≠ y → l z = s.locals z := by
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp h
  rcases shrAssign_runs hE hx h₁ with herr | ⟨l1, rfl, hfour, hframe⟩
  · cases r₁ with
    | error l g m f =>
      simp only at hrest
      subst hrest
      exact Or.inl rfl
    | _ => cases herr
  simp only at hrest
  rcases call_calm_local hcalm hrest with herr | ⟨l, g, m, f, rfl, hframe'⟩
  · exact Or.inl herr
  refine Or.inr ⟨l, g, m, f, rfl, fourVal_frame hfour (hframe' x hxy), ?_⟩
  intro z hzx hzy
  rw [hframe' z hzy]
  exact hframe z hzx

/-- A halving loop on a four-word local: within 256 iterations, or no return. -/
theorem halve_loop4 (hE : GuestEnv E) (hcalm : FunCalm E "mod_half") {x y : VarName}
    (hxy : x ≠ y) (F : (VarName → Option (PanValue Word)) → Prop)
    (hF : ∀ l l', (∀ z, z ≠ x → z ≠ y → l' z = l z) → F l → F l') (n b : Nat)
    (hb : Costs E (halveBody4 x y) b) :
    Triple E (fun s => FourVal x n s.locals ∧ F s.locals)
      (.while (evenGuard x) (halveBody4 x y))
      (256 * (panValueExpStepCost (evenGuard x) + b + 1))
      (fun r => match r with
        | .normal l _ _ _ => ∃ n', n' ≤ n ∧ n' % 2 = 1 ∧ FourVal x n' l ∧ F l
        | .continued _ _ _ _ | .broke _ _ _ _ => False
        | _ => True) := by
  by_cases hn : n = 0
  · subst hn
    intro fuel s r m hP hrun hne
    have herr := while_never (E := E) (Z := fun s => FourVal x 0 s.locals) (c := evenGuard x)
      (body := halveBody4 x y)
      (by
        intro s hZ v k hcond
        obtain ⟨w0, w1, w2, w3, hl, hval⟩ := hZ
        have hpar := limbs_parity4 w0 w1 w2 w3
        have hiff := evenGuard_eval4 hE hl (cond_of_eval hcond)
        have hv : v ≠ 0 := by
          intro hv0
          have := hiff.mp hv0
          omega
        simpa using hv)
      (by
        intro fuel s r n hZ hrun
        rcases halveBody4_runs hE hcalm hxy hZ (Runs.of_run hrun) with herr |
          ⟨l, g, m, f, rfl, hfour, -⟩
        · exact Or.inl herr
        · exact Or.inr ⟨l, g, m, f, rfl, hfour⟩)
      fuel s r m hP.1 hrun
    rw [herr] at hne
    cases hne
  · refine (Triple.while_exit
      (I := fun s => ∃ n', n' ≤ n ∧ n' ≠ 0 ∧ FourVal x n' s.locals ∧ F s.locals)
      (μ := fun s => Nat.log2 (fourNat x s.locals))
      (Q := fun r => match r with
        | .normal l _ _ _ => ∃ n', n' ≤ n ∧ n' % 2 = 1 ∧ FourVal x n' l ∧ F l
        | .continued _ _ _ _ | .broke _ _ _ _ => False
        | _ => True)
      (e := panValueExpStepCost (evenGuard x)) (b := b) 255 (condCost _ _) ?_ ?_).consequence
      ?_ (Nat.le_refl _) (fun _ h => h)
    · intro s hI hexit
      obtain ⟨n', hle, -, hfour, hFs⟩ := hI
      obtain ⟨k, hcond⟩ := hexit
      obtain ⟨w0, w1, w2, w3, hl, hval⟩ := hfour
      have hodd := (evenGuard_eval4 hE hl (cond_of_eval hcond)).mp rfl
      have hpar := limbs_parity4 w0 w1 w2 w3
      exact ⟨n', hle, by omega, ⟨w0, w1, w2, w3, hl, hval⟩, hFs⟩
    · intro k
      refine Triple.of_costs hb ?_
      intro fuel s r m hP hrun hner
      obtain ⟨⟨n', hle, hne0, hfour, hFs⟩, hμ, v, kc, hcond, hv⟩ := hP
      have hnat := hfour.fourNat_eq
      have heven : n' % 2 = 0 := by
        obtain ⟨w0, w1, w2, w3, hl, hval⟩ := hfour
        have hiff := evenGuard_eval4 hE hl (cond_of_eval hcond)
        have hpar := limbs_parity4 w0 w1 w2 w3
        have hv0 : v ≠ 0 := by simpa using hv
        have : ¬ w0.toNat % 2 = 1 := fun h1 => hv0 (hiff.mpr h1)
        omega
      rcases halveBody4_runs hE hcalm hxy hfour (Runs.of_run hrun) with herr |
        ⟨l, g, m', f, rfl, hfour', hframe⟩
      · rw [herr] at hner
        cases hner
      · have hnat' := hfour'.fourNat_eq
        refine ⟨⟨n' / 2, by omega, by omega, hfour', hF _ _ hframe hFs⟩, ?_⟩
        show Nat.log2 (fourNat x l) < k
        rw [hnat', ← hμ, hnat]
        have h2 : 2 ≤ n' := by omega
        rw [Nat.log2_def n', if_pos h2]
        omega
    · intro s hP
      obtain ⟨hfour, hFs⟩ := hP
      refine ⟨⟨n, Nat.le_refl _, hn, hfour, hFs⟩, ?_⟩
      show Nat.log2 (fourNat x s.locals) ≤ 255
      rw [hfour.fourNat_eq]
      have := (Nat.log2_lt hn (k := 256)).mpr hfour.lt
      omega

/-- `a = u256_sub(a, b); xa = mod_sub(xa, xb, m)`. -/
def subSeq (a b xa xb : VarName) : Prog Word :=
  .seq (.call (some (some (.local, a), none)) "u256_sub" [.var .local a, .var .local b])
    (.call (some (some (.local, xa), none)) "mod_sub"
      [.var .local xa, .var .local xb, .var .local "m"])

set_option maxHeartbeats 1000000 in
/-- The subtraction step replaces `a` by `a - b` and otherwise changes only `xa`. -/
theorem subSeq_runs (hE : GuestEnv E) {a b xa xb : VarName} (haxa : a ≠ xa) {A B : Nat}
    {s : St σ} {r : Result σ} (ha : FourVal a A s.locals) (hb : FourVal b B s.locals)
    (hle : B ≤ A) :
    Runs E s (subSeq a b xa xb) r →
    match r with
    | .normal l _ _ _ => FourVal a (A - B) l ∧ ∀ z, z ≠ a → z ≠ xa → l z = s.locals z
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  intro h
  obtain ⟨a0, a1, a2, a3, hla, hA⟩ := ha
  obtain ⟨b0, b1, b2, b3, hlb, hB⟩ := hb
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp h
  have herror : r₁.isError = true → r.isError = true := by
    intro herr
    cases r₁ with
    | error l g m f =>
      simp only at hrest
      subst hrest
      rfl
    | _ => cases herr
  rcases runs_call_inv (some (some (.local, a))) h₁ with herr | ⟨parameters, body, values,
    calleeLocals, rb, hlookup, hvalues, hbind, hcallee, hout⟩
  · have hre := herror herr
    cases r <;> first | trivial | cases hre
  have hparams := (fun_of_index 57 hE.functions (by guest_decl_at 57) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, hla, hlb, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hca : calleeLocals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]) := by
    rw [← hbind]
    simp [updatePanValueMap]
  have hcb : calleeLocals "b" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]) := by
    rw [← hbind]
    simp [updatePanValueMap]
  obtain ⟨cl, d0, d1, d2, d3, rfl, hd⟩ := u256_sub_spec hE parameters body hlookup
    ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb a0 a1 a2 a3 b0 b1 b2 b3 hca hcb
    (by rw [hA, hB]; exact hle) hcallee
  simp only [CallOutcome] at hout
  rcases hout with herr | ⟨l', g', hassign, rfl⟩
  · have hre := herror herr
    cases r <;> first | trivial | cases hre
  simp only [assignPanValueCallResult] at hassign
  split at hassign
  · simp only [Option.some.injEq, Prod.mk.injEq] at hassign
    obtain ⟨rfl, rfl⟩ := hassign
    simp only at hrest
    have hframe := call_local_frame hrest
    cases r with
    | normal l g m f =>
      simp only at hframe
      refine ⟨⟨d0, d1, d2, d3, ?_, ?_⟩, ?_⟩
      · rw [hframe a haxa]
        simp [updatePanValueMap]
      · rw [hd, hA, hB]
      · intro z hza hzxa
        rw [hframe z hzxa]
        have : (z == a) = false := by simpa using hza
        simp [updatePanValueMap, this]
    | continued l g m f => exact hframe.elim
    | broke l g m f => exact hframe.elim
    | _ => trivial
  · cases hassign

/-- The end of the outer loop body: compare `u` and `v`, subtract the smaller. -/
def cmpTail4 : Prog Word :=
  .decCall "ult" .one "u256_lt" [.var .local "u", .var .local "v"]
    (.ite (.cmp .equal (.var .local "ult") (.const (BitVec.ofNat 64 0)))
      (subSeq "u" "v" "x1" "x2") (subSeq "v" "u" "x2" "x1"))

set_option maxHeartbeats 1000000 in
/-- With `u` and `v` positive, the tail decreases `u + v`. -/
theorem cmpTail4_runs (hE : GuestEnv E) {U V : Nat} {s : St σ} {r : Result σ}
    (hu : FourVal "u" U s.locals) (hv : FourVal "v" V s.locals) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    Runs E s cmpTail4 r →
    match r with
    | .normal l _ _ _ => ∃ U' V', FourVal "u" U' l ∧ FourVal "v" V' l ∧ U' + V' < U + V
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  intro h
  obtain ⟨u0, u1, u2, u3, hlu, hUv⟩ := id hu
  obtain ⟨v0, v1, v2, v3, hlv, hVv⟩ := id hv
  rcases runs_decCall_inv h with herr | ⟨parameters, body, values, calleeLocals, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · cases r <;> trivial
  have hparams := (fun_of_index 46 hE.functions (by guest_decl_at 46) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, hlu, hlv, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hca : calleeLocals "a" = some (.rStruct [.word u0, .word u1, .word u2, .word u3]) := by
    rw [← hbind]
    simp [updatePanValueMap]
  have hcb : calleeLocals "b" = some (.rStruct [.word v0, .word v1, .word v2, .word v3]) := by
    rw [← hbind]
    simp [updatePanValueMap]
  have hspec := u256_lt_spec hE parameters body hlookup
    ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb u0 u1 u2 u3 v0 v1 v2 v3 hca hcb hcallee
  subst hspec
  obtain ⟨r', -, hrun', rfl⟩ := hout
  rw [hUv, hVv] at hrun'
  have hu' : ∀ c : Word, FourVal "u" U (updatePanValueMap s.locals "ult" (PanValue.word c)) :=
    fun c => hu.update_other (by decide)
  have hv' : ∀ c : Word, FourVal "v" V (updatePanValueMap s.locals "ult" (PanValue.word c)) :=
    fun c => hv.update_other (by decide)
  rw [runs_ite] at hrun'
  simp only [evalF_cmp hE.word, evalF_local, eval_const, update_lookup, beq_self_eq_true,
    if_true] at hrun'
  by_cases hlt : U < V
  · simp only [hlt, if_true, evalPanCmp] at hrun'
    have hbr := subSeq_runs hE (a := "v") (b := "u") (xa := "x2") (xb := "x1") (by decide)
      (s := ⟨updatePanValueMap s.locals "ult" (PanValue.word 1#64), s.globals, s.memory, s.ffi⟩)
      (hv' _) (hu' _) (Nat.le_of_lt hlt) hrun'
    cases r' with
    | normal l g m f =>
      obtain ⟨hfour, hframe⟩ := hbr
      simp only [restorePanValueFfiLocal]
      refine ⟨U, V - U, ?_, ?_, by omega⟩
      · refine fourVal_frame (hu' 1) ?_
        simp only [restorePanValueLocal, show (("u" : String) == "ult") = false from by decide,
          Bool.false_eq_true, if_false]
        exact hframe "u" (by decide) (by decide)
      · refine fourVal_frame hfour ?_
        simp only [restorePanValueLocal, show (("v" : String) == "ult") = false from by decide,
          Bool.false_eq_true, if_false]
    | continued l g m f => exact hbr.elim
    | broke l g m f => exact hbr.elim
    | _ => simp only [restorePanValueFfiLocal]
  · simp only [hlt, if_false, evalPanCmp] at hrun'
    have hbr := subSeq_runs hE (a := "u") (b := "v") (xa := "x1") (xb := "x2") (by decide)
      (s := ⟨updatePanValueMap s.locals "ult" (PanValue.word 0#64), s.globals, s.memory, s.ffi⟩)
      (hu' _) (hv' _) (Nat.le_of_not_lt hlt) hrun'
    cases r' with
    | normal l g m f =>
      obtain ⟨hfour, hframe⟩ := hbr
      simp only [restorePanValueFfiLocal]
      refine ⟨U - V, V, ?_, ?_, by omega⟩
      · refine fourVal_frame hfour ?_
        simp only [restorePanValueLocal, show (("u" : String) == "ult") = false from by decide,
          Bool.false_eq_true, if_false]
      · refine fourVal_frame (hv' 0) ?_
        simp only [restorePanValueLocal, show (("v" : String) == "ult") = false from by decide,
          Bool.false_eq_true, if_false]
        exact hframe "v" (by decide) (by decide)
    | continued l g m f => exact hbr.elim
    | broke l g m f => exact hbr.elim
    | _ => simp only [restorePanValueFfiLocal]

/-- `if (x.1 | x.2 | x.3) == 0 { if x.0 == 1 { return y; } }`. -/
abbrev retCheck4 (x y : VarName) : Prog Word :=
  .ite (.cmp .equal (.op .or [.rField 1 (.var .local x), .rField 2 (.var .local x),
      .rField 3 (.var .local x)]) (.const (BitVec.ofNat 64 0)))
    (.ite (.cmp .equal (.rField 0 (.var .local x)) (.const (BitVec.ofNat 64 1)))
      (.return (.var .local y)) .skip)
    .skip

/-- The body of the outer loop of `modinv_bin`. -/
def outerBody4 : Prog Word :=
  .seq (retCheck4 "u" "x1")
    (.seq (retCheck4 "v" "x2")
      (.seq (.while (evenGuard "u") (halveBody4 "u" "x1"))
        (.seq (.while (evenGuard "v") (halveBody4 "v" "x2")) cmpTail4)))

def OuterInv4 (s : St σ) : Prop := ∃ U V, FourVal "u" U s.locals ∧ FourVal "v" V s.locals

def outerMu4 (s : St σ) : Nat := fourNat "u" s.locals + fourNat "v" s.locals

/-- One outer iteration decreases `u + v`. -/
theorem outerBody4_triple (hE : GuestEnv E) (hcalm : FunCalm E "mod_half") (k : Nat)
    {br bh bt : Nat} (hr1 : Costs E (retCheck4 "u" "x1") br)
    (hr2 : Costs E (retCheck4 "v" "x2") br)
    (hh1 : Costs E (halveBody4 "u" "x1") bh) (hh2 : Costs E (halveBody4 "v" "x2") bh)
    (ht : Costs E cmpTail4 bt) :
    Triple E (fun s => OuterInv4 s ∧ outerMu4 s = k) outerBody4
      (br + (br + (256 * (panValueExpStepCost (evenGuard "u") + bh + 1) +
        (256 * (panValueExpStepCost (evenGuard "v") + bh + 1) + bt + 1) + 1) + 1) + 1)
      (loopBodyPost OuterInv4 outerMu4 k (fun _ => True)) := by
  have key : ∀ U V, U + V = k →
      Triple E (fun s => FourVal "u" U s.locals ∧ FourVal "v" V s.locals) outerBody4
        (br + (br + (256 * (panValueExpStepCost (evenGuard "u") + bh + 1) +
          (256 * (panValueExpStepCost (evenGuard "v") + bh + 1) + bt + 1) + 1) + 1) + 1)
        (loopBodyPost OuterInv4 outerMu4 k (fun _ => True)) := by
    intro U V hk
    have keep : ∀ (c : Nat) (p : Prog Word), Costs E p c →
        (∀ (s : St σ) (r : Result σ), Runs E s p r →
          match r with
          | .normal l g m f => l = s.locals ∧ g = s.globals ∧ m = s.memory ∧ f = s.ffi
          | .continued _ _ _ _ | .broke _ _ _ _ => False
          | _ => True) →
        Triple E (fun s => FourVal "u" U s.locals ∧ FourVal "v" V s.locals) p c
          (fun r => match r with
            | .normal l g m f => FourVal "u" U l ∧ FourVal "v" V l
            | r => loopBodyPost OuterInv4 outerMu4 k (fun _ => True) r) := by
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
    refine Triple.seq (Mid := fun s => FourVal "u" U s.locals ∧ FourVal "v" V s.locals)
      (keep br _ hr1 (fun s r h => retIte_runs h))
      (Triple.seq (Mid := fun s => FourVal "u" U s.locals ∧ FourVal "v" V s.locals)
        (keep br _ hr2 (fun s r h => retIte_runs h)) (Triple.seq
        (Mid := fun s => ∃ U1, U1 ≤ U ∧ U1 % 2 = 1 ∧ FourVal "u" U1 s.locals ∧
          FourVal "v" V s.locals) ?_ (Triple.seq
        (Mid := fun s => ∃ U1 V1, U1 ≤ U ∧ U1 % 2 = 1 ∧ V1 ≤ V ∧ V1 % 2 = 1 ∧
          FourVal "u" U1 s.locals ∧ FourVal "v" V1 s.locals) ?_ ?_)))
    · refine (halve_loop4 hE hcalm (x := "u") (y := "x1") (by decide)
        (fun l => FourVal "v" V l)
        (fun l l' hframe h => fourVal_frame h (hframe "v" (by decide) (by decide))) U bh
        hh1).consequence (fun _ h => h) (Nat.le_refl _) ?_
      intro r hr
      cases r with
      | normal l g m f =>
        obtain ⟨U1, hle, hodd, hfour, hv⟩ := hr
        exact ⟨U1, hle, hodd, hfour, hv⟩
      | continued l g m f => exact hr.elim
      | broke l g m f => exact hr.elim
      | _ => trivial
    · refine (halve_loop4 hE hcalm (x := "v") (y := "x2") (by decide)
        (fun l => ∃ U1, U1 ≤ U ∧ U1 % 2 = 1 ∧ FourVal "u" U1 l)
        (fun l l' hframe h => by
          obtain ⟨U1, hle, hodd, hfour⟩ := h
          exact ⟨U1, hle, hodd, fourVal_frame hfour (hframe "u" (by decide) (by decide))⟩) V bh
        hh2).consequence ?_ (Nat.le_refl _) ?_
      · intro s h
        obtain ⟨U1, hle, hodd, hfour, hv⟩ := h
        exact ⟨hv, U1, hle, hodd, hfour⟩
      · intro r hr
        cases r with
        | normal l g m f =>
          obtain ⟨V1, hle, hodd, hfour, U1, hle', hodd', hfour'⟩ := hr
          exact ⟨U1, V1, hle', hodd', hle, hodd, hfour', hfour⟩
        | continued l g m f => exact hr.elim
        | broke l g m f => exact hr.elim
        | _ => trivial
    · refine Triple.of_costs ht ?_
      intro fuel s r n hP hrun hne
      obtain ⟨U1, V1, hle, hodd, hle', hodd', hu, hv⟩ := hP
      have := cmpTail4_runs hE hu hv (by omega) (by omega) (Runs.of_run hrun)
      cases r with
      | normal l g m f =>
        obtain ⟨U', V', hu', hv', hlt⟩ := this
        refine ⟨⟨U', V', hu', hv'⟩, ?_⟩
        show fourNat "u" l + fourNat "v" l < k
        rw [hu'.fourNat_eq, hv'.fourNat_eq]
        omega
      | continued l g m f => exact this.elim
      | broke l g m f => exact this.elim
      | _ => trivial
  intro fuel s r n hP hrun hne
  obtain ⟨⟨U, V, hu, hv⟩, hμ⟩ := hP
  exact key U V (by rw [← hμ]; show U + V = fourNat "u" s.locals + fourNat "v" s.locals
                    rw [hu.fourNat_eq, hv.fourNat_eq]) fuel s r n ⟨hu, hv⟩ hrun hne

theorem fourVal_of_shape {structs : StructContext} {v : PanValue Word} {x : VarName}
    {l : VarName → Option (PanValue Word)}
    (h : panShapeMatches (panValueShape structs v) (.comb [.one, .one, .one, .one]) = true) :
    ∃ n, FourVal x n (updatePanValueMap l x v) := by
  obtain ⟨ws, rfl, hlen⟩ := panValueShape_matches_word_record_inv structs v
    [(0 : Word), 0, 0, 0] h
  match ws, hlen with
  | [w0, w1, w2, w3], _ => exact ⟨_, w0, w1, w2, w3, by simp [updatePanValueMap], rfl⟩

/-- Close a cost inequality between closed expression costs. -/
macro "cost_le4" : tactic => `(tactic| (
  simp only [stepCost_eq, stepsCost_eq, expCost, expsCost, evenGuard, shrAssign]
  omega))

namespace Manual

set_option maxHeartbeats 2000000 in
theorem «modinv_bin».cost (hE : GuestEnv E) {Z H L S B : Nat}
    (hz : FunCost E "u256_is_zero" Z) (hh : FunCost E "mod_half" H)
    (hl : FunCost E "u256_lt" L) (hs : FunCost E "u256_sub" S) (hb : FunCost E "mod_sub" B) :
    FunCost E "modinv_bin" (Z + (231584178474632390847141970017375815706539969331281128078915168015826259279872 + 1) * (512 * H + L + S + B + 60004) + 200) := by
  have hcalm : FunCalm E "mod_half" :=
    calmFn_sound hE.functions calmDepth "mod_half" (by decide +kernel)
  have hpow : (2 : Nat) ^ 256 * 2 = 231584178474632390847141970017375815706539969331281128078915168015826259279872 := by decide +kernel
  have hr1 : Costs E (retCheck4 "u" "x1") 64 :=
    (X.ite σ E _ _ _ _ _ (X.ite σ E _ _ _ _ _ (X.ret σ E _) (X.skip σ E))
      (X.skip σ E)).consequence (fun _ h => h) (by cost_le4) (fun _ h => h)
  have hr2 : Costs E (retCheck4 "v" "x2") 64 :=
    (X.ite σ E _ _ _ _ _ (X.ite σ E _ _ _ _ _ (X.ret σ E _) (X.skip σ E))
      (X.skip σ E)).consequence (fun _ h => h) (by cost_le4) (fun _ h => h)
  have hh1 : Costs E (halveBody4 "u" "x1") (H + 100) :=
    (X.seq σ E _ _ _ _ (X.assign σ E _ _ _) (X.callDest σ E _ _ _ _ hh)).consequence
      (fun _ h => h) (by cost_le4) (fun _ h => h)
  have hh2 : Costs E (halveBody4 "v" "x2") (H + 100) :=
    (X.seq σ E _ _ _ _ (X.assign σ E _ _ _) (X.callDest σ E _ _ _ _ hh)).consequence
      (fun _ h => h) (by cost_le4) (fun _ h => h)
  have hbr : ∀ a b xa xb : VarName, Costs E (subSeq a b xa xb) (S + B + 32) := by
    intro a b xa xb
    exact (X.seq σ E _ _ _ _ (X.callDest σ E _ _ _ _ hs)
      (X.callDest σ E _ _ _ _ hb)).consequence (fun _ h => h) (by cost_le4) (fun _ h => h)
  have ht : Costs E cmpTail4 (L + S + B + 100) :=
    (X.decCall σ E _ _ _ _ _ _ _ hl (X.ite σ E _ _ _ _ _ (hbr _ _ _ _)
      (hbr _ _ _ _))).consequence (fun _ h => h) (by cost_le4) (fun _ h => h)
  have hloop : Triple E OuterInv4 (.while (.const (BitVec.ofNat 64 1)) outerBody4)
      ((231584178474632390847141970017375815706539969331281128078915168015826259279872 + 1) * (512 * H + L + S + B + 60004))
      (fun r => match r with
        | .normal _ _ _ _ => True
        | _ => True) := by
    refine (Triple.while (I := OuterInv4) (μ := outerMu4) (Q := fun _ => True)
      (e := panValueExpStepCost (Exp.const (BitVec.ofNat 64 1) : Exp Word))
      231584178474632390847141970017375815706539969331281128078915168015826259279872 (condCost _ _) (fun _ _ => trivial)
      (fun k => (outerBody4_triple hE hcalm k hr1 hr2 hh1 hh2 ht).consequence
        (fun s h => ⟨h.1, h.2.1⟩) (Nat.le_refl _) (fun _ h => h))).consequence ?_ ?_
      (fun r _ => by cases r <;> trivial)
    · intro s hI
      refine ⟨hI, ?_⟩
      obtain ⟨U, V, hu, hv⟩ := hI
      show fourNat "u" s.locals + fourNat "v" s.locals ≤ 231584178474632390847141970017375815706539969331281128078915168015826259279872
      rw [hu.fourNat_eq, hv.fourNat_eq]
      have := hu.lt
      have := hv.lt
      omega
    · apply Nat.mul_le_mul_left
      cost_le4
  refine FunCost.mono (funCost_of_index 157 hE.functions (by guest_decl_at 157)
    (by decide +kernel) (B := Z + (231584178474632390847141970017375815706539969331281128078915168015826259279872 + 1) * (512 * H + L + S + B + 60004) + 200) ?_)
    (Nat.le_refl _)
  reduce_body
  refine (Triple.decCall (C := (231584178474632390847141970017375815706539969331281128078915168015826259279872 + 1) * (512 * H + L + S + B + 60004) + 180)
    (P' := fun _ => True) _ _ _ hz (fun _ _ _ _ _ _ _ => trivial) ?_).consequence
    (fun _ h => h) (by cost_le4) (fun _ h => h)
  refine (Triple.seq (B₁ := 40) (B₂ := (231584178474632390847141970017375815706539969331281128078915168015826259279872 + 1) * (512 * H + L + S + B + 60004) + 130)
    (Mid := fun _ => True) (Q := fun _ => True) ?_ ?_).consequence (fun _ h => h) (by omega)
    (fun _ h => h)
  · exact ((X.ite σ E _ _ _ _ _ (X.ret σ E _) (X.skip σ E)).consequence (fun _ h => h)
      (by cost_le4) (fun _ h => h)).consequence (fun _ h => h) (Nat.le_refl _)
      (fun r _ => by cases r <;> trivial)
  refine (Triple.dec (B := (231584178474632390847141970017375815706539969331281128078915168015826259279872 + 1) * (512 * H + L + S + B + 60004) + 120)
    (P' := fun s => ∃ U, FourVal "u" U s.locals) _ _ _
    (fun s v _ _ hshape => fourVal_of_shape hshape) ?_).consequence (fun _ h => h)
    (by cost_le4) (fun _ h => h)
  refine (Triple.dec (B := (231584178474632390847141970017375815706539969331281128078915168015826259279872 + 1) * (512 * H + L + S + B + 60004) + 90)
    (P' := OuterInv4) _ _ _ ?_ ?_).consequence (fun _ h => h) (by cost_le4) (fun _ h => h)
  · intro s v hP _ hshape
    obtain ⟨U, hu⟩ := hP
    obtain ⟨V, hv⟩ := fourVal_of_shape (x := "v") (l := s.locals) hshape
    exact ⟨U, V, hu.update_other (by decide), hv⟩
  refine (Triple.dec (B := (231584178474632390847141970017375815706539969331281128078915168015826259279872 + 1) * (512 * H + L + S + B + 60004) + 60)
    (P' := OuterInv4) _ _ _ ?_ ?_).consequence (fun _ h => h) (by cost_le4) (fun _ h => h)
  · intro s v hP _ _
    obtain ⟨U, V, hu, hv⟩ := hP
    exact ⟨U, V, hu.update_other (by decide), hv.update_other (by decide)⟩
  refine (Triple.dec (B := (231584178474632390847141970017375815706539969331281128078915168015826259279872 + 1) * (512 * H + L + S + B + 60004) + 30)
    (P' := OuterInv4) _ _ _ ?_ ?_).consequence (fun _ h => h) (by cost_le4) (fun _ h => h)
  · intro s v hP _ _
    obtain ⟨U, V, hu, hv⟩ := hP
    exact ⟨U, V, hu.update_other (by decide), hv.update_other (by decide)⟩
  exact (Triple.seq (Mid := fun _ => True) (Q := fun _ => True) hloop (X.ret σ E _)).consequence
    (fun _ h => h) (by cost_le4) (fun _ h => h)

end Manual
end InitECandidate.Solver.GuestBound
