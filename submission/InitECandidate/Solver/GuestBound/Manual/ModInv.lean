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

end InitECandidate.Solver.GuestBound
