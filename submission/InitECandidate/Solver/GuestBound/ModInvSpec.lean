import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic
import InitECandidate.Solver.GuestBound.Manual.ModInv
import InitECandidate.Solver.GuestBound.ModHalf
import InitECandidate.Solver.GuestBound.HtabDiff

/-!
# `modinv_bin` computes a modular inverse

Partial correctness of the binary extended Euclid: with `m` odd, the loop
keeps `u ≡ x1 * a` and `v ≡ x2 * a` modulo `m`, so the value returned when
`u = 1` (or `v = 1`) is an inverse of `a`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- Halving both sides keeps `u ≡ x * a (mod m)` when `m` is odd. -/
theorem half_inv {U X A M : Nat} (hM : M % 2 = 1) (hU : U % 2 = 0)
    (h : U % M = X * A % M) :
    (U / 2) % M = (if X % 2 = 0 then X / 2 else (X + M) / 2) * A % M := by
  have hcop : Nat.gcd M 2 = 1 := by
    rw [Nat.gcd_comm, Nat.gcd_rec, hM]
    exact Nat.gcd_one_left 2
  have h2 : 2 * (if X % 2 = 0 then X / 2 else (X + M) / 2) ≡ X [MOD M] := by
    by_cases hx : X % 2 = 0
    · rw [if_pos hx]
      have : 2 * (X / 2) = X := by omega
      rw [this]
    · rw [if_neg hx]
      have : 2 * ((X + M) / 2) = X + M := by omega
      rw [this]
      exact Nat.add_modEq_right
  have hU2 : 2 * (U / 2) = U := by omega
  have key : 2 * (U / 2) ≡ 2 * ((if X % 2 = 0 then X / 2 else (X + M) / 2) * A) [MOD M] := by
    rw [hU2, ← Nat.mul_assoc]
    exact (show U ≡ X * A [MOD M] from h).trans (h2.mul_right A).symm
  exact Nat.ModEq.cancel_left_of_coprime hcop key

/-- Subtracting keeps the congruences. -/
theorem sub_inv {U V X1 X2 A M : Nat} (hX2 : X2 < M) (hVU : V ≤ U)
    (hu : U % M = X1 * A % M) (hv : V % M = X2 * A % M) :
    (U - V) % M = (if X1 < X2 then X1 + M - X2 else X1 - X2) * A % M := by
  have hd : (if X1 < X2 then X1 + M - X2 else X1 - X2) + X2 ≡ X1 [MOD M] := by
    by_cases hlt : X1 < X2
    · rw [if_pos hlt]
      have : X1 + M - X2 + X2 = X1 + M := by omega
      rw [this]
      exact Nat.add_modEq_right
    · rw [if_neg hlt]
      have : X1 - X2 + X2 = X1 := by omega
      rw [this]
  have h1 : (if X1 < X2 then X1 + M - X2 else X1 - X2) * A + X2 * A ≡ (U - V) + X2 * A [MOD M] := by
    rw [← Nat.add_mul]
    have hUV : U - V + V = U := by omega
    calc ((if X1 < X2 then X1 + M - X2 else X1 - X2) + X2) * A ≡ X1 * A [MOD M] := hd.mul_right A
      _ ≡ U [MOD M] := (show U ≡ X1 * A [MOD M] from hu).symm
      _ = U - V + V := hUV.symm
      _ ≡ U - V + X2 * A [MOD M] := Nat.ModEq.add_left _ (show V ≡ X2 * A [MOD M] from hv)
  exact (Nat.ModEq.add_right_cancel' _ h1).symm

variable {σ : Type} {E : Env σ} {Q : Result σ → Prop}

set_option maxHeartbeats 4000000 in
/-- `if (x.1 | x.2 | x.3) == 0 { if x.0 == 1 { return y; } }; rest`: returns
`y` only when `x` holds 1. -/
theorem retCheck4_wp (hE : GuestEnv E) {x y : VarName} {rest : Prog Word} {s : St σ}
    {w0 w1 w2 w3 y0 y1 y2 y3 : Word}
    (hx : s.locals x = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (hy : s.locals y = some (.rStruct [.word y0, .word y1, .word y2, .word y3]))
    (hcont : WPs E s rest Q)
    (hret : limbsVal [w0, w1, w2, w3] = 1 →
      Q (.returned (fun _ => none) s.globals s.memory s.ffi
        [.rStruct [.word y0, .word y1, .word y2, .word y3]])) :
    WPs E s (.seq (retCheck4 x y) rest) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  rw [runs_ite] at h1
  simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_op hE.word, evalF_rField,
    evalF_local, eval_const, evalArgs_cons, evalArgs_nil, hx, Option.map_some,
    List.getElem?_cons_zero, List.getElem?_cons_succ, wordsProj_nil, wordsProj_cons, wordOp,
    List.foldr] at h1
  have skip : r1 = .normal s.locals s.globals s.memory s.ffi → Stopped r ∨ Q r := by
    intro e
    subst e
    exact hcont r hrest
  obtain ⟨W, hW⟩ : ∃ W : Word, W = OrOp.or w1 (OrOp.or w2 (OrOp.or w3 (0 : Word))) := ⟨_, rfl⟩
  rw [← hW] at h1
  by_cases hz : W = 0#64
  · have hc : evalPanCmp .equal W 0#64 = 1#64 := by
      rw [hz]
      rfl
    rw [hc, if_neg (by decide)] at h1
    rw [runs_ite] at h1
    simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_rField, evalF_local,
      eval_const, hx, List.getElem?_cons_zero] at h1
    by_cases h01 : w0 = 1#64
    · have hc2 : evalPanCmp .equal w0 1#64 = 1#64 := by simp [evalPanCmp, h01]
      rw [hc2, if_neg (by decide)] at h1
      rw [runs_return] at h1
      simp (config := { decide := true }) only [evalF_local, hy, payload_words4, if_true] at h1
      subst h1
      simp only at hrest
      subst hrest
      refine Or.inr (hret ?_)
      have hz' : w1 ||| (w2 ||| (w3 ||| (0 : Word))) = 0#64 := hW.symm.trans hz
      rw [BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff] at hz'
      obtain ⟨e1, e2, e3, -⟩ := hz'
      subst h01 e1 e2 e3
      rfl
    · have hc2 : evalPanCmp .equal w0 1#64 = 0#64 := by simp [evalPanCmp, h01]
      rw [hc2, if_pos (show (0#64 : Word) = 0 from rfl), runs_skip] at h1
      exact skip h1
  · have hc : evalPanCmp .equal W 0#64 = 0#64 := by
      simp [evalPanCmp, hz]
    rw [hc, if_pos (show (0#64 : Word) = 0 from rfl), runs_skip] at h1
    exact skip h1

/-- Loop invariant of a halving loop of `modinv_bin`. -/
def HalveI (x y : VarName) (A M : Nat) (s : St σ) (a : St σ) : Prop :=
  a.globals = s.globals ∧ a.memory = s.memory ∧ a.ffi = s.ffi ∧
    (∀ z, z ≠ x → z ≠ y → a.locals z = s.locals z) ∧
    ∃ U X, FourVal x U a.locals ∧ FourVal y X a.locals ∧ X < M ∧ U % M = X * A % M

set_option maxHeartbeats 8000000 in
/-- `while (x.0 & 1) == 0 { x = x >> 1; y = mod_half(y, m); }; rest`. -/
theorem halve_wp (hE : GuestEnv E) {x y : VarName} (hxy : x ≠ y) (hxm : x ≠ "m")
    (hym : y ≠ "m") {rest : Prog Word} {s : St σ} {U X A M : Nat}
    (hx : FourVal x U s.locals) (hy : FourVal y X s.locals) (hm : FourVal "m" M s.locals)
    (hM : M % 2 = 1) (hXM : X < M) (hinv : U % M = X * A % M)
    (hcont : ∀ a, HalveI x y A M s a → WPs E a rest Q) :
    WPs E s (.seq (.while (evenGuard x) (halveBody4 x y)) rest) Q := by
  refine WPs.seq (HalveI x y A M s) (WPs.loopG (I := HalveI x y A M s)
    ⟨rfl, rfl, rfl, fun _ _ _ => rfl, U, X, hx, hy, hXM, hinv⟩ ?_
    (fun a _ hI _ => ⟨_, _, _, _, rfl, hI⟩)) hcont
  rintro ⟨la, ga, ma, fa⟩ ⟨hg, hmm, hf, hfr, U', X', hxa, hya, hXa, hia⟩ hct
  simp only at hg hmm hf hfr hxa hya
  subst hg hmm hf
  have hma : FourVal "m" M la := fourVal_frame hm (hfr "m" (Ne.symm hxm) (Ne.symm hym))
  obtain ⟨w0, w1, w2, w3, hlx, hUv⟩ := id hxa
  obtain ⟨v0, v1, v2, v3, hly, hXv⟩ := id hya
  obtain ⟨m0, m1, m2, m3, hlm, hMv⟩ := id hma
  -- the guard says `x` is even
  have hUe : U' % 2 = 0 := by
    obtain ⟨w, c, hcond, hw⟩ := hct
    have hev := cond_of_eval hcond
    have := evenGuard_eval4 hE hlx hev
    have hw0 : w ≠ 0 := by simpa using hw
    have hpar := limbs_parity4 w0 w1 w2 w3
    rw [hUv] at hpar
    have : ¬ w0.toNat % 2 = 1 := fun h1 => hw0 (this.mpr h1)
    omega
  intro r hr
  unfold halveBody4 at hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  rcases shrAssign_runs hE hxa h1 with herr | ⟨l1, rfl, hfour, hframe⟩
  · cases r1 with
    | error l g m f =>
      simp only at hrest
      subst hrest
      exact Or.inl trivial
    | _ => cases herr
  simp only at hrest
  have hly1 : l1 y = some (.rStruct [.word v0, .word v1, .word v2, .word v3]) := by
    rw [hframe y (Ne.symm hxy)]
    exact hly
  have hlm1 : l1 "m" = some (.rStruct [.word m0, .word m1, .word m2, .word m3]) := by
    rw [hframe "m" (Ne.symm hxm)]
    exact hlm
  rcases runs_call_inv (some (some (.local, y))) hrest with herr | ⟨ps, cb, vals, cl, rb, hl,
    hvals, hbind, hcal, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 158 hE.functions (by guest_decl_at 158) (by decide +kernel)
    hl).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, hly1, hlm1, Option.map_some,
    Option.some.injEq] at hvals
  subst hvals
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases mod_half_spec hE ps cb hl ⟨cl, s.globals, s.memory, s.ffi⟩ rb v0 v1 v2 v3 m0 m1 m2 m3
    (by rw [← hbind]; simp [updatePanValueMap]) (by rw [← hbind]; simp [updatePanValueMap]) hcal
    with hst | ⟨lr, d0, d1, d2, d3, rfl, hd⟩
  · cases rb with
    | raised lr g m f ex v =>
      simp only [CallOutcome] at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only [CallOutcome] at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f =>
      simp only [CallOutcome] at hout
      exact Or.inl (Stopped.of_error hout)
    | _ => exact absurd hst (fun h => h)
  simp only [CallOutcome] at hout
  rcases hout with herr | ⟨l', g', hassign, rfl⟩
  · exact Or.inl (Stopped.of_error herr)
  simp only [assignPanValueCallResult] at hassign
  split at hassign
  · simp only [Option.some.injEq, Prod.mk.injEq] at hassign
    obtain ⟨rfl, rfl⟩ := hassign
    rw [hXv, hMv] at hd
    refine Or.inr ⟨rfl, rfl, rfl, ?_, U' / 2, _, hfour.update_other (by simpa using hxy),
      ⟨d0, d1, d2, d3, by simp [updatePanValueMap], hd⟩, ?_, half_inv hM hUe hia⟩
    · intro z hzx hzy
      have : (z == y) = false := by simpa using hzy
      simp only [updatePanValueMap, this]
      rw [hframe z hzx]
      exact hfr z hzx hzy
    · split <;> omega
  · cases hassign

set_option maxHeartbeats 8000000 in
/-- `a = u256_sub(a, b); xa = mod_sub(xa, xb, m);` -/
theorem subSeq_spec (hE : GuestEnv E) {a b xa xb : VarName} (h1 : a ≠ xa) (h2 : a ≠ xb)
    (h3 : a ≠ "m") {s : St σ} {r : Result σ} {Av Bv XA XB M : Nat}
    (ha : FourVal a Av s.locals) (hb : FourVal b Bv s.locals) (hxa : FourVal xa XA s.locals)
    (hxb : FourVal xb XB s.locals) (hm : FourVal "m" M s.locals) (hle : Bv ≤ Av)
    (hXA : XA < M) (hXB : XB < M) (h : Runs E s (subSeq a b xa xb) r) :
    Stopped r ∨ ∃ l, r = .normal l s.globals s.memory s.ffi ∧ FourVal a (Av - Bv) l ∧
      FourVal xa (if XA < XB then XA + M - XB else XA - XB) l ∧
      ∀ z, z ≠ a → z ≠ xa → l z = s.locals z := by
  obtain ⟨a0, a1, a2, a3, hla, hA⟩ := ha
  obtain ⟨b0, b1, b2, b3, hlb, hB⟩ := hb
  obtain ⟨p0, p1, p2, p3, hlxa, hXAv⟩ := hxa
  obtain ⟨q0, q1, q2, q3, hlxb, hXBv⟩ := hxb
  obtain ⟨m0, m1, m2, m3, hlm, hMv⟩ := hm
  unfold subSeq at h
  obtain ⟨r1, hr1, hrest⟩ := runs_seq.mp h
  have herror : r1.isError = true → Stopped r := by
    intro herr
    cases r1 with
    | error l g m f =>
      simp only at hrest
      subst hrest
      trivial
    | _ => cases herr
  rcases runs_call_inv (some (some (.local, a))) hr1 with herr | ⟨ps, cb, vals, cl, rb, hl, hvals,
    hbind, hcal, hout⟩
  · exact Or.inl (herror herr)
  have hparams := (fun_of_index 57 hE.functions (by guest_decl_at 57) (by decide +kernel) hl).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, hla, hlb, Option.map_some,
    Option.some.injEq] at hvals
  subst hvals
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  obtain ⟨lr, d0, d1, d2, d3, rfl, hd⟩ := u256_sub_spec hE ps cb hl
    ⟨cl, s.globals, s.memory, s.ffi⟩ rb a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp [updatePanValueMap]) (by rw [← hbind]; simp [updatePanValueMap])
    (by rw [hA, hB]; exact hle) hcal
  simp only [CallOutcome] at hout
  rcases hout with herr | ⟨l', g', hassign, rfl⟩
  · exact Or.inl (herror herr)
  simp only [assignPanValueCallResult] at hassign
  split at hassign
  · simp only [Option.some.injEq, Prod.mk.injEq] at hassign
    obtain ⟨rfl, rfl⟩ := hassign
    simp only at hrest
    have e1 : (xa == a) = false := by simpa using (Ne.symm h1)
    have e2 : (xb == a) = false := by simpa using (Ne.symm h2)
    have e3 : (("m" : String) == a) = false := by simpa using (Ne.symm h3)
    rcases runs_call_inv (some (some (.local, xa))) hrest with herr | ⟨ps2, cb2, vals2, cl2, rb2,
      hl2, hvals2, hbind2, hcal2, hout2⟩
    · exact Or.inl (Stopped.of_error herr)
    have hparams2 := (fun_of_index 159 hE.functions (by guest_decl_at 159) (by decide +kernel)
      hl2).2
    simp only [evalArgs_cons, evalArgs_nil, evalF_local, update_lookup, e1, e2, e3, hlxa, hlxb,
      hlm, Option.map_some, Option.some.injEq, Bool.false_eq_true, if_false] at hvals2
    subst hvals2
    rw [hparams2] at hbind2
    simp [bindPanValueParameters] at hbind2
    rcases mod_sub_spec hE ps2 cb2 hl2 ⟨cl2, s.globals, s.memory, s.ffi⟩ rb2 p0 p1 p2 p3
      q0 q1 q2 q3 m0 m1 m2 m3 (by rw [← hbind2]; simp [updatePanValueMap])
      (by rw [← hbind2]; simp [updatePanValueMap]) (by rw [← hbind2]; simp [updatePanValueMap])
      (by rw [hXAv, hMv]; exact hXA) (by rw [hXBv, hMv]; exact hXB) hcal2
      with hst | ⟨lr2, f0, f1, f2, f3, rfl, hf⟩
    · cases rb2 with
      | raised lr g m f ex v =>
        simp only [CallOutcome] at hout2
        subst hout2
        exact Or.inl trivial
      | finalFfi lr g m f ev =>
        simp only [CallOutcome] at hout2
        subst hout2
        exact Or.inl trivial
      | error lr g m f =>
        simp only [CallOutcome] at hout2
        exact Or.inl (Stopped.of_error hout2)
      | _ => exact absurd hst (fun h => h)
    simp only [CallOutcome] at hout2
    rcases hout2 with herr | ⟨l2, g2, hassign2, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    simp only [assignPanValueCallResult] at hassign2
    split at hassign2
    · simp only [Option.some.injEq, Prod.mk.injEq] at hassign2
      obtain ⟨rfl, rfl⟩ := hassign2
      have e4 : (a == xa) = false := by simpa using h1
      rw [hXAv, hXBv, hMv] at hf
      refine Or.inr ⟨_, rfl, ⟨d0, d1, d2, d3, by simp [updatePanValueMap, e4], by rw [hd, hA, hB]⟩,
        ⟨f0, f1, f2, f3, by simp [updatePanValueMap], hf⟩, ?_⟩
      intro z hza hzxa
      have z1 : (z == a) = false := by simpa using hza
      have z2 : (z == xa) = false := by simpa using hzxa
      simp [updatePanValueMap, z1, z2]
    · cases hassign2
  · cases hassign

/-- The outer invariant of `modinv_bin`. -/
def InvI (A M : Nat) (l : VarName → Option (PanValue Word)) : Prop :=
  FourVal "m" M l ∧ ∃ U V X1 X2, FourVal "u" U l ∧ FourVal "v" V l ∧ FourVal "x1" X1 l ∧
    FourVal "x2" X2 l ∧ X1 < M ∧ X2 < M ∧ U % M = X1 * A % M ∧ V % M = X2 * A % M

theorem fourVal_restore {n : VarName} {k : Nat} {l : VarName → Option (PanValue Word)}
    {old : Option (PanValue Word)} (hn : (n == "ult") = false) (h : FourVal n k l) :
    FourVal n k (restorePanValueLocal l "ult" old) := by
  refine fourVal_frame h ?_
  simp only [restorePanValueLocal, hn, Bool.false_eq_true, if_false]

set_option maxHeartbeats 8000000 in
/-- Compare `u` and `v` and subtract the smaller from the larger. -/
theorem cmpTail_spec (hE : GuestEnv E) {s : St σ} {r : Result σ} {A M : Nat}
    (hI : InvI A M s.locals) (h : Runs E s cmpTail4 r) :
    Stopped r ∨ ∃ l, r = .normal l s.globals s.memory s.ffi ∧ InvI A M l := by
  obtain ⟨hm, U, V, X1, X2, hu, hv, hx1, hx2, hX1, hX2, hiu, hiv⟩ := hI
  obtain ⟨u0, u1, u2, u3, hlu, hUv⟩ := id hu
  obtain ⟨v0, v1, v2, v3, hlv, hVv⟩ := id hv
  unfold cmpTail4 at h
  rcases runs_decCall_inv h with herr | ⟨parameters, body, values, calleeLocals, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 46 hE.functions (by guest_decl_at 46) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, hlu, hlv, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hspec := u256_lt_spec hE parameters body hlookup
    ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb u0 u1 u2 u3 v0 v1 v2 v3
    (by rw [← hbind]; simp [updatePanValueMap]) (by rw [← hbind]; simp [updatePanValueMap])
    hcallee
  subst hspec
  obtain ⟨r', -, hrun', rfl⟩ := hout
  rw [hUv, hVv] at hrun'
  have up : ∀ (n : VarName) (k : Nat) (c : Word), (n == "ult") = false → FourVal n k s.locals →
      FourVal n k (updatePanValueMap s.locals "ult" (PanValue.word c)) :=
    fun n k c hn hf => hf.update_other hn
  rw [runs_ite] at hrun'
  simp only [evalF_cmp hE.word, evalF_local, eval_const, update_lookup, beq_self_eq_true,
    if_true] at hrun'
  by_cases hlt : U < V
  · simp only [hlt, if_true, evalPanCmp] at hrun'
    rcases subSeq_spec hE (a := "v") (b := "u") (xa := "x2") (xb := "x1") (by decide) (by decide)
      (by decide)
      (s := ⟨updatePanValueMap s.locals "ult" (PanValue.word 1#64), s.globals, s.memory, s.ffi⟩)
      (up _ _ _ (by decide) hv) (up _ _ _ (by decide) hu) (up _ _ _ (by decide) hx2)
      (up _ _ _ (by decide) hx1) (up _ _ _ (by decide) hm) (Nat.le_of_lt hlt) hX2 hX1 hrun'
      with hst | ⟨l, rfl, hfv, hfx, hframe⟩
    · exact Or.inl (Stopped.restore hst)
    · refine Or.inr ⟨_, rfl, fourVal_restore (by decide) (fourVal_frame (up _ _ 1#64 (by decide) hm)
          (hframe "m" (by decide) (by decide))), U, V - U, X1, _,
        fourVal_restore (by decide) (fourVal_frame (up _ _ 1#64 (by decide) hu)
          (hframe "u" (by decide) (by decide))),
        fourVal_restore (by decide) hfv,
        fourVal_restore (by decide) (fourVal_frame (up _ _ 1#64 (by decide) hx1)
          (hframe "x1" (by decide) (by decide))),
        fourVal_restore (by decide) hfx, hX1, by split <;> omega, hiu,
        sub_inv hX1 (Nat.le_of_lt hlt) hiv hiu⟩
  · simp only [hlt, if_false, evalPanCmp] at hrun'
    rcases subSeq_spec hE (a := "u") (b := "v") (xa := "x1") (xb := "x2") (by decide) (by decide)
      (by decide)
      (s := ⟨updatePanValueMap s.locals "ult" (PanValue.word 0#64), s.globals, s.memory, s.ffi⟩)
      (up _ _ _ (by decide) hu) (up _ _ _ (by decide) hv) (up _ _ _ (by decide) hx1)
      (up _ _ _ (by decide) hx2) (up _ _ _ (by decide) hm) (Nat.le_of_not_lt hlt) hX1 hX2 hrun'
      with hst | ⟨l, rfl, hfu, hfx, hframe⟩
    · exact Or.inl (Stopped.restore hst)
    · refine Or.inr ⟨_, rfl, fourVal_restore (by decide) (fourVal_frame (up _ _ 0#64 (by decide) hm)
          (hframe "m" (by decide) (by decide))), U - V, V, _, X2,
        fourVal_restore (by decide) hfu,
        fourVal_restore (by decide) (fourVal_frame (up _ _ 0#64 (by decide) hv)
          (hframe "v" (by decide) (by decide))),
        fourVal_restore (by decide) hfx,
        fourVal_restore (by decide) (fourVal_frame (up _ _ 0#64 (by decide) hx2)
          (hframe "x2" (by decide) (by decide))), by split <;> omega, hX2,
        sub_inv hX2 (Nat.le_of_not_lt hlt) hiu hiv, hiv⟩

end InitECandidate.Solver.GuestBound
