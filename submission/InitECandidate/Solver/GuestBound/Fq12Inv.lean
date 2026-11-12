import InitECandidate.Solver.GuestBound.Fq12InvOuter

/-!
# `fq12_inv`: step bound

On canonical input coefficients, with the input below the heap pointer, every
non-error run of `fq12_inv` takes at most `10^86` steps.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' : Word → Option (PanValue Word)}

theorem ZeroRel.other {B x : Word} (hz : ZeroRel m m' B 416) (hx : ¬ InB B x) : m' x = m x := by
  rw [hz x, if_neg (by unfold InB at hx; omega)]

theorem CanonAt.of_zero {B : Word} (hB : BufOk B) (hz : ZeroRel m m' B 416) : CanonAt m' B :=
  CanonAt.of_poly (PolyAt.of_zero (n := 13) hB.1 (by have := hB.2; omega) hz)
    (fun _ _ => by decide)

theorem set4_out {B x w0 w1 w2 w3 : Word} {k : Nat} (hB : BufOk B) (hk : k < 13)
    (hx : ¬ InB B x) : set4 m (coefAddr B k) w0 w1 w2 w3 x = m x := by
  have h2 := hB.2
  have hck := coefAddr_toNat (a := B) (i := k) (by omega)
  refine set4_other (by rw [hck]; omega) ?_
  rw [hck]
  unfold InB at hx
  omega

theorem CanonAt.set {B w0 w1 w2 w3 : Word} {k : Nat} (hB : BufOk B) (hk : k < 13)
    (hc : CanonAt m B) (hv : limbsVal [w0, w1, w2, w3] < bnP) :
    CanonAt (set4 m (coefAddr B k) w0 w1 w2 w3) B := by
  obtain ⟨c, hp, hl⟩ := hc.poly
  have h2 := hB.2
  have hck := coefAddr_toNat (a := B) (i := k) (by omega)
  have h64 : (coefAddr B k).toNat + 32 ≤ 2 ^ 64 := by rw [hck]; omega
  intro i
  by_cases hi : i = k
  · subst hi
    exact ⟨_, fun _ => ⟨fe_set4 h64, hv⟩⟩
  · refine ⟨c i, fun hi13 => ⟨fe_congr (by rw [coefAddr_toNat (by omega)]; omega)
      (fun x h1 h2 => set4_other h64 ?_) (hp i hi13), hl i hi13⟩⟩
    rw [coefAddr_toNat (by omega)] at h1 h2
    rw [hck]
    omega

theorem coefAddr_zero (B : Word) : coefAddr B 0 = B := by
  unfold coefAddr
  simp

theorem coefAddr_six (B : Word) : B + 192#64 = coefAddr B 6 := rfl

theorem coefAddr_twelve (B : Word) : B + 384#64 = coefAddr B 12 := rfl

/-- A store of four words. -/
theorem WPs.store4 (hE : GuestEnv E) {a val : Exp Word} {addr : Word}
    {w0 w1 w2 w3 : Word} (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : E.eval s val = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (h : Q (.normal s.locals s.globals (set4 s.memory addr w0 w1 w2 w3) s.ffi)) :
    WPs E s (.store a val) Q := by
  rintro r ⟨fuel, n, hrun⟩
  rcases store_four_inv hE hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · exact Or.inl (Stopped.of_error herr)
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  rw [hv] at hy
  have hy' := (Option.some.inj hy).symm
  rw [hm w0 w1 w2 w3 hy']
  exact Or.inr h

/-- `memzero(x, 416)` on a buffer. -/
theorem zero_step (hE : GuestEnv E) {x : VarName} {B : Word}
    (hx : s.locals x = some (.word B)) (hB : BufOk B)
    (h : ∀ m', ZeroRel s.memory m' B 416 → Q (.normal s.locals s.globals m' s.ffi)) :
    WPs E s (.call (some (none, none)) "memzero"
      [.var .local x, .const (BitVec.ofNat 64 416)]) Q := by
  refine WPs.call_ret (fun vs g m4 ffi hret => ?_)
  have h416 : (416#64 : Word).toNat = 416 := by decide
  obtain ⟨hg, hf, hz⟩ := memzero_ret hE hret (dst := B) (nW := 416#64) (by lk [hx])
    (eval_const _ _) hB.1 (by decide) (by rw [h416]; have := hB.2; omega)
  subst g ffi
  rw [h416] at hz
  exact h m4 hz

theorem c82_lt : limbsVal [(5544790254283102953#64 : Word), 13698472384431417117#64,
    4628036095437277618#64, 2762764518496934255#64] < bnP := by decide

theorem cm18_lt : limbsVal [(10102850021236865696#64 : Word), 15026249742141879542#64,
    2169086236411634456#64, 2710440286313254821#64] < bnP := by decide

theorem cone_lt : limbsVal [(15230403791020821917#64 : Word), 754611498739239741#64,
    7381016538464732716#64, 1011752739694698287#64] < bnP := by decide

theorem fqi_suffix_cost (hE : GuestEnv E) :
    Costs E FQI_SUFFIX
      1000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  have h : ∃ B, Costs E FQI_SUFFIX B ∧ B ≤
      1000000000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

/-- `var x = alloc(416); body` in budget form. -/
theorem alloc_step_c (hE : GuestEnv E) {x : VarName} {body : Prog Word} {pv : Word} {N : Nat}
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hle : panValueExpsStepCost [(Exp.const (BitVec.ofNat 64 416) : Exp Word)] + 84 + 1 ≤ N)
    (h : ∀ qv : Word, pv.toNat + 416 ≤ qv.toNat → InHeap qv →
      WPc E ⟨updatePanValueMap s.locals x (.word pv),
        updatePanValueMap s.globals "heap_ptr" (.word qv), s.memory, s.ffi⟩ body
        (N - (panValueExpsStepCost [(Exp.const (BitVec.ofNat 64 416) : Exp Word)] + 84 + 1))
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPc E s (.decCall x .one "alloc" [.const (BitVec.ofNat 64 416)] body) N Q := by
  refine WPc.decCall_sub (Fn.«alloc» hE) hle (fun v g m ffi hret => ?_)
  obtain ⟨hv, hm, hf, qv, hg, h1, h2⟩ := alloc_ret hE hret.ret (eval_const _ _) hp hpH
  simp only [List.cons.injEq, and_true] at hv
  subst v m ffi g
  exact h qv (by rwa [show (416#64 : Word).toNat = 416 by decide] at h1) h2

set_option maxHeartbeats 16000000 in
/-- The body of `fq12_inv` after the six allocations. -/
theorem fqi_after_alloc (hE : GuestEnv E) {st : St σ} {R0 R1 S0 S1 T Qb A pv : Word}
    {cA : Nat → Nat}
    (e0 : st.locals "r0" = some (.word R0)) (e1 : st.locals "r1" = some (.word R1))
    (e2 : st.locals "s0" = some (.word S0)) (e3 : st.locals "s1" = some (.word S1))
    (e4 : st.locals "q" = some (.word Qb)) (e5 : st.locals "tmp" = some (.word T))
    (ea : st.locals "a" = some (.word A)) (geo : Geo R0 R1 S0 S1 T Qb)
    (l0 : pv.toNat ≤ R0.toNat) (l1 : pv.toNat ≤ R1.toNat) (l2 : pv.toNat ≤ S0.toNat)
    (l3 : pv.toNat ≤ S1.toNat) (halA : A.toNat % 8 = 0) (hAp : A.toNat + 384 ≤ pv.toNat)
    (hpA : PolyAt st.memory A cA 12) (hcA : ∀ i, i < 12 → cA i < bnP) :
    WPc E st FQI_REST 20000000000000000000000000000000000000000000000000000000000000000000000000000000000000
      (fun _ => True) := by
  have g0 := geo.o0
  have g1 := geo.o1
  have gS0 := geo.oS0
  have gS1 := geo.oS1
  have x01 := geo.r01
  have x0s0 := geo.r0s0
  have x0s1 := geo.r0s1
  have x1s0 := geo.r1s0
  have x1s1 := geo.r1s1
  have xs01 := geo.s01
  unfold Sep at x01 x0s0 x0s1 x1s0 x1s1 xs01
  have b0 := g0.2
  have b1 := g1.2
  have bS0 := gS0.2
  have bS1 := gS1.2
  have a0 := g0.1
  have a1 := g1.1
  have h384 : (384#64 : Word).toNat = 384 := by decide
  -- memzero(r0, 416)
  refine WPc.seq_sub (fun st1 => ∃ m1, st1 = ⟨st.locals, st.globals, m1, st.ffi⟩ ∧
      (∀ x : Word, x.toNat < pv.toNat → m1 x = st.memory x) ∧ CanonAt m1 R0)
    (WPc.of_costs (Costs.callDest none _ (Fn.«memzero» hE)) (zero_step hE e0 g0 (fun m' hz =>
      ⟨m', rfl, fun x hx => hz.other (by unfold InB; omega), CanonAt.of_zero g0 hz⟩)))
    (by budget) ?_
  rintro _ ⟨m1, rfl, lo1, k0⟩
  -- st r0, FQ_82
  refine WPc.seq_sub (fun st1 => ∃ m1, st1 = ⟨st.locals, st.globals, m1, st.ffi⟩ ∧
      (∀ x : Word, x.toNat < pv.toNat → m1 x = st.memory x) ∧ CanonAt m1 R0)
    (WPc.of_costs (Costs.store _ _) (WPs.store4 hE (addr := coefAddr R0 0)
      (w0 := 5544790254283102953#64) (w1 := 13698472384431417117#64)
      (w2 := 4628036095437277618#64) (w3 := 2762764518496934255#64)
      (of_eval (by rw [coefAddr_zero]; lk [e0]))
      (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
      ⟨_, rfl, fun x hx => (set4_out g0 (by omega) (by unfold InB; omega)).trans (lo1 x hx),
        k0.set g0 (by omega) c82_lt⟩)) (by budget) ?_
  rintro _ ⟨m2, rfl, lo2, k0⟩
  -- st r0 + 192, FQ_M18
  refine WPc.seq_sub (fun st1 => ∃ m1, st1 = ⟨st.locals, st.globals, m1, st.ffi⟩ ∧
      (∀ x : Word, x.toNat < pv.toNat → m1 x = st.memory x) ∧ CanonAt m1 R0)
    (WPc.of_costs (Costs.store _ _) (WPs.store4 hE (addr := coefAddr R0 6)
      (w0 := 10102850021236865696#64) (w1 := 15026249742141879542#64)
      (w2 := 2169086236411634456#64) (w3 := 2710440286313254821#64)
      (of_eval (by rw [← coefAddr_six]; ev [e0]))
      (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
      ⟨_, rfl, fun x hx => (set4_out g0 (by omega) (by unfold InB; omega)).trans (lo2 x hx),
        k0.set g0 (by omega) cm18_lt⟩)) (by budget) ?_
  rintro _ ⟨m3, rfl, lo3, k0⟩
  -- st r0 + 384, FQ_ONE
  refine WPc.seq_sub (fun st1 => ∃ m1, st1 = ⟨st.locals, st.globals, m1, st.ffi⟩ ∧
      (∀ x : Word, x.toNat < pv.toNat → m1 x = st.memory x) ∧ CanonAt m1 R0)
    (WPc.of_costs (Costs.store _ _) (WPs.store4 hE (addr := coefAddr R0 12)
      (w0 := 15230403791020821917#64) (w1 := 754611498739239741#64)
      (w2 := 7381016538464732716#64) (w3 := 1011752739694698287#64)
      (of_eval (by rw [← coefAddr_twelve]; ev [e0]))
      (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
      ⟨_, rfl, fun x hx => (set4_out g0 (by omega) (by unfold InB; omega)).trans (lo3 x hx),
        k0.set g0 (by omega) cone_lt⟩)) (by budget) ?_
  rintro _ ⟨m4, rfl, lo4, k0⟩
  -- memzero(r1, 416)
  refine WPc.seq_sub (fun st1 => ∃ m1, st1 = ⟨st.locals, st.globals, m1, st.ffi⟩ ∧
      (∀ x : Word, x.toNat < pv.toNat → m1 x = st.memory x) ∧ CanonAt m1 R0 ∧
      PolyAt m1 R1 (fun _ => 0) 13)
    (WPc.of_costs (Costs.callDest none _ (Fn.«memzero» hE)) (zero_step hE e1 g1 (fun m' hz =>
      ⟨m', rfl, fun x hx => (hz.other (by unfold InB; omega)).trans (lo4 x hx),
        k0.frame (by omega) (fun x hx => hz.other (by unfold InB at hx ⊢; omega)),
        PolyAt.of_zero (n := 13) a1 (by omega) hz⟩))) (by budget) ?_
  rintro _ ⟨m5, rfl, lo5, k0, z1⟩
  -- memcpy(r1, a, 384)
  refine WPc.seq_sub (fun st1 => ∃ m1, st1 = ⟨st.locals, st.globals, m1, st.ffi⟩ ∧
      (∀ x : Word, x.toNat < pv.toNat → m1 x = st.memory x) ∧ CanonAt m1 R0 ∧ CanonAt m1 R1)
    (WPc.of_costs (Costs.callDest none _ (Fn.«memcpy» hE)) (WPs.call_ret
      (fun vs g m6 ffi hret => ?_))) (by budget) ?_
  · obtain ⟨hg, hf, hcopy⟩ := memcpy_ret hE hret (dst := R1) (src := A) (nW := 384#64)
      (by lk [e1]) (by lk [ea]) (eval_const _ _)
      ⟨by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega⟩
    subst g ffi
    rw [h384] at hcopy
    have hpA5 : PolyAt m5 A cA 12 :=
      hpA.frame (by omega) (fun x h1 h2 => lo5 x (by omega))
    have hp12 : PolyAt m6 R1 cA 12 :=
      PolyAt.of_copy (n := 12) hcopy a1 halA (by omega) (by omega) hpA5
    refine ⟨m6, rfl, fun x hx => (hcopy.cells x (by omega)).trans (lo5 x hx),
      k0.frame (by omega) (fun x hx => hcopy.cells x (by unfold InB at hx; omega)), ?_⟩
    intro i
    by_cases hi : i < 12
    · exact ⟨cA i, fun _ => ⟨hp12 i hi, hcA i hi⟩⟩
    · refine ⟨0, fun hi13 => ⟨?_, by decide⟩⟩
      have : i = 12 := by omega
      subst this
      have hc12 := coefAddr_toNat (a := R1) (i := 12) (by omega)
      exact fe_congr (by rw [hc12]; omega)
        (fun x h1 h2 => hcopy.cells x (by rw [hc12] at h1; omega)) (z1 12 (by omega))
  rintro _ ⟨m6, rfl, lo6, k0, k1⟩
  -- memzero(s0, 416)
  refine WPc.seq_sub (fun st1 => ∃ m1, st1 = ⟨st.locals, st.globals, m1, st.ffi⟩ ∧
      CanonAt m1 R0 ∧ CanonAt m1 R1 ∧ CanonAt m1 S0)
    (WPc.of_costs (Costs.callDest none _ (Fn.«memzero» hE)) (zero_step hE e2 gS0 (fun m' hz =>
      ⟨m', rfl, k0.frame (by omega) (fun x hx => hz.other (by unfold InB at hx ⊢; omega)),
        k1.frame (by omega) (fun x hx => hz.other (by unfold InB at hx ⊢; omega)),
        CanonAt.of_zero gS0 hz⟩))) (by budget) ?_
  rintro _ ⟨m7, rfl, k0, k1, k2⟩
  -- memzero(s1, 416)
  refine WPc.seq_sub (fun st1 => ∃ m1, st1 = ⟨st.locals, st.globals, m1, st.ffi⟩ ∧
      CanonAt m1 R0 ∧ CanonAt m1 R1 ∧ CanonAt m1 S0 ∧ CanonAt m1 S1)
    (WPc.of_costs (Costs.callDest none _ (Fn.«memzero» hE)) (zero_step hE e3 gS1 (fun m' hz =>
      ⟨m', rfl, k0.frame (by omega) (fun x hx => hz.other (by unfold InB at hx ⊢; omega)),
        k1.frame (by omega) (fun x hx => hz.other (by unfold InB at hx ⊢; omega)),
        k2.frame (by omega) (fun x hx => hz.other (by unfold InB at hx ⊢; omega)),
        CanonAt.of_zero gS1 hz⟩))) (by budget) ?_
  rintro _ ⟨m8, rfl, k0, k1, k2, k3⟩
  -- st s1, FQ_ONE
  refine WPc.seq_sub (fun st1 => ∃ m1, st1 = ⟨st.locals, st.globals, m1, st.ffi⟩ ∧
      CanonAt m1 R0 ∧ CanonAt m1 R1 ∧ CanonAt m1 S0 ∧ CanonAt m1 S1)
    (WPc.of_costs (Costs.store _ _) (WPs.store4 hE (addr := coefAddr S1 0)
      (w0 := 15230403791020821917#64) (w1 := 754611498739239741#64)
      (w2 := 7381016538464732716#64) (w3 := 1011752739694698287#64)
      (of_eval (by rw [coefAddr_zero]; lk [e3]))
      (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil])
      ⟨_, rfl,
        k0.frame (by omega) (fun x hx => set4_out gS1 (by omega) (by unfold InB at hx ⊢; omega)),
        k1.frame (by omega) (fun x hx => set4_out gS1 (by omega) (by unfold InB at hx ⊢; omega)),
        k2.frame (by omega) (fun x hx => set4_out gS1 (by omega) (by unfold InB at hx ⊢; omega)),
        k3.set gS1 (by omega) cone_lt⟩)) (by budget) ?_
  rintro _ ⟨m9, rfl, k0, k1, k2, k3⟩
  -- the loop, then the rest
  refine WPc.seq_sub (fun _ => True)
    ((fqi_outer_loop hE (s := ⟨st.locals, st.globals, m9, st.ffi⟩) (Qb := Qb)
      ⟨rfl, rfl, R0, R1, S0, S1, T, e0, e1, e2, e3, e4, e5, geo, k0, k1, k2, k3⟩).mono
      (Nat.le_refl _) (by intro r _; cases r <;> trivial)) (by budget) ?_
  intro st' _
  exact WPc.of_costs_le (fqi_suffix_cost hE) (by budget) (WPs.of_true (fun _ => trivial))

set_option maxHeartbeats 16000000 in
/-- Step bound of `fq12_inv(d, a)`: the 12 coefficients at `a` are below `p`
and lie below the heap pointer. -/
theorem fq12_inv_cost (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq12_inv" E.functions = some (parameters, body))
    (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (A pv : Word) (cA : Nat → Nat)
    (ha : s.locals "a" = some (.word A)) (hp : s.globals "heap_ptr" = some (.word pv))
    (hpH : InHeap pv) (halA : A.toNat % 8 = 0) (hAp : A.toNat + 384 ≤ pv.toNat)
    (hpA : PolyAt s.memory A cA 12) (hcA : ∀ i, i < 12 → cA i < bnP)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ 100000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  have hbody := (fun_of_index 682 hE.functions (by guest_decl_at 682) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  refine WPc.steps (Q := fun _ => True) ?_ hrun hne
  refine WPc.decCall_sub (Fn.«heap_mark» hE) (by budget) (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, hv⟩ := heap_mark_ret hE hret.ret hp
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  refine alloc_step_c hE hp hpH (by budget) (fun p1 h1 i1 => ?_)
  refine alloc_step_c hE (by lk []) i1 (by budget) (fun p2 h2 i2 => ?_)
  refine alloc_step_c hE (by lk []) i2 (by budget) (fun p3 h3 i3 => ?_)
  refine alloc_step_c hE (by lk []) i3 (by budget) (fun p4 h4 i4 => ?_)
  refine alloc_step_c hE (by lk []) i4 (by budget) (fun p5 h5 i5 => ?_)
  refine alloc_step_c hE (by lk []) i5 (by budget) (fun p6 h6 i6 => ?_)
  unfold InHeap at hpH i1 i2 i3 i4 i5 i6
  have ok : ∀ {B : Word}, B.toNat % 8 = 0 → B.toNat + 416 ≤ 2952790016 → BufOk B :=
    fun h1 h2 => ⟨h1, by omega⟩
  have sp : ∀ {B C : Word}, B.toNat + 416 ≤ C.toNat → Sep B C := fun h => Or.inl h
  refine WPc.mono (fqi_after_alloc hE (R0 := pv) (R1 := p1) (S0 := p2) (S1 := p3) (Qb := p4) (T := p5)
    (A := A) (pv := pv) (cA := cA) (by lk []) (by lk []) (by lk []) (by lk []) (by lk [])
    (by lk []) (by lk [ha])
    ⟨ok hpH.2 (by omega), ok i1.2 (by omega), ok i2.2 (by omega), ok i3.2 (by omega),
      ok i5.2 (by omega), ok i4.2 (by omega), sp (by omega), sp (by omega), sp (by omega),
      sp (by omega), sp (by omega), sp (by omega), sp (by omega), sp (by omega), sp (by omega),
      sp (by omega), sp (by omega), sp (by omega), sp (by omega), sp (by omega),
      (sp (by omega) : Sep p4 p5).symm⟩
    (Nat.le_refl _) (by omega) (by omega) (by omega) halA hAp hpA hcA) (by budget)
    (fun _ _ => trivial)

end InitECandidate.Solver.GuestBound
