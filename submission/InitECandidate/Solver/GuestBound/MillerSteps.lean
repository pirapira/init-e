import InitECandidate.Solver.GuestBound.Twist

/-!
# Step rules used by `bn254_miller_raw`

Allocation of a point, `ecp_linefunc`, `ecp_add`, `fq12_mul`, `fq12_sqr` as
steps over the `Bufs` invariant (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word}

/-- A fresh point (three coordinates) at the old heap pointer joins `All`. -/
theorem Bufs.alloc3 {pv0 hp hp' : Word} {All Cn : List Word} (h : Bufs pv0 m0 Wr hp All Cn m)
    (hle : hp.toNat + 1152 ≤ hp'.toNat) (hb : hp'.toNat ≤ 2952790016)
    (ha' : hp'.toNat % 8 = 0) :
    Bufs pv0 m0 Wr hp' ((hp + 768#64) :: (hp + 384#64) :: hp :: All) Cn m := by
  have hpb := h.hpb
  have hpa := h.hpa
  have e1 : (hp + 384#64).toNat = hp.toNat + 384 := add_lit_toNat (k := 384) (by omega) (by omega)
  have e2 : (hp + 768#64).toNat = hp.toNat + 768 := add_lit_toNat (k := 768) (by omega) (by omega)
  have h1 := h.alloc (hp' := hp + 384#64) (by omega) (by omega) (by omega)
  have h2 := h1.alloc (hp' := hp + 768#64) (by omega) (by omega) (by omega)
  exact h2.alloc (by omega) hb ha'

/-- `var x = alloc(1152); body`: a point joins `All`. -/
theorem WPs.pt_alloc_step (hE : GuestEnv E) {x : VarName} {e : Exp Word} {body : Prog Word}
    {hp pv0 : Word} {All Cn : List Word}
    (he : E.eval s e = some (.word 1152#64)) (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : Bufs pv0 m0 Wr hp All Cn s.memory)
    (h : ∀ hp' : Word, pv0.toNat ≤ hp.toNat → hp.toNat + 1152 ≤ hp'.toNat →
      (hp + 384#64).toNat = hp.toNat + 384 → (hp + 768#64).toNat = hp.toNat + 768 →
      Bufs pv0 m0 Wr hp' ((hp + 768#64) :: (hp + 384#64) :: hp :: All) Cn s.memory →
      WPs E ⟨updatePanValueMap s.locals x (.word hp),
        updatePanValueMap s.globals "heap_ptr" (.word hp'), s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "alloc" [e] body) Q := by
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hv, hm, hf, qv, hg', h1, h2⟩ := alloc_ret hE hret he hg ⟨hB.hpb, hB.hpa⟩
  simp only [List.cons.injEq, and_true] at hv
  subst v m ffi g
  rw [show (1152#64 : Word).toNat = 1152 by decide] at h1
  have hpb := hB.hpb
  exact h qv hB.ple h1 (add_lit_toNat (k := 384) (by omega) (by omega))
    (add_lit_toNat (k := 768) (by omega) (by omega)) (hB.alloc3 h1 h2.1 h2.2)

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem ecplinefunc_ret (hE : GuestEnv E) {e1 e2 e3 e4 e5 e6 : Exp Word}
    {N Dn P1 P2 T hp pv0 : Word} {All Cn : List Word}
    (h : CalleeRet E s "ecp_linefunc" [e1, e2, e3, e4, e5, e6] vs g m ffi)
    (h1 : E.eval s e1 = some (.word 12#64)) (h2 : E.eval s e2 = some (.word N))
    (h3 : E.eval s e3 = some (.word Dn)) (h4 : E.eval s e4 = some (.word P1))
    (h5 : E.eval s e5 = some (.word P2)) (h6 : E.eval s e6 = some (.word T))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : Bufs pv0 m0 Wr hp All Cn s.memory)
    (m1a : P1 ∈ Cn) (m1b : P1 + 384#64 ∈ Cn) (m1c : P1 + 768#64 ∈ Cn)
    (m2a : P2 ∈ Cn) (m2b : P2 + 384#64 ∈ Cn) (m2c : P2 + 768#64 ∈ Cn)
    (mta : T ∈ Cn) (mtb : T + 384#64 ∈ Cn) (mtc : T + 768#64 ∈ Cn)
    (hN : N ∈ All) (hD : Dn ∈ All)
    (wN : pv0.toNat ≤ N.toNat ∨ N ∈ Wr) (wD : pv0.toNat ≤ Dn.toNat ∨ Dn ∈ Wr) :
    g = s.globals ∧ ffi = s.ffi ∧ Bufs pv0 m0 Wr hp All (N :: Dn :: Cn) m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 676 hE.functions (by guest_decl_at 676) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, h5, h6, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases ecp_linefunc12_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    N Dn P1 P2 T hp pv0 m0 Wr All Cn
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hg hB0
    m1a m1b m1c m2a m2b m2c mta mtb mtc hN hD wN wD hrun with hst | ⟨l', m', heq, hB⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hB⟩

theorem ecpadd_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {O P1 P2 hp pv0 : Word}
    {All Cn : List Word}
    (h : CalleeRet E s "ecp_add" [e1, e2, e3, e4] vs g m ffi)
    (h1 : E.eval s e1 = some (.word 12#64)) (h2 : E.eval s e2 = some (.word O))
    (h3 : E.eval s e3 = some (.word P1)) (h4 : E.eval s e4 = some (.word P2))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : Bufs pv0 m0 Wr hp All Cn s.memory)
    (m1a : P1 ∈ Cn) (m1b : P1 + 384#64 ∈ Cn) (m1c : P1 + 768#64 ∈ Cn)
    (m2a : P2 ∈ Cn) (m2b : P2 + 384#64 ∈ Cn) (m2c : P2 + 768#64 ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + 384#64 ∈ All) (hO2 : O + 768#64 ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 384#64).toNat ∨ O + 384#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 768#64).toNat ∨ O + 768#64 ∈ Wr)
    (rel1 : O = P1 ∨ O.toNat + 1152 ≤ P1.toNat ∨ P1.toNat + 1152 ≤ O.toNat)
    (rel2 : O = P2 ∨ O.toNat + 1152 ≤ P2.toNat ∨ P2.toNat + 1152 ≤ O.toNat) :
    g = s.globals ∧ ffi = s.ffi ∧
      Bufs pv0 m0 Wr hp All ((O + 768#64) :: (O + 384#64) :: O :: Cn) m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 674 hE.functions (by guest_decl_at 674) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases ecp_add12_bufs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    O P1 P2 hp pv0 m0 Wr All Cn
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hg hB0
    m1a m1b m1c m2a m2b m2c hO0 hO1 hO2 w0 w1 w2 rel1 rel2 hrun with hst | ⟨l', m', heq, hB⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hB⟩

end rets

theorem WPs.ecp_linefunc_step (hE : GuestEnv E) {e1 e2 e3 e4 e5 e6 : Exp Word}
    {rest : Prog Word} {N Dn P1 P2 T hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s e1 = some (.word 12#64)) (h2 : E.eval s e2 = some (.word N))
    (h3 : E.eval s e3 = some (.word Dn)) (h4 : E.eval s e4 = some (.word P1))
    (h5 : E.eval s e5 = some (.word P2)) (h6 : E.eval s e6 = some (.word T))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : Bufs pv0 m0 Wr hp All Cn s.memory)
    (m1a : P1 ∈ Cn) (m1b : P1 + 384#64 ∈ Cn) (m1c : P1 + 768#64 ∈ Cn)
    (m2a : P2 ∈ Cn) (m2b : P2 + 384#64 ∈ Cn) (m2c : P2 + 768#64 ∈ Cn)
    (mta : T ∈ Cn) (mtb : T + 384#64 ∈ Cn) (mtc : T + 768#64 ∈ Cn)
    (hN : N ∈ All) (hD : Dn ∈ All)
    (wN : pv0.toNat ≤ N.toNat ∨ N ∈ Wr) (wD : pv0.toNat ≤ Dn.toNat ∨ Dn ∈ Wr)
    (h : ∀ m', Bufs pv0 m0 Wr hp All (N :: Dn :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "ecp_linefunc" [e1, e2, e3, e4, e5, e6]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hB⟩ := ecplinefunc_ret hE hret h1 h2 h3 h4 h5 h6 hg hB0 m1a m1b m1c m2a m2b
    m2c mta mtb mtc hN hD wN wD
  subst g ffi
  exact h m1 hB

theorem WPs.ecp_add_step (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {rest : Prog Word}
    {O P1 P2 hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s e1 = some (.word 12#64)) (h2 : E.eval s e2 = some (.word O))
    (h3 : E.eval s e3 = some (.word P1)) (h4 : E.eval s e4 = some (.word P2))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB0 : Bufs pv0 m0 Wr hp All Cn s.memory)
    (m1a : P1 ∈ Cn) (m1b : P1 + 384#64 ∈ Cn) (m1c : P1 + 768#64 ∈ Cn)
    (m2a : P2 ∈ Cn) (m2b : P2 + 384#64 ∈ Cn) (m2c : P2 + 768#64 ∈ Cn)
    (hO0 : O ∈ All) (hO1 : O + 384#64 ∈ All) (hO2 : O + 768#64 ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 384#64).toNat ∨ O + 384#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 768#64).toNat ∨ O + 768#64 ∈ Wr)
    (rel1 : O = P1 ∨ O.toNat + 1152 ≤ P1.toNat ∨ P1.toNat + 1152 ≤ O.toNat)
    (rel2 : O = P2 ∨ O.toNat + 1152 ≤ P2.toNat ∨ P2.toNat + 1152 ≤ O.toNat)
    (h : ∀ m', Bufs pv0 m0 Wr hp All ((O + 768#64) :: (O + 384#64) :: O :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "ecp_add" [e1, e2, e3, e4]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hB⟩ := ecpadd_ret hE hret h1 h2 h3 h4 hg hB0 m1a m1b m1c m2a m2b m2c hO0 hO1
    hO2 w0 w1 w2 rel1 rel2
  subst g ffi
  exact h m1 hB

theorem WPs.fq12_mul_step (hE : GuestEnv E) {eD eA eB : Exp Word} {rest : Prog Word}
    {D A B hp pv0 : Word} {All Cn : List Word}
    (h2 : E.eval s eD = some (.word D)) (h3 : E.eval s eA = some (.word A))
    (h4 : E.eval s eB = some (.word B)) (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : Bufs pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hA : A ∈ Cn) (hBc : B ∈ Cn)
    (h : ∀ m', Bufs pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fq12_mul" [eD, eA, eB]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hfr, hc⟩ := fq12mul_ret hE hret h2 h3 h4 hg ⟨hB.hpb, hB.hpa⟩
    (hB.geo A (hB.sub A hA)).2 (hB.geo B (hB.sub B hBc)).2 (hB.geo D hD).2 (hB.geo D hD).1
    (hB.can A hA) (hB.can B hBc)
  subst g ffi
  exact h m1 (hB.write hD hDl hfr hc)

theorem WPs.fq12_sqr_step (hE : GuestEnv E) {eD eA : Exp Word} {rest : Prog Word}
    {D A hp pv0 : Word} {All Cn : List Word}
    (h2 : E.eval s eD = some (.word D)) (h3 : E.eval s eA = some (.word A))
    (hg : s.globals "heap_ptr" = some (.word hp))
    (hB : Bufs pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr) (hA : A ∈ Cn)
    (h : ∀ m', Bufs pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fq12_sqr" [eD, eA]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg', hf, hfr, hc⟩ := fq12sqr_ret hE hret h2 h3 hg ⟨hB.hpb, hB.hpa⟩
    (hB.geo A (hB.sub A hA)).2 (hB.geo D hD).2 (hB.geo D hD).1 (hB.can A hA)
  subst g ffi
  exact h m1 (hB.write hD hDl hfr hc)

end InitECandidate.Solver.GuestBound
