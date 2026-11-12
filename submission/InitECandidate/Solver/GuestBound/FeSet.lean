import InitECandidate.Solver.GuestBound.EcpDouble

/-!
# `fe_set_zero`, `fe_set_one`, `ecp_set_inf` on `Fq12`, and the read-only tests

Constants are canonical; `fe_is_zero` and `fe_eq` change nothing. Part of the
canonicity chain for `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word}

theorem fe_is_zero_quiet : keepFn quietLeaf Guest.Software.guestAst 2 "fe_is_zero" = true := by
  decide +kernel

theorem fe_eq_quiet : keepFn quietLeaf Guest.Software.guestAst 2 "fe_eq" = true := by
  decide +kernel

/-- A zeroed 384-byte block holds 12 canonical (zero) coefficients. -/
theorem CanonN.of_zero12 {D : Word} (al : D.toNat % 8 = 0) (b : D.toNat + 384 ≤ 2 ^ 63)
    (hz : ZeroRel m m' D 384) : CanonN m' D 12 :=
  CanonN.of_poly (PolyAt.of_zero (n := 12) al (by omega) hz) (fun _ _ => by decide)

/-- What the two constant setters return. -/
def SetRet (s : St σ) (D : Word) (r : Result σ) : Prop :=
  ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) → m' x = s.memory x) ∧
    CanonN m' D 12

set_option maxHeartbeats 4000000 in
theorem fe_set_zero12_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_set_zero" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (D : Word) (hfld : s.locals "fld" = some (.word 12#64))
    (hd : s.locals "d" = some (.word D)) (al : D.toNat % 8 = 0) (b : D.toNat + 384 ≤ 2 ^ 62)
    (h : Runs E s body r) : Stopped r ∨ SetRet s D r := by
  have hbody := (fun_of_index 669 hE.functions (by guest_decl_at 669) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (SetRet s D)) r h
  have hn : (12#64 * 32#64 : Word).toNat = 384 := by decide
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hz⟩ := memzero_ret hE hret (dst := D) (nW := 12#64 * 32#64) (by lk [hd])
    (by ev [evalPanOp, hfld]) al (by rw [hn]) (by rw [hn]; omega)
  subst g ffi
  rw [hn] at hz
  exact WPs.ret (of_eval (eval_const _ _)) ⟨_, m1, rfl,
    fun x hx => by rw [hz x, if_neg (by omega)], CanonN.of_zero12 al (by omega) hz⟩

set_option maxHeartbeats 4000000 in
theorem fe_set_one12_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_set_one" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (D : Word) (hfld : s.locals "fld" = some (.word 12#64))
    (hd : s.locals "d" = some (.word D)) (al : D.toNat % 8 = 0) (b : D.toNat + 384 ≤ 2 ^ 62)
    (h : Runs E s body r) : Stopped r ∨ SetRet s D r := by
  have hbody := (fun_of_index 670 hE.functions (by guest_decl_at 670) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (SetRet s D)) r h
  have hn : (12#64 * 32#64 : Word).toNat = 384 := by decide
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hz⟩ := memzero_ret hE hret (dst := D) (nW := 12#64 * 32#64) (by lk [hd])
    (by ev [evalPanOp, hfld]) al (by rw [hn]) (by rw [hn]; omega)
  subst g ffi
  rw [hn] at hz
  have hc1 : CanonN m1 D 12 := CanonN.of_zero12 al (by omega) hz
  refine WPs.seq_store4 hE (addr := coefAddr D 0)
    (w0 := 15230403791020821917#64) (w1 := 754611498739239741#64)
    (w2 := 7381016538464732716#64) (w3 := 1011752739694698287#64)
    (of_eval (by rw [coefAddr_zero]; lk [hd]))
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) ?_
  refine WPs.ret (of_eval (eval_const _ _)) ⟨_, _, rfl, fun x hx => ?_,
    hc1.set4 (n := 12) (by omega) (by omega) cone_lt⟩
  show set4 m1 (coefAddr D 0) _ _ _ _ x = s.memory x
  rw [set4_outN (n := 12) (by omega) (by omega) (by omega), hz x, if_neg (by omega)]

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem fesetzero_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {D : Word}
    (h : CalleeRet E s "fe_set_zero" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word 12#64)) (h2 : E.eval s e2 = some (.word D))
    (al : D.toNat % 8 = 0) (b : D.toNat + 384 ≤ 2 ^ 62) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D 12 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 669 hE.functions (by guest_decl_at 669) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_set_zero12_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ D
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) al b hrun with
    hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

theorem fesetone_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {D : Word}
    (h : CalleeRet E s "fe_set_one" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word 12#64)) (h2 : E.eval s e2 = some (.word D))
    (al : D.toNat % 8 = 0) (b : D.toNat + 384 ≤ 2 ^ 62) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m D 12 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 670 hE.functions (by guest_decl_at 670) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fe_set_one12_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ D
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) al b hrun with
    hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

end rets

theorem WPs.fe_set_zero_step (hE : GuestEnv E) {eF eD : Exp Word} {rest : Prog Word}
    {D hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s eF = some (.word 12#64)) (h2 : E.eval s eD = some (.word D))
    (hB : Bufs pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr)
    (h : ∀ m', Bufs pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_set_zero" [eF, eD]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := fesetzero_ret hE hret h1 h2 gD.1 (by omega)
  subst g ffi
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

theorem WPs.fe_set_one_step (hE : GuestEnv E) {eF eD : Exp Word} {rest : Prog Word}
    {D hp pv0 : Word} {All Cn : List Word}
    (h1 : E.eval s eF = some (.word 12#64)) (h2 : E.eval s eD = some (.word D))
    (hB : Bufs pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr)
    (h : ∀ m', Bufs pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.call (some (none, none)) "fe_set_one" [eF, eD]) rest) Q := by
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  have gD := hB.geo D hD
  have hpb := hB.hpb
  obtain ⟨hg, hf, hfr, hc⟩ := fesetone_ret hE hret h1 h2 gD.1 (by omega)
  subst g ffi
  exact h m1 (hB.write hD hDl (fun x _ hx => hfr x hx) hc)

set_option maxHeartbeats 4000000 in
theorem ecp_set_inf12_bufs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "ecp_set_inf" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (O hp pv0 : Word) (m0 : Word → Option (PanValue Word))
    (Wr All Cn : List Word)
    (hfld : s.locals "fld" = some (.word 12#64)) (hpt : s.locals "pt" = some (.word O))
    (hB : Bufs pv0 m0 Wr hp All Cn s.memory)
    (hO0 : O ∈ All) (hO1 : O + 384#64 ∈ All) (hO2 : O + 768#64 ∈ All)
    (w0 : pv0.toNat ≤ O.toNat ∨ O ∈ Wr)
    (w1 : pv0.toNat ≤ (O + 384#64).toNat ∨ O + 384#64 ∈ Wr)
    (w2 : pv0.toNat ≤ (O + 768#64).toNat ∨ O + 768#64 ∈ Wr) (h : Runs E s body r) :
    Stopped r ∨ BufsRet s pv0 m0 Wr hp All ((O + 768#64) :: (O + 384#64) :: O :: Cn) r := by
  have hbody := (fun_of_index 671 hE.functions (by guest_decl_at 671) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (BufsRet s pv0 m0 Wr hp All
    ((O + 768#64) :: (O + 384#64) :: O :: Cn))) r h
  refine WPs.dec (w := 384#64) (of_eval (by ev [evalPanOp, hfld])) ?_
  refine WPs.fe_set_one_step hE (D := O) (by lk [hfld]) (by lk [hpt]) hB hO0 w0
    (fun m hB => ?_)
  refine WPs.fe_set_one_step hE (D := O + 384#64) (by lk [hfld]) (by ev [hpt]) hB hO1 w1
    (fun m hB => ?_)
  refine WPs.fe_set_zero_step hE (D := O + 768#64) (by lk [hfld]) (by ev [evalPanOp, hpt]) hB
    hO2 w2 (fun m hB => ?_)
  exact WPs.ret (of_eval (eval_const _ _)) ⟨_, m, rfl, hB⟩

end InitECandidate.Solver.GuestBound
