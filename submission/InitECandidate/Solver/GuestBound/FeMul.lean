import InitECandidate.Solver.GuestBound.FeOps

/-!
# `fe_mul` and `fe_sqr` on `Fq12` keep coefficients below `p`

The field-size dispatchers, for field size 12. Part of the canonicity chain
for `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem fq12mul_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {A B D pv : Word}
    (h : CalleeRet E s "fq12_mul" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word D)) (h2 : E.eval s e2 = some (.word A))
    (h3 : E.eval s e3 = some (.word B)) (hp : s.globals "heap_ptr" = some (.word pv))
    (hpH : InHeap pv) (bA : A.toNat + 384 ≤ pv.toNat) (bB : B.toNat + 384 ≤ pv.toNat)
    (bD : D.toNat + 384 ≤ pv.toNat) (alD : D.toNat % 8 = 0)
    (cA : CanonN s.memory A 12) (cB : CanonN s.memory B 12) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, x.toNat < pv.toNat → (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) →
        m x = s.memory x) ∧ CanonN m D 12 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 659 hE.functions (by guest_decl_at 659) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq12_mul_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A B D pv
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hp hpH bA bB bD
    alD cA cB hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

theorem fq12sqr_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {A D pv : Word}
    (h : CalleeRet E s "fq12_sqr" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word D)) (h2 : E.eval s e2 = some (.word A))
    (hp : s.globals "heap_ptr" = some (.word pv))
    (hpH : InHeap pv) (bA : A.toNat + 384 ≤ pv.toNat)
    (bD : D.toNat + 384 ≤ pv.toNat) (alD : D.toNat % 8 = 0) (cA : CanonN s.memory A 12) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, x.toNat < pv.toNat → (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) →
        m x = s.memory x) ∧ CanonN m D 12 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 660 hE.functions (by guest_decl_at 660) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq12_sqr_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A D pv
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hp hpH bA bD
    alD cA hrun with hst | ⟨l', m', heq, hfr, hc⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc⟩

end rets

/-- What a canonical-preserving `Fq12` operation with destination `D` returns. -/
def Fe12Ret (s : St σ) (D pv : Word) (r : Result σ) : Prop :=
  ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    (∀ x : Word, x.toNat < pv.toNat → (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) →
      m' x = s.memory x) ∧ CanonN m' D 12

set_option maxHeartbeats 4000000 in
theorem fe_mul12_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_mul" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A B D pv : Word)
    (hfld : s.locals "fld" = some (.word 12#64))
    (ha : s.locals "a" = some (.word A)) (hb : s.locals "b" = some (.word B))
    (hd : s.locals "d" = some (.word D)) (hp : s.globals "heap_ptr" = some (.word pv))
    (hpH : InHeap pv) (bA : A.toNat + 384 ≤ pv.toNat) (bB : B.toNat + 384 ≤ pv.toNat)
    (bD : D.toNat + 384 ≤ pv.toNat) (alD : D.toNat % 8 = 0)
    (cA : CanonN s.memory A 12) (cB : CanonN s.memory B 12) (h : Runs E s body r) :
    Stopped r ∨ Fe12Ret s D pv r := by
  have hbody := (fun_of_index 661 hE.functions (by guest_decl_at 661) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (Fe12Ret s D pv)) r h
  have e1 : evalPanCmp .equal (12#64 : Word) 1#64 = 0#64 := by decide
  have e2 : evalPanCmp .equal (12#64 : Word) 2#64 = 0#64 := by decide
  refine WPs.guard0 (fun x hx => by
    rw [eval_cmp_inv hE (of_eval (w := 12#64) (by lk [hfld])) (of_eval (eval_const _ _)) x hx, e1]) ?_
  refine WPs.guard0 (fun x hx => by
    rw [eval_cmp_inv hE (of_eval (w := 12#64) (by lk [hfld])) (of_eval (eval_const _ _)) x hx, e2]) ?_
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hfr, hc⟩ := fq12mul_ret hE hret (A := A) (B := B) (D := D) (pv := pv)
    (by lk [hd]) (by lk [ha]) (by lk [hb]) hp hpH bA bB bD alD cA cB
  subst g ffi
  exact WPs.ret (of_eval (eval_const _ _)) ⟨_, m1, rfl, hfr, hc⟩

set_option maxHeartbeats 4000000 in
theorem fe_sqr12_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fe_sqr" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A D pv : Word)
    (hfld : s.locals "fld" = some (.word 12#64))
    (ha : s.locals "a" = some (.word A))
    (hd : s.locals "d" = some (.word D)) (hp : s.globals "heap_ptr" = some (.word pv))
    (hpH : InHeap pv) (bA : A.toNat + 384 ≤ pv.toNat)
    (bD : D.toNat + 384 ≤ pv.toNat) (alD : D.toNat % 8 = 0)
    (cA : CanonN s.memory A 12) (h : Runs E s body r) :
    Stopped r ∨ Fe12Ret s D pv r := by
  have hbody := (fun_of_index 662 hE.functions (by guest_decl_at 662) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (Fe12Ret s D pv)) r h
  have e1 : evalPanCmp .equal (12#64 : Word) 12#64 = 1#64 := by decide
  refine WPs.seqG (fun _ => False) (WPs.ite (w := 1#64) (fun x hx => by
    rw [eval_cmp_inv hE (of_eval (w := 12#64) (by lk [hfld])) (of_eval (eval_const _ _)) x hx, e1]) ?_)
    (fun _ hf => hf.elim)
  rw [if_neg (by decide)]
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hfr, hc⟩ := fq12sqr_ret hE hret (A := A) (D := D) (pv := pv)
    (by lk [hd]) (by lk [ha]) hp hpH bA bD alD cA
  subst g ffi
  exact WPs.ret (of_eval (eval_const _ _)) ⟨_, m1, rfl, hfr, hc⟩

end InitECandidate.Solver.GuestBound
