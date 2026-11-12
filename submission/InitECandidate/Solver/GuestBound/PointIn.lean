import InitECandidate.Solver.GuestBound.Fq12Frob

/-!
# Entering `Fq12`: `bn254_init` when already initialised, and `fq12_cast`

`fq12_cast` turns a parsed G1 point (three canonical field elements) into an
`Fq12` point with canonical coefficients. Part of the canonicity chain for
`fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word}

/-- `bn254_init` does nothing once `bn_gamma` is set. -/
theorem bn254_init_noop (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "bn254_init" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (Gt : Word) (hgm : s.globals "bn_gamma" = some (.word Gt))
    (hne : Gt ≠ 0#64) (h : Runs E s body r) :
    Stopped r ∨ ∃ l, r = .returned l s.globals s.memory s.ffi [.word 0#64] := by
  have hbody := (fun_of_index 648 hE.functions (by guest_decl_at 648) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l, r = .returned l s.globals s.memory s.ffi
    [.word 0#64])) r h
  refine WPs.seqG (fun _ => False) (WPs.ite (w := evalPanCmp .notEqual Gt 0#64)
    (eval_cmp_inv hE (of_eval (w := Gt) (by simp [eval_global, hgm]))
      (of_eval (eval_const _ _))) ?_) (fun _ hf => hf.elim)
  have : evalPanCmp .notEqual Gt 0#64 = 1#64 := by
    simp [evalPanCmp, hne]
  rw [this, if_neg (by decide)]
  exact WPs.ret (of_eval (eval_const _ _)) ⟨_, rfl⟩

/-- A 384-byte block inside a zeroed range holds 12 canonical (zero) coefficients. -/
theorem CanonN.of_zero_sub {O X : Word} {N off : Nat} (hz : ZeroRel m m' O N)
    (alO : O.toNat % 8 = 0) (hX : X.toNat = O.toNat + off) (ho : off % 8 = 0)
    (hon : off + 384 ≤ N) (b : O.toNat + N ≤ 2 ^ 63) : CanonN m' X 12 := by
  intro i
  refine ⟨0, fun hi => ⟨?_, by decide⟩⟩
  have hc := coefAddr_toNat (a := X) (i := i) (by omega)
  have hb : (coefAddr X i).toNat + 32 ≤ 2 ^ 64 := by rw [hc]; omega
  refine ⟨0#64, 0#64, 0#64, 0#64, ?_, ?_, ?_, ?_, by decide⟩
  · rw [hz, if_pos ⟨by rw [hc]; omega, by rw [hc]; omega, by rw [hc]; omega⟩]
  · rw [hz, if_pos ⟨by rw [a8_toNat hb, hc]; omega, by rw [a8_toNat hb, hc]; omega,
      by rw [a8_toNat hb, hc]; omega⟩]
  · rw [hz, if_pos ⟨by rw [a16_toNat hb, hc]; omega, by rw [a16_toNat hb, hc]; omega,
      by rw [a16_toNat hb, hc]; omega⟩]
  · rw [hz, if_pos ⟨by rw [a24_toNat hb, hc]; omega, by rw [a24_toNat hb, hc]; omega,
      by rw [a24_toNat hb, hc]; omega⟩]

/-- `st a, lds U256 b; rest`: a field element copied from `b` to `a`. -/
theorem WPs.seq_store_load4 (hE : GuestEnv E) {a b : Exp Word} {rest : Prog Word}
    {addr baddr : Word} {n : Nat} (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hb : ∀ y, E.eval s b = some y → y = .word baddr) (hfe : Fe s.memory baddr n)
    (h : ∀ w0 w1 w2 w3 : Word, limbsVal [w0, w1, w2, w3] = n →
      WPs E ⟨s.locals, s.globals, set4 s.memory addr w0 w1 w2 w3, s.ffi⟩ rest Q) :
    WPs E s (.seq (.store a (.load (.comb [.one, .one, .one, .one]) b)) rest) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  obtain ⟨fuel, k, hrun⟩ := h1
  rcases store_four_inv hE hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · cases r1 with
    | error l g m f => simp only at hrest; subst hrest; exact Or.inl trivial
    | _ => cases herr
  obtain ⟨ba, w0, w1, w2, w3, hb', rfl, c0, c1, c2, c3⟩ := eval_load_four hE hy
  have e1 := ha _ ha'
  have e2 := hb _ hb'
  simp only [PanValue.word.injEq] at e1 e2
  subst e1
  subst e2
  rw [hm w0 w1 w2 w3 rfl] at hrest
  exact h w0 w1 w2 w3 (Fe.unique ⟨w0, w1, w2, w3, c0, c1, c2, c3, rfl⟩ hfe) r hrest

/-- The three coordinates at `O` are canonical; nothing outside them changed. -/
def PointRet (s : St σ) (O : Word) (r : Result σ) : Prop :=
  ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    (∀ x : Word, (x.toNat < O.toNat ∨ O.toNat + 1152 ≤ x.toNat) → m' x = s.memory x) ∧
    CanonN m' O 12 ∧ CanonN m' (O + 384#64) 12 ∧ CanonN m' (O + 768#64) 12

set_option maxHeartbeats 8000000 in
theorem fq12_cast_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq12_cast" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (O G1 : Word)
    (hout : s.locals "out" = some (.word O)) (hg1 : s.locals "g1" = some (.word G1))
    (alO : O.toNat % 8 = 0) (bO : O.toNat + 1152 ≤ 2 ^ 62) (bG : G1.toNat + 96 ≤ 2 ^ 62)
    (hdis : G1.toNat + 96 ≤ O.toNat ∨ O.toNat + 1152 ≤ G1.toNat)
    (cG : CanonN s.memory G1 3) (h : Runs E s body r) : Stopped r ∨ PointRet s O r := by
  have hbody := (fun_of_index 678 hE.functions (by guest_decl_at 678) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (PointRet s O)) r h
  have hn : (1152#64 : Word).toNat = 1152 := by decide
  have o1 : (O + 384#64).toNat = O.toNat + 384 := add_lit_toNat (k := 384) (by omega) (by omega)
  have o2 : (O + 768#64).toNat = O.toNat + 768 := add_lit_toNat (k := 768) (by omega) (by omega)
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨hg, hf, hz⟩ := memzero_ret hE hret (dst := O) (nW := 1152#64) (by lk [hout])
    (eval_const _ _) alO (by rw [hn]) (by rw [hn]; omega)
  subst g ffi
  rw [hn] at hz
  have hz' : ∀ x : Word, (x.toNat < O.toNat ∨ O.toNat + 1152 ≤ x.toNat) → m1 x = s.memory x :=
    fun x hx => by rw [hz x, if_neg (by omega)]
  have k0 : CanonN m1 O 12 := CanonN.of_zero_sub hz alO (off := 0) rfl (by omega) (by omega)
    (by omega)
  have k1 : CanonN m1 (O + 384#64) 12 :=
    CanonN.of_zero_sub hz alO (off := 384) o1 (by omega) (by omega) (by omega)
  have k2 : CanonN m1 (O + 768#64) 12 :=
    CanonN.of_zero_sub hz alO (off := 768) o2 (by omega) (by omega) (by omega)
  have cG1 : CanonN m1 G1 3 := cG.frame (by omega) (fun x h1 h2 => hz' x (by omega))
  obtain ⟨v0, f0, l0⟩ := cG1.get (i := 0) (by omega)
  obtain ⟨v1, f1, l1⟩ := cG1.get (i := 1) (by omega)
  obtain ⟨v2, f2, l2⟩ := cG1.get (i := 2) (by omega)
  have cg1 := coefAddr_toNat (a := G1) (i := 1) (by omega)
  have cg2 := coefAddr_toNat (a := G1) (i := 2) (by omega)
  -- x
  refine WPs.seq_store_load4 hE (addr := coefAddr O 0) (baddr := coefAddr G1 0)
    (of_eval (by lk [hout, coefAddr_zero])) (of_eval (by lk [hg1, coefAddr_zero])) f0
    (fun a0 a1 a2 a3 ha => ?_)
  try dsimp only
  have hout0 : ∀ x : Word, (x.toNat < O.toNat ∨ O.toNat + 384 ≤ x.toNat) →
      set4 m1 (coefAddr O 0) a0 a1 a2 a3 x = m1 x :=
    fun x hx => set4_outN (n := 12) (by omega) (by omega) hx
  -- y
  refine WPs.seq_store_load4 hE (addr := coefAddr (O + 384#64) 0) (baddr := coefAddr G1 1)
    (of_eval (by ev [hout, coefAddr_zero])) (of_eval (by
      show E.eval _ _ = some (.word (G1 + 32#64))
      ev [hg1]))
    (fe_congr (by rw [cg1]; omega) (fun x h1 h2 => hout0 x (by rw [cg1] at h1 h2; omega)) f1)
    (fun b0 b1 b2 b3 hb => ?_)
  try dsimp only
  have hout1 : ∀ x : Word, (x.toNat < O.toNat + 384 ∨ O.toNat + 768 ≤ x.toNat) →
      set4 (set4 m1 (coefAddr O 0) a0 a1 a2 a3) (coefAddr (O + 384#64) 0) b0 b1 b2 b3 x =
        set4 m1 (coefAddr O 0) a0 a1 a2 a3 x :=
    fun x hx => set4_outN (n := 12) (by rw [o1]; omega) (by omega) (by rw [o1]; omega)
  -- z
  refine WPs.seq_store_load4 hE (addr := coefAddr (O + 768#64) 0) (baddr := coefAddr G1 2)
    (of_eval (by ev [evalPanOp, hout, coefAddr_zero])) (of_eval (by
      show E.eval _ _ = some (.word (G1 + 64#64))
      ev [hg1]))
    (fe_congr (by rw [cg2]; omega) (fun x h1 h2 => by
      rw [cg2] at h1 h2
      exact (hout1 x (by omega)).trans (hout0 x (by omega))) f2)
    (fun c0 c1 c2 c3 hc => ?_)
  try dsimp only
  have hout2 : ∀ x : Word, (x.toNat < O.toNat + 768 ∨ O.toNat + 1152 ≤ x.toNat) →
      set4 (set4 (set4 m1 (coefAddr O 0) a0 a1 a2 a3) (coefAddr (O + 384#64) 0) b0 b1 b2 b3)
        (coefAddr (O + 768#64) 0) c0 c1 c2 c3 x =
      set4 (set4 m1 (coefAddr O 0) a0 a1 a2 a3) (coefAddr (O + 384#64) 0) b0 b1 b2 b3 x :=
    fun x hx => set4_outN (n := 12) (by rw [o2]; omega) (by omega) (by rw [o2]; omega)
  refine WPs.ret (of_eval (eval_const _ _)) ⟨_, _, rfl, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hout2 x (by omega)).trans ((hout1 x (by omega)).trans ((hout0 x (by omega)).trans
      (hz' x hx)))
  · exact ((k0.set4 (n := 12) (k := 0) (by omega) (by omega) (by rw [ha]; exact l0)).frame
      (by omega) (fun x h1 h2 => hout1 x (by omega))).frame (by omega)
      (fun x h1 h2 => hout2 x (by omega))
  · exact ((k1.frame (by rw [o1]; omega) (fun x h1 h2 => hout0 x (by rw [o1] at h1; omega))).set4
      (n := 12) (k := 0) (by rw [o1]; omega) (by omega) (by rw [hb]; exact l1)).frame
      (by rw [o1]; omega) (fun x h1 h2 => hout2 x (by rw [o1] at h2; omega))
  · exact ((k2.frame (by rw [o2]; omega) (fun x h1 h2 => hout0 x (by rw [o2] at h1; omega))).frame
      (by rw [o2]; omega) (fun x h1 h2 => hout1 x (by rw [o2] at h1; omega))).set4
      (n := 12) (k := 0) (by rw [o2]; omega) (by omega) (by rw [hc]; exact l2)

end InitECandidate.Solver.GuestBound
