import InitECandidate.Solver.GuestBound.Poly

/-!
# Step rules for field elements in memory

Four-word loads and stores, and calls to `fq_mul` and `fq_sub`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `var x = lds {1,1,1,1} e; body` from a cell holding `n`. -/
theorem WPs.dec_load4 (hE : GuestEnv E) {x : VarName} {e : Exp Word} {body : Prog Word}
    {addr : Word} {n : Nat} (he : ∀ y, E.eval s e = some y → y = .word addr)
    (hfe : Fe s.memory addr n)
    (h : ∀ w0 w1 w2 w3 : Word, limbsVal [w0, w1, w2, w3] = n →
      WPs E ⟨updatePanValueMap s.locals x (.rStruct [.word w0, .word w1, .word w2, .word w3]),
        s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.dec x (.comb [.one, .one, .one, .one]) (.load (.comb [.one, .one, .one, .one]) e)
      body) Q := by
  refine WPs.dec_ev (fun v hv => ?_)
  obtain ⟨addr', w0, w1, w2, w3, ha, rfl, c0, c1, c2, c3⟩ := eval_load_four hE hv
  have e1 := he _ ha
  simp only [PanValue.word.injEq] at e1
  subst e1
  obtain ⟨v0, v1, v2, v3, d0, d1, d2, d3, hn⟩ := hfe
  have e0 : w0 = v0 := by rw [c0] at d0; simpa using d0
  have e1 : w1 = v1 := by rw [c1] at d1; simpa using d1
  have e2 : w2 = v2 := by rw [c2] at d2; simpa using d2
  have e3 : w3 = v3 := by rw [c3] at d3; simpa using d3
  subst e0 e1 e2 e3
  exact h _ _ _ _ hn

/-- `st a, v; rest` for a four-word value. -/
theorem WPs.seq_store4 (hE : GuestEnv E) {a val : Exp Word} {rest : Prog Word} {addr : Word}
    {w0 w1 w2 w3 : Word} (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : E.eval s val = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (h : WPs E ⟨s.locals, s.globals,
      setCell (setCell (setCell (setCell s.memory addr w0) (addr + 8#64) w1)
        (addr + 8#64 + 8#64) w2) (addr + 8#64 + 8#64 + 8#64) w3, s.ffi⟩ rest Q) :
    WPs E s (.seq (.store a val) rest) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  obtain ⟨fuel, n, hrun⟩ := h1
  rcases store_four_inv hE hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · cases r1 with
    | error l g m f => simp only at hrest; subst hrest; exact Or.inl trivial
    | _ => cases herr
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  rw [hv] at hy
  have hy' := (Option.some.inj hy).symm
  rw [hm w0 w1 w2 w3 hy'] at hrest
  exact h r hrest

/-- `var x = lds {1,1,1,1} e; body`, whatever the cell holds. -/
theorem WPs.dec_load4_any (hE : GuestEnv E) {x : VarName} {e : Exp Word} {body : Prog Word}
    (h : ∀ w0 w1 w2 w3 : Word,
      WPs E ⟨updatePanValueMap s.locals x (.rStruct [.word w0, .word w1, .word w2, .word w3]),
        s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.dec x (.comb [.one, .one, .one, .one]) (.load (.comb [.one, .one, .one, .one]) e)
      body) Q := by
  refine WPs.dec_ev (fun v hv => ?_)
  obtain ⟨addr', w0, w1, w2, w3, -, rfl, -⟩ := eval_load_four hE hv
  exact h _ _ _ _

/-- `var x = fq_mul(e1, e2); body` with a canonical first operand. -/
theorem WPs.decCall_fqmul1 (hE : GuestEnv E) {x : VarName} {body : Prog Word} {e1 e2 : Exp Word}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (h2 : E.eval s e2 = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP)
    (h : ∀ d0 d1 d2 d3 : Word, limbsVal [d0, d1, d2, d3] < bnP →
      limbsVal [d0, d1, d2, d3] * 2 ^ 256 % bnP =
        limbsVal [a0, a1, a2, a3] * limbsVal [b0, b1, b2, b3] % bnP →
      WPs E ⟨updatePanValueMap s.locals x (.rStruct [.word d0, .word d1, .word d2, .word d3]),
        s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x (.comb [.one, .one, .one, .one]) "fq_mul" [e1, e2] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 652 hE.functions (by guest_decl_at 652) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := fq_mul_spec1 hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb
    a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hA hcallee
  rcases hpost with hst | ⟨l, d0, d1, d2, d3, rfl, hlt, hd⟩
  · cases rb with
    | raised lr g m f ex v =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f => exact hout.elim
    | _ => exact absurd hst (fun h => h)
  · obtain ⟨r', -, hrun', rfl⟩ := hout
    rcases h d0 d1 d2 d3 hlt hd r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

/-- `var x = fq_mul(e1, e2); body` on canonical operands. -/
theorem WPs.decCall_fqmul (hE : GuestEnv E) {x : VarName} {body : Prog Word} {e1 e2 : Exp Word}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (h2 : E.eval s e2 = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) (_hB : limbsVal [b0, b1, b2, b3] < bnP)
    (h : ∀ d0 d1 d2 d3 : Word, limbsVal [d0, d1, d2, d3] < bnP →
      limbsVal [d0, d1, d2, d3] * 2 ^ 256 % bnP =
        limbsVal [a0, a1, a2, a3] * limbsVal [b0, b1, b2, b3] % bnP →
      WPs E ⟨updatePanValueMap s.locals x (.rStruct [.word d0, .word d1, .word d2, .word d3]),
        s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x (.comb [.one, .one, .one, .one]) "fq_mul" [e1, e2] body) Q :=
  WPs.decCall_fqmul1 hE h1 h2 hA h

/-- `x = fq_sub(e1, e2);` on canonical operands. -/
theorem WPs.call_fqsub (hE : GuestEnv E) {x : VarName} {e1 e2 : Exp Word}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (h2 : E.eval s e2 = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) (hB : limbsVal [b0, b1, b2, b3] < bnP)
    (h : ∀ d0 d1 d2 d3 : Word,
      limbsVal [d0, d1, d2, d3] =
        (limbsVal [a0, a1, a2, a3] + bnP - limbsVal [b0, b1, b2, b3]) % bnP →
      Q (.normal (updatePanValueMap s.locals x (.rStruct [.word d0, .word d1, .word d2, .word d3]))
        s.globals s.memory s.ffi)) :
    WPs E s (.call (some (some (.local, x), none)) "fq_sub" [e1, e2]) Q := by
  intro r hr
  rcases runs_call_inv (some (some (.local, x))) hr with herr | ⟨parameters, cbody, values, cl,
    rb, hlookup, hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 650 hE.functions (by guest_decl_at 650) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := fq_sub_spec hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb
    a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hA hB hcallee
  rcases hpost with hst | ⟨l, d0, d1, d2, d3, rfl, hd⟩
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
  · simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    simp only [assignPanValueCallResult] at hassign
    split at hassign
    · simp only [Option.some.injEq, Prod.mk.injEq] at hassign
      obtain ⟨rfl, rfl⟩ := hassign
      exact Or.inr (h d0 d1 d2 d3 hd)
    · cases hassign

end InitECandidate.Solver.GuestBound
