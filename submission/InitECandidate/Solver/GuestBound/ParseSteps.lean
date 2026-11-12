import InitECandidate.Solver.GuestBound.EcpMulK

/-!
# Pieces for the point parsers

Read-only helpers, `fq_to_mont`, and stores of canonical field elements as
steps over `BufsK` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word} {K : Nat}

theorem u256_from_be_quiet :
    keepFn quietLeaf Guest.Software.guestAst 2 "u256_from_be" = true := by
  decide +kernel

theorem u256_eq_quiet : keepFn quietLeaf Guest.Software.guestAst 2 "u256_eq" = true := by
  decide +kernel

theorem struct4_of_shape {structs : StructContext} {v : PanValue Word}
    (h : panShapeMatches (panValueShape structs v) (.comb [.one, .one, .one, .one]) = true) :
    ∃ w0 w1 w2 w3 : Word, v = .rStruct [.word w0, .word w1, .word w2, .word w3] := by
  cases v with
  | word w => simp [panValueShape, panShapeMatches] at h
  | nStruct name fields => simp [panValueShape, panShapeMatches] at h
  | rStruct fields =>
    rcases fields with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, rest⟩⟩⟩⟩⟩
    case cons.cons.cons.cons.nil =>
      simp only [panValueShape, panShapeMatches, List.map,
        panShapeMatches.panShapeListMatches, Bool.and_eq_true] at h
      obtain ⟨ha, hb, hc, hd, -⟩ := h
      obtain ⟨w0, rfl⟩ := word_of_shape_one ha
      obtain ⟨w1, rfl⟩ := word_of_shape_one hb
      obtain ⟨w2, rfl⟩ := word_of_shape_one hc
      obtain ⟨w3, rfl⟩ := word_of_shape_one hd
      exact ⟨w0, w1, w2, w3, rfl⟩
    all_goals
      exfalso
      revert h
      simp [panValueShape, panShapeMatches, panShapeMatches.panShapeListMatches]

/-- A declaring call of a four-word value. -/
theorem WPs.decCall_struct4 {x : VarName} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word}
    (h : ∀ w0 w1 w2 w3 g m ffi,
      CalleeRet E s f args [.rStruct [.word w0, .word w1, .word w2, .word w3]] g m ffi →
      WPs E ⟨updatePanValueMap s.locals x (.rStruct [.word w0, .word w1, .word w2, .word w3]),
        g, m, ffi⟩ body (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x (.comb [.one, .one, .one, .one]) f args body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  cases rb with
  | returned lr g m ffi vs =>
    cases vs with
    | nil => exact hout.elim
    | cons v rest =>
      cases rest with
      | cons v' rest' => exact hout.elim
      | nil =>
        obtain ⟨r', hshape, hrun', rfl⟩ := hout
        obtain ⟨w0, w1, w2, w3, rfl⟩ := struct4_of_shape hshape
        rcases h w0 w1 w2 w3 g m ffi ⟨parameters, cbody, values, cl, lr, hlookup, hvalues,
          hbind, hcallee⟩ r' hrun' with hs | hq
        · exact Or.inl hs.restore
        · exact Or.inr hq
  | raised lr g m ffi ex v =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m ffi ev =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | _ => exact hout.elim

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem u256lt_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : CalleeRet E s "u256_lt" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (h2 : E.eval s e2 = some (.rStruct [.word b0, .word b1, .word b2, .word b3])) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧
      vs = [.word (if limbsVal [a0, a1, a2, a3] < limbsVal [b0, b1, b2, b3] then 1 else 0)] := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 46 hE.functions (by guest_decl_at 46) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have := u256_lt_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hrun
  cases this
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem fqmul_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : CalleeRet E s "fq_mul" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (h2 : E.eval s e2 = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) (hB : limbsVal [b0, b1, b2, b3] < bnP) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ d0 d1 d2 d3 : Word,
      vs = [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] < bnP := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 652 hE.functions (by guest_decl_at 652) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq_mul_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hA hB hrun with
    hst | ⟨l', d0, d1, d2, d3, heq, hd, -⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, d0, d1, d2, d3, rfl, hd⟩

end rets

theorem r2_lt : limbsVal [(17522657719365597833#64 : Word), 13107472804851548667#64,
    5164255478447964150#64, 493319470278259999#64] < bnP := by decide

/-- `fq_to_mont` returns a canonical value on a canonical argument. -/
theorem fq_to_mont_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq_to_mont" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 : Word)
    (hx : s.locals "x" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) (h : Runs E s body r) :
    Stopped r ∨ CanonRet s r := by
  have hbody := (fun_of_index 653 hE.functions (by guest_decl_at 653) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (CanonRet s)) r h
  refine WPs.tail_ret (fun vs g m ffi hret l => ?_)
  obtain ⟨hg, hm, hf, d0, d1, d2, d3, hv, hd⟩ := fqmul_ret hE hret (a0 := a0) (a1 := a1)
    (a2 := a2) (a3 := a3) (b0 := 17522657719365597833#64) (b1 := 13107472804851548667#64)
    (b2 := 5164255478447964150#64) (b3 := 493319470278259999#64) (by lk [hx])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) hA r2_lt
  subst g m ffi vs
  exact ⟨l, d0, d1, d2, d3, rfl, hd⟩

theorem fqtomont_ret (hE : GuestEnv E) {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} {e1 : Exp Word} {a0 a1 a2 a3 : Word}
    (h : CalleeRet E s "fq_to_mont" [e1] vs g m ffi)
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ d0 d1 d2 d3 : Word,
      vs = [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] < bnP := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 653 hE.functions (by guest_decl_at 653) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq_to_mont_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    a0 a1 a2 a3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hA hrun with
    hst | ⟨l', d0, d1, d2, d3, heq, hd⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, d0, d1, d2, d3, rfl, hd⟩

/-- `st a, v; rest` writing a canonical field element into a one-coefficient buffer. -/
theorem WPs.store_stepK1 (hE : GuestEnv E) {a v : Exp Word} {rest : Prog Word}
    {D hp pv0 w0 w1 w2 w3 : Word} {All Cn : List Word}
    (ha : E.eval s a = some (.word D))
    (hv : E.eval s v = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (hlt : limbsVal [w0, w1, w2, w3] < bnP)
    (hB : BufsK 1 pv0 m0 Wr hp All Cn s.memory) (hD : D ∈ All)
    (hDl : pv0.toNat ≤ D.toNat ∨ D ∈ Wr)
    (h : ∀ m', BufsK 1 pv0 m0 Wr hp All (D :: Cn) m' →
      WPs E ⟨s.locals, s.globals, m', s.ffi⟩ rest Q) :
    WPs E s (.seq (.store a v) rest) Q := by
  have gD := hB.geo D hD
  have hpb := hB.hpb
  refine WPs.seq_store4 hE (addr := coefAddr D 0) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3)
    (of_eval (by rw [coefAddr_zero]; exact ha)) hv ?_
  refine h _ (hB.write hD hDl (fun x _ hx => ?_)
    (CanonN.snoc (k := 0) (by omega) (CanonN.nil _ _) hlt))
  exact set4_outN (n := 1) (by omega) (by omega) hx

end InitECandidate.Solver.GuestBound
