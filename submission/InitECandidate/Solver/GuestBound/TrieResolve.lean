import InitECandidate.Solver.GuestBound.TrieDecDefs
import InitECandidate.Solver.GuestBound.TrieNew
import InitECandidate.Solver.GuestBound.ResolveStep
import InitECandidate.Solver.GuestBound.WorldJset
import InitECandidate.Solver.GuestBound.TrieDelPush

/-!
# `node_new_hashed` and `_resolve_step` against the world invariant

A hash stub is a registered node of kind 0 at the level where it hangs.
`_resolve_step` returns a finished child (null or a stub) or the RLP of a child
to decode; this is the `resolve` field of the decoder interface `DecIface`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem struct3_of_shape {structs : StructContext} {v : PanValue Word}
    (h : panShapeMatches (panValueShape structs v) (.comb [.one, .one, .one]) = true) :
    ∃ w0 w1 w2 : Word, v = .rStruct [.word w0, .word w1, .word w2] := by
  cases v with
  | word w => simp [panValueShape, panShapeMatches] at h
  | nStruct name fields => simp [panValueShape, panShapeMatches] at h
  | rStruct fields =>
    rcases fields with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
    case cons.cons.cons.nil =>
      simp only [panValueShape, panShapeMatches, List.map,
        panShapeMatches.panShapeListMatches, Bool.and_eq_true] at h
      obtain ⟨ha, hb, hc, -⟩ := h
      obtain ⟨w0, rfl⟩ := word_of_shape_one ha
      obtain ⟨w1, rfl⟩ := word_of_shape_one hb
      obtain ⟨w2, rfl⟩ := word_of_shape_one hc
      exact ⟨w0, w1, w2, rfl⟩
    all_goals
      exfalso
      revert h
      simp [panValueShape, panShapeMatches, panShapeMatches.panShapeListMatches]

/-- Returning four words. -/
theorem WPs.ret_quad {e1 e2 e3 e4 : Exp Word} {a b c d : Word}
    (h1 : ∀ y, E.eval s e1 = some y → y = .word a)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word b)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word c)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word d)
    (h : Q (.returned (fun _ => none) s.globals s.memory s.ffi
      [.rStruct [.word a, .word b, .word c, .word d]])) :
    WPs E s (.return (.rStruct [e1, e2, e3, e4])) Q := by
  refine WPs.ret_ev (fun v hv => ?_)
  rw [evalF_rStruct] at hv
  simp only [evalArgs_cons, evalArgs_nil] at hv
  cases k1 : E.eval s e1 with
  | none => rw [k1] at hv; simp at hv
  | some y1 =>
    cases k2 : E.eval s e2 with
    | none => rw [k1, k2] at hv; simp at hv
    | some y2 =>
      cases k3 : E.eval s e3 with
      | none => rw [k1, k2, k3] at hv; simp at hv
      | some y3 =>
        cases k4 : E.eval s e4 with
        | none => rw [k1, k2, k3, k4] at hv; simp at hv
        | some y4 =>
          have := h1 _ k1
          subst this
          have := h2 _ k2
          subst this
          have := h3 _ k3
          subst this
          have := h4 _ k4
          subst this
          rw [k1, k2, k3, k4] at hv
          simp at hv
          subst hv
          exact h

set_option maxHeartbeats 8000000 in
/-- A hash stub: a registered node of kind 0 at level `ℓ`. -/
theorem node_new_hashed_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "node_new_hashed" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (hashw : Word)
    (hh : s.locals "hash" = some (.word hashw)) (hW : WorldTJ Rg s.globals s.memory)
    (ℓ : Nat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' a, r = .returned l g' m' s.ffi [.word a] ∧
      WorldTJ (Rg.addNd a 0#64 ℓ ℓ) g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 255 hE.functions (by guest_decl_at 255) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' a, r = .returned l g' m' s.ffi [.word a] ∧
    WorldTJ (Rg.addNd a 0#64 ℓ ℓ) g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hDT, hBT, hCT, hNT, hIT⟩ := hW
  have hpE := hpH.1
  have hp8 := hpH.2
  have hJlo := hHW.jrn.lo
  have hJhi := hHW.jrn.hi
  refine WPs.decCall_alloc hE (pv := pv) (nv := 32#64) (eval_const _ _) hp hpH
    (fun qv hq hqH => ?_)
  have hq' : pv.toNat + 32 ≤ qv.toNat := hq
  have hqE := hqH.1
  refine WPs.seq_store hE (addr := pv + 0#64) (w := 0#64) (eval_addc hE 0#64 (by lk []))
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := pv + 8#64) (w := 0#64) (eval_addc hE 8#64 (by lk []))
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := pv + 16#64) (w := 0#64) (eval_addc hE 16#64 (by lk []))
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := pv + 24#64) (w := hashw) (eval_addc hE 24#64 (by lk []))
    (of_eval (by lk [hh])) ?_
  refine WPs.ret (w := pv) (of_eval (by lk [])) ?_
  simp only [restorePanValueFfiLocal]
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have a0 : (pv + 0#64) = pv := by simp
  have a8 : (pv + 8#64).toNat = pv.toNat + 8 := by bv_omega
  have a16 : (pv + 16#64).toNat = pv.toNat + 16 := by bv_omega
  have a24 : (pv + 24#64).toNat = pv.toNat + 24 := by bv_omega
  rw [a0]
  generalize hm' : setCell (setCell (setCell (setCell s.memory pv 0#64) (pv + 8#64) 0#64)
    (pv + 16#64) 0#64) (pv + 24#64) hashw = m'
  have keep : ∀ a : Word, ¬ (pv.toNat ≤ a.toNat ∧ a.toNat < pv.toNat + 32) →
      m' a = s.memory a := by
    intro a ha
    rw [← hm', setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]
  have hkind : Rd m' pv 0#64 := by
    rw [← hm']
    exact (((Rd.here s.memory pv 0#64).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))
  have hpq : pv.toNat ≤ qv.toNat := by omega
  have hbase : HBASE ≤ pv.toNat := by omega
  have hW' : HeapW m' qv T (addN N pv 0#64) J C n :=
    hHW.node_add (fun x _ hlt => keep x (by omega))
      (fun x hx => keep x (by unfold HBASE at hx hbase; omega)) hp8 (Nat.le_refl _)
      (by show pv.toNat + nodeSize 0#64 ≤ qv.toNat; simp [nodeSize]; omega) hqE (by decide)
      hkind (fun hk => absurd hk (by decide))
      (fun hk => absurd hk (by decide))
  refine ⟨_, _, m', pv, rfl, ⟨qv, T, addN N pv 0#64, J, C, n, by simp [updatePanValueMap], hqH,
    by simp (config := { decide := true }) [update_lookup, hJg],
    by simp (config := { decide := true }) [update_lookup, hCg],
    by simp (config := { decide := true }) [update_lookup, hng], hW', hDT,
    fun lo hi hb => (hBT lo hi hb).node_add (Nat.le_refl _) hpq, fun x w hc => ?_,
    fun a ha => ?_, hIT.node_add hHW (fun x _ hlt => keep x (by omega)) (Nat.le_refl _) hpq
      (fun hk => absurd hk (by decide)) (fun hk => absurd hk (by decide))
      (fun hk => absurd hk (by decide))⟩, fun x hx => by simp [update_lookup, hx],
    fun addr ha => keep addr (by unfold HBASE at ha hbase; omega)⟩
  · obtain ⟨hr, h8, hi, hhi, hf⟩ := hCT x w hc
    refine ⟨?_, h8, hi, hhi, hf.node_add (Nat.le_refl _) hpq⟩
    have := hf.hi_
    unfold Rd at hr ⊢
    rw [keep x (by omega)]
    exact hr
  · classical
    unfold InitECandidate.Solver.GuestBound.addN
    rcases ha with ha | rfl
    · obtain ⟨k, hk⟩ := hNT a ha
      by_cases e : a = pv
      · exact ⟨0#64, by simp [e]⟩
      · exact ⟨k, by simp [e, hk]⟩
    · exact ⟨0#64, by simp⟩

/-- What a returning `node_new_hashed` leaves. -/
theorem node_new_hashed_retW (hE : GuestEnv E) {Rg : Reg} {e : Exp Word} {hw : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "node_new_hashed" [e] vs g m ffi) (he : E.eval s e = some (.word hw))
    (hW : WorldTJ Rg s.globals s.memory) (ℓ : Nat) :
    ∃ a, vs = [.word a] ∧ ffi = s.ffi ∧ WorldTJ (Rg.addNd a 0#64 ℓ ℓ) g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 255 hE.functions (by guest_decl_at 255) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, he, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases node_new_hashed_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    hw (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hW ℓ hrun
    with hst | ⟨l', g', m', a, heq, hW', hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, rfl, rfl, hW', hg, hm⟩

/-- What `_resolve_step` guarantees for a child at level `ℓ`. -/
def ResW (R : Reg) (s : St σ) (sp : Word) (ℓ : Nat) (r : Result σ) : Prop :=
  ∃ l g m r0 r1 r2 r3 R', r = .returned l g m s.ffi
      [.rStruct [.word r0, .word r1, .word r2, .word r3]] ∧
    R.Le R' ∧ WorldTJ R' g m ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
    (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ addr.toNat) →
      m addr = s.memory addr) ∧
    (r0 = 0#64 → DRes R' ℓ r1)

theorem ResW.restore {R : Reg} {sp : Word} {ℓ : Nat} {x : VarName}
    {old : Option (PanValue Word)} {r : Result σ} (h : ResW R s sp ℓ r) :
    ResW R s sp ℓ (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g, m, r0, r1, r2, r3, R', rfl, hk⟩ := h
  exact ⟨_, g, m, r0, r1, r2, r3, R', rfl, hk⟩

set_option maxHeartbeats 16000000 in
theorem resolve_step_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_resolve_step" E.functions = some (parameters, body))
    (R : Reg) (s : St σ) (r : Result σ) (sp fv pw nw : Word) (ℓ : Nat)
    (hpw : s.locals "p" = some (.word pw)) (hnw : s.locals "n" = some (.word nw))
    (hp : s.globals "scratch_ptr" = some (.word sp))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ sp.toNat)
    (hF : 2952790016 ≤ fv.toNat) (hW : WorldTJ R s.globals s.memory)
    (h : Runs E s body r) : Stopped r ∨ ResW R s sp ℓ r := by
  have hbody := (fun_of_index 260 hE.functions (by guest_decl_at 260) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (ResW R s sp ℓ)) r h
  refine WPs.dec_ev (fun vit _ => WPs.conseq (Q' := ResW R s sp ℓ) ?_ (fun r h => h.restore))
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := ResW R s sp ℓ) ?_ (fun r h => h.restore)
  try dsimp only
  generalize hL : updatePanValueMap (updatePanValueMap s.locals "it" vit) "e"
    (PanValue.word 0#64) = L
  have L_p : L "p" = some (.word pw) := by rw [← hL]; lk [hpw]
  have L_n : L "n" = some (.word nw) := by rw [← hL]; lk [hnw]
  refine WPs.seq (fun a => ∃ (m : Word → Option (PanValue Word)) (a0 a1 a2 a3 : Word),
      a = ⟨updatePanValueMap L "it" (.rStruct [.word a0, .word a1, .word a2, .word a3]),
        s.globals, m, s.ffi⟩ ∧ ScrMem sp fv s.memory m)
    (WPs.callHA_stop (fun s' r hr => stops_call_noReturn (mpt_fail_noReturn hE) hr)
      (fun v g m ffi hret => ?_)) ?_
  · obtain ⟨hg, hf', hk, a0, a1, a2, a3, hv⟩ := rlpitem_ret hE hret (pw := pw) (by lk [L_p])
      hp hf hfp
    simp only [List.cons.injEq, and_true] at hv
    subst g ffi v
    exact ⟨_, _, _, _, rfl, m, a0, a1, a2, a3, rfl, hk⟩
  rintro _ ⟨m, a0, a1, a2, a3, rfl, hk⟩
  generalize hL1 : updatePanValueMap L "it"
    (PanValue.rStruct [.word a0, .word a1, .word a2, .word a3]) = L1
  have L1_it : L1 "it" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]) := by
    rw [← hL1]; lk []
  have L1_p : L1 "p" = some (.word pw) := by rw [← hL1]; lk [L_p]
  have L1_n : L1 "n" = some (.word nw) := by rw [← hL1]; lk [L_n]
  have hW1 : WorldTJ R s.globals m :=
    hW.scratch (fun _ _ => rfl) (fun a ha => hk a (Or.inl (by omega)))
  have hmf : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ addr.toNat) →
      m addr = s.memory addr := fun addr ha =>
    hk addr (by unfold HBASE at ha; omega)
  have eit : ∀ (i : Nat) (w : Word) (L' : VarName → Option (PanValue Word))
      (g' : VarName → Option (PanValue Word)) (m' : Word → Option (PanValue Word))
      (f' : FfiState σ),
      L' "it" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]) →
      [PanValue.word a0, .word a1, .word a2, .word a3][i]? = some (.word w) →
      E.eval ⟨L', g', m', f'⟩ (.rField i (.var .local "it")) = some (.word w) := by
    intro i w L' g' m' f' h hi
    rw [eval_rField _ i "it" _ h]
    exact hi
  refine WPs.seqG (fun a => a = ⟨L1, s.globals, m, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.seqG (fun a => a = ⟨L1, s.globals, m, s.ffi⟩) (WPs.ite_both (fun w2 _ => ?_))
        ?_
      · split
        · exact WPs.skip rfl
        · exact WPs.ret_quad (of_eval (eval_const _ 0#64)) (of_eval (eval_const _ 0#64))
            (of_eval (eval_const _ 0#64)) (of_eval (eval_const _ 0#64))
            ⟨_, _, _, _, _, _, _, R, rfl, Reg.Le.refl R, hW1, fun _ _ => rfl, hmf,
              fun _ => Or.inl rfl⟩
      intro a ha
      rw [ha]
      clear ha a
      refine WPs.guard_quiet (mpt_fail_quiet hE) ?_
      refine WPs.decCall_retS (fun vr g m' ffi hret hsh =>
        WPs.conseq (Q' := ResW R s sp ℓ) ?_ (fun r h => by
          obtain ⟨l, g, m, r0, r1, r2, r3, R', rfl, hk⟩ := h
          exact ⟨_, g, m, r0, r1, r2, r3, R', rfl, hk⟩))
      obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet (nodedb_lookup_quiet hE) hret
      subst g m' ffi
      obtain ⟨q0, q1, q2, rfl⟩ := struct3_of_shape hsh
      try dsimp only
      have er : ∀ (i : Nat) (w : Word) (L' : VarName → Option (PanValue Word))
          (g' : VarName → Option (PanValue Word)) (m' : Word → Option (PanValue Word))
          (f' : FfiState σ),
          L' "r" = some (.rStruct [.word q0, .word q1, .word q2]) →
          [PanValue.word q0, .word q1, .word q2][i]? = some (.word w) →
          E.eval ⟨L', g', m', f'⟩ (.rField i (.var .local "r")) = some (.word w) := by
        intro i w L' g' m' f' h hi
        rw [eval_rField _ i "r" _ h]
        exact hi
      have qr : updatePanValueMap L1 "r" (PanValue.rStruct [.word q0, .word q1, .word q2]) "r" =
          some (.rStruct [.word q0, .word q1, .word q2]) := by lk []
      have qit : updatePanValueMap L1 "r" (PanValue.rStruct [.word q0, .word q1, .word q2]) "it" =
          some (.rStruct [.word a0, .word a1, .word a2, .word a3]) := by lk [L1_it]
      refine WPs.seqG (fun a => a = ⟨updatePanValueMap L1 "r"
          (.rStruct [.word q0, .word q1, .word q2]), s.globals, m, s.ffi⟩)
        (WPs.ite_both (fun w3 _ => ?_)) ?_
      · split
        · exact WPs.skip rfl
        · refine WPs.decCall_ret (fun vh g m' ffi hret =>
            WPs.conseq (Q' := ResW R s sp ℓ) ?_ (fun r h => by
          obtain ⟨l, g, m, r0, r1, r2, r3, R', rfl, hk⟩ := h
          exact ⟨_, g, m, r0, r1, r2, r3, R', rfl, hk⟩))
          obtain ⟨a, hv, hf', hWn, hgn, hmn⟩ := node_new_hashed_retW hE hret (hw := a1)
            (eit 1 a1 _ _ _ _ qit rfl) hW1 ℓ
          simp only [List.cons.injEq, and_true] at hv
          dsimp only at hf' hgn hmn
          subst hv hf'
          exact WPs.ret_quad (of_eval (eval_const _ 0#64)) (of_eval (by lk []))
            (of_eval (eval_const _ 0#64)) (of_eval (eval_const _ 0#64))
            ⟨_, _, _, _, _, _, _, R.addNd a 0#64 ℓ ℓ, rfl, Reg.Le.addNd R a 0#64 ℓ ℓ, hWn, hgn,
              fun addr ha => (hmn addr (by omega)).trans (hmf addr ha),
              fun _ => Or.inr ⟨0#64, Reg.addNd_kd R a 0#64 ℓ ℓ, Reg.addNd_lv R a 0#64 ℓ ℓ⟩⟩
      intro a ha
      rw [ha]
      clear ha a
      exact WPs.ret_quad (of_eval (eval_const _ 1#64))
        (of_eval (er 1 q1 _ _ _ _ qr rfl)) (of_eval (er 2 q2 _ _ _ _ qr rfl))
        (of_eval (eit 1 a1 _ _ _ _ qit rfl))
        ⟨_, _, _, _, _, _, _, R, rfl, Reg.Le.refl R, hW1, fun _ _ => rfl, hmf,
          fun h => absurd h (by decide)⟩
  intro a ha
  rw [ha]
  clear ha a
  exact WPs.ret_quad (of_eval (eval_const _ 1#64)) (of_eval (w := pw) (by lk [L1_p]))
    (of_eval (w := nw) (by lk [L1_n])) (of_eval (eval_const _ 0#64))
    ⟨_, _, _, _, _, _, _, R, rfl, Reg.Le.refl R, hW1, fun _ _ => rfl, hmf,
      fun h => absurd h (by decide)⟩

/-- The `resolve` field of the decoder interface. -/
theorem resolve_spec (hE : GuestEnv E) (R : Reg) (s : St σ) (e1 e2 e3 : Exp Word)
    (dbv pw nw sp fv : Word) (ℓ : Nat) (v : PanValue Word)
    (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (ffi : FfiState σ)
    (hret : CalleeRet E s "_resolve_step" [e1, e2, e3] [v] g m ffi)
    (h1 : E.eval s e1 = some (.word dbv)) (h2 : E.eval s e2 = some (.word pw))
    (h3 : E.eval s e3 = some (.word nw)) (hW : WorldTJ R s.globals s.memory)
    (hp : s.globals "scratch_ptr" = some (.word sp))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ sp.toNat)
    (hF : 2952790016 ≤ fv.toNat) :
    ffi = s.ffi ∧ ∃ (R' : Reg) (r0 r1 r2 r3 : Word),
      v = .rStruct [.word r0, .word r1, .word r2, .word r3] ∧
      R.Le R' ∧ WorldTJ R' g m ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ addr.toNat) →
        m addr = s.memory addr) ∧
      (r0 = 0#64 → DRes R' ℓ r1) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := hret
  have hparams := (fun_of_index 260 hE.functions (by guest_decl_at 260) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases resolve_step_world hE parameters body hlookup R ⟨cl, s.globals, s.memory, s.ffi⟩ _
    sp fv pw nw ℓ
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hp hf hfp hF hW hrun with hst | ⟨l', g', m', r0, r1, r2, r3, R', heq, hle, hW', hg, hm, hd⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, R', r0, r1, r2, r3, rfl, hle, hW', hg, hm, hd⟩

end InitECandidate.Solver.GuestBound
