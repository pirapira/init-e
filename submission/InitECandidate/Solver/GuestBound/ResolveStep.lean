import InitECandidate.Solver.GuestBound.RlpItemFrame
import InitECandidate.Solver.GuestBound.NodeNew

/-!
# `_resolve_step` writes only fresh memory

It decodes one RLP item (scratch only), may look the item up in the node
table (reads only) and may allocate a hashed node (its own heap block).
`ResP` is the resulting frame: the heap pointer did not go down, the other
globals are unchanged, and memory is unchanged outside the free scratch range
and the newly allocated heap range.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `mpt_fail` never returns. -/
theorem mpt_fail_noReturn (hE : GuestEnv E) : FunNoReturn E "mpt_fail" := by
  intro parameters body hlookup fuel s r n hrun
  have hbody := (fun_of_index 246 hE.functions (by guest_decl_at 246) (by decide +kernel)
    hlookup).1
  subst hbody
  exact seq_raise_stops hrun

theorem mpt_fail_quiet (hE : GuestEnv E) : FunKeeps (quietKeeper E) "mpt_fail" :=
  keepFn_sound (quietKeeper E) hE.functions 1 "mpt_fail"
    (show keepFn quietLeaf Guest.Software.guestAst 1 "mpt_fail" = true by decide +kernel)

/-- A call statement of a function that never returns stops. -/
theorem stops_call_noReturn {f : FunName} (hf : FunNoReturn E f) {args : List (Exp Word)}
    {s' : St σ} {r : Result σ} (h : Runs E s' (.call (some (none, none)) f args) r) :
    Stopped r := by
  obtain ⟨fuel, n, hrun⟩ := h
  obtain ⟨hl, hn⟩ := call_noReturn hf (some none) hrun
  cases r <;> first | trivial | cases hl | cases hn

/-- `try x = f(…) catch exc => hv { hp }` for a local `x`, when the handler always stops. -/
theorem WPs.callHA_stop {f : FunName} {exc : ExceptionId} {hv : VarName} {hp : Prog Word}
    {args : List (Exp Word)} {x : VarName} (hstop : ∀ s' r, Runs E s' hp r → Stopped r)
    (h : ∀ v g m ffi, CalleeRet E s f args [v] g m ffi →
      Q (.normal (updatePanValueMap s.locals x v) g m ffi)) :
    WPs E s (.call (some (some (.local, x), some (exc, hv, hp))) f args) Q := by
  intro r hr
  rcases runs_callH_inv hr with herr | ⟨parameters, body, values, cl, rb, hlookup, hvalues,
    hbind, hrun, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  cases rb with
  | returned lr g m ffi vs =>
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    · cases vs with
      | nil => simp [assignPanValueCallResult] at hassign
      | cons v tl =>
        cases tl with
        | cons _ _ => simp [assignPanValueCallResult] at hassign
        | nil =>
          simp only [assignPanValueCallResult] at hassign
          split at hassign
          · simp only [Option.some.injEq, Prod.mk.injEq] at hassign
            obtain ⟨rfl, rfl⟩ := hassign
            exact Or.inr (h v _ m ffi ⟨parameters, body, values, cl, lr, hlookup, hvalues,
              hbind, hrun⟩)
          · cases hassign
  | raised lr g m ffi e v =>
    rcases hout with ⟨-, rfl⟩ | ⟨-, hrunh⟩
    · exact Or.inl trivial
    · exact Or.inl (hstop _ _ hrunh)
  | finalFfi lr g m ffi ev =>
    subst hout
    exact Or.inl trivial
  | _ => exact Or.inl (Stopped.of_error hout)

theorem update_self {g : VarName → Option (PanValue Word)} {x : VarName} {v : PanValue Word}
    (h : g x = some v) : updatePanValueMap g x v = g := by
  funext y
  rw [update_lookup]
  by_cases hy : y = x
  · subst hy
    simp [h]
  · rw [if_neg (by simpa using hy)]

/-- Returned with only free scratch memory and newly allocated heap memory
changed; `hv0` is the heap pointer at entry. -/
def ResP (pv fv hv0 : Word) (s : St σ) (r : Result σ) : Prop :=
  ∃ l qv m v, r = .returned l (updatePanValueMap s.globals "heap_ptr" (.word qv)) m s.ffi [v] ∧
    InHeap qv ∧ hv0.toNat ≤ qv.toNat ∧
    ∀ x : Word, (x.toNat < fv.toNat ∨ pv.toNat ≤ x.toNat) →
      (x.toNat < hv0.toNat ∨ qv.toNat ≤ x.toNat) → m x = s.memory x

theorem ResP.restore {pv fv hv0 : Word} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : ResP pv fv hv0 s r) :
    ResP pv fv hv0 s (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, qv, m, v, rfl, hk⟩ := h
  exact ⟨_, qv, m, v, rfl, hk⟩

/-- A return with the heap pointer where it was. -/
theorem ResP.same {pv fv hv0 : Word} (hh : s.globals "heap_ptr" = some (.word hv0))
    (hhH : InHeap hv0) {l : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} (hk : ScrMem pv fv s.memory m) (v : PanValue Word) :
    ResP pv fv hv0 s (.returned l s.globals m s.ffi [v]) :=
  ⟨l, hv0, m, v, by rw [update_self hh], hhH, Nat.le_refl _, fun x hx _ => hk x hx⟩

theorem nodenewhashed_ret (hE : GuestEnv E) {e : Exp Word} {hw : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "node_new_hashed" [e] vs g m ffi) (he : E.eval s e = some (.word hw))
    (hH : HeapOk s.globals) :
    ffi = s.ffi ∧ ∃ pv qv : Word, s.globals "heap_ptr" = some (.word pv) ∧ vs = [.word pv] ∧
      g = updatePanValueMap s.globals "heap_ptr" (.word qv) ∧ pv.toNat + 32 ≤ qv.toNat ∧
      InHeap qv ∧ ∀ x : Word, (x.toNat < pv.toNat ∨ pv.toNat + 32 ≤ x.toNat) → m x = s.memory x := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 255 hE.functions (by guest_decl_at 255) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, he, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases node_new_hashed_fresh hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    (w_hash := hw) (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hH
    hrun with hst | ⟨l', pv, qv, m', hp, heq, h1, h2, hfr⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, pv, qv, hp, rfl, rfl, h1, h2, hfr⟩

theorem nodedb_lookup_quiet (hE : GuestEnv E) : FunKeeps (quietKeeper E) "nodedb_lookup" :=
  keepFn_sound (quietKeeper E) hE.functions 3 "nodedb_lookup"
    (show keepFn quietLeaf Guest.Software.guestAst 3 "nodedb_lookup" = true by decide +kernel)

set_option maxHeartbeats 16000000 in
theorem resolve_step_frame (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_resolve_step" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv pw hv0 : Word) (hpw : s.locals "p" = some (.word pw))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (hh : s.globals "heap_ptr" = some (.word hv0)) (hhH : InHeap hv0)
    (h : Runs E s body r) : Stopped r ∨ ResP pv fv hv0 s r := by
  have hbody := (fun_of_index 260 hE.functions (by guest_decl_at 260) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (ResP pv fv hv0 s)) r h
  refine WPs.dec_ev (fun vit _ => WPs.conseq (Q' := ResP pv fv hv0 s) ?_ (fun r h => h.restore))
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := ResP pv fv hv0 s) ?_ (fun r h => h.restore)
  try dsimp only
  generalize hL : updatePanValueMap (updatePanValueMap s.locals "it" vit) "e"
    (PanValue.word 0#64) = L
  have L_p : L "p" = some (.word pw) := by rw [← hL]; lk [hpw]
  refine WPs.seq (fun a => ∃ (m : Word → Option (PanValue Word)) (a0 a1 a2 a3 : Word),
      a = ⟨updatePanValueMap L "it" (.rStruct [.word a0, .word a1, .word a2, .word a3]),
        s.globals, m, s.ffi⟩ ∧ ScrMem pv fv s.memory m)
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
  refine WPs.seqG (fun a => a = ⟨L1, s.globals, m, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.seqG (fun a => a = ⟨L1, s.globals, m, s.ffi⟩) (WPs.ite_both (fun w2 _ => ?_))
        ?_
      · split
        · exact WPs.skip rfl
        · exact WPs.ret_ev (fun v _ => ResP.same hh hhH hk v)
      intro a ha
      rw [ha]
      clear ha a
      refine WPs.guard_quiet (mpt_fail_quiet hE) ?_
      refine WPs.decCall_ret (fun vr g m' ffi hret => WPs.conseq (Q' := ResP pv fv hv0 s) ?_
        (fun r h => by
        obtain ⟨l, qv, m, v, rfl, hk⟩ := h
        exact ⟨_, qv, m, v, rfl, hk⟩))
      obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet (nodedb_lookup_quiet hE) hret
      subst g m' ffi
      try dsimp only
      refine WPs.seqG (fun a => a = ⟨updatePanValueMap L1 "r" vr, s.globals, m, s.ffi⟩)
        (WPs.ite_both (fun w3 _ => ?_)) ?_
      · split
        · exact WPs.skip rfl
        · refine WPs.decCall_ret (fun vh g m' ffi hret =>
            WPs.conseq (Q' := ResP pv fv hv0 s) ?_ (fun r h => by
        obtain ⟨l, qv, m, v, rfl, hk⟩ := h
        exact ⟨_, qv, m, v, rfl, hk⟩))
          obtain ⟨hf', pv', qv, hp', hv, hg, h1, h2, hfr⟩ := nodenewhashed_ret hE hret (hw := a1)
            (by simp (config := { decide := true }) [evalF_rField, evalF_local, update_lookup,
              L1_it]) ⟨hv0, hh, hhH⟩
          have : pv' = hv0 := by
            rw [hh] at hp'
            simpa using hp'.symm
          subst this
          subst g ffi
          exact WPs.ret_ev (fun v _ => ⟨_, qv, m', v, rfl, h2, by omega,
            fun x hx1 hx2 => (hfr x (by omega)).trans (hk x hx1)⟩)
      intro a ha
      rw [ha]
      clear ha a
      exact WPs.ret_ev (fun v _ => ResP.same hh hhH hk v)
  intro a ha
  rw [ha]
  clear ha a
  exact WPs.ret_ev (fun v _ => ResP.same hh hhH hk v)

end InitECandidate.Solver.GuestBound
