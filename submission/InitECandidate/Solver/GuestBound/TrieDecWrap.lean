import InitECandidate.Solver.GuestBound.TrieDecFinal
import InitECandidate.Solver.GuestBound.TrieDelNode

/-!
# The wrappers of the witness decoder

`_decode_witness_node_mpt` and `_decode_witness_node` run the decoder inside
`try … catch` blocks whose handlers release the scratch arena and re-raise.
On a normal return the scratch pointer is back at its mark.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem DecQ.restore {I : DecIface E} {R0 : Reg} {sp0 fv : Word} {L0 : Nat} {x : VarName}
    {old : Option (PanValue Word)} {r : Result σ} (h : DecQ I R0 s sp0 fv L0 r) :
    DecQ I R0 s sp0 fv L0 (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g, m, res, R, sp', rfl, hk⟩ := h
  exact ⟨_, g, m, res, R, sp', rfl, hk⟩

/-- A handler that releases the arena and re-raises never returns normally. -/
theorem release_raise_stops (exc : ExceptionId) (s' : St σ) (r : Result σ)
    (hr : Runs E s' (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.raise exc (.var .local "e"))) r) : Stopped r := by
  have h : WPs E s' (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.raise exc (.var .local "e"))) (fun _ => False) :=
    WPs.seqG (fun _ => True) (WPs.call_ret (fun _ _ _ _ _ => trivial)) (fun s'' _ r' hr' => by
      rcases runs_raise_inv hr' with he | ⟨v, -, rfl⟩
      · exact Or.inl (Stopped.of_error he)
      · exact Or.inl trivial)
  rcases h r hr with hs | hf
  · exact hs
  · exact hf.elim

section rets

variable {v : PanValue Word} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

/-- What a returning `_decode_witness_node_body` leaves. -/
theorem decode_body_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {R0 : Reg}
    {dbv pw nw sp0 fv : Word} (L0 : Nat)
    (h : CalleeRet E s "_decode_witness_node_body" [e1, e2, e3] [v] g m ffi)
    (h1 : E.eval s e1 = some (.word dbv)) (h2 : E.eval s e2 = some (.word pw))
    (h3 : E.eval s e3 = some (.word nw)) (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) :
    ∃ (res : Word) (R : Reg) (sp' : Word), v = .word res ∧ ffi = s.ffi ∧ R0.Le R ∧
      WorldTJ R g m ∧ DRes R L0 res ∧
      (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = s.globals x) ∧
      g "scratch_ptr" = some (.word sp') ∧ fv.toNat ≤ sp'.toNat ∧ sp'.toNat ≤ sp0.toNat ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 262 hE.functions (by guest_decl_at 262) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases decode_witness_body_world hE parameters body hlookup R0
    ⟨cl, s.globals, s.memory, s.ffi⟩ _ dbv pw nw sp0 fv L0
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hsp hfv hfs hF hrun with
    hst | ⟨l', g', m', res, R, sp', heq, hle, hW', hres, -, hg, hs, h1', h2', hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨res, R, sp', rfl, rfl, hle, hW', hres, hg, hs, h1', h2', hm⟩

end rets

set_option maxHeartbeats 8000000 in
theorem decode_mpt_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_decode_witness_node_mpt" E.functions =
      some (parameters, body))
    (R0 : Reg) (s : St σ) (r : Result σ) (dbv pw nw sp0 fv : Word) (L0 : Nat)
    (hdb : s.locals "db" = some (.word dbv)) (hp : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw)) (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ DecQ (decIface hE) R0 s sp0 fv L0 r := by
  have hbody := (fun_of_index 263 hE.functions (by guest_decl_at 263) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (DecQ (decIface hE) R0 s sp0 fv L0)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DecQ (decIface hE) R0 s sp0 fv L0) ?_ (fun r h => h.restore)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DecQ (decIface hE) R0 s sp0 fv L0) ?_ (fun r h => h.restore)
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qdb : L "db" = some (.word dbv) := by rw [hLL]; lk [hdb]
  have qp : L "p" = some (.word pw) := by rw [hLL]; lk [hp]
  have qn : L "n" = some (.word nw) := by rw [hLL]; lk [hn]
  clear hLL
  refine WPs.seqG (fun a => ∃ (res : Word) (R : Reg) (sp' : Word), ∃ g m,
      a = ⟨updatePanValueMap L "nd" (.word res), g, m, s.ffi⟩ ∧ R0.Le R ∧ WorldTJ R g m ∧
      DRes R L0 res ∧ (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = s.globals x) ∧
      g "scratch_ptr" = some (.word sp') ∧ fv.toNat ≤ sp'.toNat ∧ sp'.toNat ≤ sp0.toNat ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m addr = s.memory addr)
    (WPs.callHA_stop (release_raise_stops "MptErr") (fun v g m ffi hret => ?_)) ?_
  · obtain ⟨res, R, sp', rfl, rfl, hle, hW', hres, hg, hs, h1, h2, hm⟩ := decode_body_ret hE L0
      hret (dbv := dbv) (pw := pw) (nw := nw) (by lk [qdb]) (by lk [qp]) (by lk [qn]) hW hsp hfv
      hfs hF
    exact ⟨res, R, sp', g, m, rfl, hle, hW', hres, hg, hs, h1, h2, hm⟩
  rintro _ ⟨res, R, sp', g, m, rfl, hle, hW', hres, hg, hs, h1, h2, hm⟩
  refine WPs.ret (w := res) (of_eval (by lk [])) ?_
  exact ⟨_, g, m, res, R, sp', rfl, hle, hW', hres, trivial, hg, hs, h1, h2, hm⟩

section rets

variable {v : PanValue Word} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

/-- What a returning `_decode_witness_node_mpt` leaves. -/
theorem decode_mpt_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {R0 : Reg}
    {dbv pw nw mk sp0 fv : Word} (L0 : Nat)
    (h : CalleeRet E s "_decode_witness_node_mpt" [e1, e2, e3, e4] [v] g m ffi)
    (h1 : E.eval s e1 = some (.word dbv)) (h2 : E.eval s e2 = some (.word pw))
    (h3 : E.eval s e3 = some (.word nw)) (h4 : E.eval s e4 = some (.word mk))
    (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) :
    ∃ (res : Word) (R : Reg) (sp' : Word), v = .word res ∧ ffi = s.ffi ∧ R0.Le R ∧
      WorldTJ R g m ∧ DRes R L0 res ∧
      (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = s.globals x) ∧
      g "scratch_ptr" = some (.word sp') ∧ fv.toNat ≤ sp'.toNat ∧ sp'.toNat ≤ sp0.toNat ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 263 hE.functions (by guest_decl_at 263) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, Option.map_some, Option.some.injEq]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases decode_mpt_world hE parameters body hlookup R0
    ⟨cl, s.globals, s.memory, s.ffi⟩ _ dbv pw nw sp0 fv L0
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hsp hfv hfs hF hrun with
    hst | ⟨l', g', m', res, R, sp', heq, hle, hW', hres, -, hg, hs, h1', h2', hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨res, R, sp', rfl, rfl, hle, hW', hres, hg, hs, h1', h2', hm⟩

end rets

/-- What `_decode_witness_node` guarantees: a node at level `L0` (or null), the
scratch pointer back at its mark. -/
def DecWQ (R0 : Reg) (s : St σ) (sp0 : Word) (L0 : Nat) (r : Result σ) : Prop :=
  ∃ l g m, ∃ (res : Word) (R : Reg), r = .returned l g m s.ffi [.word res] ∧ R0.Le R ∧
    WorldTJ R g m ∧ DRes R L0 res ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) → m addr = s.memory addr

theorem DecWQ.restore {R0 : Reg} {sp0 : Word} {L0 : Nat} {x : VarName}
    {old : Option (PanValue Word)} {r : Result σ} (h : DecWQ R0 s sp0 L0 r) :
    DecWQ R0 s sp0 L0 (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g, m, res, R, rfl, hk⟩ := h
  exact ⟨_, g, m, res, R, rfl, hk⟩

set_option maxHeartbeats 8000000 in
theorem decode_node_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_decode_witness_node" E.functions = some (parameters, body))
    (R0 : Reg) (s : St σ) (r : Result σ) (dbv pw nw sp0 fv : Word) (L0 : Nat)
    (hdb : s.locals "db" = some (.word dbv)) (hp : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw)) (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ DecWQ R0 s sp0 L0 r := by
  have hbody := (fun_of_index 264 hE.functions (by guest_decl_at 264) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (DecWQ R0 s sp0 L0)) r h
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨rfl, rfl, rfl, hv⟩ := scratch_mark_ret hE hret hsp
  simp only [List.cons.injEq, and_true] at hv
  subst hv
  refine WPs.conseq (Q' := DecWQ R0 s sp0 L0) ?_ (fun r h => h.restore)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DecWQ R0 s sp0 L0) ?_ (fun r h => h.restore)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DecWQ R0 s sp0 L0) ?_ (fun r h => h.restore)
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qdb : L "db" = some (.word dbv) := by rw [hLL]; lk [hdb]
  have qp : L "p" = some (.word pw) := by rw [hLL]; lk [hp]
  have qn : L "n" = some (.word nw) := by rw [hLL]; lk [hn]
  have qmark : L "mark" = some (.word sp0) := by rw [hLL]; lk []
  clear hLL
  refine WPs.seqG (fun a => ∃ (res : Word) (R : Reg) (sp' : Word), ∃ g m,
      a = ⟨updatePanValueMap L "nd" (.word res), g, m, s.ffi⟩ ∧ R0.Le R ∧ WorldTJ R g m ∧
      DRes R L0 res ∧ (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = s.globals x) ∧
      g "scratch_ptr" = some (.word sp') ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m addr = s.memory addr)
    (WPs.callHA_stop (release_raise_stops "RlpErr") (fun v g m ffi hret => ?_)) ?_
  · obtain ⟨res, R, sp', rfl, rfl, hle, hW', hres, hg, hs, -, -, hm⟩ := decode_mpt_ret hE L0
      hret (dbv := dbv) (pw := pw) (nw := nw) (mk := sp0) (by lk [qdb]) (by lk [qp]) (by lk [qn])
      (by lk [qmark]) hW hsp hfv hfs hF
    exact ⟨res, R, sp', g, m, rfl, hle, hW', hres, hg, hs, hm⟩
  rintro _ ⟨res, R, sp', g, m, rfl, hle, hW', hres, hg, hs, hm⟩
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap L "nd" (.word res),
      updatePanValueMap g "scratch_ptr" (.word sp0), m, s.ffi⟩)
    (WPs.call_ret (fun vs g2 m2 f2 hret2 => ?_)) ?_
  · obtain ⟨rfl, rfl, rfl⟩ := scratch_release_ret hE hret2 (mv := sp0) (pv := sp')
      (by lk [qmark]) hs
    rfl
  rintro _ rfl
  refine WPs.ret (w := res) (of_eval (by lk [])) ?_
  refine ⟨_, _, m, res, R, rfl, hle,
    hW'.of_globals (fun x hx => by simp [update_lookup, hx]), hres, fun x hx => ?_, hm⟩
  by_cases hsx : x = "scratch_ptr"
  · subst hsx
    simp [update_lookup]
    exact hsp.symm
  · show updatePanValueMap g "scratch_ptr" (.word sp0) x = _
    rw [update_lookup, if_neg (by simpa using hsx)]
    exact hg x hx hsx


theorem release_raise_cost (hE : GuestEnv E) (exc : ExceptionId) :
    Costs E (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.raise exc (.var .local "e")) : Prog Word) 1000 := by
  have h : ∃ B, Costs E (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.raise exc (.var .local "e")) : Prog Word) B ∧ B ≤ 1000 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem ret_nd_cost (hE : GuestEnv E) :
    Costs E (Prog.return (Exp.var VarKind.local "nd") : Prog Word) 10 := by
  have h : ∃ B, Costs E (Prog.return (Exp.var VarKind.local "nd") : Prog Word) B ∧ B ≤ 10 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem release_ret_nd_cost (hE : GuestEnv E) :
    Costs E (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.return (.var .local "nd")) : Prog Word) 1000 := by
  have h : ∃ B, Costs E (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.return (.var .local "nd")) : Prog Word) B ∧ B ≤ 1000 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 8000000 in
/-- Step bound of `_decode_witness_node_mpt` from a world-invariant state. -/
theorem decode_mpt_cost (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_decode_witness_node_mpt" E.functions =
      some (parameters, body))
    (R0 : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (dbv pw nw sp0 fv : Word)
    (L0 : Nat)
    (hdb : s.locals "db" = some (.word dbv)) (hp : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw)) (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 183 := by
  have hbody := (fun_of_index 263 hE.functions (by guest_decl_at 263) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hfAt : FunCostAt E "_decode_witness_node_body" (10 ^ 182)
      (⟨updatePanValueMap (updatePanValueMap s.locals "e" (.word 0#64)) "nd" (.word 0#64),
        s.globals, s.memory, s.ffi⟩ : St σ)
      [.var .local "db", .var .local "p", .var .local "n"] := by
    intro ps cbody values cl hlk hvalues hbind fuel' r' n' hrun' hne'
    have hparams := (fun_of_index 262 hE.functions (by guest_decl_at 262) (by decide +kernel)
      hlk).2
    simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, hdb, hp, hn] at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact decode_witness_body_cost hE ps cbody hlk R0 fuel' ⟨cl, s.globals, s.memory, s.ffi⟩ r'
      n' dbv pw nw sp0 fv L0
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hW hsp hfv hfs hF hrun' hne'
  have hall := Triple.dec (E := E) (P := fun a => a = s)
    (P' := fun a => a = ⟨updatePanValueMap s.locals "e" (.word 0#64), s.globals, s.memory,
      s.ffi⟩) "e" Shape.one (Exp.const (BitVec.ofNat 64 0)) ?_
    (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap s.locals "e"
        (.word 0#64)) "nd" (.word 0#64), s.globals, s.memory, s.ffi⟩) "nd" Shape.one
      (Exp.const (BitVec.ofNat 64 0)) ?_
      (Triple.seq (Mid := fun _ => True) (Q := fun _ => True)
        ((call_cost_at (H := 1000)
          (info := some (some (.local, "nd"), some ("MptErr", "e",
            (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
              (.raise "MptErr" (.var .local "e"))))))
          [.var .local "db", .var .local "p", .var .local "n"]
          hfAt (release_raise_cost hE "MptErr")).consequence (fun _ h => h) (Nat.le_refl _)
          (fun r _ => by cases r <;> trivial))
        (ret_nd_cost hE)))
  · have hn' := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq, stepsCost_eq] at hn'
    refine Nat.le_trans hn' ?_
    decide +kernel
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 0#64) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 0#64) val hval
    subst this
    rfl

set_option maxHeartbeats 8000000 in
/-- Step bound of `_decode_witness_node` from a world-invariant state. -/
theorem decode_node_cost (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_decode_witness_node" E.functions = some (parameters, body))
    (R0 : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (dbv pw nw sp0 fv : Word)
    (L0 : Nat)
    (hdb : s.locals "db" = some (.word dbv)) (hp : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw)) (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 184 := by
  have hbody := (fun_of_index 264 hE.functions (by guest_decl_at 264) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hfAt : FunCostAt E "_decode_witness_node_mpt" (10 ^ 183)
      (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "mark" (.word sp0)) "e"
        (.word 0#64)) "nd" (.word 0#64), s.globals, s.memory, s.ffi⟩ : St σ)
      [.var .local "db", .var .local "p", .var .local "n", .var .local "mark"] := by
    intro ps cbody values cl hlk hvalues hbind fuel' r' n' hrun' hne'
    have hparams := (fun_of_index 263 hE.functions (by guest_decl_at 263) (by decide +kernel)
      hlk).2
    simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, hdb, hp, hn] at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact decode_mpt_cost hE ps cbody hlk R0 fuel' ⟨cl, s.globals, s.memory, s.ffi⟩ r'
      n' dbv pw nw sp0 fv L0
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hW hsp hfv hfs hF hrun' hne'
  have hall := Triple.decCallRun (E := E) (P := fun a => a = s)
    (P' := fun a => a = ⟨updatePanValueMap s.locals "mark" (.word sp0), s.globals, s.memory,
      s.ffi⟩) "mark" Shape.one ([] : List (Exp Word)) (Fn.scratch_mark hE) ?_
    (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap s.locals "mark"
        (.word sp0)) "e" (.word 0#64), s.globals, s.memory, s.ffi⟩) "e" Shape.one
      (Exp.const (BitVec.ofNat 64 0)) ?_
      (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
          s.locals "mark" (.word sp0)) "e" (.word 0#64)) "nd" (.word 0#64), s.globals,
          s.memory, s.ffi⟩) "nd" Shape.one (Exp.const (BitVec.ofNat 64 0)) ?_
        (Triple.seq (Mid := fun _ => True) (Q := fun _ => True)
          ((call_cost_at (H := 1000)
            (info := some (some (.local, "nd"), some ("RlpErr", "e",
              (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
                (.raise "RlpErr" (.var .local "e"))))))
            [.var .local "db", .var .local "p", .var .local "n", .var .local "mark"]
            hfAt (release_raise_cost hE "RlpErr")).consequence (fun _ h => h) (Nat.le_refl _)
            (fun r _ => by cases r <;> trivial))
          (release_ret_nd_cost hE))))
  · have hn' := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq, stepsCost_eq] at hn'
    refine Nat.le_trans hn' ?_
    decide +kernel
  · rintro a v g m ffi rfl hret -
    obtain ⟨rfl, rfl, rfl, hv⟩ := scratch_mark_ret hE hret.ret hsp
    simp only [List.cons.injEq, and_true] at hv
    subst hv
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 0#64) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 0#64) val hval
    subst this
    rfl

end InitECandidate.Solver.GuestBound
