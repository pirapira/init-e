import InitECandidate.Solver.GuestBound.TrieDelete
import InitECandidate.Solver.GuestBound.CallAt
import InitECandidate.Solver.GuestBound.TripleCall

/-!
# `_mpt_delete_node`: world invariant and step bound

The wrapper marks the scratch arena, runs the walk under a handler that
releases the arena and re-raises, and releases the arena on return. The
scratch pointer is back at its entry value, so every global but `heap_ptr`
is unchanged.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Result of `_mpt_delete_node`. -/
def DelNQ (Rg : Reg) (s : St σ) (L : Nat) (sp0 : Word) (r : Result σ) : Prop :=
  ∃ l g' m' a R', r = .returned l g' m' s.ffi [.word a] ∧ Rg.Le R' ∧
    (a = 0#64 ∨ ∃ k, R'.Kd a k ∧ k ≠ 0#64 ∧ R'.Lv a L) ∧ WorldTJ R' g' m' ∧
    (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) → m' addr = s.memory addr

theorem DelNQ.restore {Rg : Reg} {s : St σ} {L : Nat} {sp0 : Word} {r : Result σ} (x : VarName)
    (old : Option (PanValue Word)) (h : DelNQ Rg s L sp0 r) :
    DelNQ Rg s L sp0 (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g', m', a, R', rfl, hq⟩ := h
  exact ⟨_, g', m', a, R', rfl, hq⟩

theorem delete_body_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {Rg : Reg}
    {node key klen level sp0 fv : Word} {v : PanValue Word}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ}
    (h : CalleeRet E s "_mpt_delete_node_body" [e1, e2, e3, e4] [v] g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word node)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word key)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word klen)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word level)
    (hW : WorldTJ Rg s.globals s.memory) (hnd : node = 0#64 ∨ ∃ k, Rg.Kd node k)
    (hLn : node ≠ 0#64 → Rg.Lv node level.toNat) (hlv : level.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) :
    ∃ a R' sp', v = .word a ∧ ffi = s.ffi ∧ Rg.Le R' ∧
      (a = 0#64 ∨ ∃ k, R'.Kd a k ∧ k ≠ 0#64 ∧ R'.Lv a level.toNat) ∧ WorldTJ R' g m ∧
      (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = s.globals x) ∧
      g "scratch_ptr" = some (.word sp') ∧ sp'.toNat ≤ sp0.toNat ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 278 hE.functions (by guest_decl_at 278) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  obtain ⟨y2, vs2, g2, hr2, rfl⟩ := evalArgs_cons_inv hr1
  obtain ⟨y3, vs3, g3, hr3, rfl⟩ := evalArgs_cons_inv hr2
  obtain ⟨y4, vs4, g4, hr4, rfl⟩ := evalArgs_cons_inv hr3
  rw [evalArgs_nil] at hr4
  simp only [Option.some.injEq] at hr4
  subst hr4
  have := h1 _ g1
  subst this
  have := h2 _ g2
  subst this
  have := h3 _ g3
  subst this
  have := h4 _ g4
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases delete_body_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    node key klen level sp0 fv
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hnd hLn hlv hkey hsp hfv hfs hF hrun with
    hst | ⟨l', g', m', a, R', sp', heq, hle, ha, hw, hg, hs, hsl, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, R', sp', rfl, rfl, hle, ha, hw, hg, hs, hsl, hm⟩

/-- The handler of the walk releases the arena and re-raises. -/
theorem del_handler_stops (hE : GuestEnv E) (s' : St σ) (r : Result σ)
    (hr : Runs E s' (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.raise "MptErr" (.var .local "e"))) r) : Stopped r := by
  have h : WPs E s' (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.raise "MptErr" (.var .local "e"))) (fun _ => False) :=
    WPs.seqG (fun _ => True) (WPs.call_ret (fun _ _ _ _ _ => trivial)) (fun s'' _ r' hr' => by
      rcases runs_raise_inv hr' with he | ⟨v, -, rfl⟩
      · exact Or.inl (Stopped.of_error he)
      · exact Or.inl trivial)
  rcases h r hr with hs | hf
  · exact hs
  · exact hf.elim

set_option maxHeartbeats 8000000 in
theorem delete_node_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_mpt_delete_node" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (node key klen level sp0 fv : Word)
    (hnode : s.locals "node" = some (.word node)) (hkeyv : s.locals "key" = some (.word key))
    (hklen : s.locals "klen" = some (.word klen))
    (hlevel : s.locals "level" = some (.word level))
    (hW : WorldTJ Rg s.globals s.memory) (hnd : node = 0#64 ∨ ∃ k, Rg.Kd node k)
    (hLn : node ≠ 0#64 → Rg.Lv node level.toNat) (hlv : level.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ DelNQ Rg s level.toNat sp0 r := by
  have hbody := (fun_of_index 279 hE.functions (by guest_decl_at 279) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (DelNQ Rg s level.toNat sp0)) r h
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨rfl, rfl, rfl, hv⟩ := scratch_mark_ret hE hret hsp
  simp only [List.cons.injEq, and_true] at hv
  subst hv
  refine WPs.conseq (Q' := DelNQ Rg s level.toNat sp0) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DelNQ Rg s level.toNat sp0) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DelNQ Rg s level.toNat sp0) ?_ (fun r h => h.restore _ _)
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qnode : L "node" = some (.word node) := by rw [hLL]; lk [hnode]
  have qkey : L "key" = some (.word key) := by rw [hLL]; lk [hkeyv]
  have qklen : L "klen" = some (.word klen) := by rw [hLL]; lk [hklen]
  have qlevel : L "level" = some (.word level) := by rw [hLL]; lk [hlevel]
  have qmark : L "mark" = some (.word sp0) := by rw [hLL]; lk []
  clear hLL
  refine WPs.seqG (fun a => ∃ av R' sp' g m, a = ⟨updatePanValueMap L "res" (.word av), g, m,
      s.ffi⟩ ∧ Rg.Le R' ∧ (av = 0#64 ∨ ∃ k, R'.Kd av k ∧ k ≠ 0#64 ∧ R'.Lv av level.toNat) ∧
      WorldTJ R' g m ∧ (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = s.globals x) ∧
      g "scratch_ptr" = some (.word sp') ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m addr = s.memory addr)
    (WPs.callHA_stop (del_handler_stops hE) (fun v g m ffi hret => ?_)) ?_
  · obtain ⟨a, R', sp', rfl, rfl, hle, ha, hW', hg, hsp', -, hm⟩ := delete_body_ret hE hret
      (node := node) (key := key) (klen := klen) (level := level) (sp0 := sp0) (fv := fv)
      (of_eval (by lk [qnode])) (of_eval (by lk [qkey])) (of_eval (by lk [qklen]))
      (of_eval (by lk [qlevel])) hW hnd hLn hlv hkey hsp hfv hfs hF
    exact ⟨a, R', sp', g, m, rfl, hle, ha, hW', hg, hsp', hm⟩
  rintro _ ⟨av, R', sp', g, m, rfl, hle, ha, hW', hg, hsp', hm⟩
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap L "res" (.word av),
      updatePanValueMap g "scratch_ptr" (.word sp0), m, s.ffi⟩)
    (WPs.call_ret (fun vs g2 m2 f2 hret2 => ?_)) ?_
  · obtain ⟨rfl, rfl, rfl⟩ := scratch_release_ret hE hret2 (mv := sp0) (pv := sp')
      (by lk [qmark]) hsp'
    rfl
  rintro _ rfl
  refine WPs.ret (w := av) (of_eval (by lk [])) ?_
  refine ⟨_, _, m, av, R', rfl, hle, ha,
    hW'.of_globals (fun x hx => by simp [update_lookup, hx]), fun x hx => ?_, hm⟩
  by_cases hs : x = "scratch_ptr"
  · subst hs
    simp [update_lookup]
    exact hsp.symm
  · show updatePanValueMap g "scratch_ptr" (.word sp0) x = _
    rw [update_lookup, if_neg (by simpa using hs)]
    exact hg x hx hs

theorem del_handler_cost (hE : GuestEnv E) :
    Costs E (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.raise "MptErr" (.var .local "e")) : Prog Word) 1000 := by
  have h : ∃ B, Costs E (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.raise "MptErr" (.var .local "e")) : Prog Word) B ∧ B ≤ 1000 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem del_tail_cost (hE : GuestEnv E) :
    Costs E (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.return (.var .local "res")) : Prog Word) 1000 := by
  have h : ∃ B, Costs E (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
      (.return (.var .local "res")) : Prog Word) B ∧ B ≤ 1000 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 8000000 in
/-- Step bound of `_mpt_delete_node` from a state satisfying the world invariant. -/
theorem delete_node_cost (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_mpt_delete_node" E.functions = some (parameters, body))
    (Rg : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat)
    (node key klen level sp0 fv : Word)
    (hnode : s.locals "node" = some (.word node)) (hkeyv : s.locals "key" = some (.word key))
    (hklen : s.locals "klen" = some (.word klen))
    (hlevel : s.locals "level" = some (.word level))
    (hW : WorldTJ Rg s.globals s.memory) (hnd : node = 0#64 ∨ ∃ k, Rg.Kd node k)
    (hLn : node ≠ 0#64 → Rg.Lv node level.toNat) (hlv : level.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 142 := by
  have hbody := (fun_of_index 279 hE.functions (by guest_decl_at 279) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hfAt : FunCostAt E "_mpt_delete_node_body" (10 ^ 141)
      (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "mark" (.word sp0)) "e"
        (.word 0#64)) "res" (.word 0#64), s.globals, s.memory, s.ffi⟩ : St σ)
      [.var .local "node", .var .local "key", .var .local "klen", .var .local "level"] := by
    intro ps cbody values cl hlk hvalues hbind fuel' r' n' hrun' hne'
    have hparams := (fun_of_index 278 hE.functions (by guest_decl_at 278) (by decide +kernel)
      hlk).2
    simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, hnode, hkeyv, hklen, hlevel] at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact delete_body_cost hE ps cbody hlk Rg fuel' ⟨cl, s.globals, s.memory, s.ffi⟩ r' n'
      node key klen level sp0 fv
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hW hnd hLn hlv hkey hsp hfv hfs hF hrun' hne'
  have hall := Triple.decCallRun (E := E) (P := fun a => a = s)
    (P' := fun a => a = ⟨updatePanValueMap s.locals "mark" (.word sp0), s.globals, s.memory,
      s.ffi⟩) "mark" Shape.one ([] : List (Exp Word)) (Fn.scratch_mark hE) ?_
    (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap s.locals "mark"
        (.word sp0)) "e" (.word 0#64), s.globals, s.memory, s.ffi⟩) "e" Shape.one
      (Exp.const (BitVec.ofNat 64 0)) ?_
      (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
          s.locals "mark" (.word sp0)) "e" (.word 0#64)) "res" (.word 0#64), s.globals,
          s.memory, s.ffi⟩) "res" Shape.one (Exp.const (BitVec.ofNat 64 0)) ?_
        (Triple.seq (Mid := fun _ => True) (Q := fun _ => True)
          ((call_cost_at (H := 1000)
            (info := some (some (.local, "res"), some ("MptErr", "e",
              (.seq (.call (some (none, none)) "scratch_release" [.var .local "mark"])
                (.raise "MptErr" (.var .local "e"))))))
            [.var .local "node", .var .local "key", .var .local "klen", .var .local "level"]
            hfAt (del_handler_cost hE)).consequence (fun _ h => h) (Nat.le_refl _)
            (fun r _ => by cases r <;> trivial))
          (del_tail_cost hE))))
  · have hn := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq, stepsCost_eq] at hn
    refine Nat.le_trans hn ?_
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
