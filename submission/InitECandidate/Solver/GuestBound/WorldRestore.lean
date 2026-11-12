import InitECandidate.Solver.GuestBound.WorldHeap

/-!
# `state_restore` keeps the tables and the journal

`WorldTJ g m`: the heap pointer, the live tables (`TabsOK`) and the journal
(`JournalOK`). `state_restore_world`: from such a state `state_restore(snap)`
returns 0 in such a state; no global other than `heap_ptr` and `journal_n`
changes and no memory outside the heap changes.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Heap pointer, live tables, journal and trie nodes. `D` is a set of table
addresses known to be live; frames refer to their tables through it. -/
def WorldTJ (D : Word → Prop) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) : Prop :=
  ∃ (pv : Word) (T : Word → Option HtabV) (N : Word → Option Word) (J C n : Word),
    g "heap_ptr" = some (.word pv) ∧ InHeap pv ∧ g "journal" = some (.word J) ∧
    g "journal_cap" = some (.word C) ∧ g "journal_n" = some (.word n) ∧
    HeapW m pv T N J C n ∧ ∀ t, D t → ∃ v, T t = some v

/-- A comparison that evaluated to a word: both sides are words. -/
theorem cmp_word_inv (hE : GuestEnv E) {op : Cmp} {a b : Exp Word} {w : Word}
    (h : E.eval s (.cmp op a b) = some (.word w)) :
    ∃ x y, E.eval s a = some (.word x) ∧ E.eval s b = some (.word y) ∧
      w = evalPanCmp op x y := by
  rw [evalF_cmp hE.word] at h
  cases ha : E.eval s a with
  | none => rw [ha] at h; cases h
  | some va =>
    cases hb : E.eval s b with
    | none => rw [ha, hb] at h; cases va <;> cases h
    | some vb =>
      rw [ha, hb] at h
      cases va with
      | word x =>
        cases vb with
        | word y =>
          simp only [Option.some.injEq, PanValue.word.injEq] at h
          exact ⟨x, y, rfl, rfl, h.symm⟩
        | _ => cases h
      | _ => cases h

/-- `g = e; rest` for a global. -/
theorem WPs.seq_assign_global {x : VarName} {e : Exp Word} {q : Prog Word} {w : Word}
    (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : WPs E ⟨s.locals, updatePanValueMap s.globals x (.word w), s.memory, s.ffi⟩ q Q) :
    WPs E s (.seq (.assign .global x e) q) Q := by
  refine WPs.seqG (fun s' => s' = ⟨s.locals, updatePanValueMap s.globals x (.word w), s.memory,
    s.ffi⟩) ?_ (by rintro _ rfl; exact h)
  intro r hr
  rw [runs_assign_global] at hr
  cases hy : E.eval s e with
  | none => rw [hy] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some y =>
    have := he y hy
    subst this
    rw [hy] at hr
    simp only at hr
    split at hr
    · subst hr; exact Or.inr rfl
    · subst hr; exact Or.inl (Stopped.err s)

/-- A call whose result is dropped, from a statement about every run of the callee. -/
theorem WPs.call_runs {f : FunName} {args : List (Exp Word)} (C : Result σ → Prop)
    (hc : ∀ parameters body values cl, lookupPanFunction f E.functions = some (parameters, body) →
      E.evalArgs s args = some values → bindPanValueParameters parameters values = some cl →
      ∀ rb, Runs E ⟨cl, s.globals, s.memory, s.ffi⟩ body rb → Stopped rb ∨ C rb)
    (hC : ∀ rb, C rb → ∃ l g m ffi v, rb = .returned l g m ffi [v])
    (hret : ∀ l g m ffi v, C (.returned l g m ffi [v]) → Q (.normal s.locals g m ffi)) :
    WPs E s (.call (some (none, none)) f args) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  rcases hc parameters body values cl hlookup hvalues hbind rb hcallee with hst | hsp
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
  · obtain ⟨l, g, m, ffi, v, rfl⟩ := hC rb hsp
    simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g'', hassign, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    · simp only [assignPanValueCallResult, Option.some.injEq, Prod.mk.injEq] at hassign
      obtain ⟨rfl, rfl⟩ := hassign
      exact Or.inr (hret l g m ffi v hsp)

/-- A journal with fewer entries. -/
theorem JournalOK.shrink {m : Word → Option (PanValue Word)} {pv : Word}
    {T : Word → Option HtabV} {J C n n' : Word} (h : JournalOK m pv T J C n)
    (hn : n'.toNat ≤ n.toNat) : JournalOK m pv T J C n' :=
  ⟨by have := h.n_le; omega, h.al, h.lo, h.hi, h.off, fun i hi => h.entry i (by omega)⟩

/-- The loop invariant of `state_restore`, relative to the entry state `s`. -/
def RestI (D : Word → Prop) (s a : St σ) : Prop :=
  a.ffi = s.ffi ∧ WorldTJ D a.globals a.memory ∧
    (∀ x, x ≠ "heap_ptr" → x ≠ "journal_n" → a.globals x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      a.memory addr = s.memory addr

theorem HeapW.shrink {m : Word → Option (PanValue Word)} {pv : Word} {T : Word → Option HtabV}
    {N : Word → Option Word} {J C n n' : Word} (h : HeapW m pv T N J C n)
    (hn : n'.toNat ≤ n.toNat) : HeapW m pv T N J C n' :=
  ⟨h.pvH, h.tabs, h.jrn.shrink hn, h.nodes, h.tn, h.jn⟩

theorem stepT_dom {D : Word → Prop} {T : Word → Option HtabV} (hD : ∀ t, D t → ∃ v, T t = some v)
    (t0 : Word) (v' : HtabV) : ∀ t, D t → ∃ v, stepT T t0 v' t = some v := by
  classical
  intro t ht
  unfold stepT
  by_cases e : t = t0
  · exact ⟨v', by simp [e]⟩
  · obtain ⟨v, hv⟩ := hD t ht
    exact ⟨v, by simp [e, hv]⟩

theorem worldTJ_step {D : Word → Prop} {g g' : VarName → Option (PanValue Word)}
    {m m' : Word → Option (PanValue Word)} {pv pv' t : Word} {T : Word → Option HtabV}
    {N : Word → Option Word} {v v' : HtabV} {J C n n' : Word}
    (hp' : g' "heap_ptr" = some (.word pv')) (hpH' : InHeap pv')
    (hg : ∀ x, x ≠ "heap_ptr" → g' x = g x) (hJg : g "journal" = some (.word J))
    (hCg : g "journal_cap" = some (.word C)) (hng : g "journal_n" = some (.word n'))
    (hW : HeapW m pv T N J C n) (hD : ∀ t, D t → ∃ v, T t = some v) (hn : n'.toNat ≤ n.toNat)
    (hs : TabStep m pv T t v m' pv' v') : WorldTJ D g' m' :=
  ⟨pv', stepT T t v', N, J, C, n', hp', hpH', by rw [hg _ (by decide)]; exact hJg,
    by rw [hg _ (by decide)]; exact hCg, by rw [hg _ (by decide)]; exact hng,
    hW.tab_step hs hn hpH'.1, stepT_dom hD t v'⟩

set_option maxHeartbeats 4000000 in
/-- `state_restore(snap)` keeps heap pointer, tables and journal well formed,
changes no global other than `heap_ptr` and `journal_n`, and no memory
outside the heap. -/
theorem state_restore_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "state_restore" E.functions = some (parameters, body))
    (D : Word → Prop) (s : St σ) (r : Result σ) (hW : WorldTJ D s.globals s.memory)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m', r = .returned l g' m' s.ffi [.word 0#64] ∧ WorldTJ D g' m' ∧
      (∀ x, x ≠ "heap_ptr" → x ≠ "journal_n" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 359 hE.functions (by guest_decl_at 359) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m', r = .returned l g' m' s.ffi [.word 0#64] ∧
    WorldTJ D g' m' ∧ (∀ x, x ≠ "heap_ptr" → x ≠ "journal_n" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  refine WPs.seqG (RestI D s) (WPs.loopG (I := RestI D s)
      ⟨rfl, hW, fun _ _ _ => rfl, fun _ _ => rfl⟩
    ?_ (fun a k hI _ => hI)) ?_
  rotate_left
  · rintro a ⟨hf, hWa, hga, hma⟩
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    exact ⟨_, _, _, by rw [hf], hWa, hga, hma⟩
  rintro ⟨la, ga, ma, fa⟩ ⟨hf, ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hD⟩, hga, hma⟩ hct
  dsimp only at hf hp hJg hCg hng hHW hD hga hma
  have hT := hHW.tabs
  have hJ := hHW.jrn
  subst hf
  obtain ⟨w, cc, hcond, hw⟩ := hct
  obtain ⟨x, y, -, hy, hwv⟩ := cmp_word_inv hE (cond_of_eval hcond)
  rw [eval_global] at hy
  dsimp only at hy
  rw [hng] at hy
  simp only [Option.some.injEq, PanValue.word.injEq] at hy
  subst hy
  have hn1 : 1 ≤ n.toNat := by
    by_contra hc
    have hz : n = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    rw [hz] at hwv
    rw [hwv] at hw
    simp [evalPanCmp] at hw
  have hnC := hJ.n_le
  have hJhi := hJ.hi
  have hpvlt := pv.isLt
  obtain ⟨t0, kc, fl, val, v0, r0, r1, r2, r3, hT0, hkf⟩ := hJ.entry (n.toNat - 1) (by omega)
  have hat := hT.at_ t0 v0 hT0
  obtain ⟨kind, rep, hok⟩ := hat.ok
  have hR : J + (n - 1#64) * 32#64 = J + BitVec.ofNat 64 (32 * (n.toNat - 1)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  generalize hRd : J + BitVec.ofNat 64 (32 * (n.toNat - 1)) = R at r0 r1 r2 r3 hR
  refine WPs.seq_assign_global (w := n - 1#64) (of_eval (by ev [eval_global, hng])) ?_
  have g1J : updatePanValueMap ga "journal_n" (.word (n - 1#64)) "journal" = some (.word J) := by
    simp (config := { decide := true }) [update_lookup, hJg]
  have g1C : updatePanValueMap ga "journal_n" (.word (n - 1#64)) "journal_cap" =
      some (.word C) := by
    simp (config := { decide := true }) [update_lookup, hCg]
  have g1n : updatePanValueMap ga "journal_n" (.word (n - 1#64)) "journal_n" =
      some (.word (n - 1#64)) := by
    simp (config := { decide := true }) [update_lookup]
  have g1p : updatePanValueMap ga "journal_n" (.word (n - 1#64)) "heap_ptr" =
      some (.word pv) := by
    simp (config := { decide := true }) [update_lookup, hp]
  have g1o : ∀ x, x ≠ "journal_n" →
      updatePanValueMap ga "journal_n" (.word (n - 1#64)) x = ga x := by
    intro x hx
    simp [update_lookup, hx]
  have hnle : (n - 1#64).toNat ≤ n.toNat := by bv_omega
  generalize hg1 : updatePanValueMap ga "journal_n" (.word (n - 1#64)) = g1 at g1J g1C g1n g1p g1o ⊢
  refine WPs.dec (w := R) (of_eval (by ev [eval_global, g1J, g1n, evalPanOp, hR])) ?_
  refine WPs.dec (w := t0) (eval_load_rd hE (by lk []) r0) ?_
  refine WPs.dec (w := kc) (eval_load_rd hE (eval_addc hE 8#64 (by lk [])) r1) ?_
  refine WPs.ite (w := evalPanCmp .notEqual fl 0#64) (eval_cmp_inv hE
    (eval_load_rd hE (eval_addc hE 16#64 (by lk [])) r2) (of_eval (eval_const _ _))) ?_
  have hk64 : kc.toNat + v0.kl.toNat < 2 ^ 64 := by have := hkf.1; omega
  obtain ⟨hkT, hkB⟩ := hkf.2 t0 v0 hT0
  by_cases hfl : fl = 0#64
  · have hwz : evalPanCmp .notEqual fl (0#64 : Word) = 0#64 := by simp [evalPanCmp, hfl]
    rw [hwz, if_pos (show (0#64 : Word) = 0 from rfl)]
    refine WPs.call_runs (fun rb => ∃ l m' w, rb = .returned l g1 m' s.ffi [.word w] ∧
        (m' = ma ∨ ∃ Lw : Word, LiveN v0 kind Lw.toNat ∧ kind Lw.toNat = .leaf ∧
          DelRel ma t0 v0 Lw m')) ?_ ?_ ?_
    · intro parameters cbody values cl hlk hvalues hbind rb hrun
      have hparams := (fun_of_index 139 hE.functions (by guest_decl_at 139) (by decide +kernel)
        hlk).2
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local,
        update_lookup] at hvalues
      subst hvalues
      rw [hparams] at hbind
      simp [bindPanValueParameters] at hbind
      rcases htab_del_any_exec hE parameters cbody hlk ⟨cl, g1, ma, s.ffi⟩ rb t0 kc v0 kind rep
        (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
        (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hok hk64
        hrun with hst | ⟨l, m', ⟨rfl, rfl⟩ | ⟨Lw, hL, hLk, rfl, hrel⟩⟩
      · exact Or.inl hst
      · exact Or.inr ⟨l, _, _, rfl, Or.inl rfl⟩
      · exact Or.inr ⟨l, m', _, rfl, Or.inr ⟨Lw, hL, hLk, hrel⟩⟩
    · rintro rb ⟨l, m', w', rfl, -⟩
      exact ⟨_, _, _, _, _, rfl⟩
    · rintro l g m ffi v ⟨l', m', w', heq, hcase⟩
      injection heq with _ hg hm hf _
      subst g m ffi
      simp only [restorePanValueFfiLocal]
      rcases hcase with rfl | ⟨Lw, hL, hLk, hrel⟩
      · exact ⟨rfl, ⟨pv, T, N, J, C, n - 1#64, g1p, hpH, g1J, g1C, g1n, hHW.shrink hnle, hD⟩,
          fun x h1 h2 => (g1o x h2).trans (hga x h1 h2), hma⟩
      · obtain ⟨v', hs⟩ := TabStep.of_del hT hT0 hok hL hLk hrel
        exact ⟨rfl, worldTJ_step g1p hpH (fun _ _ => rfl) g1J g1C g1n hHW hD hnle hs,
          fun x h1 h2 => (g1o x h2).trans (hga x h1 h2),
          fun addr ha => (hs.out addr ha).trans (hma addr ha)⟩
  · have hwz : evalPanCmp .notEqual fl (0#64 : Word) = 1#64 := by simp [evalPanCmp, hfl]
    rw [hwz, if_neg (by decide)]
    refine WPs.call_runs (fun rb => ∃ l g' m', rb = .returned l g' m' s.ffi [.word 0#64] ∧
        SetPost ma t0 pv v0 s.ffi rb ∧ ∀ x, x ≠ "heap_ptr" → g' x = g1 x) ?_ ?_ ?_
    · intro parameters cbody values cl hlk hvalues hbind rb hrun
      have hparams := (fun_of_index 138 hE.functions (by guest_decl_at 138) (by decide +kernel)
        hlk).2
      cases he3 : E.eval (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap la "r"
          (.word R)) "t" (.word t0)) "key" (.word kc), g1, ma, s.ffi⟩ : St σ)
          (.load .one (.op .add [.var .local "r", .const 24#64])) with
      | none =>
        simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local,
          update_lookup, he3] at hvalues
      | some y3 =>
        have hy3 := eval_load_rd hE (eval_addc hE 24#64 (by lk [])) r3 y3 he3
        subst hy3
        simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local,
          update_lookup, he3] at hvalues
        subst hvalues
        rw [hparams] at hbind
        simp [bindPanValueParameters] at hbind
        have honly := htab_set_only hE parameters cbody hlk
        rcases htab_set_exec hE parameters cbody hlk ⟨cl, g1, ma, s.ffi⟩ rb t0 kc val pv v0 kind
          rep (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
          (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
          (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
          hok g1p hpH hat.fin hat.t8 hk64 hkT hkB (Or.inl hkf.1) hrun with hst | hsp
        · exact Or.inl hst
        · obtain ⟨fuel, k, hrun'⟩ := hrun
          have hrel := honly fuel ⟨cl, g1, ma, s.ffi⟩ rb k hrun'
          obtain ⟨l, g', m', v', kind', rep', rfl, rest⟩ := hsp
          refine Or.inr ⟨l, g', m', rfl, ⟨l, g', m', v', kind', rep', rfl, rest⟩, fun x hx => ?_⟩
          exact hrel x (by simp [hx])
    · rintro rb ⟨l, g', m', rfl, -, -⟩
      exact ⟨_, _, _, _, _, rfl⟩
    · rintro l g m ffi v ⟨l', g', m', heq, hsp, hgl⟩
      injection heq with _ hg hm hf _
      subst g m ffi
      obtain ⟨l0, g0, m0, v', kind', rep', heq2, rest⟩ := hsp
      injection heq2 with hl0 hg0 hm0 _ _
      subst hl0 hg0 hm0
      obtain ⟨pv', v'', hp', hpH', hs⟩ := TabStep.of_set hT hT0 hpH
        (⟨_, _, _, v', kind', rep', rfl, rest⟩ :
          SetPost ma t0 pv v0 s.ffi (.returned l' g' m' s.ffi [.word 0#64]))
      simp only [restorePanValueFfiLocal]
      exact ⟨rfl, worldTJ_step hp' hpH' hgl g1J g1C g1n hHW hD hnle hs,
        fun x h1 h2 => (hgl x h1).trans ((g1o x h2).trans (hga x h1 h2)),
        fun addr ha => (hs.out addr ha).trans (hma addr ha)⟩

end InitECandidate.Solver.GuestBound
