import InitECandidate.Solver.GuestBound.WorldBlob
import InitECandidate.Solver.GuestBound.MemFrame

/-!
# `jset` keeps the world

`jset(t, key, value)` records the old binding of `key` in the journal (with a
fresh copy of the key) and then calls `htab_set`. It is the write path of the
state layer. `jset_world`: on a live table, with the key in a registered free
block or outside the heap, the world invariant is kept; only `heap_ptr` and
`journal_n` change among the globals, and no memory outside the heap changes.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem struct2_of_shape {structs : StructContext} {v : PanValue Word}
    (h : panShapeMatches (panValueShape structs v) (.comb [.one, .one]) = true) :
    ∃ w0 w1 : Word, v = .rStruct [.word w0, .word w1] := by
  cases v with
  | word w => simp [panValueShape, panShapeMatches] at h
  | nStruct name fields => simp [panValueShape, panShapeMatches] at h
  | rStruct fields =>
    rcases fields with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    case cons.cons.nil =>
      simp only [panValueShape, panShapeMatches, List.map,
        panShapeMatches.panShapeListMatches, Bool.and_eq_true] at h
      obtain ⟨ha, hb, -⟩ := h
      obtain ⟨w0, rfl⟩ := word_of_shape_one ha
      obtain ⟨w1, rfl⟩ := word_of_shape_one hb
      exact ⟨w0, w1, rfl⟩
    all_goals
      exfalso
      revert h
      simp [panValueShape, panShapeMatches, panShapeMatches.panShapeListMatches]

/-- A declaring call, with the shape of the returned value. -/
theorem WPs.decCall_retS {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word}
    (h : ∀ v g m ffi, CalleeRet E s f args [v] g m ffi →
      panShapeMatches (panValueShape E.structs v) sh = true →
      WPs E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x sh f args body) Q := by
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
        obtain ⟨r', hsh, hrun', rfl⟩ := hout
        rcases h v g m ffi ⟨parameters, cbody, values, cl, lr, hlookup, hvalues, hbind,
          hcallee⟩ hsh r' hrun' with hs | hq
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

theorem htab_get_quiet (hE : GuestEnv E) : FunKeeps (quietKeeper E) "htab_get" :=
  keepFn_sound (quietKeeper E) hE.functions 4 "htab_get"
    (show keepFn quietLeaf Guest.Software.guestAst 4 "htab_get" = true by decide +kernel)

/-- `trap_with(k)` never returns. -/
theorem WPs.call_trap (hE : GuestEnv E) {args : List (Exp Word)} :
    WPs E s (.call (some (none, none)) "trap_with" args) Q := by
  refine WPs.call_runs (fun _ => False) ?_ (fun _ h => h.elim) (fun _ _ _ _ _ h => h.elim)
  intro parameters body values cl hlk _ _ rb hrun
  rcases trap_with_traps hE parameters body hlk ⟨cl, s.globals, s.memory, s.ffi⟩ rb hrun with
    he | ht
  · exact Or.inl (Stopped.of_error he)
  · exact Or.inl ht.stopped

/-- `memcpy(e1, e2, e3);` as a statement: globals and FFI state kept, memory
changed only in the destination block. -/
theorem WPs.call_memcpy_hull (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {dst nW : Word}
    (h1 : ∀ y, E.eval s e1 = some y → y = .word dst)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word nW)
    (h64 : dst.toNat + nW.toNat + 32 < 2 ^ 64)
    (h : ∀ m', Hull s.memory dst nW m' → Q (.normal s.locals s.globals m' s.ffi)) :
    WPs E s (.call (some (none, none)) "memcpy" [e1, e2, e3]) Q := by
  refine WPs.call_runs (fun rb => ∃ l m', rb = .returned l s.globals m' s.ffi [.word 0#64] ∧
      Hull s.memory dst nW m') ?_ ?_ ?_
  · intro parameters body values cl hlk hvalues hbind rb hrun
    have hparams := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
      hlk).2
    obtain ⟨v1, v2, v3, g1, g2, g3, rfl⟩ := evalArgs3_inv hvalues
    have := h1 _ g1
    subst this
    have := h3 _ g3
    subst this
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact memcpy_frame hE parameters body hlk ⟨cl, s.globals, s.memory, s.ffi⟩ rb dst nW
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) h64 hrun
  · rintro rb ⟨l, m', rfl, -⟩
    exact ⟨_, _, _, _, _, rfl⟩
  · rintro l g m ffi v ⟨l', m', heq, hh⟩
    injection heq with _ hg hm hf _
    subst g m ffi
    exact h m' hh

/-- Where a key passed to a table operation may live: inside a registered
free block, or outside the heap. -/
def KeyLoc (Rg : Reg) (keyp kl : Word) : Prop :=
  (∃ lo hi, Rg.B lo hi ∧ lo.toNat ≤ keyp.toNat ∧ keyp.toNat + kl.toNat ≤ hi.toNat) ∨
    2952790016 ≤ keyp.toNat

set_option maxHeartbeats 8000000 in
/-- `jset(t, key, value)` on a live table keeps the world. -/
theorem jset_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "jset" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (t keyp val kl : Word)
    (ht : s.locals "t" = some (.word t)) (hkp : s.locals "key" = some (.word keyp))
    (hv : s.locals "value" = some (.word val)) (hD : Rg.D t kl) (hkey : KeyLoc Rg keyp kl)
    (hk64 : keyp.toNat + kl.toNat < 2 ^ 64) (hW : WorldTJ Rg s.globals s.memory)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m', r = .returned l g' m' s.ffi [.word 0#64] ∧ WorldTJ Rg g' m' ∧
      (∀ x, x ≠ "heap_ptr" → x ≠ "journal_n" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 356 hE.functions (by guest_decl_at 356) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m', r = .returned l g' m' s.ffi [.word 0#64] ∧
    WorldTJ Rg g' m' ∧ (∀ x, x ≠ "heap_ptr" → x ≠ "journal_n" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hDT, hBT, hCT, hNT, hIT⟩ := hW
  obtain ⟨v, hTt, hvkl⟩ := hDT t kl hD
  subst kl
  have hat := hHW.tabs.at_ t v hTt
  obtain ⟨kind, rep, hok⟩ := hat.ok
  obtain ⟨hkl0, -⟩ := hok.wf.hdr
  refine WPs.decCall_retS (fun v0 g0 m0 f0 hret hsh => ?_)
  obtain ⟨hg0, hm0, hf0⟩ := CalleeRet.quiet (htab_get_quiet hE) hret
  subst g0 m0 f0
  obtain ⟨o0, o1, rfl⟩ := struct2_of_shape hsh
  have hpE := hpH.1
  have hp8 := hpH.2
  -- the capacity check
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals "old" (.rStruct [.word o0, .word o1]),
      s.globals, s.memory, s.ffi⟩ ∧ n.toNat < C.toNat) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    rw [eval_global] at hx hy
    dsimp only at hx hy
    rw [hng] at hx
    rw [hCg] at hy
    simp only [Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      by_contra hge
      have : ¬ n < C := fun hl => hge (BitVec.lt_def.mp hl)
      rw [h0] at hwv
      simp [evalPanCmp, this] at hwv
    · exact WPs.call_trap hE
  rintro _ ⟨rfl, hnC⟩
  refine WPs.dec (w := v.kl) (eval_load_rd hE (eval_addc hE 0#64 (by lk [ht])) hkl0) ?_
  refine WPs.decCall_alloc hE (pv := pv) (nv := v.kl) (by lk []) hp hpH (fun qv hq hqH => ?_)
  have hqE := hqH.1
  refine WPs.seqG (fun a => ∃ m1, a = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
      s.locals "old" (.rStruct [.word o0, .word o1])) "klen" (.word v.kl)) "kc" (.word pv),
      updatePanValueMap s.globals "heap_ptr" (.word qv), m1, s.ffi⟩ ∧
      Hull s.memory pv v.kl m1)
    (WPs.call_memcpy_hull hE (dst := pv) (nW := v.kl) (of_eval (by lk [])) (of_eval (by lk []))
      (by omega) (fun m1 hm1 => ⟨m1, rfl, hm1⟩)) ?_
  rintro _ ⟨m1, rfl, hm1⟩
  -- the heap structures after the key copy
  have hpq : pv.toNat ≤ qv.toNat := by omega
  have hW1 : HeapW m1 pv T N J C n :=
    hHW.frame (fun a _ _ hlt => hm1 a (Or.inl (by omega)))
  have hW1q := hW1.mono hpq hqE
  obtain ⟨l1, l2, l3, l4⟩ := id hok.wf.layout
  have hkn : v.keys.toNat ≤ v.nodes.toNat := Nat.le_trans (Nat.le_add_right _ _) l2
  have hfin := hat.fin
  have hKF : KeyFree qv T pv v.kl := by
    refine ⟨hq, fun u w hu => ?_⟩
    have hau := hHW.tabs.at_ u w hu
    obtain ⟨ku, ru, hoku⟩ := hau.ok
    obtain ⟨u1, u2, u3, u4⟩ := hoku.wf.layout
    have hkn' : w.keys.toNat ≤ w.nodes.toNat := Nat.le_trans (Nat.le_add_right _ _) u2
    have := hau.fin
    exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
  have hJhi := hHW.jrn.hi
  have hJlo := hHW.jrn.lo
  have hpvlt := pv.isLt
  have hn1 : (n + 1#64).toNat = n.toNat + 1 := by bv_omega
  have hR : J + n * 32#64 = J + BitVec.ofNat 64 (32 * n.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    omega
  generalize hRd : J + BitVec.ofNat 64 (32 * n.toNat) = R at hR
  have g4J : updatePanValueMap s.globals "heap_ptr" (.word qv) "journal" = some (.word J) := by
    simp (config := { decide := true }) [update_lookup, hJg]
  have g4n : updatePanValueMap s.globals "heap_ptr" (.word qv) "journal_n" = some (.word n) := by
    simp (config := { decide := true }) [update_lookup, hng]
  refine WPs.dec (w := R) (of_eval (by ev [eval_global, g4J, g4n, evalPanOp, hR])) ?_
  refine WPs.seq_store hE (addr := R) (w := t) (by lk []) (of_eval (by lk [ht])) ?_
  refine WPs.seq_store hE (addr := R + 8#64) (w := pv) (eval_addc hE 8#64 (by lk []))
    (of_eval (by lk [])) ?_
  refine WPs.seq_store hE (addr := R + 16#64) (w := o0) (eval_addc hE 16#64 (by lk []))
    (of_eval (by simp (config := { decide := true }) [evalF_rField, evalF_local,
      update_lookup])) ?_
  refine WPs.seq_store hE (addr := R + 24#64) (w := o1) (eval_addc hE 24#64 (by lk []))
    (of_eval (by simp (config := { decide := true }) [evalF_rField, evalF_local,
      update_lookup])) ?_
  refine WPs.seq_assign_global (w := n + 1#64) (of_eval (by ev [eval_global, g4n])) ?_
  have hW2 : HeapW (setCell (setCell (setCell (setCell m1 R t) (R + 8#64) pv) (R + 16#64) o0)
      (R + 24#64) o1) qv T N J C (n + 1#64) :=
    hW1q.jpush hnC hn1 hRd.symm hTt hKF rfl
  -- addresses of the entry cells
  have e0 : R.toNat = J.toNat + 32 * n.toNat := by
    rw [← hRd, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have e1 : (R + 8#64).toNat = J.toNat + 32 * n.toNat + 8 := by
    rw [BitVec.toNat_add, e0]
    simp
    omega
  have e2 : (R + 16#64).toNat = J.toNat + 32 * n.toNat + 16 := by
    rw [BitVec.toNat_add, e0]
    simp
    omega
  have e3 : (R + 24#64).toNat = J.toNat + 32 * n.toNat + 24 := by
    rw [BitVec.toNat_add, e0]
    simp
    omega
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have keep2 : ∀ a : Word, ¬ (J.toNat ≤ a.toNat ∧ a.toNat < J.toNat + 32 * C.toNat) →
      setCell (setCell (setCell (setCell m1 R t) (R + 8#64) pv) (R + 16#64) o0) (R + 24#64) o1 a =
        m1 a := by
    intro a ha
    rw [setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]
  generalize hm2 : setCell (setCell (setCell (setCell m1 R t) (R + 8#64) pv) (R + 16#64) o0)
    (R + 24#64) o1 = m2 at hW2 keep2 ⊢
  have g5p : updatePanValueMap (updatePanValueMap s.globals "heap_ptr" (.word qv)) "journal_n"
      (.word (n + 1#64)) "heap_ptr" = some (.word qv) := by
    simp (config := { decide := true }) [update_lookup]
  have g5J : updatePanValueMap (updatePanValueMap s.globals "heap_ptr" (.word qv)) "journal_n"
      (.word (n + 1#64)) "journal" = some (.word J) := by
    simp (config := { decide := true }) [update_lookup, hJg]
  have g5C : updatePanValueMap (updatePanValueMap s.globals "heap_ptr" (.word qv)) "journal_n"
      (.word (n + 1#64)) "journal_cap" = some (.word C) := by
    simp (config := { decide := true }) [update_lookup, hCg]
  have g5n : updatePanValueMap (updatePanValueMap s.globals "heap_ptr" (.word qv)) "journal_n"
      (.word (n + 1#64)) "journal_n" = some (.word (n + 1#64)) := by
    simp (config := { decide := true }) [update_lookup]
  have g5o : ∀ x, x ≠ "heap_ptr" → x ≠ "journal_n" →
      updatePanValueMap (updatePanValueMap s.globals "heap_ptr" (.word qv)) "journal_n"
        (.word (n + 1#64)) x = s.globals x := by
    intro x h1 h2
    simp [update_lookup, h1, h2]
  generalize hg5 : updatePanValueMap (updatePanValueMap s.globals "heap_ptr" (.word qv))
    "journal_n" (.word (n + 1#64)) = g5 at g5p g5J g5C g5n g5o ⊢
  -- where the key is, relative to the table
  have hkT : keyp.toNat + v.kl.toNat ≤ t.toNat ∨ t.toNat + 88 ≤ keyp.toNat := by
    rcases hkey with ⟨lo, hi, hb, h1, h2⟩ | hge
    · obtain ⟨a1, -⟩ := (hBT lo hi hb).tabI t v hTt
      omega
    · exact Or.inr (by omega)
  have hkB : keyp.toNat + v.kl.toNat ≤ v.keys.toNat ∨
      v.order.toNat + (v.nc.toNat + 1) * 8 ≤ keyp.toNat := by
    rcases hkey with ⟨lo, hi, hb, h1, h2⟩ | hge
    · obtain ⟨-, a2⟩ := (hBT lo hi hb).tabI t v hTt
      omega
    · exact Or.inr (by omega)
  have hkP : keyp.toNat + v.kl.toNat ≤ qv.toNat ∨ 2952790016 ≤ keyp.toNat := by
    rcases hkey with ⟨lo, hi, hb, h1, h2⟩ | hge
    · have := (hBT lo hi hb).hi_
      exact Or.inl (by omega)
    · exact Or.inr hge
  have hat2 := hW2.tabs.at_ t v hTt
  obtain ⟨kind2, rep2, hok2⟩ := hat2.ok
  have hB2 : ∀ lo hi, Rg.B lo hi → FreeOK qv T N J C lo hi :=
    fun lo hi hb => (hBT lo hi hb).mono hpq
  have hC2 : ∀ x w, Rg.Cn x w → Rd m2 x w ∧ x.toNat % 8 = 0 ∧
      ∃ hi : Word, hi.toNat = x.toNat + 8 ∧ FreeOK qv T N J C x hi := by
    intro x w hc
    obtain ⟨hr, h8, hi, hhi, hf⟩ := hCT x w hc
    refine ⟨?_, h8, hi, hhi, hf.mono hpq⟩
    have hfh := hf.hi_
    unfold Rd at hr ⊢
    rw [keep2 x (by rcases hf.jrn with h3 | h3 <;> omega), hm1 x (Or.inl (by omega))]
    exact hr
  have hI2 : ImOK Rg m2 qv T N J C := by
    refine hIT.frame hpq (fun x hx => ?_)
    obtain ⟨b1, b2, b3⟩ := hIT.cell_bounds hHW hx
    rw [keep2 x ?_, hm1 x (Or.inl (by omega))]
    rcases hx with (⟨a, k, hN, hk, hx⟩ | ⟨-, lo, hi, hI, h1, h2⟩) | ⟨u, hu, hx⟩
    · have hin := seg_cell_in (hHW.nodes.at_ a k hN) hk hx
      rcases hHW.jn a k hN with h3 | h3 <;> omega
    · rcases (hIT.free lo hi hI).2.jrn with h3 | h3 <;> omega
    · obtain ⟨-, c1, c2, hi, e, hf⟩ := tr_cell_in hIT hu hx
      rcases hf.jrn with h3 | h3 <;> omega
  refine WPs.seqG (fun a => ∃ l g' m', a = ⟨l, g', m', s.ffi⟩ ∧ WorldTJ Rg g' m' ∧
      (∀ x, x ≠ "heap_ptr" → x ≠ "journal_n" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr)
    (WPs.call_runs (fun rb => ∃ l g' m', rb = .returned l g' m' s.ffi [.word 0#64] ∧
        SetPost m2 t qv v s.ffi rb ∧ ∀ x, x ≠ "heap_ptr" → g' x = g5 x) ?_ ?_ ?_) ?_
  · intro parameters cbody values cl hlk hvalues hbind rb hrun
    have hparams := (fun_of_index 138 hE.functions (by guest_decl_at 138) (by decide +kernel)
      hlk).2
    simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, ht, hkp, hv] at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    have honly := htab_set_only hE parameters cbody hlk
    rcases htab_set_exec hE parameters cbody hlk ⟨cl, g5, m2, s.ffi⟩ rb t keyp val qv v kind2
      rep2 (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hok2 g5p hqH hat2.fin hat2.t8 hk64 hkT hkB hkP hrun with hst | hsp
    · exact Or.inl hst
    · obtain ⟨fuel, k, hrun'⟩ := hrun
      have hrel := honly fuel ⟨cl, g5, m2, s.ffi⟩ rb k hrun'
      obtain ⟨l, g', m', v', kind', rep', rfl, rest⟩ := hsp
      refine Or.inr ⟨l, g', m', rfl, ⟨l, g', m', v', kind', rep', rfl, rest⟩, fun x hx => ?_⟩
      exact hrel x (by simp [hx])
  · rintro rb ⟨l, g', m', rfl, -, -⟩
    exact ⟨_, _, _, _, _, rfl⟩
  · rintro l g m ffi w ⟨l', g', m', heq, hsp, hgl⟩
    injection heq with _ hg hm hf _
    subst g m ffi
    obtain ⟨l0, g0, m0, v', kind', rep', heq2, rest⟩ := hsp
    injection heq2 with hl0 hg0 hm0 _ _
    subst hl0 hg0 hm0
    obtain ⟨pv', v'', hp', hpH', hs⟩ := TabStep.of_set hW2.tabs hTt hqH
      (⟨_, _, _, v', kind', rep', rfl, rest⟩ :
        SetPost m2 t qv v s.ffi (.returned l' g' m' s.ffi [.word 0#64]))
    refine ⟨_, g', m', rfl, worldTJ_step hp' hpH' hgl g5J g5C g5n hW2 hDT hB2 hC2 hNT hI2
      (Nat.le_refl _) hs, fun x h1 h2 => (hgl x h1).trans (g5o x h1 h2), fun addr ha => ?_⟩
    rw [hs.out addr ha, keep2 addr (by unfold HBASE at ha hJlo; omega),
      hm1 addr (by have hlo := hat.lo; unfold HBASE at ha hlo; omega)]
  rintro _ ⟨l, g', m', rfl, hW', hgl', hout'⟩
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  exact ⟨_, _, _, rfl, hW', hgl', hout'⟩

end InitECandidate.Solver.GuestBound
