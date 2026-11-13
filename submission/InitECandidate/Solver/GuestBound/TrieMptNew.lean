import InitECandidate.Solver.GuestBound.TrieDecWrap
import InitECandidate.Solver.GuestBound.TrieHandle
import InitECandidate.Solver.GuestBound.Keccak256Frame

/-!
# Trie handles from a witness: `mpt_new`, `decode_witness_to_mpt`, `mpt_from_witness`

A trie handle is a 16-byte record: the root node (null, or a node at level 0)
and the `secured` flag.  `WorldTJ.fresh_handle` registers a freshly allocated
and written record as a handle without touching the rest of the registry.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The registry with one more trie handle. -/
def Reg.addTr1 (Rg : Reg) (t : Word) : Reg :=
  { Rg with Tr := fun x => Rg.Tr x ∨ x = t }

theorem Reg.Le.addTr1 (Rg : Reg) (t : Word) : Rg.Le (Rg.addTr1 t) :=
  ⟨rfl, rfl, fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h, fun _ _ _ h => h, fun _ h => Or.inl h⟩

section world

variable {Rg : Reg} {g g' : VarName → Option (PanValue Word)}
  {m m' : Word → Option (PanValue Word)}

/-- A record allocated at the heap pointer and written becomes a trie handle. -/
theorem WorldTJ.fresh_handle {pv pv1 root sec : Word} (h : WorldTJ Rg g m)
    (hp : g "heap_ptr" = some (.word pv)) (hp1 : g' "heap_ptr" = some (.word pv1))
    (hpH1 : InHeap pv1) (hle : pv.toNat + 16 ≤ pv1.toNat)
    (hg : ∀ x, x ≠ "heap_ptr" → g' x = g x)
    (hm : ∀ a : Word, a.toNat < pv.toNat → m' a = m a)
    (r1 : Rd m' pv root) (r2 : Rd m' (pv + 8#64) sec)
    (hc : root = 0#64 ∨ Rg.Nd root) (hl0 : root ≠ 0#64 → Rg.Lv root 0) :
    WorldTJ (Rg.addTr1 pv) g' m' := by
  obtain ⟨pv0, T, N, J, C, n, hp0, hpH0, hJg, hCg, hng, hW0, hD, hB0, hCn0, hNd, hIm0⟩ := h
  have e : pv0 = pv := by
    rw [hp] at hp0
    simpa using hp0.symm
  rw [e] at hpH0 hW0 hB0 hCn0 hIm0
  have hJlo := hW0.jrn.lo
  have hJhi := hW0.jrn.hi
  have hpE := hpH0.1
  have hbase : HBASE ≤ pv.toNat := by omega
  have hpE1 := hpH1.1
  have hle' : pv.toNat ≤ pv1.toNat := by omega
  have hW : HeapW m' pv1 T N J C n :=
    (hW0.frame (fun a h8 _ hlt => hm a hlt)).mono hle' hpE1
  have hIm : ImOK Rg m' pv1 T N J C := hIm0.frame hle' (fun x hx => by
    obtain ⟨b1, b2, b3⟩ := hIm0.cell_bounds hW0 hx
    exact hm x b3)
  have e16 : (pv + 16#64).toNat = pv.toNat + 16 := by
    rw [BitVec.toNat_add, show (16#64 : Word).toNat = 16 from rfl]
    omega
  refine ⟨pv1, T, N, J, C, n, hp1, hpH1, by rw [hg _ (by decide)]; exact hJg,
    by rw [hg _ (by decide)]; exact hCg, by rw [hg _ (by decide)]; exact hng, hW, hD,
    fun lo hi hb => (hB0 lo hi hb).mono hle', fun x w hc => ?_, hNd,
    { hIm with
      trf := fun u hu => ?_
      trv := fun u hu => ?_
      offT := fun a b u hab hu => ?_
      offC := fun x w u hcx hu => ?_
      offI := fun a b u hI hu => ?_
      offTT := fun t u ht hu => ?_ }⟩
  · obtain ⟨hr, h8, hi, hhi', hf⟩ := hCn0 x w hc
    refine ⟨?_, h8, hi, hhi', hf.mono hle'⟩
    have := hf.hi_
    unfold Rd at hr ⊢
    rw [hm x (by omega)]
    exact hr
  · rcases hu with hu | hu
    · exact hIm.trf u hu
    · rw [hu]
      exact ⟨hpH0.2, pv + 16#64, e16, FreeOK.fresh hW0 (Nat.le_refl _) (by omega) hbase⟩
  · rcases hu with hu | hu
    · exact hIm.trv u hu
    · rw [hu]
      refine ⟨root, sec, r1, r2, ?_, hl0⟩
      rcases hc with rfl | hc
      · exact Or.inl rfl
      · exact Or.inr (hNd root hc)
  · rcases hu with hu | hu
    · exact hIm.offT a b u hab hu
    · rw [hu]
      have := (hB0 a b hab).hi_
      exact Or.inl this
  · rcases hu with hu | hu
    · exact hIm.offC x w u hcx hu
    · rw [hu]
      obtain ⟨-, -, hi, hhi, hf⟩ := hCn0 x w hcx
      have := hf.hi_
      exact Or.inl (by omega)
  · rcases hu with hu | hu
    · exact hIm.offI a b u hI hu
    · rw [hu]
      have := (hIm0.free a b hI).2.hi_
      exact Or.inl this
  · rcases ht with ht | ht
    · rcases hu with hu | hu
      · exact hIm.offTT t u ht hu
      · rw [hu]
        obtain ⟨-, hi, e', hf⟩ := hIm0.trf t ht
        have := hf.hi_
        exact Or.inr (Or.inl (by omega))
    · rcases hu with hu | hu
      · rw [ht]
        obtain ⟨-, hi, e', hf⟩ := hIm0.trf u hu
        have := hf.hi_
        exact Or.inr (Or.inr (by omega))
      · exact Or.inl (ht.trans hu.symm)

end world

/-- What `mpt_new` guarantees: a new handle. -/
def MnQ (Rg : Reg) (s : St σ) (r : Result σ) : Prop :=
  ∃ l g m t, r = .returned l g m s.ffi [.word t] ∧ WorldTJ (Rg.addTr1 t) g m ∧
    (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m addr = s.memory addr

set_option maxHeartbeats 8000000 in
theorem mpt_new_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "mpt_new" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (root sec : Word)
    (hr : s.locals "root_node" = some (.word root)) (hs : s.locals "secured" = some (.word sec))
    (hW : WorldTJ Rg s.globals s.memory) (hres : DRes Rg 0 root) (h : Runs E s body r) :
    Stopped r ∨ MnQ Rg s r := by
  have hbody := (fun_of_index 268 hE.functions (by guest_decl_at 268) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (MnQ Rg s)) r h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  obtain ⟨pv, hp, hpH, hpB⟩ := hW.heap_ptr
  have hpE := hpH.1
  refine WPs.decCall_alloc hE (pv := pv) (nv := 16#64) (eval_const _ _) hp hpH
    (fun qv hq hqH => ?_)
  have hq' : pv.toNat + 16 ≤ qv.toNat := hq
  have hqE := hqH.1
  have a8 : (pv + 8#64).toNat = pv.toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64 : Word).toNat = 8 from rfl]
    omega
  have a0 : (pv + 0#64) = pv := by simp
  refine WPs.seq_store hE (addr := pv + 0#64) (w := root) (eval_addc hE 0#64 (by lk []))
    (of_eval (by lk [hr])) ?_
  refine WPs.seq_store hE (addr := pv + 8#64) (w := sec) (eval_addc hE 8#64 (by lk []))
    (of_eval (by lk [hs])) ?_
  refine WPs.ret (w := pv) (of_eval (by lk [])) ?_
  simp only [restorePanValueFfiLocal]
  rw [a0]
  have keep : ∀ a : Word, ¬ (pv.toNat ≤ a.toNat ∧ a.toNat < pv.toNat + 16) →
      setCell (setCell s.memory pv root) (pv + 8#64) sec a = s.memory a := by
    intro a ha
    rw [setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]
  refine ⟨_, _, _, pv, rfl, WorldTJ.fresh_handle hW hp (by simp [updatePanValueMap]) hqH hq'
    (fun x hx => by simp [update_lookup, hx]) (fun a ha => keep a (by omega))
    ((Rd.here s.memory pv root).frame _ (NE (by omega))) (Rd.here _ _ _)
    (by
      rcases hres with h0 | ⟨k, hK, -⟩
      · exact Or.inl h0
      · exact Or.inr (hW.kd hK).1)
    (fun h0 => by
      rcases hres with h1 | ⟨k, -, hL⟩
      · exact absurd h1 h0
      · exact hL),
    fun x hx => by simp [update_lookup, hx],
    fun addr ha => keep addr (by unfold HBASE at ha hpB; omega)⟩

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

/-- What a returning `mpt_new` leaves. -/
theorem mpt_new_ret (hE : GuestEnv E) {Rg : Reg} {e1 e2 : Exp Word} {root sec : Word}
    (h : CalleeRet E s "mpt_new" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word root)) (h2 : E.eval s e2 = some (.word sec))
    (hW : WorldTJ Rg s.globals s.memory) (hres : DRes Rg 0 root) :
    ∃ t, vs = [.word t] ∧ ffi = s.ffi ∧ WorldTJ (Rg.addTr1 t) g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 268 hE.functions (by guest_decl_at 268) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases mpt_new_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    root sec (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hW hres hrun
    with hst | ⟨l', g', m', t, heq, hW', hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨t, rfl, rfl, hW', hg, hm⟩

/-- What a returning `_decode_witness_node` leaves. -/
theorem decode_node_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {R0 : Reg}
    {dbv pw nw sp0 fv : Word} {v : PanValue Word} (L0 : Nat)
    (h : CalleeRet E s "_decode_witness_node" [e1, e2, e3] [v] g m ffi)
    (h1 : E.eval s e1 = some (.word dbv)) (h2 : E.eval s e2 = some (.word pw))
    (h3 : E.eval s e3 = some (.word nw)) (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) :
    ∃ (res : Word) (R : Reg), v = .word res ∧ ffi = s.ffi ∧ R0.Le R ∧ WorldTJ R g m ∧
      DRes R L0 res ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 264 hE.functions (by guest_decl_at 264) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases decode_node_world hE parameters body hlookup R0 ⟨cl, s.globals, s.memory, s.ffi⟩ _
    dbv pw nw sp0 fv L0
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hsp hfv hfs hF hrun with hst | ⟨l', g', m', res, R, heq, hle, hW', hres, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨res, R, rfl, rfl, hle, hW', hres, hg, hm⟩

end rets


/-- What `decode_witness_to_mpt` guarantees: a root at level 0 (or null). -/
def DwQ (R0 : Reg) (s : St σ) (sp0 : Word) (r : Result σ) : Prop :=
  ∃ l g m, ∃ (res : Word) (R : Reg), r = .returned l g m s.ffi [.word res] ∧ R0.Le R ∧
    WorldTJ R g m ∧ DRes R 0 res ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) → m addr = s.memory addr

theorem DwQ.restore {R0 : Reg} {sp0 : Word} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : DwQ R0 s sp0 r) : DwQ R0 s sp0 (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g, m, res, R, rfl, hk⟩ := h
  exact ⟨_, g, m, res, R, rfl, hk⟩

set_option maxHeartbeats 16000000 in
theorem decode_witness_to_mpt_world (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "decode_witness_to_mpt" E.functions = some (parameters, body))
    (R0 : Reg) (s : St σ) (r : Result σ) (dbv rh sp0 fv : Word)
    (hdb : s.locals "db" = some (.word dbv)) (hrh : s.locals "root_hash" = some (.word rh))
    (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ DwQ R0 s sp0 r := by
  have hbody := (fun_of_index 265 hE.functions (by guest_decl_at 265) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (DwQ R0 s sp0)) r h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have dqm : ∀ r, DwQ R0 s sp0 r → DwQ R0 s sp0 r := fun _ h => h
  refine WPs.decCall_ret (fun v g m ffi hret =>
    WPs.conseq (Q' := DwQ R0 s sp0) ?_ (fun r h => h.restore))
  obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet
    (keepFn_sound (quietKeeper E) hE.functions 1 "memeq" memeq_quiet) hret
  subst g m ffi
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals "is_empty" v, s.globals, s.memory,
      s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · exact WPs.ret (w := 0#64) (of_eval (eval_const _ _))
        ⟨_, _, _, 0#64, R0, rfl, Reg.Le.refl R0, hW, Or.inl rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  intro a ha
  rw [ha]
  clear ha a
  refine WPs.decCall_retS (fun vr g m ffi hret hsh =>
    WPs.conseq (Q' := DwQ R0 s sp0) ?_ (fun r h => h.restore))
  obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet (nodedb_lookup_quiet hE) hret
  subst g m ffi
  obtain ⟨q0, q1, q2, rfl⟩ := struct3_of_shape hsh
  refine WPs.guard_quiet (mpt_fail_quiet hE) ?_
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qdb : L "db" = some (.word dbv) := by rw [hLL]; lk [hdb]
  have qrh : L "root_hash" = some (.word rh) := by rw [hLL]; lk [hrh]
  have qr : L "r" = some (.rStruct [.word q0, .word q1, .word q2]) := by rw [hLL]; lk []
  clear hLL
  refine WPs.decCall_ret (fun vn g m ffi hret =>
    WPs.conseq (Q' := DwQ R0 s sp0) ?_ (fun r h => h.restore))
  obtain ⟨res, R, rfl, rfl, hle, hW', hres, hg, hm⟩ := decode_node_ret hE 0 hret
    (dbv := dbv) (pw := q1) (nw := q2) (by lk [qdb])
    (by rw [eval_rField _ 1 "r" _ qr]; rfl) (by rw [eval_rField _ 2 "r" _ qr]; rfl)
    hW hsp hfv hfs hF
  dsimp only at hg hm
  refine WPs.seqG (fun a => ∃ L' g' m', a = ⟨L', g', m', s.ffi⟩ ∧
      L' "nd" = some (.word res) ∧ WorldTJ R g' m' ∧
      (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m' addr = s.memory addr)
    (WPs.ite_both (fun w hw => ?_)) ?_
  · split
    · exact WPs.skip ⟨_, _, _, rfl, by lk [], hW', hg, hm⟩
    · rename_i hw0
      obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
      simp (config := { decide := true }) only [evalF_local, update_lookup, if_true, eval_const,
        Option.some.injEq, PanValue.word.injEq] at hx hy
      subst hx hy
      have hr0 : res ≠ 0#64 := by
        rintro rfl
        apply hw0
        rw [hwv]
        simp [evalPanCmp]
      obtain ⟨k, hK, -⟩ : ∃ k, R.Kd res k ∧ R.Lv res 0 := by
        rcases hres with h0 | h0
        · exact absurd h0 hr0
        · exact h0
      obtain ⟨pv, hp, hpH, hpB⟩ := hW'.heap_ptr
      have hpE := hpH.1
      refine WPs.decCall_alloc hE (pv := pv) (nv := 32#64) (eval_const _ _) hp hpH
        (fun qv hq hqH => ?_)
      have hq' : pv.toNat + 32 ≤ qv.toNat := hq
      have hqE := hqH.1
      refine WPs.seq_call_ret (fun vs g2 m2 f2 hret2 => ?_)
      obtain ⟨hg2, hf2, hhull⟩ := memcpy_hull_ret hE hret2 (dst := pv) (nW := 32#64)
        (v2 := .word rh) (by lk []) (by lk [qrh]) (eval_const _ _)
        (by rw [show (32#64 : Word).toNat = 32 from rfl]; omega)
      subst hg2 hf2
      have h32 : (32#64 : Word).toNat = 32 := rfl
      have hW2 : WorldTJ R (updatePanValueMap g "heap_ptr" (.word qv)) m2 :=
        WorldTJ.grow hW' hp (by simp [updatePanValueMap]) hqH (by omega)
          (fun x h1 _ => by simp [update_lookup, h1])
          (fun a ha => hhull a (Or.inl (by have := hpH.2; omega)))
      obtain ⟨-, -, hrlo, hrhi, -⟩ := hW2.kd hK
      have hsz := nodeSize_ge k
      have e24 : (res + 24#64).toNat = res.toNat + 24 := by
        rw [BitVec.toNat_add, show (24#64 : Word).toNat = 24 from rfl]
        omega
      refine WPs.store hE (addr := res + 24#64) (w := pv) (eval_addc hE 24#64 (by lk []))
        (of_eval (by lk [])) ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨_, _, _, rfl,
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
        hW2.cache_store pv (c := 24) (Or.inr (Or.inr rfl)) hK,
        fun x hx => by
          simp only [update_lookup]
          rw [if_neg (by simpa using hx)]
          exact hg x hx,
        fun addr ha => ?_⟩
      have n1 : addr ≠ res + 24#64 := NE (by unfold HBASE at ha hrlo; omega)
      show setCell m2 (res + 24#64) pv addr = _
      rw [setCell_ne _ n1, hhull addr (by unfold HBASE at ha hpB; rw [h32]; omega)]
      exact hm addr ha
  rintro _ ⟨L', g', m', rfl, qnd, hW3, hg3, hm3⟩
  refine WPs.ret (w := res) (of_eval (by lk [qnd])) ?_
  exact ⟨_, g', m', res, R, rfl, hle, hW3, hres, hg3, hm3⟩

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

/-- What a returning `decode_witness_to_mpt` leaves. -/
theorem decode_witness_to_mpt_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {R0 : Reg}
    {dbv rh sp0 fv : Word} {v : PanValue Word}
    (h : CalleeRet E s "decode_witness_to_mpt" [e1, e2] [v] g m ffi)
    (h1 : E.eval s e1 = some (.word dbv)) (h2 : E.eval s e2 = some (.word rh))
    (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) :
    ∃ (res : Word) (R : Reg), v = .word res ∧ ffi = s.ffi ∧ R0.Le R ∧ WorldTJ R g m ∧
      DRes R 0 res ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 265 hE.functions (by guest_decl_at 265) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases decode_witness_to_mpt_world hE parameters body hlookup R0
    ⟨cl, s.globals, s.memory, s.ffi⟩ _ dbv rh sp0 fv
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hsp hfv hfs hF hrun with hst | ⟨l', g', m', res, R, heq, hle, hW', hres, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨res, R, rfl, rfl, hle, hW', hres, hg, hm⟩

end rets

/-- What `mpt_from_witness` guarantees: a trie handle in a larger registry. -/
def MfQ (R0 : Reg) (s : St σ) (sp0 : Word) (r : Result σ) : Prop :=
  ∃ l g m, ∃ (t : Word) (R : Reg), r = .returned l g m s.ffi [.word t] ∧ R0.Le R ∧ R.Tr t ∧
    WorldTJ R g m ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) → m addr = s.memory addr

set_option maxHeartbeats 8000000 in
theorem mpt_from_witness_world (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "mpt_from_witness" E.functions = some (parameters, body))
    (R0 : Reg) (s : St σ) (r : Result σ) (dbv rh sec sp0 fv : Word)
    (hdb : s.locals "db" = some (.word dbv)) (hrh : s.locals "root_hash" = some (.word rh))
    (hsec : s.locals "secured" = some (.word sec))
    (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ MfQ R0 s sp0 r := by
  have hbody := (fun_of_index 269 hE.functions (by guest_decl_at 269) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (MfQ R0 s sp0)) r h
  refine WPs.decCall_ret (fun v g m ffi hret =>
    WPs.conseq (Q' := MfQ R0 s sp0) ?_ (fun r h => by
      obtain ⟨l, g, m, t, R, rfl, hk⟩ := h
      exact ⟨_, g, m, t, R, rfl, hk⟩))
  obtain ⟨res, R, rfl, rfl, hle, hW', hres, hg, hm⟩ := decode_witness_to_mpt_ret hE hret
    (dbv := dbv) (rh := rh) (by lk [hdb]) (by lk [hrh]) hW hsp hfv hfs hF
  refine WPs.tail_call (fun vs g2 m2 f2 hret2 l => ?_)
  obtain ⟨t, rfl, hf2, hW2, hg2, hm2⟩ := mpt_new_ret hE hret2 (root := res) (sec := sec)
    (by lk []) (by lk [hsec]) hW' hres
  try dsimp only at hf2 hg2 hm2
  subst hf2
  have hsp0 := sp0.isLt
  exact ⟨l, g2, m2, t, R.addTr1 t, rfl, hle.trans (Reg.Le.addTr1 R t), Or.inr rfl, hW2,
    fun x hx => (hg2 x hx).trans (hg x hx),
    fun addr ha => (hm2 addr (by omega)).trans (hm addr ha)⟩

end InitECandidate.Solver.GuestBound
