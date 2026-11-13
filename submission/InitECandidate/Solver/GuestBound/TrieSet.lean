import InitECandidate.Solver.GuestBound.TrieDelNode

/-!
# `mpt_set` against the world invariant

`mpt_set(m, key, klen, vptr, vlen)` turns the key into nibbles, deletes or
inserts below the root of the handle `m`, and stores the new root. The step
that produces the nibble key is taken as an interface (`NibKeySpec`): its
hashed branch needs the memory footprint of `keccak256`, which is not proved
here.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- What `mpt_nibble_key` must guarantee: the world invariant is kept in a
registry that grew, and the returned nibble key lies in an immutable block.
`Pre` is whatever the eventual proof needs of the registry and the globals
(the hashing buffers). -/
def NibKeySpec (E : Env σ) (Pre : Reg → (VarName → Option (PanValue Word)) → Prop) : Prop :=
  ∀ (Rg : Reg) (s : St σ) (e1 e2 e3 : Exp Word) (v : PanValue Word)
    (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (ffi : FfiState σ),
    CalleeRet E s "mpt_nibble_key" [e1, e2, e3] [v] g m ffi →
    WorldTJ Rg s.globals s.memory → Pre Rg s.globals →
    ∃ nb nl R', v = .rStruct [.word nb, .word nl] ∧ ffi = s.ffi ∧ Rg.Le R' ∧ WorldTJ R' g m ∧
      (nl ≠ 0#64 → ∃ lo hi, R'.Im lo hi ∧ lo.toNat ≤ nb.toNat ∧
        nb.toNat + nl.toNat ≤ hi.toNat) ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr

section rets

variable {v : PanValue Word} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ} {Rg : Reg}

theorem insert_node_ret (hE : GuestEnv E) {e1 e2 e3 e4 e5 e6 : Exp Word}
    {node key klen level vptr vlen : Word}
    (h : CalleeRet E s "_mpt_insert_node" [e1, e2, e3, e4, e5, e6] [v] g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word node)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word key)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word klen)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word level)
    (h5 : ∀ y, E.eval s e5 = some y → y = .word vptr)
    (h6 : ∀ y, E.eval s e6 = some y → y = .word vlen)
    (hW : WorldTJ Rg s.globals s.memory) (hnd : node = 0#64 ∨ ∃ k, Rg.Kd node k)
    (hLn : node ≠ 0#64 → Rg.Lv node level.toNat) (hlv : level.toNat ≤ klen.toNat)
    (hblk : klen ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat) :
    ∃ a R' k, v = .word a ∧ ffi = s.ffi ∧ Rg.Le R' ∧ R'.Kd a k ∧ k ≠ 0#64 ∧
      R'.Lv a level.toNat ∧ WorldTJ R' g m ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 275 hE.functions (by guest_decl_at 275) (by decide +kernel)
    hlookup).2
  obtain ⟨y1, vs1, g1, hr1, rfl⟩ := evalArgs_cons_inv hvalues
  obtain ⟨y2, vs2, g2, hr2, rfl⟩ := evalArgs_cons_inv hr1
  obtain ⟨y3, vs3, g3, hr3, rfl⟩ := evalArgs_cons_inv hr2
  obtain ⟨y4, vs4, g4, hr4, rfl⟩ := evalArgs_cons_inv hr3
  obtain ⟨y5, vs5, g5, hr5, rfl⟩ := evalArgs_cons_inv hr4
  obtain ⟨y6, vs6, g6, hr6, rfl⟩ := evalArgs_cons_inv hr5
  rw [evalArgs_nil] at hr6
  simp only [Option.some.injEq] at hr6
  subst hr6
  have := h1 _ g1
  subst this
  have := h2 _ g2
  subst this
  have := h3 _ g3
  subst this
  have := h4 _ g4
  subst this
  have := h5 _ g5
  subst this
  have := h6 _ g6
  subst this
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases mpt_insert_node_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    node key klen level vptr vlen
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hnd hLn hlv hblk hrun with
    hst | ⟨l', g', m', a, R', k, heq, hle, hk, hk0, hlv', hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, R', k, rfl, rfl, hle, hk, hk0, hlv', hw, hg, hm⟩

theorem delete_node_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word}
    {node key klen level sp0 fv : Word}
    (h : CalleeRet E s "_mpt_delete_node" [e1, e2, e3, e4] [v] g m ffi)
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
    ∃ a R', v = .word a ∧ ffi = s.ffi ∧ Rg.Le R' ∧
      (a = 0#64 ∨ ∃ k, R'.Kd a k ∧ k ≠ 0#64 ∧ R'.Lv a level.toNat) ∧ WorldTJ R' g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 279 hE.functions (by guest_decl_at 279) (by decide +kernel)
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
  rcases delete_node_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    node key klen level sp0 fv
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hnd hLn hlv hkey hsp hfv hfs hF hrun with
    hst | ⟨l', g', m', a, R', heq, hle, ha, hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, R', rfl, rfl, hle, ha, hw, hg, hm⟩

end rets

/-- Result of `mpt_set`. -/
def SetQ (Rg : Reg) (s : St σ) (sp0 : Word) (r : Result σ) : Prop :=
  ∃ l g' m' R', r = .returned l g' m' s.ffi [.word 0#64] ∧ Rg.Le R' ∧ WorldTJ R' g' m' ∧
    (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) → m' addr = s.memory addr

theorem SetQ.restore {Rg : Reg} {s : St σ} {sp0 : Word} {r : Result σ} (x : VarName)
    (old : Option (PanValue Word)) (h : SetQ Rg s sp0 r) :
    SetQ Rg s sp0 (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g', m', R', rfl, hq⟩ := h
  exact ⟨_, g', m', R', rfl, hq⟩

set_option maxHeartbeats 16000000 in
theorem mpt_set_world (hE : GuestEnv E) {Pre : Reg → (VarName → Option (PanValue Word)) → Prop}
    (hNK : NibKeySpec E Pre) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "mpt_set" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (mh key klen vptr vlen sp0 fv : Word)
    (hmv : s.locals "m" = some (.word mh)) (hkeyv : s.locals "key" = some (.word key))
    (hklen : s.locals "klen" = some (.word klen)) (hvp : s.locals "vptr" = some (.word vptr))
    (hvl : s.locals "vlen" = some (.word vlen))
    (hW : WorldTJ Rg s.globals s.memory) (hT : Rg.Tr mh) (hPre : Pre Rg s.globals)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ SetQ Rg s sp0 r := by
  have hbody := (fun_of_index 280 hE.functions (by guest_decl_at 280) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (SetQ Rg s sp0)) r h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  refine WPs.decCall_ret (fun v g1 m1 f1 hret => ?_)
  obtain ⟨nb, nl, R1, rfl, rfl, hle1, hW1, hblk, hg1, hm1⟩ := hNK Rg s _ _ _ _ _ _ _ hret hW hPre
  refine WPs.conseq (Q' := SetQ Rg s sp0) ?_ (fun r h => h.restore _ _)
  have hT1 := hle1.Tr _ hT
  obtain ⟨root, sec, r1, -, hroot, hlo, htop, h8, hl0⟩ := hW1.root hT1
  refine WPs.dec (w := root) (eval_load_rd hE (eval_addc hE (a := mh) 0#64 (by lk [hmv]))
    (by rw [BitVec.add_zero]; exact r1)) ?_
  refine WPs.conseq (Q' := SetQ Rg s sp0) ?_ (fun r h => h.restore _ _)
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qm : L "m" = some (.word mh) := by rw [hLL]; lk [hmv]
  have qvp : L "vptr" = some (.word vptr) := by rw [hLL]; lk [hvp]
  have qvl : L "vlen" = some (.word vlen) := by rw [hLL]; lk [hvl]
  have qnk : L "nk" = some (.rStruct [.word nb, .word nl]) := by rw [hLL]; lk []
  have qroot : L "root" = some (.word root) := by rw [hLL]; lk []
  clear hLL
  have hz : (0#64 : Word).toNat = 0 := by decide
  have enb : ∀ y, E.eval (⟨L, g1, m1, s.ffi⟩ : St σ) (.rField 0 (.var .local "nk")) = some y →
      y = .word nb := of_eval (by
    simp (config := { decide := true }) [evalF_rField, evalF_local, qnk])
  have enl : ∀ y, E.eval (⟨L, g1, m1, s.ffi⟩ : St σ) (.rField 1 (.var .local "nk")) = some y →
      y = .word nl := of_eval (by
    simp (config := { decide := true }) [evalF_rField, evalF_local, qnk])
  have hm1w : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
      m1 addr = s.memory addr := by
    intro addr ha
    exact hm1 addr (by rcases ha with h1 | h1 <;> [exact Or.inl h1; exact Or.inr (by omega)])
  refine WPs.seqG (fun a => ∃ rt R2 g2 m2, a = ⟨updatePanValueMap L "root" (.word rt), g2, m2,
      s.ffi⟩ ∧ R1.Le R2 ∧ (rt = 0#64 ∨ ∃ k, R2.Kd rt k ∧ R2.Lv rt 0) ∧ WorldTJ R2 g2 m2 ∧
      (∀ x, x ≠ "heap_ptr" → g2 x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) →
        m2 addr = s.memory addr) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · -- insert
      refine WPs.callA_ret (fun v g2 m2 f2 hret2 => ?_)
      obtain ⟨a, R2, k, rfl, rfl, hle2, hk, hk0, hlv', hW2, hg2, hm2⟩ := insert_node_ret hE hret2
        (node := root) (key := nb) (klen := nl) (level := 0#64) (vptr := vptr) (vlen := vlen)
        (of_eval (by lk [qroot])) enb enl (of_eval (eval_const _ _)) (of_eval (by lk [qvp]))
        (of_eval (by lk [qvl])) hW1 hroot (fun h0 => by rw [hz]; exact hl0 h0)
        (by rw [hz]; exact Nat.zero_le _) hblk
      rw [hz] at hlv'
      exact ⟨a, R2, g2, m2, rfl, hle2, Or.inr ⟨k, hk, hlv'⟩, hW2,
        fun x hx => (hg2 x hx).trans (hg1 x hx), fun addr ha => by
          rw [hm2 addr (by rcases ha with h1 | h1 <;> [exact Or.inl h1; exact Or.inr (by omega)])]
          exact hm1w addr ha⟩
    · -- delete
      refine WPs.callA_ret (fun v g2 m2 f2 hret2 => ?_)
      obtain ⟨a, R2, rfl, rfl, hle2, ha, hW2, hg2, hm2⟩ := delete_node_ret hE hret2
        (node := root) (key := nb) (klen := nl) (level := 0#64) (sp0 := sp0) (fv := fv)
        (of_eval (by lk [qroot])) enb enl (of_eval (eval_const _ _)) hW1 hroot
        (fun h0 => by rw [hz]; exact hl0 h0) (by rw [hz]; exact Nat.zero_le _) hblk
        (by dsimp only; rw [hg1 _ (by decide)]; exact hsp)
        (by dsimp only; rw [hg1 _ (by decide)]; exact hfv) hfs hF
      rw [hz] at ha
      refine ⟨a, R2, g2, m2, rfl, hle2, ?_, hW2, fun x hx => (hg2 x hx).trans (hg1 x hx),
        fun addr hA => (hm2 addr hA).trans (hm1w addr hA)⟩
      rcases ha with h0 | ⟨k, hk, -, hl⟩
      · exact Or.inl h0
      · exact Or.inr ⟨k, hk, hl⟩
  rintro _ ⟨rt, R2, g2, m2, rfl, hle2, hrt, hW2, hg2, hm2⟩
  have hT2 := hle2.Tr _ hT1
  obtain ⟨-, -, -, -, -, hlo2, htop2, -, -⟩ := hW2.root hT2
  have W3 := hW2.set_root (c := rt) hT2
    (by
      rcases hrt with h0 | ⟨k, hk, -⟩
      · exact Or.inl h0
      · exact Or.inr (hW2.kd hk).1)
    (fun h0 => by
      rcases hrt with h1 | ⟨k, -, hl⟩
      · exact absurd h1 h0
      · exact hl)
  refine WPs.seq_store hE (addr := mh + 0#64) (w := rt)
    (eval_addc hE 0#64 (by lk [qm])) (of_eval (by lk [])) ?_
  refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  rw [BitVec.add_zero]
  refine ⟨_, g2, _, R2, rfl, hle1.trans hle2, W3, hg2, fun addr ha => ?_⟩
  show setCell m2 mh rt addr = _
  rw [setCell_ne _ (NE (by unfold HBASE at ha hlo2; omega))]
  exact hm2 addr ha

end InitECandidate.Solver.GuestBound
