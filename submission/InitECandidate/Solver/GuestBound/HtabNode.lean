import InitECandidate.Solver.GuestBound.HtabGrowInv

/-!
# Hash tables: `htab_new_node`

A node index comes from the free list, or from the never-used tail after
growing the table when it is full.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `htab_grow(t)` as a statement. -/
theorem WPs.call_grow (hE : GuestEnv E) {t pv : Word} {v : HtabV} {kind : Nat → NodeKind}
    (ht : s.locals "t" = some (.word t)) (hhdr : HtabHdr s.memory t v) (hlay : HtabLayout t v)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat)
    (h : ∀ N O q mF, GrowRel s.memory t v pv N O q mF →
      Q (.normal s.locals (updatePanValueMap (updatePanValueMap (updatePanValueMap s.globals
        "heap_ptr" (.word N)) "heap_ptr" (.word O)) "heap_ptr" (.word q)) mF s.ffi)) :
    WPs E s (.call (some (none, none)) "htab_grow" [.var .local "t"]) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 137 hE.functions (by guest_decl_at 137) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ht, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := htab_grow_exec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb t pv
    v kind (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hhdr hlay hp
    hpH hend hcallee
  rcases hpost with hst | ⟨l, N, O, q, mF, rfl, hR⟩
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
    · obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
      have : l' = s.locals := funext (fun x => hl x (by simp))
      subst this
      exact Or.inr (h N O q mF hR)

/-- The table after the optional growth in `htab_new_node`: unchanged, or grown. -/
def NodeGS (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV) (kind : Nat → NodeKind)
    (rep : KeyRep) (det : Nat → Prop) (g : VarName → Option (PanValue Word)) (pv : Word)
    (g1 : VarName → Option (PanValue Word)) (m1 : Word → Option (PanValue Word)) (v1 : HtabV) :
    Prop :=
  HtabOKd m1 t v1 kind rep det ∧ v1.kl = v.kl ∧ v1.st = v.st ∧ v1.cnt = v.cnt ∧ v1.root = v.root ∧
    v1.next = v.next ∧ v1.free = v.free ∧ v.next.toNat ≤ v1.nc.toNat ∧
    ((m1 = m ∧ v1 = v ∧ g1 = g) ∨ ∃ N O q, GrowRel m t v pv N O q m1 ∧
      v1 = ⟨v.kl, v.st, v.cp * 2#64, v.nc * 2#64, v.cnt, pv, N, O, v.root, v.next, v.free⟩ ∧
      g1 = updatePanValueMap (updatePanValueMap (updatePanValueMap g "heap_ptr" (.word N))
        "heap_ptr" (.word O)) "heap_ptr" (.word q))

/-- What `htab_new_node` did: popped the free list, or bumped `next` after an
optional growth. -/
def NewNodeRel (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV)
    (kind : Nat → NodeKind) (rep : KeyRep) (det : Nat → Prop)
    (g : VarName → Option (PanValue Word)) (pv : Word)
    (m' : Word → Option (PanValue Word)) (g' : VarName → Option (PanValue Word)) (n : Word) :
    Prop :=
  (v.free ≠ 0#64 ∧ n = v.free ∧ g' = g ∧
    ∃ nf, Rd m (nodeField v v.free.toNat 0) nf ∧ m' = setCell m (t + 72#64) nf) ∨
  (v.free = 0#64 ∧ n = v.next ∧
    ∃ m1 v1, NodeGS m t v kind rep det g pv g' m1 v1 ∧ m' = setCell m1 (t + 64#64) (v.next + 1#64))

set_option maxHeartbeats 4000000 in
theorem htab_new_node_exec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_new_node" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t pv : Word) (v : HtabV) (kind : Nat → NodeKind) (rep : KeyRep)
    (det : Nat → Prop)
    (ht : s.locals "t" = some (.word t)) (hok : HtabOKd s.memory t v kind rep det)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' n, r = .returned l g' m' s.ffi [.word n] ∧
      NewNodeRel s.memory t v kind rep det s.globals pv m' g' n := by
  have hbody := (fun_of_index 134 hE.functions (by guest_decl_at 134) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' n, r = .returned l g' m' s.ffi [.word n] ∧
      NewNodeRel s.memory t v kind rep det s.globals pv m' g' n)) r h
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  have hnl := hwf.next_le
  refine WPs.dec (eval_load_rd hE (eval_addc hE 72#64 ht) hfree) ?_
  by_cases hf0 : v.free = 0#64
  · refine WPs.guard0 (fun y hy => by
      rw [eval_cmp_inv hE (of_eval (w := v.free) (by lk [])) (of_eval (eval_const _ _)) y hy]
      simp [evalPanCmp, hf0]) ?_
    refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 64#64 (by lk [ht])) hnext) ?_
    refine WPs.seq (fun a => a.locals = updatePanValueMap (updatePanValueMap s.locals "f"
        (.word v.free)) "next" (.word v.next) ∧ a.ffi = s.ffi ∧
        ∃ v1, NodeGS s.memory t v kind rep det s.globals pv a.globals a.memory v1) ?_ ?_
    · refine WPs.ite (w := evalPanCmp .lower v.nc v.next) (eval_cmp_inv hE
        (eval_load_rd hE (eval_addc hE (a := t) 80#64 (by lk [ht])) hnc)
        (of_eval (w := v.next) (by lk []))) ?_
      split
      · rename_i hc
        have hle : v.next.toNat ≤ v.nc.toNat := by
          have := lower_zero hc
          rw [BitVec.lt_def] at this
          omega
        exact WPs.skip ⟨_, _, _, _, rfl, rfl, rfl, v, hok, rfl, rfl, rfl, rfl, rfl, rfl, hle,
          Or.inl ⟨rfl, rfl, rfl⟩⟩
      · refine WPs.call_grow hE (kind := kind) (by lk [ht]) hwf.hdr hlay hp hpH hend ?_
        intro N O q mF hR
        have h2 : (2#64 : Word).toNat = 2 := by decide
        have hnc2 : (v.nc * 2#64).toNat = v.nc.toNat * 2 := by
          rw [BitVec.toNat_mul, h2]
          exact Nat.mod_eq_of_lt (by omega)
        have hpos := hok.nc_pos
        exact ⟨_, _, _, _, rfl, rfl, rfl, _, htab_grow_ok hok hpH hend hR, rfl, rfl, rfl, rfl,
          rfl, rfl, by show v.next.toNat ≤ (v.nc * 2#64).toNat; omega, Or.inr ⟨N, O, q, hR, rfl, rfl⟩⟩
    · rintro a ⟨hl, hf, v1, hok1, e1, e2, e3, e4, e5, e6, hle, hcase⟩
      have hta : a.locals "t" = some (.word t) := by rw [hl]; lk [ht]
      have hnext1 : Rd a.memory (t + 64#64) v.next := by
        have := hok1.wf.hdr.2.2.2.2.2.2.2.2.1
        rw [e5] at this
        exact this
      refine WPs.dec (eval_load_rd hE (eval_addc hE 64#64 hta) hnext1) ?_
      refine WPs.seq_store hE (eval_addc hE (a := t) 64#64 (by lk [hta]))
        (of_eval (eval_addc hE (a := v.next) 1#64 (by lk []))) ?_
      refine WPs.ret (of_eval (w := v.next) (by lk [])) ?_
      refine ⟨_, a.globals, _, v.next, by simp only [restorePanValueFfiLocal]; rw [hf],
        Or.inr ⟨hf0, rfl, a.memory, v1, ⟨hok1, e1, e2, e3, e4, e5, e6, hle, hcase⟩, rfl⟩⟩
  · obtain ⟨hf1, hf2, nf, hnf⟩ : 1 ≤ v.free.toNat ∧ v.free.toNat < v.next.toNat ∧
        ∃ nf, Rd s.memory (nodeField v v.free.toNat 0) nf := by
      obtain ⟨fl, hfl⟩ := hwf.free_chain
      cases fl with
      | nil => exact absurd hfl hf0
      | cons i rest =>
        obtain ⟨hi, a, b, -, -, nf, hnf, -⟩ := hfl
        subst hi
        exact ⟨a, b, nf, hnf⟩
    refine WPs.seqG (fun _ => False) ?_ (fun _ hF => hF.elim)
    refine WPs.ite (w := 1#64) (fun y hy => by
      rw [eval_cmp_inv hE (of_eval (w := v.free) (by lk [])) (of_eval (eval_const _ _)) y hy]
      simp [evalPanCmp, hf0]) ?_
    split
    · rename_i h10
      exact absurd h10 (by decide)
    refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 40#64 (by lk [ht])) hnd) ?_
    refine WPs.dec (eval_load_rd hE (eval_node hE hlay (idx := "f") (by omega) (by lk [])
      (by lk []) 0#64 (by decide)) hnf) ?_
    refine WPs.seq_store hE (eval_addc hE (a := t) 72#64 (by lk [ht]))
      (of_eval (w := nf) (by lk [])) ?_
    refine WPs.ret (of_eval (w := v.free) (by lk [])) ?_
    exact ⟨_, _, _, _, rfl, Or.inl ⟨hf0, rfl, rfl, nf, hnf, rfl⟩⟩

variable {m : Word → Option (PanValue Word)} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
  {rep : KeyRep}

/-- A header store does not change a node cell. -/
theorem rd_hdrSet_node (hlay : HtabLayout t v) {i o k : Nat} (hi : i ≤ v.nc.toNat) (ho : o < 32)
    (hk : k < 88) (x w : Word) :
    Rd (setCell m (t + BitVec.ofNat 64 k) x) (v.nodes + BitVec.ofNat 64 (i * 32 + o)) w ↔
      Rd m (nodeField v i o) w := by
  show Rd _ (nodeField v i o) w ↔ _
  unfold Rd
  rw [setCell_ne' _ (fun h => (node_ne_hdr hlay hi ho hk).mp h)]

/-- A header store does not change an order slot. -/
theorem rd_hdrSet_ord (hlay : HtabLayout t v) {p k : Nat} (hp : p ≤ v.nc.toNat) (hk : k < 88)
    (x w : Word) :
    Rd (setCell m (t + BitVec.ofNat 64 k) x) (v.order + BitVec.ofNat 64 (p * 8)) w ↔
      Rd m (orderSlot v p) w := by
  show Rd _ (orderSlot v p) w ↔ _
  unfold Rd
  rw [setCell_ne' _ (fun h => (ord_ne_hdr hlay hp hk).mp h)]

/-- Key bits survive any change outside the key block. -/
theorem keybit_frame (hlay : HtabLayout t v) (hk8 : v.keys.toNat % 8 = 0)
    (hkl : v.kl.toNat ≤ v.st.toNat) (hkl8 : v.kl.toNat * 8 < 2 ^ 64)
    {m' : Word → Option (PanValue Word)}
    (hK : ∀ a : Word, v.keys.toNat ≤ a.toNat → a.toNat < v.nodes.toNat → m' a = m a) {i : Nat}
    (hi : i ≤ v.nc.toNat) {j : Word} {bit : Bool} (hj : j.toNat < (v.kl * 8#64).toNat)
    (h : KeyBitIs 8#64 m (v.keys + BitVec.ofNat 64 i * v.st) j bit) :
    KeyBitIs 8#64 m' (v.keys + BitVec.ofNat 64 i * v.st) j bit := by
  obtain ⟨hkp, hkp'⟩ := keyptr_bounds hlay hi
  have h8 : (8#64 : Word).toNat = 8 := by decide
  have hmul : (v.kl * 8#64).toNat = v.kl.toNat * 8 := by
    rw [BitVec.toNat_mul, h8]
    exact Nat.mod_eq_of_lt hkl8
  obtain ⟨-, -, -, h4⟩ := hlay
  exact KeyBitIs.frame (lo := v.keys.toNat) (hi := v.nodes.toNat) hk8 (by omega) (by omega)
    (by omega) hK h

set_option maxHeartbeats 4000000 in
/-- After `htab_new_node` the table is well formed again, and the node it
returned is a free node that is not on the free list. -/
theorem htab_new_node_ok {det : Nat → Prop} (hok : HtabOKd m t v kind rep det)
    {g g' : VarName → Option (PanValue Word)} {pv n : Word}
    {m' : Word → Option (PanValue Word)}
    (hrel : NewNodeRel m t v kind rep det g pv m' g' n) :
    ∃ v' kind', HtabOKd m' t v' kind' rep det ∧ v'.kl = v.kl ∧ v'.st = v.st ∧ v'.cnt = v.cnt ∧
      v'.root = v.root ∧ 1 ≤ n.toNat ∧ n.toNat < v'.next.toNat ∧ kind' n.toNat = .free ∧
      (∃ fl, FreeChain m' v' kind' v'.free fl ∧ n.toNat ∉ fl) ∧
      (∀ i, i < v.next.toNat → i ≠ n.toNat → kind' i = kind i) ∧
      v.next.toNat ≤ v'.next.toNat := by
  rcases hrel with ⟨hf0, rfl, -, nf, hnf, rfl⟩ | ⟨hf0, rfl, m1, v1, ⟨hok1, e1, e2, e3, e4, e5, e6,
    hle, -⟩, rfl⟩
  · -- popped the free list
    have hwf := hok.wf
    have hlay := hwf.layout
    have hnl := hwf.next_le
    obtain ⟨fl, hfl⟩ := hwf.free_chain
    cases fl with
    | nil => exact absurd hfl hf0
    | cons i rest =>
      obtain ⟨hi, a, b, hki, hnot, f, hf, hc⟩ := hfl
      subst hi
      have := Rd.inj hf hnf
      subst this
      obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
      have hne : ∀ k, k < 88 → k ≠ 72 → t + BitVec.ofNat 64 k ≠ t + 72#64 :=
        fun k hk hkk h => hkk ((hdr_eq_hdr hlay hk (by omega)).mp h)
      have hmem := FreeChain.kind_mem rest f hc
      have hchain : FreeChain (setCell m (t + 72#64) f)
          ⟨v.kl, v.st, v.cp, v.nc, v.cnt, v.keys, v.nodes, v.order, v.root, v.next, f⟩ kind f
          rest :=
        FreeChain.congr (v := v) (kind := kind)
          (v' := ⟨v.kl, v.st, v.cp, v.nc, v.cnt, v.keys, v.nodes, v.order, v.root, v.next, f⟩)
          (Nat.le_refl v.next.toNat) rest f hc
          (fun i hi => ⟨(hmem i hi).1, fun w hw =>
            (rd_hdrSet_node hlay (by have := (hmem i hi).2.2; omega) (by omega) (k := 72)
              (by omega) f w).mpr hw⟩)
      refine ⟨⟨v.kl, v.st, v.cp, v.nc, v.cnt, v.keys, v.nodes, v.order, v.root, v.next, f⟩, kind,
        ?_, rfl, rfl, rfl, rfl, a, b, hki, ⟨rest, hchain, hnot⟩, fun _ _ _ => rfl, Nat.le_refl _⟩
      refine hok.reshape (Nat.le_refl _) (fun _ _ => rfl) (fun i h1 h2 => absurd h2 (by omega))
        (Nat.le_refl _) hnl ⟨rest, hc⟩ hlay ?_ hok.keys8 hok.nodes8 hok.order8 ?_ ?_ ?_
      · exact ⟨hkl.frame _ (hne 0 (by omega) (by omega)), hst.frame _ (hne 8 (by omega) (by omega)),
          hcp.frame _ (hne 16 (by omega) (by omega)), hcnt.frame _ (hne 24 (by omega) (by omega)),
          hkeys.frame _ (hne 32 (by omega) (by omega)), hnd.frame _ (hne 40 (by omega) (by omega)),
          hord.frame _ (hne 48 (by omega) (by omega)), hroot.frame _ (hne 56 (by omega) (by omega)),
          hnext.frame _ (hne 64 (by omega) (by omega)), Rd.here _ _ _,
          hnc.frame _ (hne 80 (by omega) (by omega))⟩
      · intro i o w hi ho _
        exact rd_hdrSet_node hlay hi ho (k := 72) (by omega) f w
      · intro p w hp
        exact rd_hdrSet_ord hlay hp (k := 72) (by omega) f w
      · intro i hi j bit hj hb
        exact keybit_frame hlay hok.keys8 hok.kl_st hok.kl8
          (fun a ha _ => setCell_key_hdr hlay (k := 72) (by omega) f ha) hi hj hb
  · -- bumped `next`
    have hwf := hok1.wf
    have hlay := hwf.layout
    have hnl := hwf.next_le
    obtain ⟨l1, l2, l3, l4⟩ := id hlay
    have h1 : (1#64 : Word).toNat = 1 := by decide
    have hn1 : (v.next + 1#64).toNat = v.next.toNat + 1 := by
      rw [BitVec.toNat_add, h1]
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
    have hne : ∀ k, k < 88 → k ≠ 64 → t + BitVec.ofNat 64 k ≠ t + 64#64 :=
      fun k hk hkk h => hkk ((hdr_eq_hdr hlay hk (by omega)).mp h)
    obtain ⟨fl, hfl⟩ := hwf.free_chain
    have hmem := FreeChain.kind_mem fl _ hfl
    have hchain : FreeChain (setCell m1 (t + 64#64) (v.next + 1#64))
        ⟨v1.kl, v1.st, v1.cp, v1.nc, v1.cnt, v1.keys, v1.nodes, v1.order, v1.root, v.next + 1#64,
          v1.free⟩ (fun i => if i = v.next.toNat then NodeKind.free else kind i) v1.free fl :=
      FreeChain.congr (v := v1) (kind := kind)
        (v' := ⟨v1.kl, v1.st, v1.cp, v1.nc, v1.cnt, v1.keys, v1.nodes, v1.order, v1.root,
          v.next + 1#64, v1.free⟩)
        (by rw [e5]; show v.next.toNat ≤ (v.next + 1#64).toNat; omega)
        fl _ hfl (fun i hi => ⟨by
            have := (hmem i hi).2.2
            rw [e5] at this
            rw [if_neg (by omega)]
            exact (hmem i hi).1, fun w hw =>
          (rd_hdrSet_node hlay (by have := (hmem i hi).2.2; omega) (by omega) (k := 64)
            (by omega) _ w).mpr hw⟩)
    refine ⟨⟨v1.kl, v1.st, v1.cp, v1.nc, v1.cnt, v1.keys, v1.nodes, v1.order, v1.root,
        v.next + 1#64, v1.free⟩, (fun i => if i = v.next.toNat then NodeKind.free else kind i), ?_,
      e1, e2, e3, e4, ?_, ?_, if_pos rfl, ⟨fl, hchain, ?_⟩, fun i _ hi => if_neg hi, ?_⟩
    · refine hok1.reshape (Nat.le_refl _) (fun i hi => if_neg (by rw [e5] at hi; omega))
        (fun i hi1 hi2 => by rw [e5] at hi1; rw [hn1] at hi2; exact if_pos (by omega))
        (by rw [e5, hn1]; omega) (by rw [hn1]; omega) ⟨fl, hfl⟩ hlay ?_ hok1.keys8 hok1.nodes8
        hok1.order8 ?_ ?_ ?_
      · exact ⟨hkl.frame _ (hne 0 (by omega) (by omega)), hst.frame _ (hne 8 (by omega) (by omega)),
          hcp.frame _ (hne 16 (by omega) (by omega)), hcnt.frame _ (hne 24 (by omega) (by omega)),
          hkeys.frame _ (hne 32 (by omega) (by omega)), hnd.frame _ (hne 40 (by omega) (by omega)),
          hord.frame _ (hne 48 (by omega) (by omega)), hroot.frame _ (hne 56 (by omega) (by omega)),
          Rd.here _ _ _, hfree.frame _ (hne 72 (by omega) (by omega)),
          hnc.frame _ (hne 80 (by omega) (by omega))⟩
      · intro i o w hi ho _
        exact rd_hdrSet_node hlay hi ho (k := 64) (by omega) _ w
      · intro p w hp
        exact rd_hdrSet_ord hlay hp (k := 64) (by omega) _ w
      · intro i hi j bit hj hb
        exact keybit_frame hlay hok1.keys8 hok1.kl_st hok1.kl8
          (fun a ha _ => setCell_key_hdr hlay (k := 64) (by omega) _ ha) hi hj hb
    · have := hok.wf.next_pos
      omega
    · show v.next.toNat < (v.next + 1#64).toNat
      omega
    · intro hin
      have := (hmem _ hin).2.2
      rw [e5] at this
      omega
    · show v.next.toNat ≤ (v.next + 1#64).toNat
      omega

end InitECandidate.Solver.GuestBound
