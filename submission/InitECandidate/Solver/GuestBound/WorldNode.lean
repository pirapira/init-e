import InitECandidate.Solver.GuestBound.TrieNew

/-!
# Writing into trie nodes keeps the world

`WorldTJ.node_other`: a store into a cell of a known node that is not one of
its structural cells (kind, extension length/child, branch children).
`WorldTJ.node_child`: a store of null or a known node into a child slot.
`node_invalidate_world`: `node_invalidate(nd)` on a known node of kind 1–3.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {Rg : Reg} {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}

/-- The kind of a known node is what its first cell holds. -/
theorem WorldTJ.node_kind {a k : Word} (h : WorldTJ Rg g m) (ha : Rg.Nd a) (hk : Rd m a k) :
    k.toNat ≤ 3 ∧ HBASE ≤ a.toNat ∧ a.toNat + nodeSize k ≤ 2952790016 ∧ a.toNat % 8 = 0 := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  obtain ⟨k', hk'⟩ := hNd a ha
  have hat := hW.nodes.at_ a k' hk'
  have : k' = k := Rd.inj hat.kind hk
  subst this
  have := hat.hi
  have := hpH.1
  exact ⟨hat.k3, hat.lo, by omega, hat.al⟩

/-- `ImOK` after a store into a node, away from the segment cells. -/
theorem ImOK.store_node {pv a k x : Word} {T : Word → Option HtabV} {N : Word → Option Word}
    {J C n : Word} (w : Word) (h : ImOK Rg m pv T N J C) (hW : HeapW m pv T N J C n)
    (hN : N a = some k) (hin : a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k)
    (hns : (k = 1#64 ∨ k = 2#64) → x ≠ a + 32#64 ∧ x ≠ a + 40#64) :
    ImOK Rg (setCell m x w) pv T N J C := by
  refine h.frame (Nat.le_refl _) (fun y hy => setCell_ne _ ?_)
  rintro rfl
  rcases hy with (⟨b, j, hb, hj, hy⟩ | ⟨-, lo, hi, hI, h1, h2⟩) | ⟨u, hu, hy⟩
  rotate_right
  · obtain ⟨-, c1, c2, hi, e, hf⟩ := tr_cell_in h hu hy
    rcases hf.node a k hN with h3 | h3 <;> omega
  · by_cases e : b = a
    · subst e
      have : j = k := Option.some.inj (hb.symm.trans hN)
      subst this
      rcases hy with hy | hy
      · exact (hns hj).1 hy
      · exact (hns hj).2 hy
    · have hi' := seg_cell_in (hW.nodes.at_ b j hb) hj hy
      rcases hW.nodes.disj b j a k hb hN e with h3 | h3 <;> omega
  · rcases (h.free lo hi hI).2.node a k hN with h3 | h3 <;> omega

/-- A store into a non-structural cell of a known node. -/
theorem WorldTJ.node_other {a k x : Word} (w : Word) (h : WorldTJ Rg g m) (ha : Rg.Nd a)
    (hk : Rd m a k) (hin : a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k)
    (hx : ¬ StructCell a k x)
    (hns : (k = 1#64 ∨ k = 2#64) → x ≠ a + 32#64 ∧ x ≠ a + 40#64) :
    WorldTJ Rg g (setCell m x w) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  obtain ⟨k', hk'⟩ := hNd a ha
  have hat := hW.nodes.at_ a k' hk'
  have : k' = k := Rd.inj hat.kind hk
  subst this
  refine ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW.node_other w hk' hin hx, hD, hB,
    fun y v hc => ?_, hNd, hIm.store_node w hW hk' hin hns⟩
  obtain ⟨hr, h8, hi, hhi, hf⟩ := hCn y v hc
  refine ⟨hr.frame _ ?_, h8, hi, hhi, hf⟩
  rintro rfl
  rcases hf.node a k' hk' with h1 | h1 <;> omega

/-- A store of null or a known node into a child slot of a known node. -/
theorem WorldTJ.node_child {a k x c : Word} (h : WorldTJ Rg g m) (ha : Rg.Nd a)
    (hk : Rd m a k)
    (hslot : (k = 2#64 ∧ x = a + 48#64) ∨
      (k = 3#64 ∧ ∃ i : Nat, i < 16 ∧ x = a + BitVec.ofNat 64 (32 + 8 * i)))
    (hc : c = 0#64 ∨ Rg.Nd c) : WorldTJ Rg g (setCell m x c) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  obtain ⟨k', hk'⟩ := hNd a ha
  have hat := hW.nodes.at_ a k' hk'
  have : k' = k := Rd.inj hat.kind hk
  subst this
  have hcN : IsChild N c := by
    rcases hc with rfl | hc
    · exact Or.inl rfl
    · exact Or.inr (hNd c hc)
  have hsx : StructCell a k' x := by
    rcases hslot with ⟨hk2, rfl⟩ | ⟨hk3, i, hi, rfl⟩
    · exact Or.inr (Or.inl ⟨hk2, Or.inr rfl⟩)
    · exact Or.inr (Or.inr ⟨hk3, i, hi, rfl⟩)
  have hin := hsx.inside hat
  refine ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW.node_child hk' hslot hcN, hD, hB,
    fun y v hcn => ?_, hNd, hIm.store_node c hW hk' hin (fun hj => ?_)⟩
  rotate_left
  · have e32 : (a + 32#64).toNat = a.toNat + 32 := by have := hat.top; bv_omega
    have e40 : (a + 40#64).toNat = a.toNat + 40 := by have := hat.top; bv_omega
    have e48 : (a + 48#64).toNat = a.toNat + 48 := by have := hat.top; bv_omega
    rcases hslot with ⟨hk2, rfl⟩ | ⟨hk3, -⟩
    · exact ⟨fun e => by have := congrArg BitVec.toNat e; omega,
        fun e => by have := congrArg BitVec.toNat e; omega⟩
    · subst hk3
      rcases hj with hj | hj <;> exact absurd hj (by decide)
  obtain ⟨hr, h8, hi, hhi, hf⟩ := hCn y v hcn
  refine ⟨hr.frame _ ?_, h8, hi, hhi, hf⟩
  rintro rfl
  rcases hf.node a k' hk' with h1 | h1 <;> omega

/-- A cache field (`+8`, `+16`, `+24`) of a node of kind 1–3 is inside the node
and not structural. -/
theorem cache_cell {a k : Word} {c : Nat} (hc : c = 8 ∨ c = 16 ∨ c = 24) (hk0 : k ≠ 0#64)
    (hk3 : k.toNat ≤ 3) (htop : a.toNat + nodeSize k ≤ 2952790016) :
    (a.toNat ≤ (a + BitVec.ofNat 64 c).toNat ∧
      (a + BitVec.ofNat 64 c).toNat + 8 ≤ a.toNat + nodeSize k) ∧
      ¬ StructCell a k (a + BitVec.ofNat 64 c) := by
  have hsz : 56 ≤ nodeSize k := by
    unfold nodeSize
    split
    · rename_i h0
      exact absurd h0 hk0
    · split <;> [omega; (split <;> omega)]
  have e : (a + BitVec.ofNat 64 c).toNat = a.toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rintro (h | ⟨-, h | h⟩ | ⟨-, i, hi, h⟩)
  · have := congrArg BitVec.toNat h
    omega
  · have := congrArg BitVec.toNat h
    have e40 : (a + 40#64).toNat = a.toNat + 40 := by bv_omega
    omega
  · have := congrArg BitVec.toNat h
    have e48 : (a + 48#64).toNat = a.toNat + 48 := by bv_omega
    omega
  · have := congrArg BitVec.toNat h
    have ei : (a + BitVec.ofNat 64 (32 + 8 * i)).toNat = a.toNat + (32 + 8 * i) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    omega

set_option maxHeartbeats 2000000 in
/-- `node_invalidate(nd)` on a known node of kind 1–3: the cache fields are
cleared, the world is kept. -/
theorem node_invalidate_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "node_invalidate" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (a k : Word)
    (hnd : s.locals "nd" = some (.word a)) (ha : Rg.Nd a) (hk : Rd s.memory a k)
    (hk0 : k ≠ 0#64) (hW : WorldTJ Rg s.globals s.memory) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      WorldTJ Rg s.globals m' ∧ Rd m' a k ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 259 hE.functions (by guest_decl_at 259) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    WorldTJ Rg s.globals m' ∧ Rd m' a k ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  obtain ⟨hk3, hlo, htop, -⟩ := hW.node_kind ha hk
  have NE : ∀ {x y : Word}, x.toNat ≠ y.toNat → x ≠ y := fun h e => h (congrArg _ e)
  have hsz := nodeSize_pos k
  have e8 : (a + 8#64).toNat = a.toNat + 8 := by bv_omega
  have e16 : (a + 16#64).toNat = a.toNat + 16 := by bv_omega
  have e24 : (a + 24#64).toNat = a.toNat + 24 := by bv_omega
  obtain ⟨hin8, hs8⟩ := cache_cell (c := 8) (Or.inl rfl) hk0 hk3 htop
  obtain ⟨hin16, hs16⟩ := cache_cell (c := 16) (Or.inr (Or.inl rfl)) hk0 hk3 htop
  obtain ⟨hin24, hs24⟩ := cache_cell (c := 24) (Or.inr (Or.inr rfl)) hk0 hk3 htop
  have e32 : (a + 32#64).toNat = a.toNat + 32 := by bv_omega
  have e40 : (a + 40#64).toNat = a.toNat + 40 := by bv_omega
  have W1 := hW.node_other 0#64 ha hk hin8 hs8 (fun _ => ⟨NE (by omega), NE (by omega)⟩)
  have k1 : Rd (setCell s.memory (a + 8#64) 0#64) a k := hk.frame _ (NE (by omega))
  have W2 := W1.node_other 0#64 ha k1 hin16 hs16 (fun _ => ⟨NE (by omega), NE (by omega)⟩)
  have k2 : Rd (setCell (setCell s.memory (a + 8#64) 0#64) (a + 16#64) 0#64) a k :=
    k1.frame _ (NE (by omega))
  have W3 := W2.node_other 0#64 ha k2 hin24 hs24 (fun _ => ⟨NE (by omega), NE (by omega)⟩)
  have k3 := k2.frame (a' := a + 24#64) 0#64 (NE (by omega))
  refine WPs.seq_store hE (addr := a + 8#64) (w := 0#64) (eval_addc hE 8#64 hnd)
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := a + 16#64) (w := 0#64) (eval_addc hE 16#64 (by lk [hnd]))
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := a + 24#64) (w := 0#64) (eval_addc hE 24#64 (by lk [hnd]))
    (of_eval (eval_const _ _)) ?_
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  refine ⟨_, _, rfl, W3, k3, fun addr hx => ?_⟩
  unfold HBASE at hx hlo
  dsimp only
  rw [setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]

end InitECandidate.Solver.GuestBound
