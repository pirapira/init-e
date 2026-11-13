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

/-- A store into a node leaves the segment cells, the immutable blocks and the
handles alone, when it is not one of the node's own segment cells. -/
theorem node_store_keep {pv a k x : Word} {T : Word → Option HtabV} {N : Word → Option Word}
    {J C n : Word} (w : Word) (h : ImOK Rg m pv T N J C) (hW : HeapW m pv T N J C n)
    (hN : N a = some k) (hin : a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k)
    (hns : (k = 1#64 ∨ k = 2#64) → x ≠ a + 32#64 ∧ x ≠ a + 40#64) :
    ∀ y, SegCell Rg.Im N y ∨ TrCell Rg.Tr y → setCell m x w y = m y := by
  intro y hy
  refine setCell_ne _ ?_
  rintro rfl
  rcases hy with (⟨b, j, hb, hj, hy⟩ | ⟨-, lo, hi, hI, h1, h2⟩) | ⟨u, hu, hy⟩
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
  · obtain ⟨-, c1, c2, hi, e, hf⟩ := tr_cell_in h hu hy
    rcases hf.node a k hN with h3 | h3 <;> omega

/-- Structural cells of different nodes, or a structural and a non-structural
cell of one node, are different. -/
theorem struct_cell_ne {pv a k b j x y : Word} {T : Word → Option HtabV}
    {N : Word → Option Word} {J C n : Word} (hW : HeapW m pv T N J C n)
    (hN : N a = some k) (hin : a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k)
    (hb : N b = some j) (hy : StructCell b j y) (hba : b ≠ a) : y ≠ x := by
  have hi' := hy.inside (hW.nodes.at_ b j hb)
  rintro rfl
  rcases hW.nodes.disj b j a k hb hN hba with h3 | h3 <;> omega

/-- Cells of different nodes are different. -/
theorem ncell_ne {pv a k b j x y : Word} {T : Word → Option HtabV}
    {N : Word → Option Word} {J C n : Word} (hW : HeapW m pv T N J C n)
    (hN : N a = some k) (hin : a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k)
    (hb : N b = some j) (hy : NCell b j y) (hba : b ≠ a) : y ≠ x := by
  have hi' := hy.inside (hW.nodes.at_ b j hb)
  rintro rfl
  rcases hW.nodes.disj b j a k hb hN hba with h3 | h3 <;> omega

/-- A structural cell and a value cell of one node are different. -/
theorem struct_val_ne {pv a k x y : Word} {N : Word → Option Word} (hat : NodeAt m pv N a k)
    (hs : StructCell a k y) (hv : ValCell a k x) : y ≠ x := by
  have NE : ∀ {u v : Word}, u.toNat ≠ v.toNat → u ≠ v := fun h e => h (congrArg _ e)
  have e40 := node_off hat 40 (by omega)
  change (a + 40#64).toNat = _ at e40
  have e48 := node_off hat 48 (by omega)
  change (a + 48#64).toNat = _ at e48
  have e56 := node_off hat 56 (by omega)
  change (a + 56#64).toNat = _ at e56
  have e160 := node_off hat 160 (by omega)
  change (a + 160#64).toNat = _ at e160
  have e168 := node_off hat 168 (by omega)
  change (a + 168#64).toNat = _ at e168
  rcases hv with ⟨hk, rfl | rfl⟩ | ⟨hk, rfl | rfl⟩ <;>
    rcases hs with rfl | ⟨hk2, rfl | rfl⟩ | ⟨hk3, i, hi, rfl⟩ <;>
    first
      | exact absurd (hk.symm.trans hk2) (by decide)
      | exact absurd (hk.symm.trans hk3) (by decide)
      | exact NE (by omega)
      | (have ei := node_off hat (32 + 8 * i) (by omega); exact NE (by omega))

/-- `ImOK` after a store into a non-structural cell of a node, away from its segment cells. -/
theorem ImOK.store_node {pv a k x : Word} {T : Word → Option HtabV} {N : Word → Option Word}
    {J C n : Word} (w : Word) (h : ImOK Rg m pv T N J C) (hW : HeapW m pv T N J C n)
    (hN : N a = some k) (hin : a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k)
    (hx : ¬ StructCell a k x)
    (hns : (k = 1#64 ∨ k = 2#64) → x ≠ a + 32#64 ∧ x ≠ a + 40#64)
    (hnv : ¬ ValCell a k x) :
    ImOK Rg (setCell m x w) pv T N J C := by
  have keep := node_store_keep w h hW hN hin hns
  refine h.frame (Nat.le_refl _) (fun y hy => ?_)
  rcases hy with hy | hy | ⟨b, j, hb, hsy⟩
  · exact keep y (Or.inl hy)
  · exact keep y (Or.inr hy)
  · refine setCell_ne _ ?_
    by_cases e : b = a
    · subst e
      have : j = k := Option.some.inj (hb.symm.trans hN)
      subst this
      rintro rfl
      exact hsy.elim hx hnv
    · exact ncell_ne hW hN hin hb hsy e

/-- `ImOK` after a store into a child slot: the stored node must sit at the
child level of the parent, when the parent has one. -/
theorem ImOK.store_child {pv a k x c : Word} {T : Word → Option HtabV} {N : Word → Option Word}
    {J C n : Word} (h : ImOK Rg m pv T N J C) (hW : HeapW m pv T N J C n) (hN : N a = some k)
    (hslot : (k = 2#64 ∧ x = a + 48#64) ∨
      (k = 3#64 ∧ ∃ i : Nat, i < 16 ∧ x = a + BitVec.ofNat 64 (32 + 8 * i)))
    (hl : ∀ ℓc, Rg.Cv a ℓc → c ≠ 0#64 → Rg.Lv c ℓc) :
    ImOK Rg (setCell m x c) pv T N J C := by
  have NE : ∀ {u v : Word}, u.toNat ≠ v.toNat → u ≠ v := fun h e => h (congrArg _ e)
  have hat := hW.nodes.at_ a k hN
  have hsx : StructCell a k x := by
    rcases hslot with ⟨hk2, rfl⟩ | ⟨hk3, i, hi, rfl⟩
    · exact Or.inr (Or.inl ⟨hk2, Or.inr rfl⟩)
    · exact Or.inr (Or.inr ⟨hk3, i, hi, rfl⟩)
  have hin := hsx.inside hat
  have e32 : (a + 32#64).toNat = a.toNat + 32 := by have := hat.top; bv_omega
  have e40 : (a + 40#64).toNat = a.toNat + 40 := by have := hat.top; bv_omega
  have e48 : (a + 48#64).toNat = a.toNat + 48 := by have := hat.top; bv_omega
  have hns : (k = 1#64 ∨ k = 2#64) → x ≠ a + 32#64 ∧ x ≠ a + 40#64 := by
    intro hj
    rcases hslot with ⟨hk2, rfl⟩ | ⟨hk3, -⟩
    · exact ⟨NE (by omega), NE (by omega)⟩
    · subst hk3
      rcases hj with hj | hj <;> exact absurd hj (by decide)
  have keep := node_store_keep c h hW hN hin hns
  have rdk : ∀ {y w : Word}, y ≠ x → Rd (setCell m x c) y w → Rd m y w := by
    intro y w hne hr
    unfold Rd at hr ⊢
    rw [setCell_ne _ hne] at hr
    exact hr
  refine ⟨h.free, h.offB, h.segs.frame (fun y hy => keep y (Or.inl hy)),
    nib_frame (fun lo hi hI => (h.free lo hi hI).1) h.nib (fun y hy => keep y (Or.inl hy)),
    h.kd, h.kn, h.full, h.trf, fun u hu => ?_, h.offT, h.offC, h.offI, h.offTT, h.lvk, h.lvu,
    ?_, ?_, h.cvk, h.cvu, ?_, h.cvb, h.lvc, h.sg.frame (fun y hy => keep y (Or.inl hy)),
    h.vals.frame' (fun y hy => by
      obtain ⟨b, j, hb, hvy⟩ := hy
      refine setCell_ne _ ?_
      by_cases e : b = a
      · subst e
        have : j = k := Option.some.inj (hb.symm.trans hN)
        subst this
        exact (struct_val_ne hat hsx hvy).symm
      · exact ncell_ne hW hN hin hb (Or.inr hvy) e)⟩
  · obtain ⟨root, sec, r1, r2, hc⟩ := h.trv u hu
    refine ⟨root, sec, ?_, ?_, hc⟩
    · unfold Rd at r1 ⊢
      rw [keep u (Or.inr ⟨u, hu, Or.inl rfl⟩)]
      exact r1
    · unfold Rd at r2 ⊢
      rw [keep _ (Or.inr ⟨u, hu, Or.inr rfl⟩)]
      exact r2
  · intro b ℓc c' hNb hcv r2 hc'
    have s48 : StructCell b 2#64 (b + 48#64) := Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)
    by_cases e : b = a
    · subst e
      have hk2 : k = 2#64 := (Option.some.inj (hNb.symm.trans hN)).symm
      subst hk2
      have hx48 : x = b + 48#64 := by
        rcases hslot with ⟨-, hx⟩ | ⟨hk3, -⟩
        · exact hx
        · exact absurd hk3 (by decide)
      subst hx48
      have hcc : c' = c := Rd.inj r2 (Rd.here m _ c)
      subst hcc
      exact hl ℓc hcv hc'
    · exact h.lvx b ℓc c' hNb hcv (rdk (struct_cell_ne hW hN hin hNb s48 e) r2) hc'
  · intro b ℓc i c' hNb hcv hi r1 hc'
    have si : StructCell b 3#64 (b + BitVec.ofNat 64 (32 + 8 * i)) :=
      Or.inr (Or.inr ⟨rfl, i, hi, rfl⟩)
    by_cases e : b = a
    · subst e
      by_cases hxi : b + BitVec.ofNat 64 (32 + 8 * i) = x
      · subst hxi
        have hcc : c' = c := Rd.inj r1 (Rd.here m _ c)
        subst hcc
        exact hl ℓc hcv hc'
      · exact h.lvb b ℓc i c' hNb hcv hi (rdk hxi r1) hc'
    · exact h.lvb b ℓc i c' hNb hcv hi (rdk (struct_cell_ne hW hN hin hNb si e) r1) hc'
  · intro b ℓ ℓc nl hlb hcv hNb r1
    have s40 : StructCell b 2#64 (b + 40#64) := Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)
    by_cases e : b = a
    · subst e
      have hk2 : k = 2#64 := (Option.some.inj (hNb.symm.trans hN)).symm
      subst hk2
      have hx48 : x = b + 48#64 := by
        rcases hslot with ⟨-, hx⟩ | ⟨hk3, -⟩
        · exact hx
        · exact absurd hk3 (by decide)
      subst hx48
      exact h.cvx b ℓ ℓc nl hlb hcv hNb (rdk (NE (by omega)) r1)
    · exact h.cvx b ℓ ℓc nl hlb hcv hNb (rdk (struct_cell_ne hW hN hin hNb s40 e) r1)

/-- A store into a non-structural cell of a known node. -/
theorem WorldTJ.node_other {a k x : Word} (w : Word) (h : WorldTJ Rg g m) (ha : Rg.Nd a)
    (hk : Rd m a k) (hin : a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k)
    (hx : ¬ StructCell a k x)
    (hns : (k = 1#64 ∨ k = 2#64) → x ≠ a + 32#64 ∧ x ≠ a + 40#64)
    (hnv : ¬ ValCell a k x) :
    WorldTJ Rg g (setCell m x w) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  obtain ⟨k', hk'⟩ := hNd a ha
  have hat := hW.nodes.at_ a k' hk'
  have : k' = k := Rd.inj hat.kind hk
  subst this
  refine ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW.node_other w hk' hin hx, hD, hB,
    fun y v hc => ?_, hNd, hIm.store_node w hW hk' hin hx hns hnv⟩
  obtain ⟨hr, h8, hi, hhi, hf⟩ := hCn y v hc
  refine ⟨hr.frame _ ?_, h8, hi, hhi, hf⟩
  rintro rfl
  rcases hf.node a k' hk' with h1 | h1 <;> omega

/-- A store of null or a known node into a child slot of a known node. -/
theorem WorldTJ.node_child {a k x c : Word} (h : WorldTJ Rg g m) (ha : Rg.Nd a)
    (hk : Rd m a k)
    (hslot : (k = 2#64 ∧ x = a + 48#64) ∨
      (k = 3#64 ∧ ∃ i : Nat, i < 16 ∧ x = a + BitVec.ofNat 64 (32 + 8 * i)))
    (hc : c = 0#64 ∨ Rg.Nd c)
    (hl : ∀ ℓc, Rg.Cv a ℓc → c ≠ 0#64 → Rg.Lv c ℓc) :
    WorldTJ Rg g (setCell m x c) := by
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
    fun y v hcn => ?_, hNd, hIm.store_child hW hk' hslot hl⟩
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

/-- The two value cells named by `hc`. -/
theorem val_pair {a k x1 x2 : Word}
    (hc : (k = 1#64 ∧ x1 = a + 48#64 ∧ x2 = a + 56#64) ∨
      (k = 3#64 ∧ x1 = a + 160#64 ∧ x2 = a + 168#64)) : ValCell a k x1 ∧ ValCell a k x2 := by
  rcases hc with ⟨hk, rfl, rfl⟩ | ⟨hk, rfl, rfl⟩
  · exact ⟨Or.inl ⟨hk, Or.inl rfl⟩, Or.inl ⟨hk, Or.inr rfl⟩⟩
  · exact ⟨Or.inr ⟨hk, Or.inl rfl⟩, Or.inr ⟨hk, Or.inr rfl⟩⟩

/-- `ImOK` after both value cells of a leaf or a branch are overwritten with a
`VRange` pair. -/
theorem ImOK.store_value {pv a k x1 x2 vp vl : Word} {T : Word → Option HtabV}
    {N : Word → Option Word} {J C n : Word} (h : ImOK Rg m pv T N J C)
    (hW : HeapW m pv T N J C n) (hN : N a = some k)
    (hc : (k = 1#64 ∧ x1 = a + 48#64 ∧ x2 = a + 56#64) ∨
      (k = 3#64 ∧ x1 = a + 160#64 ∧ x2 = a + 168#64))
    (hv : VRange Rg vp vl) : ImOK Rg (setCell (setCell m x1 vp) x2 vl) pv T N J C := by
  have NE : ∀ {u v : Word}, u.toNat ≠ v.toNat → u ≠ v := fun h e => h (congrArg _ e)
  have hat := hW.nodes.at_ a k hN
  obtain ⟨v1, v2⟩ := val_pair hc
  have hin1 := v1.inside hat
  have hin2 := v2.inside hat
  have e32 := node_off hat 32 (by omega)
  change (a + 32#64).toNat = _ at e32
  have e40 := node_off hat 40 (by omega)
  change (a + 40#64).toNat = _ at e40
  have e48 := node_off hat 48 (by omega)
  change (a + 48#64).toNat = _ at e48
  have e56 := node_off hat 56 (by omega)
  change (a + 56#64).toNat = _ at e56
  have e160 := node_off hat 160 (by omega)
  change (a + 160#64).toNat = _ at e160
  have e168 := node_off hat 168 (by omega)
  change (a + 168#64).toNat = _ at e168
  have hns : (k = 1#64 ∨ k = 2#64) →
      (x1 ≠ a + 32#64 ∧ x1 ≠ a + 40#64) ∧ (x2 ≠ a + 32#64 ∧ x2 ≠ a + 40#64) := by
    intro hj
    rcases hc with ⟨hk, rfl, rfl⟩ | ⟨hk, rfl, rfl⟩
    · exact ⟨⟨NE (by omega), NE (by omega)⟩, NE (by omega), NE (by omega)⟩
    · subst hk
      rcases hj with hj | hj <;> exact absurd hj (by decide)
  have x12 : x1 ≠ x2 := by
    rcases hc with ⟨hk, rfl, rfl⟩ | ⟨hk, rfl, rfl⟩ <;> exact NE (by omega)
  have ne_of : ∀ {x : Word}, a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k →
      ((k = 1#64 ∨ k = 2#64) → x ≠ a + 32#64 ∧ x ≠ a + 40#64) →
      ∀ y, SegCell Rg.Im N y ∨ TrCell Rg.Tr y → y ≠ x := by
    intro x hin hnsx y hy e
    have k0 := node_store_keep 0#64 h hW hN hin hnsx y hy
    have k1 := node_store_keep 1#64 h hW hN hin hnsx y hy
    rw [e] at k0 k1
    simp only [setCell, beq_self_eq_true, if_true] at k0 k1
    rw [← k0] at k1
    simp at k1
  have hm : ∀ y, SegCell Rg.Im N y ∨ TrCell Rg.Tr y ∨ SCellN N y →
      setCell (setCell m x1 vp) x2 vl y = m y := by
    intro y hy
    have n1 : y ≠ x1 := by
      rcases hy with hy | hy | ⟨b, j, hb, hsy⟩
      · exact ne_of hin1 (fun hj => (hns hj).1) y (Or.inl hy)
      · exact ne_of hin1 (fun hj => (hns hj).1) y (Or.inr hy)
      · by_cases e : b = a
        · subst e
          have : j = k := Option.some.inj (hb.symm.trans hN)
          subst this
          exact struct_val_ne hat hsy v1
        · exact ncell_ne hW hN hin1 hb (Or.inl hsy) e
    have n2 : y ≠ x2 := by
      rcases hy with hy | hy | ⟨b, j, hb, hsy⟩
      · exact ne_of hin2 (fun hj => (hns hj).2) y (Or.inl hy)
      · exact ne_of hin2 (fun hj => (hns hj).2) y (Or.inr hy)
      · by_cases e : b = a
        · subst e
          have : j = k := Option.some.inj (hb.symm.trans hN)
          subst this
          exact struct_val_ne hat hsy v2
        · exact ncell_ne hW hN hin2 hb (Or.inl hsy) e
    rw [setCell_ne _ n2, setCell_ne _ n1]
  refine h.frame' (Nat.le_refl _) hm (fun b j hb => ?_)
  by_cases e : b = a
  · subst e
    have : j = k := Option.some.inj (hb.symm.trans hN)
    subst this
    rcases hc with ⟨hk, rfl, rfl⟩ | ⟨hk, rfl, rfl⟩
    · subst hk
      exact ⟨fun _ => ⟨vp, vl, (Rd.here _ _ _).frame _ x12, Rd.here _ _ _, hv⟩,
        fun hk => absurd hk (by decide)⟩
    · subst hk
      exact ⟨fun hk => absurd hk (by decide),
        fun _ => ⟨vp, vl, (Rd.here _ _ _).frame _ x12, Rd.here _ _ _, hv⟩⟩
  · have fr : ∀ {y w : Word}, ValCell b j y → Rd m y w →
        Rd (setCell (setCell m x1 vp) x2 vl) y w := fun hy hr =>
      (hr.frame _ (ncell_ne hW hN hin1 hb (Or.inr hy) e)).frame _
        (ncell_ne hW hN hin2 hb (Or.inr hy) e)
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · obtain ⟨p, l, r1, r2, hr⟩ := (h.vals b j hb).1 hk
      exact ⟨p, l, fr (Or.inl ⟨hk, Or.inl rfl⟩) r1, fr (Or.inl ⟨hk, Or.inr rfl⟩) r2, hr⟩
    · obtain ⟨p, l, r1, r2, hr⟩ := (h.vals b j hb).2 hk
      exact ⟨p, l, fr (Or.inr ⟨hk, Or.inl rfl⟩) r1, fr (Or.inr ⟨hk, Or.inr rfl⟩) r2, hr⟩

/-- Storing a value (pointer and length) into a leaf or a branch. -/
theorem WorldTJ.node_value {a k x1 x2 vp vl : Word} (h : WorldTJ Rg g m) (ha : Rg.Nd a)
    (hk : Rd m a k)
    (hc : (k = 1#64 ∧ x1 = a + 48#64 ∧ x2 = a + 56#64) ∨
      (k = 3#64 ∧ x1 = a + 160#64 ∧ x2 = a + 168#64))
    (hv : VRange Rg vp vl) : WorldTJ Rg g (setCell (setCell m x1 vp) x2 vl) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  obtain ⟨k', hk'⟩ := hNd a ha
  have hat := hW.nodes.at_ a k' hk'
  have : k' = k := Rd.inj hat.kind hk
  subst this
  obtain ⟨v1, v2⟩ := val_pair hc
  have hin1 := v1.inside hat
  have hin2 := v2.inside hat
  have hW1 := hW.node_other vp hk' hin1 (fun hs => struct_val_ne hat hs v1 rfl)
  have hW2 := hW1.node_other vl hk' hin2 (fun hs => struct_val_ne hat hs v2 rfl)
  refine ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW2, hD, hB, fun y v hc' => ?_, hNd,
    hIm.store_value hW hk' hc hv⟩
  obtain ⟨hr, h8, hi, hhi, hf⟩ := hCn y v hc'
  refine ⟨(hr.frame _ ?_).frame _ ?_, h8, hi, hhi, hf⟩
  · rintro rfl
    rcases hf.node a k' hk' with h1 | h1 <;> omega
  · rintro rfl
    rcases hf.node a k' hk' with h1 | h1 <;> omega

/-- The value of a known leaf or branch. -/
theorem WorldTJ.value {a k : Word} (h : WorldTJ Rg g m) (hK : Rg.Kd a k) :
    (k = 1#64 → ∃ vp vl, Rd m (a + 48#64) vp ∧ Rd m (a + 56#64) vl ∧ VRange Rg vp vl) ∧
    (k = 3#64 → ∃ vp vl, Rd m (a + 160#64) vp ∧ Rd m (a + 168#64) vl ∧ VRange Rg vp vl) := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  exact hIm.vals a k (hIm.kd a k hK)

/-- A cache cell is not a value cell. -/
theorem cache_not_val {a k : Word} {c : Nat} (hc : c = 8 ∨ c = 16 ∨ c = 24)
    (htop : a.toNat + nodeSize k ≤ 2952790016) : ¬ ValCell a k (a + BitVec.ofNat 64 c) := by
  have hsz := nodeSize_pos k
  rcases hc with rfl | rfl | rfl <;> rintro (⟨-, h | h⟩ | ⟨-, h | h⟩) <;> bv_omega

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
    (cache_not_val (Or.inl rfl) htop)
  have k1 : Rd (setCell s.memory (a + 8#64) 0#64) a k := hk.frame _ (NE (by omega))
  have W2 := W1.node_other 0#64 ha k1 hin16 hs16 (fun _ => ⟨NE (by omega), NE (by omega)⟩)
    (cache_not_val (Or.inr (Or.inl rfl)) htop)
  have k2 : Rd (setCell (setCell s.memory (a + 8#64) 0#64) (a + 16#64) 0#64) a k :=
    k1.frame _ (NE (by omega))
  have W3 := W2.node_other 0#64 ha k2 hin24 hs24 (fun _ => ⟨NE (by omega), NE (by omega)⟩)
    (cache_not_val (Or.inr (Or.inr rfl)) htop)
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
