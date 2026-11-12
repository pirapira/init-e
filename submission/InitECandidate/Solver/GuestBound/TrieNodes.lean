import InitECandidate.Solver.GuestBound.HtabFrame

/-!
# Trie nodes in the heap

A trie node is a block whose first word is its kind: 0 hashed (32 bytes),
1 leaf (64), 2 extension (56, segment length at +40, child at +48), 3 branch
(176, children at +32 … +152, value at +160/+168). The trie code writes nodes
in place (cache fields, child slots, branch value), so memory safety needs:

* `NodesOK m pv N`: `N` maps node addresses to kinds; each node is aligned,
  lies in the heap below the heap pointer `pv`, its kind cell holds its kind,
  node blocks are pairwise disjoint, and every child pointer is null or a
  node of `N`. Extension segments are non-empty, which is what makes the
  descents terminate by key length (no acyclicity argument needed).

The invariant only reads kind cells, extension length/child cells and branch
child cells (`NodesOK.frame`). `NodesOK.store_other` covers a store into any
other cell of a node, `NodesOK.store_child` a store of a node or null into a
child slot, `NodesOK.add` a freshly built node above the old heap pointer.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m m' : Word → Option (PanValue Word)} {pv pv' : Word} {N : Word → Option Word}

/-- Size of a node of kind `k`. -/
def nodeSize (k : Word) : Nat :=
  if k = 0#64 then 32 else if k = 1#64 then 64 else if k = 2#64 then 56 else 176

theorem nodeSize_le (k : Word) : nodeSize k ≤ 176 := by
  unfold nodeSize
  split <;> [omega; (split <;> [omega; (split <;> omega)])]

theorem nodeSize_pos (k : Word) : 32 ≤ nodeSize k := by
  unfold nodeSize
  split <;> [omega; (split <;> [omega; (split <;> omega)])]

/-- A child pointer: null or a registered node. -/
def IsChild (N : Word → Option Word) (c : Word) : Prop := c = 0#64 ∨ ∃ k, N c = some k

/-- The structural cells of the node at `a` of kind `k`: what the invariant reads. -/
def StructCell (a k x : Word) : Prop :=
  x = a ∨ (k = 2#64 ∧ (x = a + 40#64 ∨ x = a + 48#64)) ∨
    (k = 3#64 ∧ ∃ i : Nat, i < 16 ∧ x = a + BitVec.ofNat 64 (32 + 8 * i))

/-- One node. -/
structure NodeAt (m : Word → Option (PanValue Word)) (pv : Word) (N : Word → Option Word)
    (a k : Word) : Prop where
  al : a.toNat % 8 = 0
  lo : HBASE ≤ a.toNat
  top : a.toNat < 2952790016
  hi : a.toNat + nodeSize k ≤ pv.toNat
  k3 : k.toNat ≤ 3
  kind : Rd m a k
  ext : k = 2#64 → ∃ nl c : Word, Rd m (a + 40#64) nl ∧ 1 ≤ nl.toNat ∧ Rd m (a + 48#64) c ∧
    IsChild N c
  br : k = 3#64 → ∀ i : Nat, i < 16 → ∃ c : Word, Rd m (a + BitVec.ofNat 64 (32 + 8 * i)) c ∧
    IsChild N c

/-- The trie nodes. -/
structure NodesOK (m : Word → Option (PanValue Word)) (pv : Word) (N : Word → Option Word) :
    Prop where
  at_ : ∀ a k, N a = some k → NodeAt m pv N a k
  disj : ∀ a k b j, N a = some k → N b = some j → a ≠ b →
    a.toNat + nodeSize k ≤ b.toNat ∨ b.toNat + nodeSize j ≤ a.toNat

/-- Address of a field of a node. -/
theorem node_off {a k : Word} (h : NodeAt m pv N a k) (c : Nat) (hc : c < 2 ^ 32) :
    (a + BitVec.ofNat 64 c).toNat = a.toNat + c := by
  have := h.top
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A structural cell lies inside its node. -/
theorem StructCell.inside {a k x : Word} (h : NodeAt m pv N a k) (hx : StructCell a k x) :
    a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k := by
  have hs := nodeSize_pos k
  rcases hx with rfl | ⟨hk, rfl | rfl⟩ | ⟨hk, i, hi, rfl⟩
  · omega
  · have e := node_off h 40 (by omega)
    have hsz : nodeSize k = 56 := by rw [hk]; rfl
    change (a + 40#64).toNat = _ at e
    omega
  · have e := node_off h 48 (by omega)
    have hsz : nodeSize k = 56 := by rw [hk]; rfl
    change (a + 48#64).toNat = _ at e
    omega
  · have e := node_off h (32 + 8 * i) (by omega)
    have hsz : nodeSize k = 176 := by rw [hk]; rfl
    omega

/-- The invariant only reads structural cells. -/
theorem NodesOK.frame (h : NodesOK m pv N) (hpv : pv.toNat ≤ pv'.toNat)
    (hm : ∀ a k x, N a = some k → StructCell a k x → m' x = m x) : NodesOK m' pv' N := by
  refine ⟨fun a k hN => ?_, h.disj⟩
  have hat := h.at_ a k hN
  have rd : ∀ x w, StructCell a k x → Rd m x w → Rd m' x w := by
    intro x w hx hr
    unfold Rd at hr ⊢
    rw [hm a k x hN hx]
    exact hr
  refine ⟨hat.al, hat.lo, hat.top, by have := hat.hi; omega, hat.k3, rd _ _ (Or.inl rfl) hat.kind,
    fun hk => ?_, fun hk i hi => ?_⟩
  · obtain ⟨nl, c, r1, h1, r2, hc⟩ := hat.ext hk
    exact ⟨nl, c, rd _ _ (Or.inr (Or.inl ⟨hk, Or.inl rfl⟩)) r1, h1,
      rd _ _ (Or.inr (Or.inl ⟨hk, Or.inr rfl⟩)) r2, hc⟩
  · obtain ⟨c, r1, hc⟩ := hat.br hk i hi
    exact ⟨c, rd _ _ (Or.inr (Or.inr ⟨hk, i, hi, rfl⟩)) r1, hc⟩

/-- A store into a cell that is not structural for any node. -/
theorem NodesOK.store_other (h : NodesOK m pv N) (x w : Word)
    (hx : ∀ a k, N a = some k → ¬ StructCell a k x) : NodesOK (setCell m x w) pv N := by
  refine h.frame (Nat.le_refl _) (fun a k y hN hy => ?_)
  apply setCell_ne
  rintro rfl
  exact hx a k hN hy

/-- A cell inside node `a` that is structural for no node, given that it is
not structural for `a`. -/
theorem NodesOK.not_struct (h : NodesOK m pv N) {a k x : Word} (hN : N a = some k)
    (hin : a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k) (hx : ¬ StructCell a k x) :
    ∀ b j, N b = some j → ¬ StructCell b j x := by
  intro b j hb hs
  by_cases e : b = a
  · subst e
    have : j = k := Option.some.inj (hb.symm.trans hN)
    subst this
    exact hx hs
  · have hi := hs.inside (h.at_ b j hb)
    rcases h.disj b j a k hb hN e with h1 | h1 <;> omega

/-- A store of a node or null into a child slot of node `a`. -/
theorem NodesOK.store_child (h : NodesOK m pv N) {a k x c : Word} (hN : N a = some k)
    (hslot : (k = 2#64 ∧ x = a + 48#64) ∨
      (k = 3#64 ∧ ∃ i : Nat, i < 16 ∧ x = a + BitVec.ofNat 64 (32 + 8 * i)))
    (hc : IsChild N c) : NodesOK (setCell m x c) pv N := by
  have hat := h.at_ a k hN
  have hsx : StructCell a k x := by
    rcases hslot with ⟨hk, rfl⟩ | ⟨hk, i, hi, rfl⟩
    · exact Or.inr (Or.inl ⟨hk, Or.inr rfl⟩)
    · exact Or.inr (Or.inr ⟨hk, i, hi, rfl⟩)
  have hin := hsx.inside hat
  -- cells of other nodes are untouched
  have other : ∀ b j y, N b = some j → b ≠ a → StructCell b j y → setCell m x c y = m y := by
    intro b j y hb hne hy
    apply setCell_ne
    rintro rfl
    have hi := hy.inside (h.at_ b j hb)
    rcases h.disj b j a k hb hN hne with h1 | h1 <;> omega
  refine ⟨fun b j hb => ?_, h.disj⟩
  have hbt := h.at_ b j hb
  by_cases e : b = a
  · subst e
    have : j = k := Option.some.inj (hb.symm.trans hN)
    subst this
    have rdne : ∀ y w, y ≠ x → Rd m y w → Rd (setCell m x c) y w := by
      intro y w hy hr
      unfold Rd at hr ⊢
      rw [setCell_ne _ hy]
      exact hr
    have rdeq : Rd (setCell m x c) x c := by
      unfold Rd setCell
      simp
    have hxb : x ≠ b := by
      rcases hslot with ⟨hk, rfl⟩ | ⟨hk, i, hi, rfl⟩
      · intro hh
        have e1 := node_off hbt 48 (by omega)
        change (b + 48#64).toNat = _ at e1
        rw [hh] at e1
        omega
      · intro hh
        have e1 := node_off hbt (32 + 8 * i) (by omega)
        rw [hh] at e1
        omega
    refine ⟨hbt.al, hbt.lo, hbt.top, hbt.hi, hbt.k3, rdne _ _ (Ne.symm hxb) hbt.kind, fun hk => ?_,
      fun hk i hi => ?_⟩
    · obtain ⟨nl, c0, r1, h1, r2, hc0⟩ := hbt.ext hk
      have e40 := node_off hbt 40 (by omega)
      have e48 := node_off hbt 48 (by omega)
      change (b + 40#64).toNat = _ at e40
      change (b + 48#64).toNat = _ at e48
      rcases hslot with ⟨-, rfl⟩ | ⟨hk3, -⟩
      · exact ⟨nl, c, rdne _ _ (by intro hh; rw [hh] at e40; omega) r1, h1, rdeq, hc⟩
      · rw [hk] at hk3
        exact absurd hk3 (by decide)
    · rcases hslot with ⟨hk2, -⟩ | ⟨-, i0, hi0, rfl⟩
      · rw [hk] at hk2
        exact absurd hk2 (by decide)
      · by_cases ei : i = i0
        · subst ei
          exact ⟨c, rdeq, hc⟩
        · obtain ⟨c0, r1, hc0⟩ := hbt.br hk i hi
          have e1 := node_off hbt (32 + 8 * i) (by omega)
          have e2 := node_off hbt (32 + 8 * i0) (by omega)
          exact ⟨c0, rdne _ _ (by intro hh; rw [hh] at e1; omega) r1, hc0⟩
  · have rd : ∀ y w, StructCell b j y → Rd m y w → Rd (setCell m x c) y w := by
      intro y w hy hr
      unfold Rd at hr ⊢
      rw [other b j y hb e hy]
      exact hr
    refine ⟨hbt.al, hbt.lo, hbt.top, hbt.hi, hbt.k3, rd _ _ (Or.inl rfl) hbt.kind, fun hk => ?_,
      fun hk i hi => ?_⟩
    · obtain ⟨nl, c0, r1, h1, r2, hc0⟩ := hbt.ext hk
      exact ⟨nl, c0, rd _ _ (Or.inr (Or.inl ⟨hk, Or.inl rfl⟩)) r1, h1,
        rd _ _ (Or.inr (Or.inl ⟨hk, Or.inr rfl⟩)) r2, hc0⟩
    · obtain ⟨c0, r1, hc0⟩ := hbt.br hk i hi
      exact ⟨c0, rd _ _ (Or.inr (Or.inr ⟨hk, i, hi, rfl⟩)) r1, hc0⟩

end InitECandidate.Solver.GuestBound
