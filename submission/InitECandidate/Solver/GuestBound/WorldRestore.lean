import InitECandidate.Solver.GuestBound.TrieSeg

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

/-- What the rest of the proof may rely on about the heap: `D t kl` tables
known to be live, with their key length (frames name their tables through it), `B` ranges known to
be free blocks (buffers), `Cn` cells known to hold a given word inside a free
block (fields of container records such as `ts`), `Nd` addresses known to be
trie nodes, `Im` blocks that are never written again (nibble arrays). -/
structure Reg where
  D : Word → Word → Prop
  B : Word → Word → Prop
  Cn : Word → Word → Prop
  Nd : Word → Prop
  Im : Word → Word → Prop
  /-- Known nodes with their kinds. -/
  Kd : Word → Word → Prop
  /-- Trie handles: 16 bytes, the root pointer at `+0`. -/
  Tr : Word → Prop
  /-- Levels of trie nodes: depth in nibbles below the root. -/
  Lv : Word → Nat → Prop
  /-- The level at which the children of an extension or branch sit. -/
  Cv : Word → Nat → Prop
  /-- Recorded segments (pointer and length) of leaves and extensions. -/
  Sg : Word → Word → Word → Prop

/-- The cells of the trie handles. -/
def TrCell (Tr : Word → Prop) (x : Word) : Prop := ∃ t, Tr t ∧ (x = t ∨ x = t + 8#64)

/-- The value cells of a node: pointer and length of a leaf's or a branch's value. -/
def ValCell (a k x : Word) : Prop :=
  (k = 1#64 ∧ (x = a + 48#64 ∨ x = a + 56#64)) ∨
    (k = 3#64 ∧ (x = a + 160#64 ∨ x = a + 168#64))

theorem ValCell.inside {m : Word → Option (PanValue Word)} {pv : Word} {N : Word → Option Word}
    {a k x : Word} (h : NodeAt m pv N a k) (hx : ValCell a k x) :
    a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k := by
  rcases hx with ⟨hk, rfl | rfl⟩ | ⟨hk, rfl | rfl⟩
  · have e := node_off h 48 (by omega)
    have hsz : nodeSize k = 64 := by rw [hk]; rfl
    change (a + 48#64).toNat = _ at e
    omega
  · have e := node_off h 56 (by omega)
    have hsz : nodeSize k = 64 := by rw [hk]; rfl
    change (a + 56#64).toNat = _ at e
    omega
  · have e := node_off h 160 (by omega)
    have hsz : nodeSize k = 176 := by rw [hk]; rfl
    change (a + 160#64).toNat = _ at e
    omega
  · have e := node_off h 168 (by omega)
    have hsz : nodeSize k = 176 := by rw [hk]; rfl
    change (a + 168#64).toNat = _ at e
    omega

theorem ValCell.al {m : Word → Option (PanValue Word)} {pv : Word} {N : Word → Option Word}
    {a k x : Word} (h : NodeAt m pv N a k) (hx : ValCell a k x) : x.toNat % 8 = 0 := by
  have hal := h.al
  rcases hx with ⟨hk, rfl | rfl⟩ | ⟨hk, rfl | rfl⟩
  · have e := node_off h 48 (by omega)
    change (a + 48#64).toNat = _ at e
    omega
  · have e := node_off h 56 (by omega)
    change (a + 56#64).toNat = _ at e
    omega
  · have e := node_off h 160 (by omega)
    change (a + 160#64).toNat = _ at e
    omega
  · have e := node_off h 168 (by omega)
    change (a + 168#64).toNat = _ at e
    omega

/-- A structural or value cell of a node. -/
def NCell (a k x : Word) : Prop := StructCell a k x ∨ ValCell a k x

theorem NCell.inside {m : Word → Option (PanValue Word)} {pv : Word} {N : Word → Option Word}
    {a k x : Word} (h : NodeAt m pv N a k) (hx : NCell a k x) :
    a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k :=
  hx.elim (fun h1 => h1.inside h) (fun h1 => h1.inside h)

/-- A value `(vp, vl)` that later steps do not write: short, and either in the
input area below the heap or made of frozen cells. -/
def VRange (Rg : Reg) (vp vl : Word) : Prop :=
  vl.toNat < 2 ^ 32 ∧ (vp.toNat + vl.toNat ≤ HBASE ∨
    ∀ (x : Word) (j : Nat), x.toNat % 8 = 0 → j < vl.toNat → x.toNat ≤ vp.toNat + j →
      vp.toNat + j < x.toNat + 8 → ∃ w, Rg.Cn x w)

theorem VRange.zero (Rg : Reg) (vp : Word) : VRange Rg vp 0#64 :=
  ⟨by decide, Or.inr (fun x j _ hj => absurd hj (by simp))⟩

/-- The structural and value cells of the nodes. -/
def LvCell (N : Word → Option Word) (x : Word) : Prop :=
  ∃ a k, N a = some k ∧ NCell a k x

/-- Leaf and branch values are `VRange`s. -/
def ValsOK (Rg : Reg) (m : Word → Option (PanValue Word)) (N : Word → Option Word) : Prop :=
  ∀ a k, N a = some k →
    (k = 1#64 → ∃ vp vl, Rd m (a + 48#64) vp ∧ Rd m (a + 56#64) vl ∧ VRange Rg vp vl) ∧
    (k = 3#64 → ∃ vp vl, Rd m (a + 160#64) vp ∧ Rd m (a + 168#64) vl ∧ VRange Rg vp vl)

/-- The value cells of the nodes. -/
def VCellN (N : Word → Option Word) (x : Word) : Prop :=
  ∃ a k, N a = some k ∧ ValCell a k x

theorem VCellN.lv {N : Word → Option Word} {x : Word} (h : VCellN N x) : LvCell N x := by
  obtain ⟨a, k, hN, hs⟩ := h
  exact ⟨a, k, hN, Or.inr hs⟩

theorem ValsOK.frame' {Rg : Reg} {m m' : Word → Option (PanValue Word)} {N : Word → Option Word}
    (h : ValsOK Rg m N) (hm : ∀ x, VCellN N x → m' x = m x) : ValsOK Rg m' N := by
  intro a k hN
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨vp, vl, r1, r2, hv⟩ := (h a k hN).1 hk
    refine ⟨vp, vl, ?_, ?_, hv⟩
    · unfold Rd at r1 ⊢
      rw [hm _ ⟨a, k, hN, Or.inl ⟨hk, Or.inl rfl⟩⟩]
      exact r1
    · unfold Rd at r2 ⊢
      rw [hm _ ⟨a, k, hN, Or.inl ⟨hk, Or.inr rfl⟩⟩]
      exact r2
  · obtain ⟨vp, vl, r1, r2, hv⟩ := (h a k hN).2 hk
    refine ⟨vp, vl, ?_, ?_, hv⟩
    · unfold Rd at r1 ⊢
      rw [hm _ ⟨a, k, hN, Or.inr ⟨hk, Or.inl rfl⟩⟩]
      exact r1
    · unfold Rd at r2 ⊢
      rw [hm _ ⟨a, k, hN, Or.inr ⟨hk, Or.inr rfl⟩⟩]
      exact r2

theorem ValsOK.frame {Rg : Reg} {m m' : Word → Option (PanValue Word)} {N : Word → Option Word}
    (h : ValsOK Rg m N) (hm : ∀ x, LvCell N x → m' x = m x) : ValsOK Rg m' N :=
  h.frame' (fun x hx => hm x hx.lv)

theorem VRange.mono {Rg Rg' : Reg} {vp vl : Word} (h : VRange Rg vp vl)
    (hc : ∀ x w, Rg.Cn x w → Rg'.Cn x w) : VRange Rg' vp vl := by
  obtain ⟨h1, h2 | h2⟩ := h
  · exact ⟨h1, Or.inl h2⟩
  · refine ⟨h1, Or.inr (fun x j a b c d => ?_)⟩
    obtain ⟨w, hw⟩ := h2 x j a b c d
    exact ⟨w, hc x w hw⟩

theorem ValsOK.mono {Rg Rg' : Reg} {m : Word → Option (PanValue Word)} {N : Word → Option Word}
    (h : ValsOK Rg m N) (hc : ∀ x w, Rg.Cn x w → Rg'.Cn x w) : ValsOK Rg' m N := by
  intro a k hN
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨vp, vl, r1, r2, hv⟩ := (h a k hN).1 hk
    exact ⟨vp, vl, r1, r2, hv.mono hc⟩
  · obtain ⟨vp, vl, r1, r2, hv⟩ := (h a k hN).2 hk
    exact ⟨vp, vl, r1, r2, hv.mono hc⟩

/-- The child of an extension sits at the extension's child level. -/
def LvX (Rg : Reg) (m : Word → Option (PanValue Word)) (N : Word → Option Word) : Prop :=
  ∀ a ℓc c, N a = some 2#64 → Rg.Cv a ℓc → Rd m (a + 48#64) c → c ≠ 0#64 → Rg.Lv c ℓc

/-- The children of a branch sit at the branch's child level. -/
def LvB (Rg : Reg) (m : Word → Option (PanValue Word)) (N : Word → Option Word) : Prop :=
  ∀ a ℓc i c, N a = some 3#64 → Rg.Cv a ℓc → i < 16 →
    Rd m (a + BitVec.ofNat 64 (32 + 8 * i)) c → c ≠ 0#64 → Rg.Lv c ℓc

/-- The child level of an extension is its level plus the segment length. -/
def CvX (Rg : Reg) (m : Word → Option (PanValue Word)) (N : Word → Option Word) : Prop :=
  ∀ a ℓ ℓc nl, Rg.Lv a ℓ → Rg.Cv a ℓc → N a = some 2#64 → Rd m (a + 40#64) nl →
    ℓc = ℓ + nl.toNat

/-- The structural cells of the nodes. -/
def SCellN (N : Word → Option Word) (x : Word) : Prop :=
  ∃ a k, N a = some k ∧ StructCell a k x

theorem SCellN.lv {N : Word → Option Word} {x : Word} (h : SCellN N x) : LvCell N x := by
  obtain ⟨a, k, hN, hs⟩ := h
  exact ⟨a, k, hN, Or.inl hs⟩

theorem LvX.frame' {Rg : Reg} {m m' : Word → Option (PanValue Word)} {N : Word → Option Word}
    (h : LvX Rg m N) (hm : ∀ x, SCellN N x → m' x = m x) : LvX Rg m' N := by
  intro a ℓc c hN hcv r2 hc
  refine h a ℓc c hN hcv ?_ hc
  unfold Rd at r2 ⊢
  rw [← hm _ ⟨a, _, hN, Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)⟩]
  exact r2

theorem LvB.frame' {Rg : Reg} {m m' : Word → Option (PanValue Word)} {N : Word → Option Word}
    (h : LvB Rg m N) (hm : ∀ x, SCellN N x → m' x = m x) : LvB Rg m' N := by
  intro a ℓc i c hN hcv hi r1 hc
  refine h a ℓc i c hN hcv hi ?_ hc
  unfold Rd at r1 ⊢
  rw [← hm _ ⟨a, _, hN, Or.inr (Or.inr ⟨rfl, i, hi, rfl⟩)⟩]
  exact r1

theorem CvX.frame' {Rg : Reg} {m m' : Word → Option (PanValue Word)} {N : Word → Option Word}
    (h : CvX Rg m N) (hm : ∀ x, SCellN N x → m' x = m x) : CvX Rg m' N := by
  intro a ℓ ℓc nl hl hcv hN r1
  refine h a ℓ ℓc nl hl hcv hN ?_
  unfold Rd at r1 ⊢
  rw [← hm _ ⟨a, _, hN, Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)⟩]
  exact r1

theorem LvX.frame {Rg : Reg} {m m' : Word → Option (PanValue Word)} {N : Word → Option Word}
    (h : LvX Rg m N) (hm : ∀ x, LvCell N x → m' x = m x) : LvX Rg m' N :=
  h.frame' (fun x hx => hm x hx.lv)

theorem LvB.frame {Rg : Reg} {m m' : Word → Option (PanValue Word)} {N : Word → Option Word}
    (h : LvB Rg m N) (hm : ∀ x, LvCell N x → m' x = m x) : LvB Rg m' N :=
  h.frame' (fun x hx => hm x hx.lv)

theorem CvX.frame {Rg : Reg} {m m' : Word → Option (PanValue Word)} {N : Word → Option Word}
    (h : CvX Rg m N) (hm : ∀ x, LvCell N x → m' x = m x) : CvX Rg m' N :=
  h.frame' (fun x hx => hm x hx.lv)

/-- Recorded segments are what the segment cells hold. -/
def SgOK (Rg : Reg) (m : Word → Option (PanValue Word)) (N : Word → Option Word) : Prop :=
  ∀ a sp nl, Rg.Sg a sp nl → (∃ k, N a = some k ∧ (k = 1#64 ∨ k = 2#64)) ∧
    Rd m (a + 32#64) sp ∧ Rd m (a + 40#64) nl

theorem SgOK.frame {Rg : Reg} {m m' : Word → Option (PanValue Word)} {N : Word → Option Word}
    (h : SgOK Rg m N) (hm : ∀ x, SegCell Rg.Im N x → m' x = m x) : SgOK Rg m' N := by
  intro a sp nl hS
  obtain ⟨⟨k, hN, hk⟩, r1, r2⟩ := h a sp nl hS
  refine ⟨⟨k, hN, hk⟩, ?_, ?_⟩
  · unfold Rd at r1 ⊢
    rw [hm _ (Or.inl ⟨a, k, hN, hk, Or.inl rfl⟩)]
    exact r1
  · unfold Rd at r2 ⊢
    rw [hm _ (Or.inl ⟨a, k, hN, hk, Or.inr rfl⟩)]
    exact r2

/-- A structural cell is aligned. -/
theorem StructCell.al {m : Word → Option (PanValue Word)} {pv : Word} {N : Word → Option Word}
    {a k x : Word} (h : NodeAt m pv N a k) (hx : StructCell a k x) : x.toNat % 8 = 0 := by
  have hal := h.al
  rcases hx with rfl | ⟨hk, rfl | rfl⟩ | ⟨hk, i, hi, rfl⟩
  · exact hal
  · have e := node_off h 40 (by omega)
    change (a + 40#64).toNat = _ at e
    omega
  · have e := node_off h 48 (by omega)
    change (a + 48#64).toNat = _ at e
    omega
  · have e := node_off h (32 + 8 * i) (by omega)
    omega

theorem NCell.al {m : Word → Option (PanValue Word)} {pv : Word} {N : Word → Option Word}
    {a k x : Word} (h : NodeAt m pv N a k) (hx : NCell a k x) : x.toNat % 8 = 0 :=
  hx.elim (fun h1 => StructCell.al h h1) (fun h1 => h1.al h)

/-- Immutable blocks and the nibble segments of trie nodes: the blocks are
free of every structure and of the writable blocks `B`, and every leaf or
extension segment is empty or a nibble array inside one of them. -/
structure ImOK (Rg : Reg) (m : Word → Option (PanValue Word)) (pv : Word)
    (T : Word → Option HtabV) (N : Word → Option Word) (J C : Word) : Prop where
  free : ∀ lo hi, Rg.Im lo hi → lo.toNat % 8 = 0 ∧ FreeOK pv T N J C lo hi
  offB : ∀ lo hi a b, Rg.B lo hi → Rg.Im a b → hi.toNat ≤ a.toNat ∨ b.toNat ≤ lo.toNat
  segs : SegsOK Rg.Im m N
  nib : ∀ lo hi, Rg.Im lo hi → Nibs m lo (hi.toNat - lo.toNat)
  kd : ∀ a k, Rg.Kd a k → N a = some k
  kn : ∀ a k, Rg.Kd a k → Rg.Nd a
  /-- Every node is registered, so children of registered nodes are. -/
  full : ∀ a k, N a = some k → Rg.Kd a k
  /-- A trie handle is an aligned free range of 16 bytes. -/
  trf : ∀ t, Rg.Tr t → t.toNat % 8 = 0 ∧
    ∃ hi : Word, hi.toNat = t.toNat + 16 ∧ FreeOK pv T N J C t hi
  /-- Its root pointer is null or a node. -/
  trv : ∀ t, Rg.Tr t → ∃ root sec : Word, Rd m t root ∧ Rd m (t + 8#64) sec ∧ IsChild N root ∧
    (root ≠ 0#64 → Rg.Lv root 0)
  offT : ∀ lo hi t, Rg.B lo hi → Rg.Tr t → hi.toNat ≤ t.toNat ∨ t.toNat + 16 ≤ lo.toNat
  offC : ∀ x w t, Rg.Cn x w → Rg.Tr t → x.toNat + 8 ≤ t.toNat ∨ t.toNat + 16 ≤ x.toNat
  offI : ∀ lo hi t, Rg.Im lo hi → Rg.Tr t → hi.toNat ≤ t.toNat ∨ t.toNat + 16 ≤ lo.toNat
  offTT : ∀ t u, Rg.Tr t → Rg.Tr u → t = u ∨ t.toNat + 16 ≤ u.toNat ∨ u.toNat + 16 ≤ t.toNat
  /-- Levelled addresses are nodes, with one level each. -/
  lvk : ∀ a ℓ, Rg.Lv a ℓ → ∃ k, N a = some k
  lvu : ∀ a ℓ ℓ', Rg.Lv a ℓ → Rg.Lv a ℓ' → ℓ = ℓ'
  lvx : LvX Rg m N
  lvb : LvB Rg m N
  cvk : ∀ a ℓc, Rg.Cv a ℓc → ∃ k, N a = some k
  cvu : ∀ a x y, Rg.Cv a x → Rg.Cv a y → x = y
  cvx : CvX Rg m N
  cvb : ∀ a ℓ ℓc, Rg.Lv a ℓ → Rg.Cv a ℓc → N a = some 3#64 → ℓc = ℓ + 1
  /-- A levelled extension or branch has a child level. -/
  lvc : ∀ a ℓ k, Rg.Lv a ℓ → N a = some k → (k = 2#64 ∨ k = 3#64) → ∃ ℓc, Rg.Cv a ℓc
  sg : SgOK Rg m N
  /-- Leaf and branch values are short and immutable. -/
  vals : ValsOK Rg m N

/-- A handle cell is an aligned cell inside the handle. -/
theorem tr_cell_in {Rg : Reg} {m : Word → Option (PanValue Word)} {pv : Word}
    {T : Word → Option HtabV} {N : Word → Option Word} {J C t x : Word}
    (h : ImOK Rg m pv T N J C) (ht : Rg.Tr t) (hx : x = t ∨ x = t + 8#64) :
    x.toNat % 8 = 0 ∧ t.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ t.toNat + 16 ∧
      ∃ hi : Word, hi.toNat = t.toNat + 16 ∧ FreeOK pv T N J C t hi := by
  obtain ⟨h8, hi, e, hf⟩ := h.trf t ht
  have := hf.hi_
  have := pv.isLt
  have e8 : (t + 8#64).toNat = t.toNat + 8 := by
    rw [BitVec.toNat_add, show (8#64 : Word).toNat = 8 by decide]
    omega
  rcases hx with rfl | rfl
  · exact ⟨h8, by omega, by omega, hi, e, hf⟩
  · exact ⟨by omega, by omega, by omega, hi, e, hf⟩

/-- A segment cell of a node is an aligned cell inside the node. -/
theorem seg_cell_in {m : Word → Option (PanValue Word)} {pv a k x : Word}
    {N : Word → Option Word} (hat : NodeAt m pv N a k) (hk : k = 1#64 ∨ k = 2#64)
    (hx : x = a + 32#64 ∨ x = a + 40#64) :
    x.toNat % 8 = 0 ∧ a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k := by
  have hal := hat.al
  have htop := hat.top
  have hsz : 56 ≤ nodeSize k := by
    rcases hk with rfl | rfl <;> simp [nodeSize]
  have e32 : (a + 32#64).toNat = a.toNat + 32 := by bv_omega
  have e40 : (a + 40#64).toNat = a.toNat + 40 := by bv_omega
  rcases hx with rfl | rfl <;> omega

/-- A heap step that misses the segment cells leaves them alone. -/
theorem seg_cell_step {Im : Word → Word → Prop} {m m' : Word → Option (PanValue Word)}
    {pv pv' : Word} {T : Word → Option HtabV} {N : Word → Option Word} {J C n : Word}
    {F : Word → Prop} (hW : HeapW m pv T N J C n)
    (hfree : ∀ lo hi, Im lo hi → FreeOK pv T N J C lo hi) (hs : HeapStep m pv m' pv' F)
    (hF : ∀ x, SegCell Im N x → ¬ F x) : ∀ x, SegCell Im N x → m' x = m x := by
  intro x hx
  refine hs.frame x ?_ (hF x hx) ?_
  · rcases hx with ⟨a, k, hN, hk, hx⟩ | ⟨h8, -⟩
    · exact (seg_cell_in (hW.nodes.at_ a k hN) hk hx).1
    · exact h8
  · rcases hx with ⟨a, k, hN, hk, hx⟩ | ⟨-, lo, hi, hI, h1, h2⟩
    · have hat := hW.nodes.at_ a k hN
      have := seg_cell_in hat hk hx
      have := hat.hi
      omega
    · have := (hfree lo hi hI).hi_
      omega

/-- The nibbles of the immutable blocks, when their cells did not change. -/
theorem nib_frame {Im : Word → Word → Prop} {m m' : Word → Option (PanValue Word)}
    {N : Word → Option Word}
    (h8 : ∀ lo hi, Im lo hi → lo.toNat % 8 = 0)
    (h : ∀ lo hi, Im lo hi → Nibs m lo (hi.toNat - lo.toNat))
    (hm : ∀ x, SegCell Im N x → m' x = m x) :
    ∀ lo hi, Im lo hi → Nibs m' lo (hi.toNat - lo.toNat) := by
  intro lo hi hI
  have := hi.isLt
  exact (h lo hi hI).frame (lo := lo) (h8 lo hi hI) (Nat.le_refl _) (by omega)
    (fun x hx8 h1 h2 => hm x (Or.inr ⟨hx8, lo, hi, hI, h1, by omega⟩))

/-- The segments survive a heap step that misses the segment cells. -/
theorem SegsOK.step {Im : Word → Word → Prop} {m m' : Word → Option (PanValue Word)}
    {pv pv' : Word} {T : Word → Option HtabV} {N : Word → Option Word} {J C n : Word}
    {F : Word → Prop} (h : SegsOK Im m N) (hW : HeapW m pv T N J C n)
    (hfree : ∀ lo hi, Im lo hi → FreeOK pv T N J C lo hi) (hs : HeapStep m pv m' pv' F)
    (hF : ∀ x, SegCell Im N x → ¬ F x) : SegsOK Im m' N :=
  h.frame (seg_cell_step hW hfree hs hF)

/-- After a table step. -/
theorem ImOK.tab_step {Rg : Reg} {m m' : Word → Option (PanValue Word)} {pv pv' t : Word}
    {T : Word → Option HtabV} {N : Word → Option Word} {J C n : Word} {v v' : HtabV}
    (h : ImOK Rg m pv T N J C) (hW : HeapW m pv T N J C n)
    (hs : TabStep m pv T t v m' pv' v') : ImOK Rg m' pv' (stepT T t v') N J C := by
  have hF : ∀ x, SegCell Rg.Im N x → ¬ TabFoot t v x := by
    intro x hx hfoot
    rcases hx with ⟨a, k, hN, hk, hx⟩ | ⟨-, lo, hi, hI, h1, h2⟩
    · have hin := seg_cell_in (hW.nodes.at_ a k hN) hk hx
      rcases hW.tn t v a k hs.hT hN x hfoot with h3 | h3 <;> omega
    · rcases (h.free lo hi hI).2.tab t v hs.hT x hfoot with h3 | h3 <;> omega
  have hT : ∀ x, TrCell Rg.Tr x → m' x = m x := by
    rintro x ⟨u, hu, hx⟩
    obtain ⟨h8, h1, h2, hi, e, hf⟩ := tr_cell_in h hu hx
    have := hf.hi_
    refine hs.heapStep.frame x h8 (fun hfoot => ?_) (by omega)
    rcases hf.tab t v hs.hT x hfoot with h3 | h3 <;> omega
  have hLv : ∀ x, LvCell N x → m' x = m x := by
    rintro x ⟨a, k, hN, hsx⟩
    have hat := hW.nodes.at_ a k hN
    have hin := hsx.inside hat
    have := hat.hi
    refine hs.heapStep.frame x (hsx.al hat) (fun hfoot => ?_) (by omega)
    rcases hW.tn t v a k hs.hT hN x hfoot with h3 | h3 <;> omega
  exact ⟨fun lo hi hI => ⟨(h.free lo hi hI).1, (h.free lo hi hI).2.tab_step hs⟩, h.offB,
    h.segs.step hW (fun lo hi hI => (h.free lo hi hI).2) hs.heapStep hF,
    nib_frame (fun lo hi hI => (h.free lo hi hI).1) h.nib
      (seg_cell_step hW (fun lo hi hI => (h.free lo hi hI).2) hs.heapStep hF), h.kd, h.kn, h.full,
    fun u hu => ⟨(h.trf u hu).1, by
      obtain ⟨hi, e, hf⟩ := (h.trf u hu).2
      exact ⟨hi, e, hf.tab_step hs⟩⟩,
    fun u hu => by
      obtain ⟨root, sec, r1, r2, hc⟩ := h.trv u hu
      refine ⟨root, sec, ?_, ?_, hc⟩
      · unfold Rd at r1 ⊢
        rw [hT u ⟨u, hu, Or.inl rfl⟩]
        exact r1
      · unfold Rd at r2 ⊢
        rw [hT _ ⟨u, hu, Or.inr rfl⟩]
        exact r2,
    h.offT, h.offC, h.offI, h.offTT, h.lvk, h.lvu, h.lvx.frame hLv, h.lvb.frame hLv, h.cvk, h.cvu,
    h.cvx.frame hLv, h.cvb, h.lvc,
    h.sg.frame (seg_cell_step hW (fun lo hi hI => (h.free lo hi hI).2) hs.heapStep hF),
    h.vals.frame hLv⟩

/-- A cell `ImOK` depends on is an aligned heap cell below the heap pointer. -/
theorem ImOK.cell_bounds {Rg : Reg} {m : Word → Option (PanValue Word)} {pv x : Word}
    {T : Word → Option HtabV} {N : Word → Option Word} {J C n : Word}
    (h : ImOK Rg m pv T N J C) (hW : HeapW m pv T N J C n)
    (hx : SegCell Rg.Im N x ∨ TrCell Rg.Tr x ∨ LvCell N x) :
    x.toNat % 8 = 0 ∧ HBASE ≤ x.toNat ∧ x.toNat < pv.toNat := by
  rcases hx with (⟨a, k, hN, hk, hx⟩ | ⟨h8, lo, hi, hI, h1, h2⟩) | ⟨u, hu, hx⟩ | ⟨a, k, hN, hsx⟩
  · have hat := hW.nodes.at_ a k hN
    have hin := seg_cell_in hat hk hx
    have h1 := hat.hi
    have h2 := hat.lo
    exact ⟨hin.1, by omega, by omega⟩
  · have hf := (h.free lo hi hI).2
    have := hf.lo_
    have := hf.hi_
    exact ⟨h8, by omega, by omega⟩
  · obtain ⟨h8, h1, h2, hi, e, hf⟩ := tr_cell_in h hu hx
    have := hf.lo_
    have := hf.hi_
    exact ⟨h8, by omega, by omega⟩
  · have hat := hW.nodes.at_ a k hN
    have hin := hsx.inside hat
    have h1 := hat.hi
    have h2 := hat.lo
    exact ⟨hsx.al hat, by omega, by omega⟩

/-- `ImOK` after a change that leaves the segment, handle and structural cells
alone, with the value invariant supplied. -/
theorem ImOK.frame' {Rg : Reg} {m m' : Word → Option (PanValue Word)} {pv pv' : Word}
    {T : Word → Option HtabV} {N : Word → Option Word} {J C : Word}
    (h : ImOK Rg m pv T N J C) (hpv : pv.toNat ≤ pv'.toNat)
    (hm : ∀ x, SegCell Rg.Im N x ∨ TrCell Rg.Tr x ∨ SCellN N x → m' x = m x)
    (hv : ValsOK Rg m' N) :
    ImOK Rg m' pv' T N J C :=
  ⟨fun lo hi hI => ⟨(h.free lo hi hI).1, (h.free lo hi hI).2.mono hpv⟩, h.offB,
    h.segs.frame (fun x hx => hm x (Or.inl hx)),
    nib_frame (fun lo hi hI => (h.free lo hi hI).1) h.nib (fun x hx => hm x (Or.inl hx)),
    h.kd, h.kn, h.full,
    fun u hu => ⟨(h.trf u hu).1, by
      obtain ⟨hi, e, hf⟩ := (h.trf u hu).2
      exact ⟨hi, e, hf.mono hpv⟩⟩,
    fun u hu => by
      obtain ⟨root, sec, r1, r2, hc⟩ := h.trv u hu
      refine ⟨root, sec, ?_, ?_, hc⟩
      · unfold Rd at r1 ⊢
        rw [hm u (Or.inr (Or.inl ⟨u, hu, Or.inl rfl⟩))]
        exact r1
      · unfold Rd at r2 ⊢
        rw [hm _ (Or.inr (Or.inl ⟨u, hu, Or.inr rfl⟩))]
        exact r2,
    h.offT, h.offC, h.offI, h.offTT, h.lvk, h.lvu,
    h.lvx.frame' (fun x hx => hm x (Or.inr (Or.inr hx))),
    h.lvb.frame' (fun x hx => hm x (Or.inr (Or.inr hx))), h.cvk, h.cvu,
    h.cvx.frame' (fun x hx => hm x (Or.inr (Or.inr hx))), h.cvb, h.lvc,
    h.sg.frame (fun x hx => hm x (Or.inl hx)),
    hv⟩

/-- `ImOK` after a change that leaves its cells alone (same structures). -/
theorem ImOK.frame {Rg : Reg} {m m' : Word → Option (PanValue Word)} {pv pv' : Word}
    {T : Word → Option HtabV} {N : Word → Option Word} {J C : Word}
    (h : ImOK Rg m pv T N J C) (hpv : pv.toNat ≤ pv'.toNat)
    (hm : ∀ x, SegCell Rg.Im N x ∨ TrCell Rg.Tr x ∨ LvCell N x → m' x = m x) :
    ImOK Rg m' pv' T N J C :=
  ⟨fun lo hi hI => ⟨(h.free lo hi hI).1, (h.free lo hi hI).2.mono hpv⟩, h.offB,
    h.segs.frame (fun x hx => hm x (Or.inl hx)),
    nib_frame (fun lo hi hI => (h.free lo hi hI).1) h.nib (fun x hx => hm x (Or.inl hx)),
    h.kd, h.kn, h.full,
    fun u hu => ⟨(h.trf u hu).1, by
      obtain ⟨hi, e, hf⟩ := (h.trf u hu).2
      exact ⟨hi, e, hf.mono hpv⟩⟩,
    fun u hu => by
      obtain ⟨root, sec, r1, r2, hc⟩ := h.trv u hu
      refine ⟨root, sec, ?_, ?_, hc⟩
      · unfold Rd at r1 ⊢
        rw [hm u (Or.inr (Or.inl ⟨u, hu, Or.inl rfl⟩))]
        exact r1
      · unfold Rd at r2 ⊢
        rw [hm _ (Or.inr (Or.inl ⟨u, hu, Or.inr rfl⟩))]
        exact r2,
    h.offT, h.offC, h.offI, h.offTT, h.lvk, h.lvu,
    h.lvx.frame (fun x hx => hm x (Or.inr (Or.inr hx))),
    h.lvb.frame (fun x hx => hm x (Or.inr (Or.inr hx))), h.cvk, h.cvu,
    h.cvx.frame (fun x hx => hm x (Or.inr (Or.inr hx))), h.cvb, h.lvc,
    h.sg.frame (fun x hx => hm x (Or.inl hx)),
    h.vals.frame (fun x hx => hm x (Or.inr (Or.inr hx)))⟩

/-- Heap pointer, live tables, journal and trie nodes, with the registry `Rg`. -/
def WorldTJ (Rg : Reg) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) : Prop :=
  ∃ (pv : Word) (T : Word → Option HtabV) (N : Word → Option Word) (J C n : Word),
    g "heap_ptr" = some (.word pv) ∧ InHeap pv ∧ g "journal" = some (.word J) ∧
    g "journal_cap" = some (.word C) ∧ g "journal_n" = some (.word n) ∧
    HeapW m pv T N J C n ∧ (∀ t kl, Rg.D t kl → ∃ v, T t = some v ∧ v.kl = kl) ∧
    (∀ lo hi, Rg.B lo hi → FreeOK pv T N J C lo hi) ∧
    (∀ x w, Rg.Cn x w → Rd m x w ∧ x.toNat % 8 = 0 ∧
      ∃ hi : Word, hi.toNat = x.toNat + 8 ∧ FreeOK pv T N J C x hi) ∧
    (∀ a, Rg.Nd a → ∃ k, N a = some k) ∧ ImOK Rg m pv T N J C

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
def RestI (Rg : Reg) (s a : St σ) : Prop :=
  a.ffi = s.ffi ∧ WorldTJ Rg a.globals a.memory ∧
    (∀ x, x ≠ "heap_ptr" → x ≠ "journal_n" → a.globals x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      a.memory addr = s.memory addr

theorem HeapW.shrink {m : Word → Option (PanValue Word)} {pv : Word} {T : Word → Option HtabV}
    {N : Word → Option Word} {J C n n' : Word} (h : HeapW m pv T N J C n)
    (hn : n'.toNat ≤ n.toNat) : HeapW m pv T N J C n' :=
  ⟨h.pvH, h.tabs, h.jrn.shrink hn, h.nodes, h.tn, h.jn⟩

theorem stepT_dom {D : Word → Word → Prop} {T : Word → Option HtabV}
    (hD : ∀ t kl, D t kl → ∃ v, T t = some v ∧ v.kl = kl) {t0 : Word} {v0 v' : HtabV}
    (hT0 : T t0 = some v0) (hkl : v'.kl = v0.kl) :
    ∀ t kl, D t kl → ∃ v, stepT T t0 v' t = some v ∧ v.kl = kl := by
  classical
  intro t kl ht
  obtain ⟨v, hv, hk⟩ := hD t kl ht
  unfold stepT
  by_cases e : t = t0
  · subst e
    have : v = v0 := Option.some.inj (hv.symm.trans hT0)
    subst this
    exact ⟨v', by simp, hkl.trans hk⟩
  · exact ⟨v, by simp [e, hv], hk⟩

/-- The live tables of a registry, without key lengths. -/
def Reg.live (Rg : Reg) : Word → Prop := fun t => ∃ kl, Rg.D t kl

theorem worldTJ_step {Rg : Reg}
    {g g' : VarName → Option (PanValue Word)}
    {m m' : Word → Option (PanValue Word)} {pv pv' t : Word} {T : Word → Option HtabV}
    {N : Word → Option Word} {v v' : HtabV} {J C n n' : Word}
    (hp' : g' "heap_ptr" = some (.word pv')) (hpH' : InHeap pv')
    (hg : ∀ x, x ≠ "heap_ptr" → g' x = g x) (hJg : g "journal" = some (.word J))
    (hCg : g "journal_cap" = some (.word C)) (hng : g "journal_n" = some (.word n'))
    (hW : HeapW m pv T N J C n) (hD : ∀ t kl, Rg.D t kl → ∃ v, T t = some v ∧ v.kl = kl)
    (hB : ∀ lo hi, Rg.B lo hi → FreeOK pv T N J C lo hi)
    (hCn : ∀ x w, Rg.Cn x w → Rd m x w ∧ x.toNat % 8 = 0 ∧
      ∃ hi : Word, hi.toNat = x.toNat + 8 ∧ FreeOK pv T N J C x hi)
    (hNd : ∀ a, Rg.Nd a → ∃ k, N a = some k) (hIm : ImOK Rg m pv T N J C)
    (hn : n'.toNat ≤ n.toNat)
    (hs : TabStep m pv T t v m' pv' v') : WorldTJ Rg g' m' := by
  refine ⟨pv', stepT T t v', N, J, C, n', hp', hpH', by rw [hg _ (by decide)]; exact hJg,
    by rw [hg _ (by decide)]; exact hCg, by rw [hg _ (by decide)]; exact hng,
    hW.tab_step hs hn hpH'.1, stepT_dom hD hs.hT hs.kl, fun lo hi h => (hB lo hi h).tab_step hs,
    fun x w h => ?_, hNd, hIm.tab_step hW hs⟩
  obtain ⟨hr, h8, hi, hhi, hf⟩ := hCn x w h
  refine ⟨?_, h8, hi, hhi, hf.tab_step hs⟩
  unfold Rd at hr ⊢
  rw [hs.frame x h8 (fun hfoot => ?_) (by have := hf.hi_; omega)]
  · exact hr
  · rcases hf.tab t v hs.hT x hfoot with h1 | h1 <;> omega

set_option maxHeartbeats 4000000 in
/-- `state_restore(snap)` keeps heap pointer, tables and journal well formed,
changes no global other than `heap_ptr` and `journal_n`, and no memory
outside the heap. -/
theorem state_restore_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "state_restore" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ)
    (hW : WorldTJ Rg s.globals s.memory)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m', r = .returned l g' m' s.ffi [.word 0#64] ∧ WorldTJ Rg g' m' ∧
      (∀ x, x ≠ "heap_ptr" → x ≠ "journal_n" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 359 hE.functions (by guest_decl_at 359) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m', r = .returned l g' m' s.ffi [.word 0#64] ∧
    WorldTJ Rg g' m' ∧ (∀ x, x ≠ "heap_ptr" → x ≠ "journal_n" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  refine WPs.seqG (RestI Rg s) (WPs.loopG (I := RestI Rg s)
      ⟨rfl, hW, fun _ _ _ => rfl, fun _ _ => rfl⟩
    ?_ (fun a k hI _ => hI)) ?_
  rotate_left
  · rintro a ⟨hf, hWa, hga, hma⟩
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    exact ⟨_, _, _, by rw [hf], hWa, hga, hma⟩
  rintro ⟨la, ga, ma, fa⟩ ⟨hf, ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hD, hB, hCn, hNd, hIm⟩, hga, hma⟩ hct
  dsimp only at hf hp hJg hCg hng hHW hD hB hCn hNd hIm hga hma
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
      · exact ⟨rfl, ⟨pv, T, N, J, C, n - 1#64, g1p, hpH, g1J, g1C, g1n, hHW.shrink hnle, hD, hB, hCn, hNd, hIm⟩,
          fun x h1 h2 => (g1o x h2).trans (hga x h1 h2), hma⟩
      · obtain ⟨v', hs⟩ := TabStep.of_del hT hT0 hok hL hLk hrel
        exact ⟨rfl, worldTJ_step g1p hpH (fun _ _ => rfl) g1J g1C g1n hHW hD hB hCn hNd hIm hnle hs,
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
      exact ⟨rfl, worldTJ_step hp' hpH' hgl g1J g1C g1n hHW hD hB hCn hNd hIm hnle hs,
        fun x h1 h2 => (hgl x h1).trans ((g1o x h2).trans (hga x h1 h2)),
        fun addr ha => (hs.out addr ha).trans (hma addr ha)⟩

end InitECandidate.Solver.GuestBound
