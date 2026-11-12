import InitECandidate.Solver.GuestBound.WorldJournal
import InitECandidate.Solver.GuestBound.TrieNodes

/-!
# Tables, journal and trie nodes together

`HeapStep m pv m' pv' F`: a step that changed, below the old heap pointer,
only aligned cells in `F`, did not lower the heap pointer and changed nothing
outside the heap. Each structure persists across a step whose `F` misses its
cells (`TabsOK.persist`, `JournalOK.persist`, `NodesOK.persist`).

`HeapW`: the three structures with their mutual disjointness. Its lemmas are
the interface the world functions are proved against:

* `HeapW.tab_step`  – a table operation (`TabStep`);
* `HeapW.node_other` / `HeapW.node_child` – a store into a node;
* `HeapW.node_add` – a node built in fresh heap.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m m' : Word → Option (PanValue Word)} {pv pv' : Word} {T : Word → Option HtabV}
  {N : Word → Option Word} {J C n : Word}

/-- A step on the heap that, below the old heap pointer, changed only aligned cells in `F`. -/
structure HeapStep (m : Word → Option (PanValue Word)) (pv : Word)
    (m' : Word → Option (PanValue Word)) (pv' : Word) (F : Word → Prop) : Prop where
  pv_le : pv.toNat ≤ pv'.toNat
  frame : ∀ a : Word, a.toNat % 8 = 0 → ¬ F a → a.toNat < pv.toNat → m' a = m a
  out : ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m' a = m a

theorem TabStep.heapStep {t : Word} {v v' : HtabV} (h : TabStep m pv T t v m' pv' v') :
    HeapStep m pv m' pv' (TabFoot t v) :=
  ⟨h.pv_le, h.frame, h.out⟩

/-- A single store at an aligned heap address. -/
theorem HeapStep.store (x w : Word) (hlo : HBASE ≤ x.toNat) (hhi : x.toNat < 2952790016) :
    HeapStep m pv (setCell m x w) pv (fun a => a = x) := by
  refine ⟨Nat.le_refl _, fun a _ ha _ => setCell_ne _ ha, fun a ha => setCell_ne _ ?_⟩
  rintro rfl
  unfold HBASE at ha hlo
  omega

theorem TabsOK.persist {F : Word → Prop} (h : TabsOK m pv T) (hs : HeapStep m pv m' pv' F)
    (hF : ∀ t v, T t = some v → ∀ x, TabFoot t v x → ¬ F x) : TabsOK m' pv' T := by
  refine ⟨fun t v ht => ?_, h.disj⟩
  have hat := h.at_ t v ht
  obtain ⟨kind, rep, hok⟩ := hat.ok
  have := hs.pv_le
  exact ⟨⟨kind, rep, hok.frame hat.t8 (fun a ha => hs.frame a ha.1 (hF t v ht a ha)
    (hat.foot_lt ha).2)⟩, hat.t8, hat.lo, by have := hat.fin; omega⟩

theorem KeyFree.mono {kc kl : Word} (h : KeyFree pv T kc kl) (hpv : pv.toNat ≤ pv'.toNat) :
    KeyFree pv' T kc kl :=
  ⟨by have := h.1; omega, h.2⟩

theorem JournalOK.persist {F : Word → Prop} (h : JournalOK m pv T J C n)
    (hs : HeapStep m pv m' pv' F)
    (hF : ∀ x : Word, J.toNat ≤ x.toNat → x.toNat < J.toNat + 32 * C.toNat → ¬ F x) :
    JournalOK m' pv' T J C n := by
  have hJhi := h.hi
  have hal := h.al
  have hC := h.n_le
  have hpvlt := pv.isLt
  have hpp := hs.pv_le
  refine ⟨h.n_le, h.al, h.lo, by omega, h.off, fun i hi => ?_⟩
  obtain ⟨t0, kc, fl, val, v0, r0, r1, r2, r3, hT0, hkf⟩ := h.entry i hi
  have hbase : (J + BitVec.ofNat 64 (32 * i)).toNat = J.toNat + 32 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have keep : ∀ (c : Nat) (a : Word), a.toNat = J.toNat + 32 * i + c → c % 8 = 0 → c < 32 →
      ∀ w, Rd m a w → Rd m' a w := by
    intro c a ha hc8 hc w hr
    unfold Rd at hr ⊢
    rw [hs.frame a (by omega) (hF a (by omega) (by omega)) (by omega)]
    exact hr
  have b1 : (J + BitVec.ofNat 64 (32 * i) + 8#64).toNat = J.toNat + 32 * i + 8 := by
    rw [BitVec.toNat_add, hbase]
    simp
    omega
  have b2 : (J + BitVec.ofNat 64 (32 * i) + 16#64).toNat = J.toNat + 32 * i + 16 := by
    rw [BitVec.toNat_add, hbase]
    simp
    omega
  have b3 : (J + BitVec.ofNat 64 (32 * i) + 24#64).toNat = J.toNat + 32 * i + 24 := by
    rw [BitVec.toNat_add, hbase]
    simp
    omega
  exact ⟨t0, kc, fl, val, v0, keep 0 _ (by rw [hbase]; omega) (by omega) (by omega) _ r0,
    keep 8 _ b1 (by omega) (by omega) _ r1, keep 16 _ b2 (by omega) (by omega) _ r2,
    keep 24 _ b3 (by omega) (by omega) _ r3, hT0, hkf.mono hpp⟩

/-- A structural cell is aligned. -/
theorem StructCell.aligned {a k x : Word} (h : NodeAt m pv N a k) (hx : StructCell a k x) :
    x.toNat % 8 = 0 := by
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

theorem NodesOK.persist {F : Word → Prop} (h : NodesOK m pv N) (hs : HeapStep m pv m' pv' F)
    (hF : ∀ a k x, N a = some k → StructCell a k x → ¬ F x) : NodesOK m' pv' N := by
  refine h.frame hs.pv_le (fun a k x hN hx => ?_)
  have hat := h.at_ a k hN
  have hin := hx.inside hat
  have := hat.hi
  exact hs.frame x (hx.aligned hat) (hF a k x hN hx) (by omega)

/-- Tables, journal and trie nodes with their mutual disjointness. -/
structure HeapW (m : Word → Option (PanValue Word)) (pv : Word) (T : Word → Option HtabV)
    (N : Word → Option Word) (J C n : Word) : Prop where
  pvH : pv.toNat ≤ 2952790016
  tabs : TabsOK m pv T
  jrn : JournalOK m pv T J C n
  nodes : NodesOK m pv N
  tn : ∀ t v a k, T t = some v → N a = some k → ∀ x, TabFoot t v x →
    x.toNat < a.toNat ∨ a.toNat + nodeSize k ≤ x.toNat
  jn : ∀ a k, N a = some k →
    a.toNat + nodeSize k ≤ J.toNat ∨ J.toNat + 32 * C.toNat ≤ a.toNat

/-- A table operation. -/
theorem HeapW.tab_step {t : Word} {v v' : HtabV} {n' : Word} (h : HeapW m pv T N J C n)
    (hs : TabStep m pv T t v m' pv' v') (hn : n'.toNat ≤ n.toNat)
    (hpH' : pv'.toNat ≤ 2952790016) : HeapW m' pv' (stepT T t v') N J C n' := by
  classical
  refine ⟨hpH', h.tabs.step hs, h.jrn.step h.tabs hs hn,
    h.nodes.persist hs.heapStep (fun a k x hN hx hf => ?_), fun u w a k hu hN x hx => ?_, h.jn⟩
  · have hi := hx.inside (h.nodes.at_ a k hN)
    rcases h.tn t v a k hs.hT hN x hf with h1 | h1 <;> omega
  · unfold stepT at hu
    by_cases e : u = t
    · subst e
      simp only [if_true, Option.some.injEq] at hu
      subst hu
      rcases hs.foot x hx with hold | hge
      · exact h.tn u v a k hs.hT hN x hold
      · have := (h.nodes.at_ a k hN).hi
        exact Or.inr (by omega)
    · simp only [if_neg e] at hu
      exact h.tn u w a k hu hN x hx

/-- A store into a cell of node `a` that is not structural. -/
theorem HeapW.node_other (h : HeapW m pv T N J C n) {a k x : Word} (w : Word)
    (hN : N a = some k) (hin : a.toNat ≤ x.toNat ∧ x.toNat + 8 ≤ a.toNat + nodeSize k)
    (hx : ¬ StructCell a k x) : HeapW (setCell m x w) pv T N J C n := by
  have hat := h.nodes.at_ a k hN
  have hlo := hat.lo
  have htop := hat.top
  have hsz := nodeSize_le k
  have hpH := h.pvH
  have hstep : HeapStep m pv (setCell m x w) pv (fun y => y = x) := by
    refine ⟨Nat.le_refl _, fun y _ hy _ => setCell_ne _ hy, fun y hy => setCell_ne _ ?_⟩
    rintro rfl
    unfold HBASE at hy hlo
    have := hat.hi
    have := h.jrn.hi
    rcases hy with h1 | h1
    · omega
    · omega
  refine ⟨h.pvH, h.tabs.persist hstep (fun t v ht y hy hf => ?_),
    h.jrn.persist hstep (fun y h1 h2 hf => ?_), h.nodes.store_other x w
      (h.nodes.not_struct hN hin hx), h.tn, h.jn⟩
  · subst hf
    rcases h.tn t v a k ht hN y hy with h1 | h1 <;> omega
  · subst hf
    rcases h.jn a k hN with h3 | h3 <;> omega

/-- A store of a node or null into a child slot of node `a`. -/
theorem HeapW.node_child (h : HeapW m pv T N J C n) {a k x c : Word} (hN : N a = some k)
    (hslot : (k = 2#64 ∧ x = a + 48#64) ∨
      (k = 3#64 ∧ ∃ i : Nat, i < 16 ∧ x = a + BitVec.ofNat 64 (32 + 8 * i)))
    (hc : IsChild N c) : HeapW (setCell m x c) pv T N J C n := by
  have hat := h.nodes.at_ a k hN
  have hsx : StructCell a k x := by
    rcases hslot with ⟨hk, rfl⟩ | ⟨hk, i, hi, rfl⟩
    · exact Or.inr (Or.inl ⟨hk, Or.inr rfl⟩)
    · exact Or.inr (Or.inr ⟨hk, i, hi, rfl⟩)
  have hin := hsx.inside hat
  have hlo := hat.lo
  have hhi := hat.hi
  have hpH := h.pvH
  have hstep : HeapStep m pv (setCell m x c) pv (fun y => y = x) := by
    refine ⟨Nat.le_refl _, fun y _ hy _ => setCell_ne _ hy, fun y hy => setCell_ne _ ?_⟩
    rintro rfl
    unfold HBASE at hy hlo
    omega
  refine ⟨h.pvH, h.tabs.persist hstep (fun t v ht y hy hf => ?_),
    h.jrn.persist hstep (fun y h1 h2 hf => ?_), h.nodes.store_child hN hslot hc, h.tn, h.jn⟩
  · subst hf
    rcases h.tn t v a k ht hN y hy with h1 | h1 <;> omega
  · subst hf
    rcases h.jn a k hN with h3 | h3 <;> omega

open Classical in
/-- The nodes with one more. -/
noncomputable def addN (N : Word → Option Word) (a k : Word) : Word → Option Word :=
  fun x => if x = a then some k else N x

theorem IsChild.addN {c : Word} (h : IsChild N c) (a k : Word) : IsChild (addN N a k) c := by
  classical
  rcases h with rfl | ⟨j, hj⟩
  · exact Or.inl rfl
  · refine Or.inr ?_
    unfold InitECandidate.Solver.GuestBound.addN
    by_cases e : c = a
    · exact ⟨k, by simp [e]⟩
    · exact ⟨j, by simp [e, hj]⟩

/-- A node built in fresh heap at `a ≥ pv`; everything below the old heap
pointer is unchanged. Its children are old nodes or null. -/
theorem HeapW.node_add (h : HeapW m pv T N J C n) {a k : Word}
    (hfr : ∀ x : Word, x.toNat % 8 = 0 → x.toNat < pv.toNat → m' x = m x)
    (hout : ∀ x : Word, (x.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ x.toNat) → m' x = m x)
    (ha8 : a.toNat % 8 = 0) (hlo : pv.toNat ≤ a.toNat) (hhi : a.toNat + nodeSize k ≤ pv'.toNat)
    (hpH' : pv'.toNat ≤ 2952790016) (hk3 : k.toNat ≤ 3) (hkind : Rd m' a k)
    (hext : k = 2#64 → ∃ nl c : Word, Rd m' (a + 40#64) nl ∧ 1 ≤ nl.toNat ∧
      Rd m' (a + 48#64) c ∧ IsChild N c)
    (hbr : k = 3#64 → ∀ i : Nat, i < 16 → ∃ c : Word,
      Rd m' (a + BitVec.ofNat 64 (32 + 8 * i)) c ∧ IsChild N c) :
    HeapW m' pv' T (addN N a k) J C n := by
  classical
  have hsz := nodeSize_pos k
  have hpv : pv.toNat ≤ pv'.toNat := by omega
  have hstep : HeapStep m pv m' pv' (fun _ => False) :=
    ⟨hpv, fun x hx _ hlt => hfr x hx hlt, hout⟩
  have hJlo := h.jrn.lo
  have hJhi := h.jrn.hi
  have hbase : HBASE ≤ a.toNat := by omega
  refine ⟨hpH', h.tabs.persist hstep (fun _ _ _ _ _ hf => hf),
    h.jrn.persist hstep (fun _ _ _ hf => hf), ⟨fun b j hb => ?_, fun b j b' j' hb hb' hne => ?_⟩,
    fun t v b j ht hb x hx => ?_, fun b j hb => ?_⟩
  · unfold addN at hb
    by_cases e : b = a
    · subst e
      simp only [if_true, Option.some.injEq] at hb
      subst hb
      refine ⟨ha8, hbase, by omega, hhi, hk3, hkind, fun hk => ?_, fun hk i hi => ?_⟩
      · obtain ⟨nl, c, r1, h1, r2, hc⟩ := hext hk
        exact ⟨nl, c, r1, h1, r2, hc.addN _ _⟩
      · obtain ⟨c, r1, hc⟩ := hbr hk i hi
        exact ⟨c, r1, hc.addN _ _⟩
    · simp only [if_neg e] at hb
      have hold := (h.nodes.persist hstep (fun _ _ _ _ _ hf => hf)).at_ b j hb
      refine ⟨hold.al, hold.lo, hold.top, hold.hi, hold.k3, hold.kind, fun hk => ?_,
        fun hk i hi => ?_⟩
      · obtain ⟨nl, c, r1, h1, r2, hc⟩ := hold.ext hk
        exact ⟨nl, c, r1, h1, r2, hc.addN _ _⟩
      · obtain ⟨c, r1, hc⟩ := hold.br hk i hi
        exact ⟨c, r1, hc.addN _ _⟩
  · unfold addN at hb hb'
    by_cases e : b = a
    · subst e
      simp only [if_true, Option.some.injEq] at hb
      subst hb
      have e' : b' ≠ b := fun x => hne x.symm
      simp only [if_neg e'] at hb'
      have := (h.nodes.at_ b' j' hb').hi
      exact Or.inr (by omega)
    · simp only [if_neg e] at hb
      by_cases e' : b' = a
      · subst e'
        simp only [if_true, Option.some.injEq] at hb'
        subst hb'
        have := (h.nodes.at_ b j hb).hi
        exact Or.inl (by omega)
      · simp only [if_neg e'] at hb'
        exact h.nodes.disj b j b' j' hb hb' hne
  · unfold addN at hb
    by_cases e : b = a
    · subst e
      have := ((h.tabs.at_ t v ht).foot_lt hx).2
      exact Or.inl (by omega)
    · simp only [if_neg e] at hb
      exact h.tn t v b j ht hb x hx
  · unfold addN at hb
    by_cases e : b = a
    · subst e
      exact Or.inr (by omega)
    · simp only [if_neg e] at hb
      exact h.jn b j hb

/-- The range `[lo, hi)` is in the heap below the heap pointer and off every
table, node and the journal: a block that was allocated and belongs to no
structure (a buffer, a key copy). -/
structure FreeOK (pv : Word) (T : Word → Option HtabV) (N : Word → Option Word) (J C : Word)
    (lo hi : Word) : Prop where
  lo_ : HBASE ≤ lo.toNat
  hi_ : hi.toNat ≤ pv.toNat
  tab : ∀ t v, T t = some v → ∀ x, TabFoot t v x → x.toNat < lo.toNat ∨ hi.toNat ≤ x.toNat
  /-- The same, on intervals: header and blocks of every table lie off the range. -/
  tabI : ∀ t v, T t = some v → (hi.toNat ≤ t.toNat ∨ t.toNat + 88 ≤ lo.toNat) ∧
    (hi.toNat ≤ v.keys.toNat ∨ v.order.toNat + (v.nc.toNat + 1) * 8 ≤ lo.toNat)
  node : ∀ a k, N a = some k → a.toNat + nodeSize k ≤ lo.toNat ∨ hi.toNat ≤ a.toNat
  jrn : J.toNat + 32 * C.toNat ≤ lo.toNat ∨ hi.toNat ≤ J.toNat

/-- A block allocated at the heap pointer is free. -/
theorem FreeOK.fresh (h : HeapW m pv T N J C n) {lo hi : Word} (hlo : pv.toNat ≤ lo.toNat)
    (hhi : hi.toNat ≤ pv'.toNat) (hb : HBASE ≤ lo.toNat) : FreeOK pv' T N J C lo hi := by
  refine ⟨hb, hhi, fun t v ht x hx => ?_, fun t v ht => ?_, fun a k hN => ?_, ?_⟩
  · have := ((h.tabs.at_ t v ht).foot_lt hx).2
    exact Or.inl (by omega)
  · have hat := h.tabs.at_ t v ht
    obtain ⟨kind, rep, hok⟩ := hat.ok
    obtain ⟨l1, l2, l3, l4⟩ := hok.wf.layout
    have hkn : v.keys.toNat ≤ v.nodes.toNat := Nat.le_trans (Nat.le_add_right _ _) l2
    have := hat.fin
    exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
  · have := (h.nodes.at_ a k hN).hi
    exact Or.inl (by omega)
  · have := h.jrn.hi
    exact Or.inl (by omega)

theorem FreeOK.tab_step {t : Word} {v v' : HtabV} {lo hi : Word}
    (hf : FreeOK pv T N J C lo hi) (hs : TabStep m pv T t v m' pv' v') :
    FreeOK pv' (stepT T t v') N J C lo hi := by
  classical
  have := hs.pv_le
  have := hf.hi_
  refine ⟨hf.lo_, by omega, fun u w hu x hx => ?_, fun u w hu => ?_, hf.node, hf.jrn⟩
  · unfold stepT at hu
    by_cases e : u = t
    · subst e
      simp only [if_true, Option.some.injEq] at hu
      subst hu
      rcases hs.foot x hx with hold | hge
      · exact hf.tab u v hs.hT x hold
      · exact Or.inr (by omega)
    · simp only [if_neg e] at hu
      exact hf.tab u w hu x hx
  · unfold stepT at hu
    by_cases e : u = t
    · subst e
      simp only [if_true, Option.some.injEq] at hu
      subst hu
      obtain ⟨a1, a2⟩ := hf.tabI u v hs.hT
      refine ⟨a1, ?_⟩
      rcases hs.loc with ⟨e1, -, e3, e4⟩ | hge
      · rw [e1, e3, e4]; exact a2
      · exact Or.inl (by omega)
    · simp only [if_neg e] at hu
      exact hf.tabI u w hu

theorem FreeOK.node_add {a k lo hi : Word} (hf : FreeOK pv T N J C lo hi)
    (hlo : pv.toNat ≤ a.toNat) (hpv : pv.toNat ≤ pv'.toNat) :
    FreeOK pv' T (addN N a k) J C lo hi := by
  classical
  have := hf.hi_
  refine ⟨hf.lo_, by omega, hf.tab, hf.tabI, fun b j hb => ?_, hf.jrn⟩
  unfold addN at hb
  by_cases e : b = a
  · subst e
    exact Or.inr (by omega)
  · simp only [if_neg e] at hb
    exact hf.node b j hb

theorem FreeOK.mono {lo hi : Word} (hf : FreeOK pv T N J C lo hi) (hpv : pv.toNat ≤ pv'.toNat) :
    FreeOK pv' T N J C lo hi :=
  ⟨hf.lo_, by have := hf.hi_; omega, hf.tab, hf.tabI, hf.node, hf.jrn⟩

/-- Any change confined to a free range keeps the heap structures. -/
theorem HeapW.change_free (h : HeapW m pv T N J C n) {lo hi : Word}
    (hf : FreeOK pv T N J C lo hi)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → ¬ (lo.toNat ≤ a.toNat ∧ a.toNat < hi.toNat) →
      a.toNat < pv.toNat → m' a = m a)
    (hout : ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m' a = m a) :
    HeapW m' pv T N J C n := by
  have hstep : HeapStep m pv m' pv (fun a => lo.toNat ≤ a.toNat ∧ a.toNat < hi.toNat) :=
    ⟨Nat.le_refl _, hm, hout⟩
  refine ⟨h.pvH, h.tabs.persist hstep (fun t v ht x hx hF => ?_),
    h.jrn.persist hstep (fun x h1 h2 hF => ?_),
    h.nodes.persist hstep (fun a k x hN hx hF => ?_), h.tn, h.jn⟩
  · rcases hf.tab t v ht x hx with h1 | h1 <;> omega
  · rcases hf.jrn with h3 | h3 <;> omega
  · have hin := hx.inside (h.nodes.at_ a k hN)
    rcases hf.node a k hN with h1 | h1 <;> omega

/-- The heap structures with a higher heap pointer. -/
theorem HeapW.mono (h : HeapW m pv T N J C n) (hpv : pv.toNat ≤ pv'.toNat)
    (hpH' : pv'.toNat ≤ 2952790016) : HeapW m pv' T N J C n := by
  refine ⟨hpH', ⟨fun t v ht => ?_, h.tabs.disj⟩,
    ⟨h.jrn.n_le, h.jrn.al, h.jrn.lo, by have := h.jrn.hi; omega, h.jrn.off, fun i hi => ?_⟩,
    ⟨fun a k hN => ?_, h.nodes.disj⟩, h.tn, h.jn⟩
  · have hat := h.tabs.at_ t v ht
    exact ⟨hat.ok, hat.t8, hat.lo, by have := hat.fin; omega⟩
  · obtain ⟨t0, kc, fl, val, v0, r0, r1, r2, r3, hT0, hkf⟩ := h.jrn.entry i hi
    exact ⟨t0, kc, fl, val, v0, r0, r1, r2, r3, hT0, hkf.mono hpv⟩
  · have hat := h.nodes.at_ a k hN
    exact ⟨hat.al, hat.lo, hat.top, by have := hat.hi; omega, hat.k3, hat.kind, hat.ext, hat.br⟩

/-- Appending a journal entry: four stores at entry `n` of the journal block. -/
theorem HeapW.jpush (h : HeapW m pv T N J C n) {t kc o0 o1 n' R : Word} {v : HtabV}
    (hn : n.toNat < C.toNat) (hn' : n'.toNat = n.toNat + 1)
    (hR : R = J + BitVec.ofNat 64 (32 * n.toNat)) (hT : T t = some v)
    (hk : KeyFree pv T kc v.kl)
    (hm : m' = setCell (setCell (setCell (setCell m R t) (R + 8#64) kc) (R + 16#64) o0)
      (R + 24#64) o1) :
    HeapW m' pv T N J C n' := by
  have hJhi := h.jrn.hi
  have hJlo := h.jrn.lo
  have hal := h.jrn.al
  have hpH := h.pvH
  have hpvlt := pv.isLt
  have e0 : R.toNat = J.toNat + 32 * n.toNat := by
    rw [hR, BitVec.toNat_add, BitVec.toNat_ofNat]
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
  -- cells outside entry `n` are unchanged
  have keep : ∀ a : Word, ¬ (J.toNat + 32 * n.toNat ≤ a.toNat ∧
      a.toNat < J.toNat + 32 * n.toNat + 32) → m' a = m a := by
    intro a ha
    rw [hm, setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]
  have hstep : HeapStep m pv m' pv (fun a => J.toNat + 32 * n.toNat ≤ a.toNat ∧
      a.toNat < J.toNat + 32 * n.toNat + 32) := by
    refine ⟨Nat.le_refl _, fun a _ ha _ => keep a ha, fun a ha => keep a ?_⟩
    unfold HBASE at ha hJlo
    omega
  refine ⟨h.pvH, h.tabs.persist hstep (fun u w hu x hx hF => ?_), ?_,
    h.nodes.persist hstep (fun a k x hN hx hF => ?_), h.tn, h.jn⟩
  · rcases h.jrn.off u w hu x hx with h1 | h1 <;> omega
  · refine ⟨by omega, hal, hJlo, hJhi, h.jrn.off, fun i hi => ?_⟩
    have hbase : (J + BitVec.ofNat 64 (32 * i)).toNat = J.toNat + 32 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    by_cases e : i = n.toNat
    · subst e
      unfold JEntry
      rw [← hR]
      refine ⟨t, kc, o0, o1, v, ?_, ?_, ?_, ?_, hT, hk⟩
      · rw [hm]
        exact (((Rd.here m R t).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
          (NE (by omega))
      · rw [hm]
        exact ((Rd.here _ (R + 8#64) kc).frame _ (NE (by omega))).frame _ (NE (by omega))
      · rw [hm]
        exact (Rd.here _ (R + 16#64) o0).frame _ (NE (by omega))
      · rw [hm]
        exact Rd.here _ (R + 24#64) o1
    · obtain ⟨t0, kc0, fl, val, v0, r0, r1, r2, r3, hT0, hkf⟩ := h.jrn.entry i (by omega)
      have b1 : (J + BitVec.ofNat 64 (32 * i) + 8#64).toNat = J.toNat + 32 * i + 8 := by
        rw [BitVec.toNat_add, hbase]
        simp
        omega
      have b2 : (J + BitVec.ofNat 64 (32 * i) + 16#64).toNat = J.toNat + 32 * i + 16 := by
        rw [BitVec.toNat_add, hbase]
        simp
        omega
      have b3 : (J + BitVec.ofNat 64 (32 * i) + 24#64).toNat = J.toNat + 32 * i + 24 := by
        rw [BitVec.toNat_add, hbase]
        simp
        omega
      have keepR : ∀ (a w : Word), ¬ (J.toNat + 32 * n.toNat ≤ a.toNat ∧
          a.toNat < J.toNat + 32 * n.toNat + 32) → Rd m a w → Rd m' a w := by
        intro a w ha hr
        unfold Rd at hr ⊢
        rw [keep a ha]
        exact hr
      exact ⟨t0, kc0, fl, val, v0, keepR _ _ (by omega) r0, keepR _ _ (by omega) r1,
        keepR _ _ (by omega) r2, keepR _ _ (by omega) r3, hT0, hkf⟩
  · have hin := hx.inside (h.nodes.at_ a k hN)
    rcases h.jn a k hN with h3 | h3 <;> omega

end InitECandidate.Solver.GuestBound
