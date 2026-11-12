import InitECandidate.Solver.GuestBound.HtabSet

/-!
# Several hash tables side by side

`TabFoot t v`: the aligned cells of a table, header `[t, t + 88)` and blocks
`[keys, order + 8·(nc + 1))`. `HtabOK` only reads these cells
(`HtabOK.frame`).

`TabsOK m pv T`: every table of the partial map `T` (header address ↦ header
values) is well formed, lies in the heap below the heap pointer `pv`, and the
footprints are pairwise disjoint. `TabsOK.update` replaces one table after an
operation that wrote only that table's footprint and fresh heap;
`TabsOK.set` instantiates it for `htab_set`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {m m' : Word → Option (PanValue Word)} {t : Word} {v : HtabV}
  {kind : Nat → NodeKind} {rep : KeyRep}

/-- The cells of a table: header and blocks, at aligned addresses. -/
def TabFoot (t : Word) (v : HtabV) (a : Word) : Prop :=
  a.toNat % 8 = 0 ∧ ((t.toNat ≤ a.toNat ∧ a.toNat < t.toNat + 88) ∨
    (v.keys.toNat ≤ a.toNat ∧ a.toNat < v.order.toNat + (v.nc.toNat + 1) * 8))

/-- A key bit only depends on the aligned cells of the key. -/
theorem KeyBitIs.frame8 {kp j : Word} {bit : Bool} {lo hi : Nat} (hlo8 : lo % 8 = 0)
    (hkp : lo ≤ kp.toNat) (hhi : kp.toNat + j.toNat / 8 < hi) (hhi64 : hi ≤ 2 ^ 64)
    (hframe : ∀ a : Word, a.toNat % 8 = 0 → lo ≤ a.toNat → a.toNat < hi → m' a = m a)
    (h : KeyBitIs 8#64 m kp j bit) : KeyBitIs 8#64 m' kp j bit := by
  intro a cell y hs hcell hy
  refine h a cell y hs ?_ hy
  have ha : a.toNat = j.toNat / 8 := by
    unfold RiscV.panRiscVShift at hs
    split at hs
    · simp only [Option.some.injEq] at hs
      subst hs
      have h3 : (3#64 : Word).toNat = 3 := by decide
      rw [h3, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    · cases hs
  have hsum : (kp + a).toNat = kp.toNat + a.toNat := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  rw [← hframe _ (by rw [align8_toNat]; omega) (by rw [align8_toNat, hsum]; omega)
    (by rw [align8_toNat, hsum]; omega)]
  exact hcell

/-- The table invariant only depends on the table's footprint. -/
theorem HtabOK.frame (hok : HtabOK m t v kind rep) (ht8 : t.toNat % 8 = 0)
    (h : ∀ a, TabFoot t v a → m' a = m a) : HtabOK m' t v kind rep := by
  have hlay := hok.wf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  have hk8 := hok.keys8
  have hn8 := hok.nodes8
  have ho8 := hok.order8
  have hkn : v.keys.toNat ≤ v.nodes.toNat := Nat.le_trans (Nat.le_add_right _ _) l2
  have hH : ∀ (k : Nat) (w : Word), k < 88 → k % 8 = 0 → Rd m (t + BitVec.ofNat 64 k) w →
      Rd m' (t + BitVec.ofNat 64 k) w := by
    intro k w hk hk8' hr
    unfold Rd at hr ⊢
    rw [h _ ⟨by rw [hdr_toNat hlay hk]; omega, Or.inl (by rw [hdr_toNat hlay hk]; omega)⟩]
    exact hr
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hok.wf.hdr
  have hhdr : HtabHdr m' t v :=
    ⟨hH 0 _ (by omega) (by omega) h0, hH 8 _ (by omega) (by omega) h1,
      hH 16 _ (by omega) (by omega) h2, hH 24 _ (by omega) (by omega) h3,
      hH 32 _ (by omega) (by omega) h4, hH 40 _ (by omega) (by omega) h5,
      hH 48 _ (by omega) (by omega) h6, hH 56 _ (by omega) (by omega) h7,
      hH 64 _ (by omega) (by omega) h8, hH 72 _ (by omega) (by omega) h9,
      hH 80 _ (by omega) (by omega) h10⟩
  exact (hok.toDet.transport (m' := m') (cp' := v.cp) (nc' := v.nc) (K := v.keys)
    (N := v.nodes) (O := v.order) (Nat.le_refl _) hlay hhdr hk8 hn8 ho8
    (fun i o w hi ho ho8' => by
      show Rd m' (nodeField v i o) w ↔ Rd m (nodeField v i o) w
      unfold Rd
      rw [h _ ⟨by rw [node_toNat hlay hi ho]; omega,
        Or.inr (by rw [node_toNat hlay hi ho]; constructor <;> omega)⟩])
    (fun p w hp => by
      show Rd m' (orderSlot v p) w ↔ Rd m (orderSlot v p) w
      unfold Rd
      rw [h _ ⟨by rw [ord_toNat hlay hp]; omega,
        Or.inr (by rw [ord_toNat hlay hp]; constructor <;> omega)⟩])
    (fun i hi j bit hj hb => by
      obtain ⟨hkp, hkp'⟩ := keyptr_bounds hlay hi
      have h8' : (8#64 : Word).toNat = 8 := by decide
      have hmul : (v.kl * 8#64).toNat = v.kl.toNat * 8 := by
        rw [BitVec.toNat_mul, h8']
        exact Nat.mod_eq_of_lt hok.kl8
      have hks := hok.kl_st
      exact KeyBitIs.frame8 (lo := v.keys.toNat) (hi := v.nodes.toNat) hk8 (by omega) (by omega)
        (by omega) (fun a ha8 ha1 ha2 => h a ⟨ha8, Or.inr ⟨ha1, by omega⟩⟩) hb)).toOK

/-- The lowest heap address. -/
def HBASE : Nat := 2701131776

/-- One live table below the heap pointer `pv`. -/
structure TabAt (m : Word → Option (PanValue Word)) (pv t : Word) (v : HtabV) : Prop where
  ok : ∃ kind rep, HtabOK m t v kind rep
  t8 : t.toNat % 8 = 0
  lo : HBASE ≤ t.toNat
  fin : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat

/-- The live tables: well formed, below the heap pointer, pairwise disjoint. -/
structure TabsOK (m : Word → Option (PanValue Word)) (pv : Word) (T : Word → Option HtabV) :
    Prop where
  at_ : ∀ t v, T t = some v → TabAt m pv t v
  disj : ∀ t v t' v', T t = some v → T t' = some v' → t ≠ t' →
    ∀ a, TabFoot t v a → TabFoot t' v' a → False

/-- Every cell of a live table is in the heap below the heap pointer. -/
theorem TabAt.foot_lt {pv : Word} (h : TabAt m pv t v) {a : Word} (ha : TabFoot t v a) :
    HBASE ≤ a.toNat ∧ a.toNat < pv.toNat := by
  obtain ⟨kind, rep, hok⟩ := h.ok
  obtain ⟨l1, l2, l3, l4⟩ := hok.wf.layout
  have hkn : v.keys.toNat ≤ v.nodes.toNat := Nat.le_trans (Nat.le_add_right _ _) l2
  have := h.lo
  have := h.fin
  rcases ha.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> omega

open Classical in
/-- Replace table `t` after an operation that wrote only its footprint and
heap at or above the old heap pointer. -/
theorem TabsOK.update {pv pv' : Word} {T : Word → Option HtabV} (h : TabsOK m pv T)
    {v' : HtabV} (hT : T t = some v) (hpv : pv.toNat ≤ pv'.toNat) (hnew : TabAt m' pv' t v')
    (hloc : ∀ a, TabFoot t v' a → TabFoot t v a ∨ pv.toNat ≤ a.toNat)
    (hfr : ∀ a : Word, a.toNat % 8 = 0 → ¬ TabFoot t v a → a.toNat < pv.toNat → m' a = m a) :
    TabsOK m' pv' (fun x => if x = t then some v' else T x) := by
  refine ⟨fun u w hu => ?_, fun u w u' w' hu hu' hne a ha ha' => ?_⟩
  · by_cases e : u = t
    · subst e
      simp only [if_true, Option.some.injEq] at hu
      subst hu
      exact hnew
    · simp only [if_neg e] at hu
      have hat := h.at_ u w hu
      obtain ⟨kind, rep, hok⟩ := hat.ok
      refine ⟨⟨kind, rep, hok.frame hat.t8 (fun a ha => ?_)⟩, hat.t8, hat.lo, by
        have := hat.fin; omega⟩
      exact hfr a ha.1 (fun hta => h.disj u w t v hu hT e a ha hta) (hat.foot_lt ha).2
  · by_cases e : u = t
    · subst e
      simp only [if_true, Option.some.injEq] at hu
      subst hu
      have e' : u' ≠ u := fun x => hne x.symm
      simp only [if_neg e'] at hu'
      rcases hloc a ha with hold | hge
      · exact h.disj u v u' w' hT hu' hne a hold ha'
      · have := ((h.at_ u' w' hu').foot_lt ha').2
        omega
    · simp only [if_neg e] at hu
      by_cases e' : u' = t
      · subst e'
        simp only [if_true, Option.some.injEq] at hu'
        subst hu'
        rcases hloc a ha' with hold | hge
        · exact h.disj u w u' v hu hT hne a ha hold
        · have := ((h.at_ u w hu).foot_lt ha).2
          omega
      · simp only [if_neg e'] at hu'
        exact h.disj u w u' w' hu hu' hne a ha ha'

open Classical in
/-- `htab_set` on a live table keeps the tables. -/
theorem TabsOK.set {pv : Word} {T : Word → Option HtabV} (h : TabsOK m pv T) (hT : T t = some v)
    (hpH : InHeap pv) {f : FfiState σ} {l g' : VarName → Option (PanValue Word)}
    (hpost : SetPost m t pv v f (.returned l g' m' f [.word 0#64])) :
    ∃ pv' v', g' "heap_ptr" = some (.word pv') ∧ InHeap pv' ∧ pv.toNat ≤ pv'.toNat ∧
      TabsOK m' pv' (fun x => if x = t then some v' else T x) ∧
      ∀ a : Word, a.toNat % 8 = 0 → ¬ TabFoot t v a → a.toNat < pv.toNat → m' a = m a := by
  obtain ⟨l0, g0, m0, v', kind', rep', heq, hok', -, hloc, ⟨pv', hp', hpH', hend', hpp'⟩, hfr⟩ :=
    hpost
  injection heq with _ hg hm _ _
  subst hg hm
  have hat := h.at_ t v hT
  obtain ⟨kind, rep, hok⟩ := hat.ok
  have hk8 := hok.keys8
  have ho8 := hok.order8
  have hframe : ∀ a : Word, a.toNat % 8 = 0 → ¬ TabFoot t v a → a.toNat < pv.toNat →
      m' a = m a := by
    intro a ha8 hna hlt
    have ht8 := hat.t8
    have hp8 := hpH.2
    refine hfr a ?_ (Or.inl (by omega)) ?_
    · by_contra hc
      exact hna ⟨ha8, Or.inl (by omega)⟩
    · by_contra hc
      exact hna ⟨ha8, Or.inr (by omega)⟩
  refine ⟨pv', v', hp', hpH', hpp', h.update hT hpp' ⟨⟨kind', rep', hok'⟩, hat.t8, hat.lo, hend'⟩
    (fun a ha => ?_) hframe, hframe⟩
  rcases ha.2 with hh | hb
  · exact Or.inl ⟨ha.1, Or.inl hh⟩
  · rcases hloc with ⟨e1, -, e3, e4⟩ | hge
    · exact Or.inl ⟨ha.1, Or.inr (by rw [← e1, ← e3, ← e4]; exact hb)⟩
    · exact Or.inr (by omega)

end InitECandidate.Solver.GuestBound
