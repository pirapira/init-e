import InitECandidate.Solver.GuestBound.HtabSetAux

/-!
# Hash tables: the linking stores of `htab_set`
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- Memory after the linking stores: the new internal node `ni` gets parent
`p` and children `li`, `ri`; the leaf `nl` and the displaced node `n` get
parent `ni`; the cell `X` that pointed to `n` now points to `ni`. -/
def linkMem (M : Word → Option (PanValue Word)) (V : HtabV) (nl ni n p li ri X : Word) :
    Word → Option (PanValue Word) :=
  setCell (setCell (setCell (setCell (setCell (setCell M (nodeField V ni.toNat 0) p)
    (nodeField V nl.toNat 0) ni) (nodeField V n.toNat 0) ni) (nodeField V ni.toNat 8) li)
    (nodeField V ni.toNat 16) ri) X ni

set_option maxHeartbeats 16000000 in
theorem set_link_mem_ok {M : Word → Option (PanValue Word)} {t : Word} {V : HtabV}
    {K : Nat → NodeKind} {R R' : KeyRep} {det : Nat → Prop}
    (hok : HtabOKd M t V K R det) {nl ni n p d bn lp li ri X : Word} {κ : Word → Bool}
    (hdet : ∀ i, det i ↔ (i = nl.toNat ∨ i = ni.toNat))
    (hnl : LiveN V K nl.toNat) (hnlk : K nl.toNat = .leaf)
    (hni : LiveN V K ni.toNat) (hnik : K ni.toNat = .internal)
    (hn : LiveN V K n.toNat) (hnnl : n.toNat ≠ nl.toNat) (hnni : n.toNat ≠ ni.toNat)
    (hd : Rd M (nodeField V ni.toNat 24) d) (hdlt : d.toNat < (V.kl * 8#64).toNat)
    (hnp : Rd M (nodeField V n.toNat 0) p) (hbn : Rd M (nodeField V n.toNat 24) bn)
    (hdbn : d.toNat < bn.toNat)
    (hpc : p ≠ 0 → ∃ bp, Rd M (nodeField V p.toNat 24) bp ∧ bp.toNat < d.toNat)
    (hlp : p ≠ 0 → Rd M (nodeField V p.toNat 8) lp)
    (hpl : p ≠ 0 → p.toNat < V.next.toNat ∧ p.toNat ≠ ni.toNat)
    (hκnl : ∀ j : Word, j.toNat < (V.kl * 8#64).toNat → R nl.toNat j = κ j)
    (hκd : R n.toNat d = !κ d) (hκlt : ∀ j : Word, j.toNat < d.toNat → R n.toNat j = κ j)
    (hR'ni : R' ni.toNat = R n.toNat) (hR'o : ∀ i, i ≠ ni.toNat → R' i = R i)
    (hside : (li = nl ∧ ri = n ∧ κ d = false) ∨ (li = n ∧ ri = nl ∧ κ d = true))
    (hX : X = if p = 0 then t + 56#64 else nodeField V p.toNat (if lp = n then 8 else 16)) :
    HtabOK (linkMem M V nl ni n p li ri X) t (setRoot V (if p = 0 then ni else V.root)) K R' := by
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  have hnxl := hwf.next_le
  have hnle : n.toNat ≤ V.nc.toNat := by have := hn.2.1; omega
  have hnlle : nl.toNat ≤ V.nc.toNat := by have := hnl.2.1; omega
  have hnile : ni.toNat ≤ V.nc.toNat := by have := hni.2.1; omega
  have hnlni : nl.toNat ≠ ni.toNat := fun e => by rw [e, hnik] at hnlk; cases hnlk
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hNf : ∀ i o, i ≤ V.nc.toNat → o < 32 →
      (nodeField V i o).toNat = V.nodes.toNat + (i * 32 + o) := fun i o hi ho => node_toNat hlay hi ho
  have hT : ∀ k, k < 88 → (t + BitVec.ofNat 64 k).toNat = t.toNat + k :=
    fun k hk => hdr_toNat hlay hk
  obtain ⟨sN, hsN, hs⟩ : ∃ sN : Nat, sN = (if lp = n then 8 else 16) ∧ (sN = 8 ∨ sN = 16) :=
    ⟨_, rfl, by split <;> simp⟩
  rw [← hsN] at hX
  -- where the last store goes
  have hXn : (p = 0 ∧ X = t + 56#64 ∧ X.toNat = t.toNat + 56) ∨
      (p ≠ 0 ∧ X = nodeField V p.toNat sN ∧ p.toNat ≤ V.nc.toNat ∧ p.toNat ≠ ni.toNat ∧
        X.toNat = V.nodes.toNat + (p.toNat * 32 + sN)) := by
    by_cases hp0 : p = 0
    · rw [if_pos hp0] at hX
      exact Or.inl ⟨hp0, hX, by rw [hX]; exact hT 56 (by omega)⟩
    · rw [if_neg hp0] at hX
      obtain ⟨a, b⟩ := hpl hp0
      exact Or.inr ⟨hp0, hX, by omega, b, by rw [hX]; exact hNf _ _ (by omega) (by omega)⟩
  have F : ∀ A : Word, A.toNat ≠ V.nodes.toNat + (ni.toNat * 32 + 0) →
      A.toNat ≠ V.nodes.toNat + (nl.toNat * 32 + 0) →
      A.toNat ≠ V.nodes.toNat + (n.toNat * 32 + 0) →
      A.toNat ≠ V.nodes.toNat + (ni.toNat * 32 + 8) →
      A.toNat ≠ V.nodes.toNat + (ni.toNat * 32 + 16) → A.toNat ≠ X.toNat →
      linkMem M V nl ni n p li ri X A = M A := by
    intro A a1 a2 a3 a4 a5 a6
    unfold linkMem
    rw [setCell_ne' _ (NE a6),
      setCell_ne' _ (NE (by rw [hNf _ 16 hnile (by omega)]; exact a5)),
      setCell_ne' _ (NE (by rw [hNf _ 8 hnile (by omega)]; exact a4)),
      setCell_ne' _ (NE (by rw [hNf _ 0 hnle (by omega)]; exact a3)),
      setCell_ne' _ (NE (by rw [hNf _ 0 hnlle (by omega)]; exact a2)),
      setCell_ne' _ (NE (by rw [hNf _ 0 hnile (by omega)]; exact a1))]
  have hXne : ∀ (i o : Nat), i ≤ V.nc.toNat → o < 32 → ¬(p ≠ 0 ∧ i = p.toNat ∧ o = sN) →
      V.nodes.toNat + (i * 32 + o) ≠ X.toNat := by
    intro i o hi ho hc
    rcases hXn with ⟨-, -, e⟩ | ⟨hp0, -, -, -, e⟩
    · rw [e]
      omega
    · rw [e]
      intro h
      exact hc ⟨hp0, by omega, by omega⟩
  have hni0 : Rd (linkMem M V nl ni n p li ri X) (nodeField V ni.toNat 0) p :=
    (((((Rd.here _ _ _).frame _ (NE (by rw [hNf _ 0 hnile (by omega), hNf _ 0 hnlle (by omega)]; omega))).frame _
      (NE (by rw [hNf _ 0 hnile (by omega), hNf _ 0 hnle (by omega)]; omega))).frame _
      (NE (by rw [hNf _ 0 hnile (by omega), hNf _ 8 hnile (by omega)]; omega))).frame _
      (NE (by rw [hNf _ 0 hnile (by omega), hNf _ 16 hnile (by omega)]; omega))).frame _
      (NE (by rw [hNf _ 0 hnile (by omega)]; exact hXne _ 0 hnile (by omega) (fun h => by omega)))
  have hnl0 : Rd (linkMem M V nl ni n p li ri X) (nodeField V nl.toNat 0) ni :=
    ((((Rd.here _ _ _).frame _
      (NE (by rw [hNf _ 0 hnlle (by omega), hNf _ 0 hnle (by omega)]; omega))).frame _
      (NE (by rw [hNf _ 0 hnlle (by omega), hNf _ 8 hnile (by omega)]; omega))).frame _
      (NE (by rw [hNf _ 0 hnlle (by omega), hNf _ 16 hnile (by omega)]; omega))).frame _
      (NE (by rw [hNf _ 0 hnlle (by omega)]; exact hXne _ 0 hnlle (by omega) (fun h => by omega)))
  have hn0 : Rd (linkMem M V nl ni n p li ri X) (nodeField V n.toNat 0) ni :=
    (((Rd.here _ _ _).frame _
      (NE (by rw [hNf _ 0 hnle (by omega), hNf _ 8 hnile (by omega)]; omega))).frame _
      (NE (by rw [hNf _ 0 hnle (by omega), hNf _ 16 hnile (by omega)]; omega))).frame _
      (NE (by rw [hNf _ 0 hnle (by omega)]; exact hXne _ 0 hnle (by omega) (fun h => by omega)))
  have hpni : ¬(p ≠ 0 ∧ ni.toNat = p.toNat) := by
    rintro ⟨hp0, e⟩
    exact (hpl hp0).2 e.symm
  have hni8 : Rd (linkMem M V nl ni n p li ri X) (nodeField V ni.toNat 8) li :=
    ((Rd.here _ _ _).frame _
      (NE (by rw [hNf _ 8 hnile (by omega), hNf _ 16 hnile (by omega)]; omega))).frame _
      (NE (by rw [hNf _ 8 hnile (by omega)]
              exact hXne _ 8 hnile (by omega) (fun h => hpni ⟨h.1, h.2.1⟩)))
  have hni16 : Rd (linkMem M V nl ni n p li ri X) (nodeField V ni.toNat 16) ri :=
    (Rd.here _ _ _).frame _
      (NE (by rw [hNf _ 16 hnile (by omega)]
              exact hXne _ 16 hnile (by omega) (fun h => hpni ⟨h.1, h.2.1⟩)))
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  have H : ∀ (k : Nat) (w : Word), k < 88 → k ≠ 56 → k % 8 = 0 → Rd M (t + BitVec.ofNat 64 k) w →
      Rd (linkMem M V nl ni n p li ri X) (t + BitVec.ofNat 64 k) w := by
    intro k w hk hk56 hk8 h
    unfold Rd
    rw [F _ (by rw [hT k hk]; omega) (by rw [hT k hk]; omega) (by rw [hT k hk]; omega)
      (by rw [hT k hk]; omega) (by rw [hT k hk]; omega) (by
        rw [hT k hk]
        rcases hXn with ⟨-, -, e⟩ | ⟨-, -, -, -, e⟩ <;> rw [e] <;> omega)]
    exact h
  have H56 : Rd (linkMem M V nl ni n p li ri X) (t + 56#64) (if p = 0 then ni else V.root) := by
    rcases hXn with ⟨hp0, e, -⟩ | ⟨hp0, -, -, -, e⟩
    · rw [if_pos hp0, ← e]
      exact Rd.here _ _ _
    · rw [if_neg hp0]
      unfold Rd
      have h56 := hT 56 (by omega)
      rw [F _ (by rw [h56]; omega) (by rw [h56]; omega) (by rw [h56]; omega)
        (by rw [h56]; omega) (by rw [h56]; omega) (by rw [h56, e]; omega)]
      exact hroot
  refine set_link_ok hok hdet hnl hnlk hni hnik hn hnnl hnni hd hdlt hnp hbn hdbn hpc hlp hκnl hκd
    hκlt hR'ni hR'o ?_ hni0 hni8 hni16 hside hnl0 hn0 ?_ ?_
    ⟨H 0 _ (by omega) (by omega) (by omega) hkl, H 8 _ (by omega) (by omega) (by omega) hst,
      H 16 _ (by omega) (by omega) (by omega) hcp, H 24 _ (by omega) (by omega) (by omega) hcnt,
      H 32 _ (by omega) (by omega) (by omega) hkeys, H 40 _ (by omega) (by omega) (by omega) hnd,
      H 48 _ (by omega) (by omega) (by omega) hord, H56,
      H 64 _ (by omega) (by omega) (by omega) hnext, H 72 _ (by omega) (by omega) (by omega) hfree,
      H 80 _ (by omega) (by omega) (by omega) hnc⟩ ?_
  · intro i o w hi ho ho8 c1 c2 c3 c4
    rw [← hsN] at c4
    unfold Rd
    rw [F _ (by rw [hNf i o hi ho]; omega) (by rw [hNf i o hi ho]; omega)
      (by rw [hNf i o hi ho]; omega) (by rw [hNf i o hi ho]; omega)
      (by rw [hNf i o hi ho]; omega) (by rw [hNf i o hi ho]; exact hXne i o hi ho c4)]
  · intro hp0
    rw [← hsN]
    rcases hXn with ⟨h0, -, -⟩ | ⟨-, e, -⟩
    · exact absurd h0 hp0
    · rw [← e]
      exact Rd.here _ _ _
  · intro pos w hp
    have ho := ord_toNat hlay hp
    unfold Rd
    rw [F _ (by rw [ho]; omega) (by rw [ho]; omega) (by rw [ho]; omega) (by rw [ho]; omega)
      (by rw [ho]; omega) (by
        rw [ho]
        rcases hXn with ⟨-, -, e⟩ | ⟨-, -, hple, -, e⟩ <;> rw [e] <;> omega)]
  · intro i hi j bit hj hb
    refine keybit_frame hlay hok.keys8 hok.kl_st hok.kl8 (fun a ha1 ha2 => ?_) hi hj hb
    exact F a (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rcases hXn with ⟨-, -, e⟩ | ⟨-, -, hple, -, e⟩ <;> rw [e] <;> omega)

end InitECandidate.Solver.GuestBound
