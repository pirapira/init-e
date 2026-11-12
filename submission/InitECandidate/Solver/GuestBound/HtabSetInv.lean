import InitECandidate.Solver.GuestBound.HtabNode

/-!
# Hash tables: linking a new leaf into the trie

`htab_set` for a new key allocates a leaf `nl` and an internal node `ni`
testing the first bit `d` where the key differs from its neighbours, and puts
`ni` in the place of the node `n` where the descent stopped. This file shows
the table is well formed after the linking stores.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- The table values with another root. -/
abbrev setRoot (V : HtabV) (r : Word) : HtabV :=
  ⟨V.kl, V.st, V.cp, V.nc, V.cnt, V.keys, V.nodes, V.order, r, V.next, V.free⟩

set_option maxHeartbeats 16000000 in
theorem set_link_ok {M M' : Word → Option (PanValue Word)} {t : Word} {V : HtabV}
    {K : Nat → NodeKind} {R R' : KeyRep} {det : Nat → Prop}
    (hok : HtabOKd M t V K R det) {nl ni n p d bn lp li ri : Word} {κ : Word → Bool}
    (hdet : ∀ i, det i ↔ (i = nl.toNat ∨ i = ni.toNat))
    (hnl : LiveN V K nl.toNat) (hnlk : K nl.toNat = .leaf)
    (hni : LiveN V K ni.toNat) (hnik : K ni.toNat = .internal)
    (hn : LiveN V K n.toNat) (hnnl : n.toNat ≠ nl.toNat) (hnni : n.toNat ≠ ni.toNat)
    (hd : Rd M (nodeField V ni.toNat 24) d) (hdlt : d.toNat < (V.kl * 8#64).toNat)
    (hnp : Rd M (nodeField V n.toNat 0) p) (hbn : Rd M (nodeField V n.toNat 24) bn)
    (hdbn : d.toNat < bn.toNat)
    (hpc : p ≠ 0 → ∃ bp, Rd M (nodeField V p.toNat 24) bp ∧ bp.toNat < d.toNat)
    (hlp : p ≠ 0 → Rd M (nodeField V p.toNat 8) lp)
    (hκnl : ∀ j : Word, j.toNat < (V.kl * 8#64).toNat → R nl.toNat j = κ j)
    (hκd : R n.toNat d = !κ d) (hκlt : ∀ j : Word, j.toNat < d.toNat → R n.toNat j = κ j)
    (hR'ni : R' ni.toNat = R n.toNat) (hR'o : ∀ i, i ≠ ni.toNat → R' i = R i)
    (hN : ∀ (i o : Nat) (w : Word), i ≤ V.nc.toNat → o < 32 → o % 8 = 0 →
      ¬(i = ni.toNat ∧ o ≠ 24) → ¬(i = nl.toNat ∧ o = 0) → ¬(i = n.toNat ∧ o = 0) →
      ¬(p ≠ 0 ∧ i = p.toNat ∧ o = (if lp = n then 8 else 16)) →
      (Rd M' (nodeField V i o) w ↔ Rd M (nodeField V i o) w))
    (hni0 : Rd M' (nodeField V ni.toNat 0) p) (hni8 : Rd M' (nodeField V ni.toNat 8) li)
    (hni16 : Rd M' (nodeField V ni.toNat 16) ri)
    (hside : (li = nl ∧ ri = n ∧ κ d = false) ∨ (li = n ∧ ri = nl ∧ κ d = true))
    (hnl0 : Rd M' (nodeField V nl.toNat 0) ni) (hn0 : Rd M' (nodeField V n.toNat 0) ni)
    (hps : p ≠ 0 → Rd M' (nodeField V p.toNat (if lp = n then 8 else 16)) ni)
    (hO : ∀ (pos : Nat) (w : Word), pos ≤ V.nc.toNat →
      (Rd M' (orderSlot V pos) w ↔ Rd M (orderSlot V pos) w))
    (hhdr : HtabHdr M' t (setRoot V (if p = 0 then ni else V.root)))
    (hKey : ∀ i, i ≤ V.nc.toNat → ∀ (j : Word) (bit : Bool), j.toNat < (V.kl * 8#64).toNat →
      KeyBitIs 8#64 M (V.keys + BitVec.ofNat 64 i * V.st) j bit →
      KeyBitIs 8#64 M' (V.keys + BitVec.ofNat 64 i * V.st) j bit) :
    HtabOK M' t (setRoot V (if p = 0 then ni else V.root)) K R' := by
  have hwf := hok.wf
  have hnxl := hwf.next_le
  have ofn : ∀ x : Word, BitVec.ofNat 64 x.toNat = x := fun x => by simp
  have hnlni : nl.toNat ≠ ni.toNat := fun e => by rw [e, hnik] at hnlk; cases hnlk
  have dnl : det nl.toNat := (hdet _).mpr (Or.inl rfl)
  have dni : det ni.toNat := (hdet _).mpr (Or.inr rfl)
  have nd : ∀ i, i ≠ nl.toNat → i ≠ ni.toNat → ¬ det i :=
    fun i a b h => ((hdet i).mp h).elim a b
  have ndn := nd _ hnnl hnni
  have wne : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have h00 : (0 : Word).toNat = 0 := rfl
  -- the parent of `n`
  have hparN : ParentOkd M V K det n.toNat p := by
    cases hk : K n.toNat with
    | free => exact absurd hk hn.2.2
    | leaf =>
      obtain ⟨p', _, _, hp', -, -, -, hpar, -⟩ := hwf.leaf_ok _ hn.1 hn.2.1 hk
      rw [Rd.inj hnp hp']
      exact hpar ndn
    | internal =>
      obtain ⟨p', _, _, _, hp', -, -, -, -, hrest⟩ := hwf.internal_ok _ hn.1 hn.2.1 hk
      rw [Rd.inj hnp hp']
      exact (hrest ndn).1
  have hpn : p.toNat ≠ n.toNat := by
    by_cases hp0 : p = 0
    · intro e
      have h1 := hn.1
      rw [hp0] at e
      omega
    · obtain ⟨bp, hbp, hlt⟩ := hpc hp0
      intro e
      rw [e] at hbp
      have := Rd.inj hbp hbn
      rw [this] at hlt
      omega
  have hP : p ≠ 0 → 1 ≤ p.toNat ∧ p.toNat < V.next.toNat ∧ K p.toNat = .internal ∧
      ¬ det p.toNat ∧ ∃ pp rp b, Rd M (nodeField V p.toNat 0) pp ∧
        Rd M (nodeField V p.toNat 16) rp ∧ Rd M (nodeField V p.toNat 24) b ∧
        b ≠ V.kl * 8#64 ∧ ParentOkd M V K det p.toNat pp ∧ ChildOk M V K p.toNat lp ∧
        ChildOk M V K p.toNat rp ∧ ¬ det lp.toNat ∧ ¬ det rp.toNat ∧ lp ≠ rp ∧
        (lp = n ∨ rp = n) := by
    intro hp0
    rcases hparN.1 with ⟨h0, -⟩ | ⟨a, b, k, hch⟩
    · exact absurd h0 hp0
    have hdp := hparN.2 hp0
    obtain ⟨pp, l, r, bb, h0', hl, hr, hb, hbne, hrest⟩ := hwf.internal_ok _ a b k
    obtain ⟨hpar, hcl, hcr, hdl, hdr, hlr⟩ := hrest hdp
    have el : lp = l := Rd.inj (hlp hp0) hl
    subst el
    refine ⟨a, b, k, hdp, pp, r, bb, h0', hr, hb, hbne, hpar, hcl, hcr, hdl, hdr, hlr, ?_⟩
    rw [ofn] at hch
    exact hch.imp (fun h => Rd.inj hl h) (fun h => Rd.inj hr h)
  -- untouched cells
  have U := fun (i o : Nat) (w : Word) (hi : i < V.next.toNat) (ho : o < 32) (ho8 : o % 8 = 0)
      (c1 : i = ni.toNat → o = 24) (c2 : i = nl.toNat → o ≠ 0) (c3 : i = n.toNat → o ≠ 0)
      (c4 : p ≠ 0 → i = p.toNat → o ≠ (if lp = n then 8 else 16)) =>
    hN i o w (by omega) ho ho8 (fun h => h.2 (c1 h.1)) (fun h => c2 h.1 h.2)
      (fun h => c3 h.1 h.2) (fun h => c4 h.1 h.2.1 h.2.2)
  have U24 : ∀ (i : Nat) (w : Word), i < V.next.toNat →
      (Rd M' (nodeField V i 24) w ↔ Rd M (nodeField V i 24) w) :=
    fun i w hi => U i 24 w hi (by omega) (by omega) (fun _ => rfl) (fun _ => by omega)
      (fun _ => by omega) (fun _ _ h => by split at h <;> omega)
  have U0 : ∀ (i : Nat) (w : Word), i < V.next.toNat → i ≠ ni.toNat → i ≠ nl.toNat →
      i ≠ n.toNat → (Rd M' (nodeField V i 0) w ↔ Rd M (nodeField V i 0) w) :=
    fun i w hi a b c => U i 0 w hi (by omega) (by omega) (fun e => absurd e a)
      (fun e => absurd e b) (fun e => absurd e c) (fun _ _ h => by split at h <;> omega)
  have U8 : ∀ (i : Nat) (w : Word), i < V.next.toNat → i ≠ ni.toNat →
      ¬(p ≠ 0 ∧ i = p.toNat ∧ lp = n) →
      (Rd M' (nodeField V i 8) w ↔ Rd M (nodeField V i 8) w) :=
    fun i w hi a c => U i 8 w hi (by omega) (by omega) (fun e => absurd e a) (fun _ => by omega)
      (fun _ => by omega) (fun h1 h2 h => by
        by_cases hs : lp = n
        · exact c ⟨h1, h2, hs⟩
        · rw [if_neg hs] at h
          omega)
  have U16 : ∀ (i : Nat) (w : Word), i < V.next.toNat → i ≠ ni.toNat →
      ¬(p ≠ 0 ∧ i = p.toNat ∧ lp ≠ n) →
      (Rd M' (nodeField V i 16) w ↔ Rd M (nodeField V i 16) w) :=
    fun i w hi a c => U i 16 w hi (by omega) (by omega) (fun e => absurd e a) (fun _ => by omega)
      (fun _ => by omega) (fun h1 h2 h => by
        by_cases hs : lp = n
        · rw [if_pos hs] at h
          omega
        · exact c ⟨h1, h2, hs⟩)
  -- a child link to a node other than `n` survives
  have Uc : ∀ (q i : Nat), q < V.next.toNat → q ≠ ni.toNat → i ≠ n.toNat → i < 2 ^ 64 →
      (Rd M (nodeField V q 8) (BitVec.ofNat 64 i) ∨ Rd M (nodeField V q 16) (BitVec.ofNat 64 i)) →
      (Rd M' (nodeField V q 8) (BitVec.ofNat 64 i) ∨
        Rd M' (nodeField V q 16) (BitVec.ofNat 64 i)) := by
    intro q i hq hqni hin hi64 h
    have key : ∀ x : Word, x = n → BitVec.ofNat 64 i = x → False := by
      intro x hx e
      rw [hx] at e
      apply hin
      rw [← e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
    rcases h with h | h
    · refine Or.inl ((U8 q _ hq hqni (fun hc => ?_)).mpr h)
      obtain ⟨hp0, hqp, hs⟩ := hc
      rw [hqp] at h
      exact key lp hs (Rd.inj h (hlp hp0))
    · refine Or.inr ((U16 q _ hq hqni (fun hc => ?_)).mpr h)
      obtain ⟨hp0, hqp, hs⟩ := hc
      obtain ⟨-, -, -, -, pp, rp, b, -, hrp, -, -, -, -, -, -, -, -, hor⟩ := hP hp0
      rw [hqp] at h
      exact key rp (hor.resolve_left hs) (Rd.inj h hrp)
  have hPar : ∀ (i : Nat) (q : Word), i ≠ n.toNat → i < 2 ^ 64 → ParentOkd M V K det i q →
      ParentOk M' (setRoot V (if p = 0 then ni else V.root)) K i q := by
    rintro i q hin hi64 ⟨hpar, hqd⟩
    rcases hpar with ⟨hq0, hroot⟩ | ⟨a, b, k, hch⟩
    · refine Or.inl ⟨hq0, ?_⟩
      show (if p = 0 then ni else V.root).toNat = i
      by_cases hp0 : p = 0
      · rcases hparN.1 with ⟨-, hr⟩ | ⟨h1, -⟩
        · exact absurd (hroot.symm.trans hr) hin
        · rw [hp0] at h1
          omega
      · rw [if_neg hp0]
        exact hroot
    · have hq0 : q ≠ 0 := fun e => by rw [e] at a; omega
      exact Or.inr ⟨a, b, k, Uc _ i b (fun e => hqd hq0 (by rw [e]; exact dni)) hin hi64 hch⟩
  have hChild : ∀ (i : Nat) (c : Word), ChildOk M V K i c → c.toNat ≠ n.toNat →
      ¬ det c.toNat → ChildOk M' (setRoot V (if p = 0 then ni else V.root)) K i c := by
    rintro i c ⟨a, b, k, hrd⟩ hcn hcd
    exact ⟨a, b, k, (U0 _ _ b (fun e => hcd (by rw [e]; exact dni))
      (fun e => hcd (by rw [e]; exact dnl)) hcn).mpr hrd⟩
  have hParN' : ParentOk M' (setRoot V (if p = 0 then ni else V.root)) K n.toNat ni :=
    Or.inr ⟨hni.1, hni.2.1, hnik, by
      rcases hside with ⟨-, e, -⟩ | ⟨e, -, -⟩
      · right
        rw [ofn, ← e]
        exact hni16
      · left
        rw [ofn, ← e]
        exact hni8⟩
  have hParNl' : ParentOk M' (setRoot V (if p = 0 then ni else V.root)) K nl.toNat ni :=
    Or.inr ⟨hni.1, hni.2.1, hnik, by
      rcases hside with ⟨e, -, -⟩ | ⟨-, e, -⟩
      · left
        rw [ofn, ← e]
        exact hni8
      · right
        rw [ofn, ← e]
        exact hni16⟩
  have hroot' : ∀ r : Word, r = (if p = 0 then ni else V.root) →
      (r = 0 ∨ (1 ≤ r.toNat ∧ r.toNat < V.next.toNat ∧ K r.toNat ≠ .free ∧
        Rd M' (nodeField V r.toNat 0) 0)) := by
    intro r hr
    by_cases hp0 : p = 0
    · rw [if_pos hp0] at hr
      subst hr
      exact Or.inr ⟨hni.1, hni.2.1, hni.2.2, hp0 ▸ hni0⟩
    · rw [if_neg hp0] at hr
      subst hr
      rcases hwf.root_ok with h | ⟨a, b, k, d', hrd⟩
      · exact Or.inl h
      · refine Or.inr ⟨a, b, k, (U0 _ _ b (fun e => d' (by rw [e]; exact dni))
          (fun e => d' (by rw [e]; exact dnl)) (fun e => ?_)).mpr hrd⟩
        rw [e] at hrd
        exact hp0 (Rd.inj hnp hrd)
  refine
    { wf :=
        { hdr := hhdr
          layout := hwf.layout
          next_pos := hwf.next_pos
          next_le := hwf.next_le
          cnt_le := hwf.cnt_le
          root_ok := hroot' _ rfl
          free_chain := ?_
          internal_ok := ?_
          leaf_ok := ?_
          order_ok := ?_ }
      keys := ⟨?_⟩
      keys8 := hok.keys8
      nodes8 := hok.nodes8
      order8 := hok.order8
      nc_pos := hok.nc_pos
      kl_st := hok.kl_st
      kl8 := hok.kl8
      leaf_key := ?_ }
  · obtain ⟨fl, hfl⟩ := hwf.free_chain
    have hmem := FreeChain.kind_mem fl _ hfl
    exact ⟨fl, FreeChain.congr (v := V) (kind := K)
      (v' := setRoot V (if p = 0 then ni else V.root)) (Nat.le_refl _) fl _ hfl
      (fun i hi => ⟨(hmem i hi).1, fun w hw => (U0 i w (hmem i hi).2.2
        (fun e => by have := (hmem i hi).1; rw [e, hnik] at this; cases this)
        (fun e => by have := (hmem i hi).1; rw [e, hnlk] at this; cases this)
        (fun e => by have := (hmem i hi).1; rw [e] at this; exact hn.2.2 this)).mpr hw⟩)⟩
  · -- internal nodes
    intro i hi1 hi2 hk
    have hi2 : i < V.next.toNat := hi2
    have hi64 : i < 2 ^ 64 := by have := V.next.isLt; omega
    by_cases hini : i = ni.toNat
    · subst hini
      refine ⟨p, li, ri, d, hni0, hni8, hni16, (U24 _ _ hi2).mpr hd,
        fun e => by have e' : d = V.kl * 8#64 := e; rw [e'] at hdlt; omega, ?_, ?_, ?_, ?_⟩
      · by_cases hp0 : p = 0
        · exact Or.inl ⟨hp0, show (if p = 0 then ni else V.root).toNat = ni.toNat by
            rw [if_pos hp0]⟩
        · obtain ⟨a, b, k, -⟩ := hP hp0
          refine Or.inr ⟨a, b, k, ?_⟩
          have := hps hp0
          by_cases hs : lp = n
          · rw [if_pos hs] at this
            left
            rw [ofn]
            exact this
          · rw [if_neg hs] at this
            right
            rw [ofn]
            exact this
      · rcases hside with ⟨e, -, -⟩ | ⟨e, -, -⟩
        · rw [e]
          exact ⟨hnl.1, hnl.2.1, hnl.2.2, by rw [ofn]; exact hnl0⟩
        · rw [e]
          exact ⟨hn.1, hn.2.1, hn.2.2, by rw [ofn]; exact hn0⟩
      · rcases hside with ⟨-, e, -⟩ | ⟨-, e, -⟩
        · rw [e]
          exact ⟨hn.1, hn.2.1, hn.2.2, by rw [ofn]; exact hn0⟩
        · rw [e]
          exact ⟨hnl.1, hnl.2.1, hnl.2.2, by rw [ofn]; exact hnl0⟩
      · rcases hside with ⟨e1, e2, -⟩ | ⟨e1, e2, -⟩
        · rw [e1, e2]
          exact wne (Ne.symm hnnl)
        · rw [e1, e2]
          exact wne hnnl
    by_cases hip : p ≠ 0 ∧ i = p.toNat
    · obtain ⟨hp0, rfl⟩ := hip
      obtain ⟨a, b, k, hdp, pp, rp, bb, hpp, hrp, hb, hbne, hparP, hcl, hcr, hdl, hdr, hlr,
        hor⟩ := hP hp0
      have hpnl : p.toNat ≠ nl.toNat := fun e => hdp (by rw [e]; exact dnl)
      have hps' := hps hp0
      have hParP' := hPar _ pp hpn hi64 hparP
      have hpp' := (U0 _ _ hi2 hini hpnl hpn).mpr hpp
      have hCni : ChildOk M' (setRoot V (if p = 0 then ni else V.root)) K p.toNat ni :=
        ⟨hni.1, hni.2.1, hni.2.2, by rw [ofn]; exact hni0⟩
      by_cases hs : lp = n
      · rw [if_pos hs] at hps'
        have hrn : rp.toNat ≠ n.toNat :=
          fun e => hlr (hs.trans (BitVec.eq_of_toNat_eq e).symm)
        exact ⟨pp, ni, rp, bb, hpp', hps', (U16 _ _ hi2 hini (fun h => h.2.2 hs)).mpr hrp,
          (U24 _ _ hi2).mpr hb, hbne, hParP', hCni, hChild _ rp hcr hrn hdr,
          wne (fun e => hdr (by rw [← e]; exact dni))⟩
      · rw [if_neg hs] at hps'
        have hln : lp.toNat ≠ n.toNat := fun e => hs (BitVec.eq_of_toNat_eq e)
        exact ⟨pp, lp, ni, bb, hpp', (U8 _ _ hi2 hini (fun h => hs h.2.2)).mpr (hlp hp0), hps',
          (U24 _ _ hi2).mpr hb, hbne, hParP', hChild _ lp hcl hln hdl, hCni,
          wne (fun e => hdl (by rw [e]; exact dni))⟩
    · have hinl : i ≠ nl.toNat := fun e => by rw [e, hnlk] at hk; cases hk
      have hdi := nd i hinl hini
      obtain ⟨q, l, r, b, hq, hl, hr, hb, hbne, hrest⟩ := hwf.internal_ok i hi1 hi2 hk
      obtain ⟨hpar, hcl, hcr, hdl, hdr, hlr⟩ := hrest hdi
      have hnp' : ¬(p ≠ 0 ∧ i = p.toNat ∧ lp = n) := fun h => hip ⟨h.1, h.2.1⟩
      have hnp'' : ¬(p ≠ 0 ∧ i = p.toNat ∧ lp ≠ n) := fun h => hip ⟨h.1, h.2.1⟩
      have hcne : ∀ c : Word, ChildOk M V K i c → c.toNat ≠ n.toNat := by
        intro c hc e
        have h0 := hc.2.2.2
        rw [e] at h0
        have hpi : p.toNat = i := toNat_of_eq_ofNat hi64 (Rd.inj hnp h0)
        exact hip ⟨fun e0 => by rw [e0] at hpi; omega, hpi.symm⟩
      by_cases hin : i = n.toNat
      · subst hin
        exact ⟨ni, l, r, b, hn0, (U8 _ _ hi2 hini hnp').mpr hl, (U16 _ _ hi2 hini hnp'').mpr hr,
          (U24 _ _ hi2).mpr hb, hbne, hParN', hChild _ l hcl (hcne l hcl) hdl,
          hChild _ r hcr (hcne r hcr) hdr, hlr⟩
      · exact ⟨q, l, r, b, (U0 _ _ hi2 hini hinl hin).mpr hq, (U8 _ _ hi2 hini hnp').mpr hl,
          (U16 _ _ hi2 hini hnp'').mpr hr, (U24 _ _ hi2).mpr hb, hbne, hPar i q hin hi64 hpar,
          hChild _ l hcl (hcne l hcl) hdl, hChild _ r hcr (hcne r hcr) hdr, hlr⟩
  · -- leaves
    intro i hi1 hi2 hk
    have hi2 : i < V.next.toNat := hi2
    have hi64 : i < 2 ^ 64 := by have := V.next.isLt; omega
    have hini : i ≠ ni.toNat := fun e => by rw [e, hnik] at hk; cases hk
    have hnotp : ∀ P : Prop, ¬(p ≠ 0 ∧ i = p.toNat ∧ P) := by
      intro P h
      obtain ⟨-, -, kp, -⟩ := hP h.1
      rw [← h.2.1, hk] at kp
      cases kp
    obtain ⟨q, value, pos, hq, hv, hpos, hb, hpar, hlt, hord⟩ := hwf.leaf_ok i hi1 hi2 hk
    have h8 := (U8 _ _ hi2 hini (hnotp _)).mpr hv
    have h16 := (U16 _ _ hi2 hini (hnotp _)).mpr hpos
    have h24 := (U24 _ _ hi2).mpr hb
    have ho := (hO _ _ (by have := hwf.cnt_le; omega)).mpr hord
    by_cases hinl : i = nl.toNat
    · subst hinl
      exact ⟨ni, value, pos, hnl0, h8, h16, h24, hParNl', hlt, ho⟩
    by_cases hin : i = n.toNat
    · subst hin
      exact ⟨ni, value, pos, hn0, h8, h16, h24, hParN', hlt, ho⟩
    · exact ⟨q, value, pos, (U0 _ _ hi2 hini hinl hin).mpr hq, h8, h16, h24,
        hPar i q hin hi64 (hpar (nd i hinl hini)), hlt, ho⟩
  · -- insertion order
    intro pos hpos
    have hpos : pos < V.cnt.toNat := hpos
    obtain ⟨i, hi, a, b, k, hrd⟩ := hwf.order_ok pos hpos
    refine ⟨i, (hO _ _ (by have := hwf.cnt_le; omega)).mpr hi, a, b, k,
      (U16 _ _ b (fun e => by rw [e, hnik] at k; cases k) (fun h => ?_)).mpr hrd⟩
    obtain ⟨-, -, kp, -⟩ := hP h.1
    rw [← h.2.1, k] at kp
    cases kp
  · -- bit order
    intro i hi1 hi2 hk b l r hb hl hr
    have hi2 : i < V.next.toNat := hi2
    have hb0 := (U24 _ _ hi2).mp hb
    by_cases hini : i = ni.toNat
    · subst hini
      have eb : d = b := Rd.inj hd hb0
      subst eb
      have el : li = l := Rd.inj hni8 hl
      have er : ri = r := Rd.inj hni16 hr
      subst el
      subst er
      have hnl24 : ∀ bl, Rd M' (nodeField V nl.toNat 24) bl → d.toNat < bl.toNat := by
        intro bl h
        obtain ⟨_, _, _, -, -, -, hb', -⟩ := hwf.leaf_ok _ hnl.1 hnl.2.1 hnlk
        rw [Rd.inj ((U24 _ _ hnl.2.1).mp h) hb']
        exact hdlt
      have hn24 : ∀ bl, Rd M' (nodeField V n.toNat 24) bl → d.toNat < bl.toNat := by
        intro bl h
        rw [Rd.inj ((U24 _ _ hn.2.1).mp h) hbn]
        exact hdbn
      rw [hR'ni]
      rcases hside with ⟨e1, e2, hκ⟩ | ⟨e1, e2, hκ⟩
      · rw [e1, e2, hR'o _ hnlni, hR'o _ hnni]
        exact ⟨hdlt, by rw [hκnl d hdlt, hκ], by simp [hκd, hκ],
          fun j hj => ⟨by rw [hκnl j (by omega), hκlt j hj], rfl⟩, hnl24, hn24⟩
      · rw [e1, e2, hR'o _ hnlni, hR'o _ hnni]
        exact ⟨hdlt, by simp [hκd, hκ], by rw [hκnl d hdlt, hκ],
          fun j hj => ⟨rfl, by rw [hκnl j (by omega), hκlt j hj]⟩, hn24, hnl24⟩
    by_cases hip : p ≠ 0 ∧ i = p.toNat
    · obtain ⟨hp0, rfl⟩ := hip
      obtain ⟨a, bq, k, hdp, pp, rp, bb, hpp, hrp, hbb, hbne, hparP, hcl, hcr, hdl, hdr, hlr,
        hor⟩ := hP hp0
      have eb : b = bb := Rd.inj hb0 hbb
      subst eb
      obtain ⟨bp, hbp, hbplt⟩ := hpc hp0
      have ebp : b = bp := Rd.inj hb0 hbp
      subst ebp
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hok.bits _ a bq k hdp b lp rp hb0 (hlp hp0) hrp
      have hps' := hps hp0
      have hni24 : ∀ bl, Rd M' (nodeField V ni.toNat 24) bl → b.toNat < bl.toNat := by
        intro bl h
        rw [Rd.inj ((U24 _ _ hni.2.1).mp h) hd]
        exact hbplt
      have hRp : R' p.toNat = R p.toNat := hR'o _ hini
      by_cases hs : lp = n
      · rw [if_pos hs] at hps'
        have el : ni = l := Rd.inj hps' hl
        subst el
        have er : rp = r := Rd.inj ((U16 _ _ hi2 hini (fun h => h.2.2 hs)).mpr hrp) hr
        subst er
        have hrni : rp.toNat ≠ ni.toNat := fun e => hdr (by rw [e]; exact dni)
        rw [hR'ni, hR'o _ hrni, hRp, ← hs]
        exact ⟨g1, g2, g3, g4, hni24, fun br h => g6 br ((U24 _ _ hcr.2.1).mp h)⟩
      · rw [if_neg hs] at hps'
        have el : lp = l :=
          Rd.inj ((U8 _ _ hi2 hini (fun h => hs h.2.2)).mpr (hlp hp0)) hl
        subst el
        have er : ni = r := Rd.inj hps' hr
        subst er
        have hrn := hor.resolve_left hs
        have hlni : lp.toNat ≠ ni.toNat := fun e => hdl (by rw [e]; exact dni)
        rw [hR'ni, hR'o _ hlni, hRp, ← hrn]
        exact ⟨g1, g2, g3, g4, fun bl h => g5 bl ((U24 _ _ hcl.2.1).mp h), hni24⟩
    · have hinl : i ≠ nl.toNat := fun e => by rw [e, hnlk] at hk; cases hk
      have hdi := nd i hinl hini
      obtain ⟨q, l', r', b', hq, hl', hr', hb', hbne, hrest⟩ := hwf.internal_ok i hi1 hi2 hk
      obtain ⟨-, hcl, hcr, hdl, hdr, -⟩ := hrest hdi
      have hl0 := (U8 _ _ hi2 hini (fun h => hip ⟨h.1, h.2.1⟩)).mp hl
      have hr0 := (U16 _ _ hi2 hini (fun h => hip ⟨h.1, h.2.1⟩)).mp hr
      have el : l = l' := Rd.inj hl0 hl'
      subst el
      have er : r = r' := Rd.inj hr0 hr'
      subst er
      obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hok.bits i hi1 hi2 hk hdi b l r hb0 hl0 hr0
      rw [hR'o _ (fun e => hdl (by rw [e]; exact dni)),
        hR'o _ (fun e => hdr (by rw [e]; exact dni)), hR'o _ hini]
      exact ⟨g1, g2, g3, g4, fun bl h => g5 bl ((U24 _ _ hcl.2.1).mp h),
        fun br h => g6 br ((U24 _ _ hcr.2.1).mp h)⟩
  · intro i hi1 hi2 hk j hj
    have hi2 : i < V.next.toNat := hi2
    have hini : i ≠ ni.toNat := fun e => by rw [e, hnik] at hk; cases hk
    rw [hR'o _ hini]
    exact hKey i (by omega) j _ hj (hok.leaf_key i hi1 hi2 hk j hj)

set_option maxHeartbeats 8000000 in
/-- The first key of an empty table: the detached leaf becomes the root. -/
theorem set_root_ok {M : Word → Option (PanValue Word)} {t : Word} {V : HtabV}
    {K : Nat → NodeKind} {R : KeyRep} {det : Nat → Prop}
    (hok : HtabOKd M t V K R det) {nl : Word} (hdet : ∀ i, det i ↔ i = nl.toNat)
    (hr0 : V.root = 0) (hnl : LiveN V K nl.toNat) (hnlk : K nl.toNat = .leaf)
    (hnl0 : Rd M (nodeField V nl.toNat 0) 0) :
    HtabOK (setCell M (t + 56#64) nl) t (setRoot V nl) K R := by
  have hwf := hok.wf
  have hlay := hwf.layout
  have hnxl := hwf.next_le
  have h00 : (0 : Word).toNat = 0 := rfl
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  have hne : ∀ k, k < 88 → k ≠ 56 → t + BitVec.ofNat 64 k ≠ t + 56#64 :=
    fun k hk hkk h => hkk ((hdr_eq_hdr hlay hk (by omega)).mp h)
  have N : ∀ (i o : Nat) (w : Word), i < V.next.toNat → o < 32 →
      (Rd (setCell M (t + 56#64) nl) (nodeField V i o) w ↔ Rd M (nodeField V i o) w) :=
    fun i o w hi ho => rd_hdrSet_node hlay (by omega) ho (k := 56) (by omega) nl w
  have O : ∀ (pos : Nat) (w : Word), pos ≤ V.nc.toNat →
      (Rd (setCell M (t + 56#64) nl) (orderSlot V pos) w ↔ Rd M (orderSlot V pos) w) :=
    fun pos w hp => rd_hdrSet_ord hlay hp (k := 56) (by omega) nl w
  have hPar : ∀ (i : Nat) (q : Word), 1 ≤ i → ParentOkd M V K det i q →
      ParentOk (setCell M (t + 56#64) nl) (setRoot V nl) K i q := by
    rintro i q hi1 ⟨hpar, -⟩
    rcases hpar with ⟨-, hroot'⟩ | ⟨a, b, k, hch⟩
    · rw [hr0] at hroot'
      omega
    · exact Or.inr ⟨a, b, k, hch.imp (N _ 8 _ b (by omega)).mpr (N _ 16 _ b (by omega)).mpr⟩
  have hChild : ∀ (i : Nat) (c : Word), ChildOk M V K i c →
      ChildOk (setCell M (t + 56#64) nl) (setRoot V nl) K i c := by
    rintro i c ⟨a, b, k, hrd⟩
    exact ⟨a, b, k, (N _ 0 _ b (by omega)).mpr hrd⟩
  refine
    { wf :=
        { hdr := ⟨hkl.frame _ (hne 0 (by omega) (by omega)),
            hst.frame _ (hne 8 (by omega) (by omega)), hcp.frame _ (hne 16 (by omega) (by omega)),
            hcnt.frame _ (hne 24 (by omega) (by omega)),
            hkeys.frame _ (hne 32 (by omega) (by omega)),
            hnd.frame _ (hne 40 (by omega) (by omega)),
            hord.frame _ (hne 48 (by omega) (by omega)), Rd.here _ _ _,
            hnext.frame _ (hne 64 (by omega) (by omega)),
            hfree.frame _ (hne 72 (by omega) (by omega)),
            hnc.frame _ (hne 80 (by omega) (by omega))⟩
          layout := hlay
          next_pos := hwf.next_pos
          next_le := hwf.next_le
          cnt_le := hwf.cnt_le
          root_ok := Or.inr ⟨hnl.1, hnl.2.1, hnl.2.2, (N _ 0 _ hnl.2.1 (by omega)).mpr hnl0⟩
          free_chain := ?_
          internal_ok := ?_
          leaf_ok := ?_
          order_ok := ?_ }
      keys := ⟨?_⟩
      keys8 := hok.keys8
      nodes8 := hok.nodes8
      order8 := hok.order8
      nc_pos := hok.nc_pos
      kl_st := hok.kl_st
      kl8 := hok.kl8
      leaf_key := ?_ }
  · obtain ⟨fl, hfl⟩ := hwf.free_chain
    have hmem := FreeChain.kind_mem fl _ hfl
    exact ⟨fl, FreeChain.congr (v := V) (kind := K) (v' := setRoot V nl) (Nat.le_refl _) fl _ hfl
      (fun i hi => ⟨(hmem i hi).1, fun w hw => (N i 0 w (hmem i hi).2.2 (by omega)).mpr hw⟩)⟩
  · intro i hi1 hi2 hk
    have hi2 : i < V.next.toNat := hi2
    have hdi : ¬ det i := fun h => by rw [(hdet i).mp h, hnlk] at hk; cases hk
    obtain ⟨q, l, r, b, hq, hl, hr, hb, hbne, hrest⟩ := hwf.internal_ok i hi1 hi2 hk
    obtain ⟨hpar, hcl, hcr, -, -, hlr⟩ := hrest hdi
    exact ⟨q, l, r, b, (N _ 0 _ hi2 (by omega)).mpr hq, (N _ 8 _ hi2 (by omega)).mpr hl,
      (N _ 16 _ hi2 (by omega)).mpr hr, (N _ 24 _ hi2 (by omega)).mpr hb, hbne, hPar i q hi1 hpar,
      hChild i l hcl, hChild i r hcr, hlr⟩
  · intro i hi1 hi2 hk
    have hi2 : i < V.next.toNat := hi2
    obtain ⟨q, value, pos, hq, hv, hpos, hb, hpar, hlt, hord'⟩ := hwf.leaf_ok i hi1 hi2 hk
    refine ⟨q, value, pos, (N _ 0 _ hi2 (by omega)).mpr hq, (N _ 8 _ hi2 (by omega)).mpr hv,
      (N _ 16 _ hi2 (by omega)).mpr hpos, (N _ 24 _ hi2 (by omega)).mpr hb, ?_, hlt,
      (O _ _ (by have := hwf.cnt_le; omega)).mpr hord'⟩
    by_cases hin : i = nl.toNat
    · subst hin
      exact Or.inl ⟨Rd.inj hq hnl0, rfl⟩
    · exact hPar i q hi1 (hpar (fun h => hin ((hdet i).mp h)))
  · intro pos hpos
    have hpos : pos < V.cnt.toNat := hpos
    obtain ⟨i, hi, a, b, k, hrd⟩ := hwf.order_ok pos hpos
    exact ⟨i, (O _ _ (by have := hwf.cnt_le; omega)).mpr hi, a, b, k,
      (N _ 16 _ b (by omega)).mpr hrd⟩
  · intro i hi1 hi2 hk b l r hb hl hr
    have hi2 : i < V.next.toNat := hi2
    have hdi : ¬ det i := fun h => by rw [(hdet i).mp h, hnlk] at hk; cases hk
    have hb0 := (N _ 24 _ hi2 (by omega)).mp hb
    have hl0 := (N _ 8 _ hi2 (by omega)).mp hl
    have hr0' := (N _ 16 _ hi2 (by omega)).mp hr
    obtain ⟨q, l', r', b', -, hl', hr', -, -, hrest⟩ := hwf.internal_ok i hi1 hi2 hk
    obtain ⟨-, hcl, hcr, -⟩ := hrest hdi
    have el : l = l' := Rd.inj hl0 hl'
    subst el
    have er : r = r' := Rd.inj hr0' hr'
    subst er
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hok.bits i hi1 hi2 hk hdi b l r hb0 hl0 hr0'
    exact ⟨g1, g2, g3, g4, fun bl h => g5 bl ((N _ 24 _ hcl.2.1 (by omega)).mp h),
      fun br h => g6 br ((N _ 24 _ hcr.2.1 (by omega)).mp h)⟩
  · intro i hi1 hi2 hk j hj
    have hi2 : i < V.next.toNat := hi2
    exact keybit_frame hlay hok.keys8 hok.kl_st hok.kl8
      (fun a ha _ => setCell_key_hdr hlay (k := 56) (by omega) nl ha) (by omega) hj
      (hok.leaf_key i hi1 hi2 hk j hj)

set_option maxHeartbeats 8000000 in
/-- Overwriting the value of a stored key. -/
theorem set_value_ok {M : Word → Option (PanValue Word)} {t : Word} {V : HtabV}
    {K : Nat → NodeKind} {R : KeyRep} (hok : HtabOK M t V K R) {L val : Word}
    (hL : LiveN V K L.toNat) (hLk : K L.toNat = .leaf) :
    HtabOK (setCell M (nodeField V L.toNat 8) val) t V K R := by
  have hwf := hok.wf
  have hlay := hwf.layout
  have hnxl := hwf.next_le
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  have hLle : L.toNat ≤ V.nc.toNat := by have := hL.2.1; omega
  have hLa := node_toNat hlay hLle (o := 8) (by omega)
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  have H : ∀ (k : Nat) (w : Word), k < 88 → Rd M (t + BitVec.ofNat 64 k) w →
      Rd (setCell M (nodeField V L.toNat 8) val) (t + BitVec.ofNat 64 k) w :=
    fun k w hk h => h.frame _ (NE (by rw [hdr_toNat hlay hk, hLa]; omega))
  have N : ∀ (i o : Nat) (w : Word), i < V.next.toNat → o < 32 → (i = L.toNat → o ≠ 8) →
      o % 8 = 0 → (Rd (setCell M (nodeField V L.toNat 8) val) (nodeField V i o) w ↔
        Rd M (nodeField V i o) w) := by
    intro i o w hi ho hc ho8
    rw [rd_setCell, if_neg (NE (by
      rw [node_toNat hlay (i := i) (by omega) ho, hLa]
      intro e
      have : i = L.toNat := by omega
      exact hc this (by omega)))]
  have O : ∀ (pos : Nat) (w : Word), pos ≤ V.nc.toNat →
      (Rd (setCell M (nodeField V L.toNat 8) val) (orderSlot V pos) w ↔
        Rd M (orderSlot V pos) w) := by
    intro pos w hp
    rw [rd_setCell, if_neg (NE (by rw [ord_toNat hlay hp, hLa]; omega))]
  have nL : ∀ i, K i = .internal → i ≠ L.toNat := fun i k e => by rw [e, hLk] at k; cases k
  have hPar : ∀ (i : Nat) (q : Word), ParentOk M V K i q →
      ParentOk (setCell M (nodeField V L.toNat 8) val) V K i q := by
    rintro i q (h | ⟨a, b, k, hch⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a, b, k, hch.imp (N _ 8 _ b (by omega) (fun e => absurd e (nL _ k))
        (by omega)).mpr (N _ 16 _ b (by omega) (fun _ => by omega) (by omega)).mpr⟩
  have hChild : ∀ (i : Nat) (c : Word), ChildOk M V K i c →
      ChildOk (setCell M (nodeField V L.toNat 8) val) V K i c := by
    rintro i c ⟨a, b, k, hrd⟩
    exact ⟨a, b, k, (N _ 0 _ b (by omega) (fun _ => by omega) (by omega)).mpr hrd⟩
  refine
    { wf :=
        { hdr := ⟨H 0 _ (by omega) hkl, H 8 _ (by omega) hst, H 16 _ (by omega) hcp,
            H 24 _ (by omega) hcnt, H 32 _ (by omega) hkeys, H 40 _ (by omega) hnd,
            H 48 _ (by omega) hord, H 56 _ (by omega) hroot, H 64 _ (by omega) hnext,
            H 72 _ (by omega) hfree, H 80 _ (by omega) hnc⟩
          layout := hlay
          next_pos := hwf.next_pos
          next_le := hwf.next_le
          cnt_le := hwf.cnt_le
          root_ok := hwf.root_ok.imp id (fun ⟨a, b, k, hrd⟩ =>
            ⟨a, b, k, (N _ 0 _ b (by omega) (fun _ => by omega) (by omega)).mpr hrd⟩)
          free_chain := ?_
          internal_ok := ?_
          leaf_ok := ?_
          order_ok := ?_ }
      keys := ⟨?_⟩
      keys8 := hok.keys8
      nodes8 := hok.nodes8
      order8 := hok.order8
      nc_pos := hok.nc_pos
      kl_st := hok.kl_st
      kl8 := hok.kl8
      leaf_key := ?_ }
  · obtain ⟨fl, hfl⟩ := hwf.free_chain
    have hmem := FreeChain.kind_mem fl _ hfl
    exact ⟨fl, FreeChain.congr (v := V) (kind := K) (v' := V) (Nat.le_refl _) fl _ hfl
      (fun i hi => ⟨(hmem i hi).1, fun w hw =>
        (N i 0 w (hmem i hi).2.2 (by omega) (fun _ => by omega) (by omega)).mpr hw⟩)⟩
  · intro i hi1 hi2 hk
    have hiL := nL i hk
    obtain ⟨q, l, r, b, hq, hl, hr, hb, hbne, hpar, hcl, hcr, hlr⟩ :=
      hwf.internal_ok i hi1 hi2 hk
    exact ⟨q, l, r, b, (N _ 0 _ hi2 (by omega) (fun _ => by omega) (by omega)).mpr hq,
      (N _ 8 _ hi2 (by omega) (fun e => absurd e hiL) (by omega)).mpr hl,
      (N _ 16 _ hi2 (by omega) (fun _ => by omega) (by omega)).mpr hr,
      (N _ 24 _ hi2 (by omega) (fun _ => by omega) (by omega)).mpr hb, hbne, hPar i q hpar,
      hChild i l hcl, hChild i r hcr, hlr⟩
  · intro i hi1 hi2 hk
    obtain ⟨q, value, pos, hq, hv, hpos, hb, hpar, hlt, hord'⟩ := hwf.leaf_ok i hi1 hi2 hk
    have hv' : ∃ value', Rd (setCell M (nodeField V L.toNat 8) val) (nodeField V i 8) value' := by
      by_cases hiL : i = L.toNat
      · subst hiL
        exact ⟨val, Rd.here _ _ _⟩
      · exact ⟨value, (N _ 8 _ hi2 (by omega) (fun e => absurd e hiL) (by omega)).mpr hv⟩
    obtain ⟨value', hv''⟩ := hv'
    exact ⟨q, value', pos, (N _ 0 _ hi2 (by omega) (fun _ => by omega) (by omega)).mpr hq, hv'',
      (N _ 16 _ hi2 (by omega) (fun _ => by omega) (by omega)).mpr hpos,
      (N _ 24 _ hi2 (by omega) (fun _ => by omega) (by omega)).mpr hb, hPar i q hpar, hlt,
      (O _ _ (by have := hwf.cnt_le; omega)).mpr hord'⟩
  · intro pos hpos
    obtain ⟨i, hi, a, b, k, hrd⟩ := hwf.order_ok pos hpos
    exact ⟨i, (O _ _ (by have := hwf.cnt_le; omega)).mpr hi, a, b, k,
      (N _ 16 _ b (by omega) (fun _ => by omega) (by omega)).mpr hrd⟩
  · intro i hi1 hi2 hk b l r hb hl hr
    have hiL := nL i hk
    have hb0 := (N _ 24 _ hi2 (by omega) (fun _ => by omega) (by omega)).mp hb
    have hl0 := (N _ 8 _ hi2 (by omega) (fun e => absurd e hiL) (by omega)).mp hl
    have hr0 := (N _ 16 _ hi2 (by omega) (fun _ => by omega) (by omega)).mp hr
    obtain ⟨q, l', r', b', -, hl', hr', -, -, -, hcl, hcr, -⟩ := hwf.internal_ok i hi1 hi2 hk
    have el : l = l' := Rd.inj hl0 hl'
    subst el
    have er : r = r' := Rd.inj hr0 hr'
    subst er
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hok.keys.internal_bits i hi1 hi2 hk b l r hb0 hl0 hr0
    exact ⟨g1, g2, g3, g4,
      fun bl h => g5 bl ((N _ 24 _ hcl.2.1 (by omega) (fun _ => by omega) (by omega)).mp h),
      fun br h => g6 br ((N _ 24 _ hcr.2.1 (by omega) (fun _ => by omega) (by omega)).mp h)⟩
  · intro i hi1 hi2 hk j hj
    exact keybit_frame hlay hok.keys8 hok.kl_st hok.kl8
      (fun a _ ha => setCell_key_node hlay hLle (by omega) val ha) (by omega) hj
      (hok.leaf_key i hi1 hi2 hk j hj)

end InitECandidate.Solver.GuestBound
