import InitECandidate.Solver.GuestBound.HtabLeafRun

/-!
# Hash tables: `htab_new_internal`

The new internal node is detached: it has its bit index, but no parent and no
children yet.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- Memory after the stores of `htab_new_internal`. -/
def intMem (m : Word → Option (PanValue Word)) (v : HtabV) (n bit : Word) :
    Word → Option (PanValue Word) :=
  setCell (setCell (setCell (setCell m (nodeField v n.toNat 0) 0#64) (nodeField v n.toNat 8) 0#64)
    (nodeField v n.toNat 16) 0#64) (nodeField v n.toNat 24) bit

variable {m0 : Word → Option (PanValue Word)} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
  {rep : KeyRep}

/-- The stores of `htab_new_internal` touch only node `n`. -/
theorem intMem_other (hlay : HtabLayout t v) {n bit : Word} (hnle : n.toNat ≤ v.nc.toNat)
    (A : Word) (h : ∀ o, o < 32 → A.toNat ≠ v.nodes.toNat + (n.toNat * 32 + o)) :
    intMem m0 v n bit A = m0 A := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  unfold intMem
  rw [setCell_ne' _ (NE (by rw [node_toNat hlay hnle (o := 24) (by omega)]; exact h 24 (by omega))),
    setCell_ne' _ (NE (by rw [node_toNat hlay hnle (o := 16) (by omega)]; exact h 16 (by omega))),
    setCell_ne' _ (NE (by rw [node_toNat hlay hnle (o := 8) (by omega)]; exact h 8 (by omega))),
    setCell_ne' _ (NE (by rw [node_toNat hlay hnle (o := 0) (by omega)]; exact h 0 (by omega)))]

set_option maxHeartbeats 8000000 in
/-- The table after `htab_new_internal`: node `n` is a detached internal node. -/
theorem internal_ok {det : Nat → Prop} (hok : HtabOKd m0 t v kind rep det) {n bit : Word}
    (hn1 : 1 ≤ n.toNat) (hn2 : n.toNat < v.next.toNat) (hfree : kind n.toNat = .free)
    (hfl : ∃ fl, FreeChain m0 v kind v.free fl ∧ n.toNat ∉ fl) (hbit : bit ≠ v.kl * 8#64)
    {kind' : Nat → NodeKind} {det' : Nat → Prop}
    (hkn : kind' n.toNat = .internal) (hko : ∀ i, i ≠ n.toNat → kind' i = kind i)
    (hdet : ∀ i, det' i ↔ (i = n.toNat ∨ det i)) :
    HtabOKd (intMem m0 v n bit) t v kind' rep det' := by
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  have hnl := hwf.next_le
  have hcl := hwf.cnt_le
  have hnle : n.toNat ≤ v.nc.toNat := by omega
  have hT : ∀ k, k < 88 → (t + BitVec.ofNat 64 k).toNat = t.toNat + k :=
    fun k hk => hdr_toNat hlay hk
  have hNf : ∀ i o, i ≤ v.nc.toNat → o < 32 →
      (nodeField v i o).toNat = v.nodes.toNat + (i * 32 + o) := fun i o hi ho => node_toNat hlay hi ho
  have hOs : ∀ p, p ≤ v.nc.toNat → (orderSlot v p).toNat = v.order.toNat + p * 8 :=
    fun p hp => ord_toNat hlay hp
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hoth := intMem_other (m0 := m0) hlay (bit := bit) hnle
  have hNode : ∀ (i o : Nat) (w : Word), i ≤ v.nc.toNat → i ≠ n.toNat → o < 32 →
      (Rd (intMem m0 v n bit) (nodeField v i o) w ↔ Rd m0 (nodeField v i o) w) := by
    intro i o w hi hin ho
    unfold Rd
    rw [hoth _ (fun o' ho' => by rw [hNf i o hi ho]; omega)]
  have hOrd : ∀ (p : Nat) (w : Word), p ≤ v.nc.toNat →
      (Rd (intMem m0 v n bit) (orderSlot v p) w ↔ Rd m0 (orderSlot v p) w) := by
    intro p w hp
    unfold Rd
    rw [hoth _ (fun o' ho' => by rw [hOs p hp]; omega)]
  have hH : ∀ (k : Nat) (w : Word), k ≤ 80 → Rd m0 (t + BitVec.ofNat 64 k) w →
      Rd (intMem m0 v n bit) (t + BitVec.ofNat 64 k) w := by
    intro k w hk h
    unfold Rd
    rw [hoth _ (fun o' ho' => by rw [hT k (by omega)]; omega)]
    exact h
  have hne : ∀ o o', o < 32 → o' < 32 → o ≠ o' → nodeField v n.toNat o ≠ nodeField v n.toNat o' :=
    fun o o' ho ho' h => NE (by rw [hNf _ o hnle ho, hNf _ o' hnle ho']; omega)
  have hN0 : Rd (intMem m0 v n bit) (nodeField v n.toNat 0) 0#64 :=
    (((Rd.here _ _ _).frame _ (hne 0 8 (by omega) (by omega) (by omega))).frame _
      (hne 0 16 (by omega) (by omega) (by omega))).frame _
      (hne 0 24 (by omega) (by omega) (by omega))
  have hN8 : Rd (intMem m0 v n bit) (nodeField v n.toNat 8) 0#64 :=
    ((Rd.here _ _ _).frame _ (hne 8 16 (by omega) (by omega) (by omega))).frame _
      (hne 8 24 (by omega) (by omega) (by omega))
  have hN16 : Rd (intMem m0 v n bit) (nodeField v n.toNat 16) 0#64 :=
    (Rd.here _ _ _).frame _ (hne 16 24 (by omega) (by omega) (by omega))
  have hN24 : Rd (intMem m0 v n bit) (nodeField v n.toNat 24) bit := Rd.here _ _ _
  have hnk : ∀ i, kind i ≠ .free → i ≠ n.toNat := fun i h e => h (e ▸ hfree)
  have hPar : ∀ i p, i ≠ n.toNat → ParentOkd m0 v kind det i p →
      ParentOkd (intMem m0 v n bit) v kind' det' i p := by
    rintro i p hin ⟨hp, hpd⟩
    refine ⟨?_, fun hp0 hd => ?_⟩
    · rcases hp with hr | ⟨a, b, k, hrd⟩
      · exact Or.inl hr
      · have hpn : p.toNat ≠ n.toNat := hnk _ (by rw [k]; exact NodeKind.noConfusion)
        exact Or.inr ⟨a, b, by rw [hko _ hpn]; exact k,
          hrd.imp (hNode _ 8 _ (by omega) hpn (by omega)).mpr
            (hNode _ 16 _ (by omega) hpn (by omega)).mpr⟩
    · rcases (hdet _).mp hd with e | hd
      · rcases hp with ⟨hr, -⟩ | ⟨-, -, k, -⟩
        · exact hp0 hr
        · exact hnk _ (by rw [k]; exact NodeKind.noConfusion) e
      · exact hpd hp0 hd
  have hChild : ∀ i cw, ChildOk m0 v kind i cw →
      ChildOk (intMem m0 v n bit) v kind' i cw ∧ cw.toNat ≠ n.toNat := by
    rintro i cw ⟨a, b, k, hrd⟩
    have hcn := hnk _ k
    exact ⟨⟨a, b, by rw [hko _ hcn]; exact k, (hNode _ 0 _ (by omega) hcn (by omega)).mpr hrd⟩, hcn⟩
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfreeh, hnc⟩ := hwf.hdr
  obtain ⟨fl, hflc, hnfl⟩ := hfl
  have hmem := FreeChain.kind_mem fl _ hflc
  refine
    { wf :=
        { hdr := ⟨hH 0 _ (by omega) hkl, hH 8 _ (by omega) hst, hH 16 _ (by omega) hcp,
            hH 24 _ (by omega) hcnt, hH 32 _ (by omega) hkeys, hH 40 _ (by omega) hnd,
            hH 48 _ (by omega) hord, hH 56 _ (by omega) hroot, hH 64 _ (by omega) hnext,
            hH 72 _ (by omega) hfreeh, hH 80 _ (by omega) hnc⟩
          layout := hlay
          next_pos := hwf.next_pos
          next_le := hnl
          cnt_le := hcl
          root_ok := ?_
          free_chain := ⟨fl, FreeChain.congr (v := v) (kind := kind) (v' := v) (Nat.le_refl _) fl _
            hflc (fun i hi => by
              have hin : i ≠ n.toNat := fun e => hnfl (e ▸ hi)
              have := hmem i hi
              exact ⟨by rw [hko _ hin]; exact this.1,
                fun w hw => (hNode i 0 w (by omega) hin (by omega)).mpr hw⟩)⟩
          internal_ok := ?_
          leaf_ok := ?_
          order_ok := ?_ }
      bits := ?_
      keys8 := hok.keys8
      nodes8 := hok.nodes8
      order8 := hok.order8
      nc_pos := hok.nc_pos
      kl_st := hok.kl_st
      kl8 := hok.kl8
      leaf_key := ?_ }
  · rcases hwf.root_ok with h | ⟨a, b, k, d, hrd⟩
    · exact Or.inl h
    · have hrn' := hnk _ k
      exact Or.inr ⟨a, b, by rw [hko _ hrn']; exact k,
        fun hd => ((hdet _).mp hd).elim hrn' d, (hNode _ 0 _ (by omega) hrn' (by omega)).mpr hrd⟩
  · intro i hi1 hi2 hk
    by_cases hin : i = n.toNat
    · subst hin
      exact ⟨0#64, 0#64, 0#64, bit, hN0, hN8, hN16, hN24, hbit,
        fun hd => absurd ((hdet _).mpr (Or.inl rfl)) hd⟩
    rw [hko _ hin] at hk
    obtain ⟨p, l, r, b, hp, hl, hr, hb, hbne, hrest⟩ := hwf.internal_ok i hi1 hi2 hk
    refine ⟨p, l, r, b, (hNode i 0 _ (by omega) hin (by omega)).mpr hp,
      (hNode i 8 _ (by omega) hin (by omega)).mpr hl,
      (hNode i 16 _ (by omega) hin (by omega)).mpr hr,
      (hNode i 24 _ (by omega) hin (by omega)).mpr hb, hbne, fun hd => ?_⟩
    obtain ⟨hpar, hcl', hcr', hdl, hdr, hlr⟩ := hrest (fun d => hd ((hdet _).mpr (Or.inr d)))
    have hL := hChild i l hcl'
    have hR := hChild i r hcr'
    exact ⟨hPar i p hin hpar, hL.1, hR.1, fun d => ((hdet _).mp d).elim hL.2 hdl,
      fun d => ((hdet _).mp d).elim hR.2 hdr, hlr⟩
  · intro i hi1 hi2 hk
    have hin : i ≠ n.toNat := fun e => by rw [e, hkn] at hk; cases hk
    rw [hko _ hin] at hk
    obtain ⟨p, value, pos, hp, hv, hpos, hb, hpar, hlt, hord'⟩ := hwf.leaf_ok i hi1 hi2 hk
    exact ⟨p, value, pos, (hNode i 0 _ (by omega) hin (by omega)).mpr hp,
      (hNode i 8 _ (by omega) hin (by omega)).mpr hv,
      (hNode i 16 _ (by omega) hin (by omega)).mpr hpos,
      (hNode i 24 _ (by omega) hin (by omega)).mpr hb,
      fun hd => hPar i p hin (hpar (fun d => hd ((hdet _).mpr (Or.inr d)))), hlt,
      (hOrd _ _ (by omega)).mpr hord'⟩
  · intro pos hpos
    obtain ⟨i, hi, a, b, k, hrd⟩ := hwf.order_ok pos hpos
    have hin := hnk i.toNat (by rw [k]; exact NodeKind.noConfusion)
    exact ⟨i, (hOrd _ _ (by omega)).mpr hi, a, b, by rw [hko _ hin]; exact k,
      (hNode _ 16 _ (by omega) hin (by omega)).mpr hrd⟩
  · intro i hi1 hi2 hk hd b l r hb hl hr
    have hin : i ≠ n.toNat := fun e => hd ((hdet _).mpr (Or.inl e))
    rw [hko _ hin] at hk
    have hd0 : ¬ det i := fun d => hd ((hdet _).mpr (Or.inr d))
    have hb0 := (hNode i 24 _ (by omega) hin (by omega)).mp hb
    have hl0 := (hNode i 8 _ (by omega) hin (by omega)).mp hl
    have hr0 := (hNode i 16 _ (by omega) hin (by omega)).mp hr
    obtain ⟨p', l', r', b', -, hl', hr', -, -, hrest⟩ := hwf.internal_ok i hi1 hi2 hk
    obtain ⟨-, hcl', hcr', -⟩ := hrest hd0
    have el := Rd.inj hl' hl0
    have er := Rd.inj hr' hr0
    subst el
    subst er
    have hln := hnk _ hcl'.2.2.1
    have hrn' := hnk _ hcr'.2.2.1
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hok.bits i hi1 hi2 hk hd0 b l' r' hb0 hl0 hr0
    exact ⟨g1, g2, g3, g4,
      fun bl hbl => g5 bl ((hNode _ 24 _ (by have := hcl'.2.1; omega) hln (by omega)).mp hbl),
      fun br hbr => g6 br ((hNode _ 24 _ (by have := hcr'.2.1; omega) hrn' (by omega)).mp hbr)⟩
  · intro i hi1 hi2 hk j hj
    have hin : i ≠ n.toNat := fun e => by rw [e, hkn] at hk; cases hk
    rw [hko _ hin] at hk
    exact keybit_frame hlay hok.keys8 hok.kl_st hok.kl8
      (fun a _ ha => hoth a (fun o' ho' => by omega)) (by omega) hj
      (hok.leaf_key i hi1 hi2 hk j hj)

variable {σ : Type} {E : Env σ}

set_option maxHeartbeats 8000000 in
theorem htab_new_internal_exec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_new_internal" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t bit pv : Word) (v : HtabV) (kind : Nat → NodeKind)
    (rep : KeyRep) (det : Nat → Prop)
    (ht : s.locals "t" = some (.word t)) (hb : s.locals "bit" = some (.word bit))
    (hok : HtabOKd s.memory t v kind rep det)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (hbit : bit ≠ v.kl * 8#64)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' n v' kind', r = .returned l g' m' s.ffi [.word n] ∧
      HtabOKd m' t v' kind' rep (fun i => i = n.toNat ∨ det i) ∧
      v'.kl = v.kl ∧ v'.st = v.st ∧ v'.cnt = v.cnt ∧ v'.root = v.root ∧ 1 ≤ n.toNat ∧
      n.toNat < v'.next.toNat ∧ kind' n.toNat = .internal ∧
      (∀ i, i < v.next.toNat → i ≠ n.toNat → kind' i = kind i) ∧
      v.next.toNat ≤ v'.next.toNat ∧ (kind n.toNat = .free ∨ n.toNat = v.next.toNat) ∧
      ((v'.keys = v.keys ∧ v'.nodes = v.nodes ∧ v'.order = v.order ∧ v'.nc = v.nc) ∨
        pv.toNat ≤ v'.keys.toNat) ∧
      Rd m' (nodeField v' n.toNat 24) bit ∧
      (∀ (i o : Nat) (w : Word), i ≤ v.nc.toNat → i ≠ n.toNat → o < 32 → o % 8 = 0 →
        (Rd m' (nodeField v' i o) w ↔ Rd s.memory (nodeField v i o) w)) ∧
      (∃ pv' : Word, g' "heap_ptr" = some (.word pv') ∧ InHeap pv' ∧
        v'.order.toNat + (v'.nc.toNat + 1) * 8 ≤ pv'.toNat ∧ pv.toNat ≤ pv'.toNat) ∧
      ∀ A : Word, (A.toNat + 8 ≤ t.toNat ∨ t.toNat + 88 ≤ A.toNat) →
        (A.toNat + 8 ≤ pv.toNat ∨ 2952790016 ≤ A.toNat) →
        (A.toNat + 8 ≤ v.keys.toNat ∨ v.order.toNat + (v.nc.toNat + 1) * 8 ≤ A.toNat) →
        m' A = s.memory A := by
  have hbody := (fun_of_index 136 hE.functions (by guest_decl_at 136) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' n v' kind', r = .returned l g' m' s.ffi [.word n] ∧
      HtabOKd m' t v' kind' rep (fun i => i = n.toNat ∨ det i) ∧
      v'.kl = v.kl ∧ v'.st = v.st ∧ v'.cnt = v.cnt ∧ v'.root = v.root ∧ 1 ≤ n.toNat ∧
      n.toNat < v'.next.toNat ∧ kind' n.toNat = .internal ∧
      (∀ i, i < v.next.toNat → i ≠ n.toNat → kind' i = kind i) ∧
      v.next.toNat ≤ v'.next.toNat ∧ (kind n.toNat = .free ∨ n.toNat = v.next.toNat) ∧
      ((v'.keys = v.keys ∧ v'.nodes = v.nodes ∧ v'.order = v.order ∧ v'.nc = v.nc) ∨
        pv.toNat ≤ v'.keys.toNat) ∧
      Rd m' (nodeField v' n.toNat 24) bit ∧
      (∀ (i o : Nat) (w : Word), i ≤ v.nc.toNat → i ≠ n.toNat → o < 32 → o % 8 = 0 →
        (Rd m' (nodeField v' i o) w ↔ Rd s.memory (nodeField v i o) w)) ∧
      (∃ pv' : Word, g' "heap_ptr" = some (.word pv') ∧ InHeap pv' ∧
        v'.order.toNat + (v'.nc.toNat + 1) * 8 ≤ pv'.toNat ∧ pv.toNat ≤ pv'.toNat) ∧
      ∀ A : Word, (A.toNat + 8 ≤ t.toNat ∨ t.toNat + 88 ≤ A.toNat) →
        (A.toNat + 8 ≤ pv.toNat ∨ 2952790016 ≤ A.toNat) →
        (A.toNat + 8 ≤ v.keys.toNat ∨ v.order.toNat + (v.nc.toNat + 1) * 8 ≤ A.toNat) →
        m' A = s.memory A)) r h
  refine WPs.decCall_newnode hE ht hok hp hpH hend (fun g' m' n hrel => ?_)
  have hwas : kind n.toNat = .free ∨ n.toNat = v.next.toNat := by
    rcases hrel with ⟨hf0, rfl, -⟩ | ⟨-, rfl, -⟩
    · obtain ⟨fl, hc⟩ := hok.wf.free_chain
      cases fl with
      | nil => exact absurd hc hf0
      | cons i rest =>
        obtain ⟨hi, -, -, k, -⟩ := hc
        left
        rw [hi]
        exact k
    · exact Or.inr rfl
  have hfr := new_node_frame hok hrel
  have hrd := fun {v' kind' rep' det'} (h' : HtabOKd m' t v' kind' rep' det') =>
    new_node_rd hok hpH hend hrel h'
  obtain ⟨v1, kind1, hok1, e1, e2, e3, e4, hn1, hn2, hkf, hfl, hkold, hnext, hloc, pv', hp',
    hpH', hend', hpp⟩ := htab_new_node_ok hok hp hpH hend hrel
  have hlay1 := hok1.wf.layout
  have hncle : v.nc.toNat ≤ v1.nc.toNat := new_node_nc hok hrel hok1
  obtain ⟨l1, l2, l3, l4⟩ := id hlay1
  have hnl1 := hok1.wf.next_le
  have hnle : n.toNat ≤ v1.nc.toNat := by omega
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnx, hfreeh, hnc⟩ := hok1.wf.hdr
  obtain ⟨hpvle', -⟩ := id hpH'
  refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 40#64 (by lk [ht])) hnd) ?_
  refine WPs.seq_store hE (eval_node hE hlay1 (idx := "n") hnle (by lk []) (by lk []) 0#64
    (by decide)) (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (eval_node hE hlay1 (idx := "n") hnle (by lk []) (by lk []) 8#64
    (by decide)) (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (eval_node hE hlay1 (idx := "n") hnle (by lk []) (by lk []) 16#64
    (by decide)) (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (eval_node hE hlay1 (idx := "n") hnle (by lk []) (by lk []) 24#64
    (by decide)) (of_eval (w := bit) (by lk [hb])) ?_
  refine WPs.ret (of_eval (w := n) (by lk [])) ?_
  refine ⟨_, g', intMem m' v1 n bit, n, v1,
    (fun i => if i = n.toNat then NodeKind.internal else kind1 i), rfl, ?_, e1, e2, e3, e4,
    hn1, hn2, if_pos rfl, fun i hi hin => (if_neg hin).trans (hkold i hi hin), hnext, hwas,
    hloc,
    Rd.here _ _ _, fun i o w hi hin ho ho8 => ?_, ⟨pv', hp', hpH', hend', hpp⟩,
    fun A hT hP hB => ?_⟩
  · exact internal_ok hok1 hn1 hn2 hkf hfl (by rw [e1]; exact hbit) (if_pos rfl)
      (fun i hin => if_neg hin) (fun i => Iff.rfl)
  · refine Iff.trans ?_ (hrd hok1 i o w hi ho ho8)
    unfold Rd
    rw [intMem_other hlay1 hnle _ (fun o' ho' => by
      rw [node_toNat hlay1 (i := i) (by
        rcases hloc with ⟨a, b, c', d⟩ | hge
        · rw [d]; exact hi
        · exact Nat.le_trans hi hncle) ho]
      omega)]
  · rw [intMem_other hlay1 hnle A (fun o ho => by
      rcases hloc with ⟨a, b, c', d⟩ | hge
      · rw [← a, ← c', ← d] at hB
        omega
      · omega)]
    exact hfr A hT hP

end InitECandidate.Solver.GuestBound
