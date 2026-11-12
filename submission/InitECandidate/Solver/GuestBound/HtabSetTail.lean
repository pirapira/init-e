import InitECandidate.Solver.GuestBound.HtabSetWalk

/-!
# Hash tables: `htab_set` after the second descent

Allocate the leaf and the internal node, then link them in.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ}

local notation "LINK_TAIL" => ((Prog.decCall "nl" Shape.one "htab_new_leaf" [(Exp.var VarKind.local "t"), (Exp.var VarKind.local "key"), (Exp.var VarKind.local "value")] (Prog.decCall "ni" Shape.one "htab_new_internal" [(Exp.var VarKind.local "t"), (Exp.var VarKind.local "d")] (Prog.seq (Prog.assign VarKind.local "nodes" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 40))]))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "ni"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "p")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "nl"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "ni")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "ni")) (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.op BinOp.and [(Exp.shift Shift.lsr (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.shift Shift.lsr (Exp.var VarKind.local "d") (Exp.const (BitVec.ofNat 64 3)))])) (Exp.op BinOp.sub [(Exp.const (BitVec.ofNat 64 7)), (Exp.op BinOp.and [(Exp.var VarKind.local "d"), (Exp.const (BitVec.ofNat 64 7))])])), (Exp.const (BitVec.ofNat 64 1))]) (Exp.const (BitVec.ofNat 64 0))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "ni"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "nl")) (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "ni"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 16))]) (Exp.var VarKind.local "n"))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "ni"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "n")) (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "ni"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 16))]) (Exp.var VarKind.local "nl")))) (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "p") (Exp.const (BitVec.ofNat 64 0))) (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "t"), (Exp.const (BitVec.ofNat 64 56))]) (Exp.var VarKind.local "ni")) (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "p"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 8))])) (Exp.var VarKind.local "n")) (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "p"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "ni")) (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "p"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 16))]) (Exp.var VarKind.local "ni")))) (Prog.return (Exp.const (BitVec.ofNat 64 0))))))))))) : Prog Word)

/-- What `htab_set` returns: a well-formed table of the same key length, a
heap pointer past its blocks, and everything outside the table and the fresh
heap untouched. -/
def SetPost (m : Word → Option (PanValue Word)) (t pv : Word) (v : HtabV) (f : FfiState σ)
    (r : Result σ) : Prop :=
  ∃ l g' m' v' kind' rep', r = .returned l g' m' f [.word 0#64] ∧ HtabOK m' t v' kind' rep' ∧
    v'.kl = v.kl ∧
    (∃ pv' : Word, g' "heap_ptr" = some (.word pv') ∧ InHeap pv' ∧
      v'.order.toNat + (v'.nc.toNat + 1) * 8 ≤ pv'.toNat ∧ pv.toNat ≤ pv'.toNat) ∧
    ∀ A : Word, (A.toNat + 8 ≤ t.toNat ∨ t.toNat + 88 ≤ A.toNat) →
      (A.toNat + 8 ≤ pv.toNat ∨ 2952790016 ≤ A.toNat) →
      (A.toNat + 8 ≤ v.keys.toNat ∨ v.order.toNat + (v.nc.toNat + 1) * 8 ≤ A.toNat) →
      m' A = m A

set_option maxHeartbeats 32000000 in
theorem set_link_tail (hE : GuestEnv E) {t keyp val pv d L nw pw bn : Word} {v : HtabV}
    {kind : Nat → NodeKind} {rep : KeyRep} (hok : HtabOK s.memory t v kind rep)
    (ht : s.locals "t" = some (.word t)) (hkp : s.locals "key" = some (.word keyp))
    (hv : s.locals "value" = some (.word val)) (hd : s.locals "d" = some (.word d))
    (hnodes : s.locals "nodes" = some (.word v.nodes)) (hn : s.locals "n" = some (.word nw))
    (hpl : s.locals "p" = some (.word pw))
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (ht8 : t.toNat % 8 = 0)
    (hk64 : keyp.toNat + v.kl.toNat < 2 ^ 64)
    (hkT : keyp.toNat + v.kl.toNat ≤ t.toNat ∨ t.toNat + 88 ≤ keyp.toNat)
    (hkB : keyp.toNat + v.kl.toNat ≤ v.keys.toNat ∨
      v.order.toNat + (v.nc.toNat + 1) * 8 ≤ keyp.toNat)
    (hkP : keyp.toNat + v.kl.toNat ≤ pv.toNat ∨ 2952790016 ≤ keyp.toNat)
    (hL : LiveN v kind L.toNat) (hLk : kind L.toNat = .leaf)
    (hpa : PathAgree s.memory v rep (srcBit s.memory keyp) L.toNat)
    (hdlt : d.toNat < (v.kl * 8#64).toNat)
    (hLd : rep L.toNat d = !srcBit s.memory keyp d)
    (hLlt : ∀ j : Word, j.toNat < d.toNat → rep L.toNat j = srcBit s.memory keyp j)
    (hW : WalkFacts s.memory v kind L.toNat d nw pw)
    (hbn : Rd s.memory (nodeField v nw.toNat 24) bn) (hdle : d.toNat ≤ bn.toNat) :
    WPs E s LINK_TAIL (SetPost s.memory t pv v s.ffi) := by
  have hwf := hok.wf
  have hk := hok.keys
  have hlay := hwf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  have hnxl := hwf.next_le
  obtain ⟨hlive, hanc, hpar, hpb⟩ := hW
  set κ := srcBit s.memory keyp with hκ
  have h8 : (8#64 : Word).toNat = 8 := by decide
  have hkl8 : (v.kl * 8#64).toNat = v.kl.toNat * 8 := by
    rw [BitVec.toNat_mul, h8]
    exact Nat.mod_eq_of_lt hok.kl8
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hL24 : Rd s.memory (nodeField v L.toNat 24) (v.kl * 8#64) := by
    obtain ⟨_, _, _, -, -, -, hb, -⟩ := hwf.leaf_ok _ hL.1 hL.2.1 hLk
    exact hb
  have hdbn : d.toNat < bn.toNat := by
    by_cases hne : nw.toNat = L.toNat
    · rw [hne] at hbn
      rw [Rd.inj hbn hL24]
      exact hdlt
    · have h1 := hpa nw.toNat hanc hne bn hbn
      by_contra hge
      have e : bn = d := BitVec.eq_of_toNat_eq (by omega)
      rw [e, hLd] at h1
      cases hc : κ d <;> simp [hc] at h1
  have hrepn : ∀ j : Word, j.toNat < bn.toNat → rep nw.toNat j = rep L.toNat j :=
    fun j hj => (anc_rep hwf hk hanc hL bn hbn j hj).symm
  have hnd' : rep nw.toNat d = !κ d := (hrepn d hdbn).trans hLd
  have hnlt : ∀ j : Word, j.toNat < d.toNat → rep nw.toNat j = κ j :=
    fun j hj => (hrepn j (by omega)).trans (hLlt j hj)
  obtain ⟨lp, hlpF⟩ : ∃ lp : Word, pw ≠ 0 →
      LiveN v kind pw.toNat ∧ Rd s.memory (nodeField v pw.toNat 8) lp := by
    by_cases hp0 : pw = 0
    · exact ⟨0, fun h => absurd hp0 h⟩
    · obtain ⟨p', hp', hparok⟩ := live_parent hwf hlive
      have e : pw = p' := Rd.inj hpar hp'
      subst e
      obtain ⟨hpl', -, b, l, r, -, hl, -⟩ := parent_internal hwf hk hlive.2.1 hparok hp0
      exact ⟨l, fun _ => ⟨hpl', hl⟩⟩
  refine WPs.decCall_newleaf hE ht hkp hv hok.toDet hp hpH hend ht8 hk64 hkT hkB hkP
    (fun g1 m1 nl v1 kind1 P1 => ?_)
  obtain ⟨hok1, e1, e2, e3, e4, hnl1, hnl2, hk1, hkold1, hnext1, hwas1, hnl0, hloc1, hrd1,
    ⟨pv1, hp1, hpH1, hend1, hpp1⟩, hfr1⟩ := P1
  have hdne : d ≠ v1.kl * 8#64 := by
    rw [e1]
    intro e
    rw [e] at hdlt
    omega
  refine WPs.decCall_newinternal hE (e2 := .var .local "d") (bit := d) (by lk [ht]) (by lk [hd])
    hok1 hp1 hpH1 hend1 hdne (fun g2 m2 ni v2 kind2 P2 => ?_)
  obtain ⟨hok2, f1, f2, f3, f4, hni1, hni2, hk2, hkold2, hnext2, hwas2, hloc2, hd24, hrd2,
    ⟨pv2, hp2, hpH2, hend2, hpp2⟩, hfr2⟩ := P2
  have hnx1 := hok1.wf.next_le
  have hnx2 := hok2.wf.next_le
  have hlay2 := hok2.wf.layout
  obtain ⟨k1, k2, k3, k4⟩ := id hlay2
  have old_ne : ∀ i, LiveN v kind i →
      i ≠ nl.toNat ∧ i ≠ ni.toNat ∧ kind2 i = kind i ∧ LiveN v2 kind2 i := by
    intro i hi
    have a1 : i ≠ nl.toNat := by
      intro e
      rcases hwas1 with h | h
      · exact hi.2.2 (by rw [e]; exact h)
      · have := hi.2.1
        omega
    have c1 : kind1 i = kind i := hkold1 i hi.2.1 a1
    have a2 : i ≠ ni.toNat := by
      intro e
      rcases hwas2 with h | h
      · rw [← e, c1] at h
        exact hi.2.2 h
      · have := hi.2.1
        omega
    have c2 : kind2 i = kind i := (hkold2 i (by have := hi.2.1; omega) a2).trans c1
    exact ⟨a1, a2, c2, hi.1, by have := hi.2.1; omega, by rw [c2]; exact hi.2.2⟩
  have hnlni : nl.toNat ≠ ni.toNat := by
    intro e
    rcases hwas2 with h | h
    · rw [← e, hk1] at h
      cases h
    · omega
  have hk2nl : kind2 nl.toNat = .leaf := (hkold2 _ hnl2 hnlni).trans hk1
  have hLnl : LiveN v2 kind2 nl.toNat :=
    ⟨hnl1, by omega, by rw [hk2nl]; exact NodeKind.noConfusion⟩
  have hLni : LiveN v2 kind2 ni.toNat := ⟨hni1, hni2, by rw [hk2]; exact NodeKind.noConfusion⟩
  obtain ⟨hnnl, hnni, hk2n, hLn⟩ := old_ne _ hlive
  have R12 : ∀ (i o : Nat) (w : Word), LiveN v kind i → o < 32 → o % 8 = 0 →
      (Rd m2 (nodeField v2 i o) w ↔ Rd s.memory (nodeField v i o) w) := by
    intro i o w hi ho ho8
    obtain ⟨a1, a2, -, -⟩ := old_ne i hi
    exact (hrd2 i o w (by have := hi.2.1; omega) a2 ho ho8).trans
      (hrd1 i o w (by have := hi.2.1; omega) a1 ho ho8)
  obtain ⟨hpvle, hpv8⟩ := id hpH
  obtain ⟨hpv1le, hpv18⟩ := id hpH1
  obtain ⟨hpv2le, hpv28⟩ := id hpH2
  have hout : ∀ A : Word, (A.toNat + 8 ≤ t.toNat ∨ t.toNat + 88 ≤ A.toNat) →
      (A.toNat + 8 ≤ pv.toNat ∨ 2952790016 ≤ A.toNat) →
      (A.toNat + 8 ≤ v.keys.toNat ∨ v.order.toNat + (v.nc.toNat + 1) * 8 ≤ A.toNat) →
      m2 A = s.memory A ∧
        (A.toNat + 8 ≤ v2.keys.toNat ∨ v2.order.toNat + (v2.nc.toNat + 1) * 8 ≤ A.toNat) := by
    intro A hT hP hB
    have hB1 : A.toNat + 8 ≤ v1.keys.toNat ∨
        v1.order.toNat + (v1.nc.toNat + 1) * 8 ≤ A.toNat := by
      rcases hloc1 with ⟨a, b, c, d'⟩ | hge
      · rw [a, c, d']
        exact hB
      · omega
    have hP1 : A.toNat + 8 ≤ pv1.toNat ∨ 2952790016 ≤ A.toNat := by omega
    have hB2 : A.toNat + 8 ≤ v2.keys.toNat ∨
        v2.order.toNat + (v2.nc.toNat + 1) * 8 ≤ A.toNat := by
      rcases hloc2 with ⟨a, b, c, d'⟩ | hge
      · rw [a, c, d']
        exact hB1
      · omega
    exact ⟨(hfr2 A hT hP1 hB1).trans (hfr1 A hT hP hB), hB2⟩
  have hkA : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      ((al8 (keyp + (j >>> (3 : Nat)))).toNat + 8 ≤ t.toNat ∨
        t.toNat + 88 ≤ (al8 (keyp + (j >>> (3 : Nat)))).toNat) ∧
      ((al8 (keyp + (j >>> (3 : Nat)))).toNat + 8 ≤ pv.toNat ∨
        2952790016 ≤ (al8 (keyp + (j >>> (3 : Nat)))).toNat) ∧
      ((al8 (keyp + (j >>> (3 : Nat)))).toNat + 8 ≤ v.keys.toNat ∨
        v.order.toNat + (v.nc.toNat + 1) * 8 ≤ (al8 (keyp + (j >>> (3 : Nat)))).toNat) := by
    intro j hj
    have hat : (j >>> (3 : Nat)).toNat = j.toNat / 8 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hadd : (keyp + (j >>> (3 : Nat))).toNat = keyp.toNat + j.toNat / 8 := by
      rw [BitVec.toNat_add, hat]
      exact Nat.mod_eq_of_lt (by omega)
    have hal : (al8 (keyp + (j >>> (3 : Nat)))).toNat = (keyp.toNat + j.toNat / 8) / 8 * 8 := by
      rw [← hadd]
      exact align8_toNat _
    have := hok.keys8
    have := hok.order8
    rw [hal]
    exact ⟨by omega, by omega, by omega⟩
  obtain ⟨hkl2, hst2, hcp2, hcnt2, hkeys2, hnd2, hord2, hroot2, hnext2', hfree2, hnc2⟩ :=
    hok2.wf.hdr
  refine WPs.seq (fun a' => a' = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "nl" (.word nl)) "ni"
      (.word ni)) "nodes" (.word v2.nodes)), g2, m2, s.ffi⟩)
    (WPs.assign (old := v.nodes) (by lk [hnodes])
      (eval_load_rd hE (eval_addc hE (a := t) 40#64 (by lk [ht])) hnd2) ⟨_, _, _, _, rfl, rfl⟩) ?_
  rintro _ rfl
  have hnile : ni.toNat ≤ v2.nc.toNat := by omega
  have hnlle : nl.toNat ≤ v2.nc.toNat := by have := hLnl.2.1; omega
  have hnle : nw.toNat ≤ v2.nc.toNat := by have := hLn.2.1; omega
  have hNf2 : ∀ i o, i ≤ v2.nc.toNat → o < 32 →
      (nodeField v2 i o).toNat = v2.nodes.toNat + (i * 32 + o) :=
    fun i o hi ho => node_toNat hlay2 hi ho
  refine WPs.seq_store hE (eval_node hE hlay2 (idx := "ni") hnile (by lk []) (by lk []) 0#64
    (by decide)) (of_eval (w := pw) (by lk [hpl])) ?_
  refine WPs.seq_store hE (eval_node hE hlay2 (idx := "nl") hnlle (by lk []) (by lk []) 0#64
    (by decide)) (of_eval (w := ni) (by lk [])) ?_
  refine WPs.seq_store hE (eval_node hE hlay2 (idx := "n") hnle (by lk []) (by lk [hn]) 0#64
    (by decide)) (of_eval (w := ni) (by lk [])) ?_
  have hMthree : ∀ A : Word,
      (A.toNat + 8 ≤ v2.keys.toNat ∨ v2.order.toNat + (v2.nc.toNat + 1) * 8 ≤ A.toNat) →
      (setCell (setCell (setCell m2 (nodeField v2 ni.toNat 0) pw) (nodeField v2 nl.toNat 0) ni)
      (nodeField v2 nw.toNat 0) ni) A = m2 A := by
    intro A hA
    rw [setCell_ne' _ (NE (by rw [hNf2 _ 0 hnle (by omega)]; omega)),
      setCell_ne' _ (NE (by rw [hNf2 _ 0 hnlle (by omega)]; omega)),
      setCell_ne' _ (NE (by rw [hNf2 _ 0 hnile (by omega)]; omega))]
  have hkd : KeyBitIs 8#64 (setCell (setCell (setCell m2 (nodeField v2 ni.toNat 0) pw) (nodeField v2 nl.toNat 0) ni)
      (nodeField v2 nw.toNat 0) ni) keyp d (κ d) := by
    refine KeyBitIs.of_byte (fun x hx => ?_)
    obtain ⟨c1, c2, c3⟩ := hkA d hdlt
    obtain ⟨c4, c5⟩ := hout _ c1 c2 c3
    rw [byteAt_congr ((hMthree _ c5).trans c4)] at hx
    rw [hκ]
    unfold srcBit
    rw [hx]
  obtain ⟨li, ri, hside⟩ : ∃ li ri : Word,
      (li = nl ∧ ri = nw ∧ κ d = false) ∨ (li = nw ∧ ri = nl ∧ κ d = true) := by
    cases hc : κ d
    · exact ⟨nl, nw, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨nw, nl, Or.inr ⟨rfl, rfl, rfl⟩⟩
  refine WPs.seq (fun a' => a' = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "nl" (.word nl)) "ni"
      (.word ni)) "nodes" (.word v2.nodes)), g2,
    setCell (setCell (setCell (setCell (setCell m2 (nodeField v2 ni.toNat 0) pw) (nodeField v2 nl.toNat 0) ni)
      (nodeField v2 nw.toNat 0) ni) (nodeField v2 ni.toNat 8) li) (nodeField v2 ni.toNat 16) ri, s.ffi⟩) ?_ ?_
  · refine WPs.ite (c := htBitZeroV "d") (fun x hx => htbit_cond_v hE "d" (kp := keyp) (bv := d)
      (bit := κ d) (by lk [hkp]) (by lk [hd]) (by rw [hE.bytes]; exact hkd) hx) ?_
    rcases hside with ⟨rfl, rfl, hc⟩ | ⟨rfl, rfl, hc⟩
    · rw [hc]
      split
      · rename_i h0
        simp at h0
      · refine WPs.seq_store hE (eval_node hE hlay2 (idx := "ni") hnile (by lk []) (by lk [])
          8#64 (by decide)) (of_eval (w := li) (by lk [])) ?_
        exact WPs.store hE (eval_node hE hlay2 (idx := "ni") hnile (by lk []) (by lk []) 16#64
          (by decide)) (of_eval (w := ri) (by lk [hn])) ⟨_, _, _, _, rfl, rfl⟩
    · rw [hc]
      split
      · refine WPs.seq_store hE (eval_node hE hlay2 (idx := "ni") hnile (by lk []) (by lk [])
          8#64 (by decide)) (of_eval (w := li) (by lk [hn])) ?_
        exact WPs.store hE (eval_node hE hlay2 (idx := "ni") hnile (by lk []) (by lk []) 16#64
          (by decide)) (of_eval (w := ri) (by lk [])) ⟨_, _, _, _, rfl, rfl⟩
      · rename_i h0
        simp at h0
  rintro _ rfl
  refine WPs.seq (fun a' => a' = ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "nl" (.word nl)) "ni"
      (.word ni)) "nodes" (.word v2.nodes)), g2, linkMem m2 v2 nl ni nw pw li ri
    (if pw = 0 then t + 56#64 else nodeField v2 pw.toNat (if lp = nw then 8 else 16)),
    s.ffi⟩) ?_ ?_
  · refine WPs.ite (w := evalPanCmp .equal pw 0#64)
      (eval_cmp_inv hE (of_eval (w := pw) (by lk [hpl])) (of_eval (eval_const _ _))) ?_
    by_cases hp0 : pw = 0
    · have hw : evalPanCmp .equal pw (0#64 : Word) = 1#64 := by simp [evalPanCmp, hp0]
      rw [hw, if_neg (by decide)]
      refine WPs.store hE (eval_addc hE (a := t) 56#64 (by lk [ht])) (of_eval (w := ni) (by lk []))
        ⟨_, _, _, _, rfl, ?_⟩
      rw [if_pos hp0]
      rfl
    · have hw : evalPanCmp .equal pw (0#64 : Word) = 0#64 := by
        simp [evalPanCmp]
        exact hp0
      rw [hw, if_pos (show (0#64 : Word) = 0 from rfl)]
      obtain ⟨hpL, hlpR⟩ := hlpF hp0
      obtain ⟨hpnl, hpni, -, hLp⟩ := old_ne _ hpL
      have hple : pw.toNat ≤ v2.nc.toNat := by have := hLp.2.1; omega
      have hlp2 : Rd m2 (nodeField v2 pw.toNat 8) lp :=
        (R12 _ 8 _ hpL (by omega) (by omega)).mpr hlpR
      have hlp5 : Rd (setCell (setCell (setCell (setCell (setCell m2 (nodeField v2 ni.toNat 0) pw) (nodeField v2 nl.toNat 0) ni)
      (nodeField v2 nw.toNat 0) ni) (nodeField v2 ni.toNat 8) li) (nodeField v2 ni.toNat 16)
          ri) (nodeField v2 pw.toNat 8) lp :=
        ((((hlp2.frame _ (NE (by rw [hNf2 _ 8 hple (by omega), hNf2 _ 0 hnile (by omega)]; omega))).frame _
          (NE (by rw [hNf2 _ 8 hple (by omega), hNf2 _ 0 hnlle (by omega)]; omega))).frame _
          (NE (by rw [hNf2 _ 8 hple (by omega), hNf2 _ 0 hnle (by omega)]; omega))).frame _
          (NE (by rw [hNf2 _ 8 hple (by omega), hNf2 _ 8 hnile (by omega)]; omega))).frame _
          (NE (by rw [hNf2 _ 8 hple (by omega), hNf2 _ 16 hnile (by omega)]; omega))
      refine WPs.ite (w := evalPanCmp .equal lp nw) (eval_cmp_inv hE
        (eval_load_rd hE (eval_node hE hlay2 (idx := "p") hple (by lk []) (by lk [hpl]) 8#64
          (by decide)) hlp5) (of_eval (w := nw) (by lk [hn]))) ?_
      by_cases hs : lp = nw
      · have hw2 : evalPanCmp .equal lp nw = 1#64 := by simp [evalPanCmp, hs]
        rw [hw2, if_neg (by decide)]
        refine WPs.store hE (eval_node hE hlay2 (idx := "p") hple (by lk []) (by lk [hpl]) 8#64
          (by decide)) (of_eval (w := ni) (by lk [])) ⟨_, _, _, _, rfl, ?_⟩
        rw [if_neg hp0, if_pos hs]
        rfl
      · have hw2 : evalPanCmp .equal lp nw = 0#64 := by simp [evalPanCmp, hs]
        rw [hw2, if_pos (show (0#64 : Word) = 0 from rfl)]
        refine WPs.store hE (eval_node hE hlay2 (idx := "p") hple (by lk []) (by lk [hpl]) 16#64
          (by decide)) (of_eval (w := ni) (by lk [])) ⟨_, _, _, _, rfl, ?_⟩
        rw [if_neg hp0, if_neg hs]
        rfl
  rintro _ rfl
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  refine ⟨_, g2, _, setRoot v2 (if pw = 0 then ni else v2.root), kind2,
    (fun i => if i = ni.toNat then rep nw.toNat else if i = nl.toNat then κ else rep i), rfl, ?_,
    f1.trans e1, ⟨pv2, hp2, hpH2, hend2, by omega⟩, fun A hT hP hB => ?_⟩
  · refine set_link_mem_ok (κ := κ) (lp := lp) (bn := bn) (d := d) hok2
      (fun i => ⟨fun h => h.elim Or.inr (fun h' => h'.elim Or.inl False.elim),
        fun h => h.elim (fun a => Or.inr (Or.inl a)) Or.inl⟩)
      hLnl hk2nl hLni hk2 hLn hnnl hnni hd24 (by rw [f1, e1]; exact hdlt)
      ((R12 _ 0 _ hlive (by omega) (by omega)).mpr hpar)
      ((R12 _ 24 _ hlive (by omega) (by omega)).mpr hbn) hdbn ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun i hi => if_neg hi) hside rfl
    · intro hp0
      obtain ⟨bp, h, hlt⟩ := hpb hp0
      exact ⟨bp, (R12 _ 24 _ (hlpF hp0).1 (by omega) (by omega)).mpr h, hlt⟩
    · intro hp0
      exact (R12 _ 8 _ (hlpF hp0).1 (by omega) (by omega)).mpr (hlpF hp0).2
    · intro hp0
      obtain ⟨-, a2, -, a4⟩ := old_ne _ (hlpF hp0).1
      exact ⟨a4.2.1, a2⟩
    · intro j _
      show (if nl.toNat = nl.toNat then κ else rep nl.toNat) j = κ j
      rw [if_pos rfl]
    · show (if nw.toNat = nl.toNat then κ else rep nw.toNat) d = !κ d
      rw [if_neg hnnl]
      exact hnd'
    · intro j hj
      show (if nw.toNat = nl.toNat then κ else rep nw.toNat) j = κ j
      rw [if_neg hnnl]
      exact hnlt j hj
    · show (if ni.toNat = ni.toNat then rep nw.toNat else if ni.toNat = nl.toNat then κ
        else rep ni.toNat) = (if nw.toNat = nl.toNat then κ else rep nw.toNat)
      rw [if_pos rfl, if_neg hnnl]
  · obtain ⟨c4, c5⟩ := hout A hT hP hB
    rw [← c4]
    have hXA : A ≠ (if pw = 0 then t + 56#64
        else nodeField v2 pw.toNat (if lp = nw then 8 else 16)) := by
      by_cases hp0 : pw = 0
      · rw [if_pos hp0]
        exact NE (by rw [hdr_toNat hlay2 (k := 56) (by omega)]; omega)
      · rw [if_neg hp0]
        obtain ⟨-, -, -, a4⟩ := old_ne _ (hlpF hp0).1
        have hple : pw.toNat ≤ v2.nc.toNat := by have := a4.2.1; omega
        split
        · exact NE (by rw [hNf2 _ 8 hple (by omega)]; omega)
        · exact NE (by rw [hNf2 _ 16 hple (by omega)]; omega)
    show linkMem m2 v2 nl ni nw pw li ri _ A = m2 A
    unfold linkMem
    rw [setCell_ne' _ hXA, setCell_ne' _ (NE (by rw [hNf2 _ 16 hnile (by omega)]; omega)),
      setCell_ne' _ (NE (by rw [hNf2 _ 8 hnile (by omega)]; omega)),
      setCell_ne' _ (NE (by rw [hNf2 _ 0 hnle (by omega)]; omega)),
      setCell_ne' _ (NE (by rw [hNf2 _ 0 hnlle (by omega)]; omega)),
      setCell_ne' _ (NE (by rw [hNf2 _ 0 hnile (by omega)]; omega))]

end InitECandidate.Solver.GuestBound
