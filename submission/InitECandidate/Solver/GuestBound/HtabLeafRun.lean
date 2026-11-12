import InitECandidate.Solver.GuestBound.HtabLeafInv

/-!
# Hash tables: `htab_new_leaf` as a whole

Running `htab_new_leaf(t, key, value)` on a table with detached nodes `det`
gives the table with one more detached leaf holding the key bytes.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

set_option maxHeartbeats 8000000 in
theorem htab_new_leaf_exec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_new_leaf" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t keyp val pv : Word) (v : HtabV) (kind : Nat → NodeKind)
    (rep : KeyRep) (det : Nat → Prop)
    (ht : s.locals "t" = some (.word t)) (hk : s.locals "key" = some (.word keyp))
    (hv : s.locals "value" = some (.word val)) (hok : HtabOKd s.memory t v kind rep det)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (ht8 : t.toNat % 8 = 0)
    (hk64 : keyp.toNat + v.kl.toNat < 2 ^ 64)
    (hkT : keyp.toNat + v.kl.toNat ≤ t.toNat ∨ t.toNat + 88 ≤ keyp.toNat)
    (hkB : keyp.toNat + v.kl.toNat ≤ v.keys.toNat ∨
      v.order.toNat + (v.nc.toNat + 1) * 8 ≤ keyp.toNat)
    (hkP : keyp.toNat + v.kl.toNat ≤ pv.toNat ∨ 2952790016 ≤ keyp.toNat)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' n v' kind', r = .returned l g' m' s.ffi [.word n] ∧
      HtabOKd m' t v' kind' (fun i => if i = n.toNat then srcBit s.memory keyp else rep i)
        (fun i => i = n.toNat ∨ det i) ∧
      v'.kl = v.kl ∧ v'.st = v.st ∧ v'.cnt = v.cnt + 1#64 ∧ v'.root = v.root ∧ 1 ≤ n.toNat ∧
      n.toNat < v'.next.toNat ∧ kind' n.toNat = .leaf ∧
      (∀ i, i < v.next.toNat → i ≠ n.toNat → kind' i = kind i) ∧
      v.next.toNat ≤ v'.next.toNat ∧ (kind n.toNat = .free ∨ n.toNat = v.next.toNat) ∧
      Rd m' (nodeField v' n.toNat 0) 0#64 ∧
      ((v'.keys = v.keys ∧ v'.nodes = v.nodes ∧ v'.order = v.order ∧ v'.nc = v.nc) ∨
        pv.toNat ≤ v'.keys.toNat) ∧
      (∀ (i o : Nat) (w : Word), i ≤ v.nc.toNat → i ≠ n.toNat → o < 32 → o % 8 = 0 →
        (Rd m' (nodeField v' i o) w ↔ Rd s.memory (nodeField v i o) w)) ∧
      (∃ pv' : Word, g' "heap_ptr" = some (.word pv') ∧ InHeap pv' ∧
        v'.order.toNat + (v'.nc.toNat + 1) * 8 ≤ pv'.toNat ∧ pv.toNat ≤ pv'.toNat) ∧
      ∀ A : Word, (A.toNat + 8 ≤ t.toNat ∨ t.toNat + 88 ≤ A.toNat) →
        (A.toNat + 8 ≤ pv.toNat ∨ 2952790016 ≤ A.toNat) →
        (A.toNat + 8 ≤ v.keys.toNat ∨ v.order.toNat + (v.nc.toNat + 1) * 8 ≤ A.toNat) →
        m' A = s.memory A := by
  have hbody := (fun_of_index 135 hE.functions (by guest_decl_at 135) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' n v' kind', r = .returned l g' m' s.ffi [.word n] ∧
      HtabOKd m' t v' kind' (fun i => if i = n.toNat then srcBit s.memory keyp else rep i)
        (fun i => i = n.toNat ∨ det i) ∧
      v'.kl = v.kl ∧ v'.st = v.st ∧ v'.cnt = v.cnt + 1#64 ∧ v'.root = v.root ∧ 1 ≤ n.toNat ∧
      n.toNat < v'.next.toNat ∧ kind' n.toNat = .leaf ∧
      (∀ i, i < v.next.toNat → i ≠ n.toNat → kind' i = kind i) ∧
      v.next.toNat ≤ v'.next.toNat ∧ (kind n.toNat = .free ∨ n.toNat = v.next.toNat) ∧
      Rd m' (nodeField v' n.toNat 0) 0#64 ∧
      ((v'.keys = v.keys ∧ v'.nodes = v.nodes ∧ v'.order = v.order ∧ v'.nc = v.nc) ∨
        pv.toNat ≤ v'.keys.toNat) ∧
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
  have hnn : BitVec.ofNat 64 n.toNat = n := by simp
  obtain ⟨hslot, hslot'⟩ := keyptr_bounds hlay1 hnle
  rw [hnn] at hslot
  have hks := hok1.kl_st
  have hkl8 := hok1.kl8
  obtain ⟨hpvle, hpv8⟩ := id hpH
  obtain ⟨hpvle', -⟩ := id hpH'
  rw [← e1] at hk64 hkT hkB hkP
  have P : CpPre (v1.keys + n * v1.st) keyp v1.kl := by
    refine ⟨by rw [hslot]; omega, hk64, ?_, by omega⟩
    rw [hslot]
    rcases hloc with ⟨a, b, c, d⟩ | hge
    · rw [← a, ← c, ← d] at hkB
      omega
    · omega
  refine (leaf_tail hE (s := ⟨updatePanValueMap s.locals "n" (.word n), g', m', s.ffi⟩)
    (t := t) (n := n) (keyp := keyp) (val := val) (v := v1)
    (by lk [ht]) (by lk []) (by lk [hk]) (by lk [hv]) hok1 hnle P hslot).conseq ?_
  rintro r' ⟨l, mc, rfl, c⟩
  -- the key bytes are where they were
  have hsrc : ∀ j : Word, j.toNat < (v1.kl * 8#64).toNat →
      srcBit m' keyp j = srcBit s.memory keyp j := by
    intro j hj
    have h8 : (8#64 : Word).toNat = 8 := by decide
    have hmul : (v1.kl * 8#64).toNat = v1.kl.toNat * 8 := by
      rw [BitVec.toNat_mul, h8]
      exact Nat.mod_eq_of_lt hkl8
    have hat : (j >>> (3 : Nat)).toNat = j.toNat / 8 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have hadd : (keyp + (j >>> (3 : Nat))).toNat = keyp.toNat + j.toNat / 8 := by
      rw [BitVec.toNat_add, hat]
      exact Nat.mod_eq_of_lt (by omega)
    have hal : (al8 (keyp + (j >>> (3 : Nat)))).toNat = (keyp.toNat + j.toNat / 8) / 8 * 8 := by
      rw [← hadd]
      exact align8_toNat _
    unfold srcBit
    rw [byteAt_congr (hfr _ (by rw [hal]; omega) (by rw [hal]; omega))]
  refine ⟨_, g', leafMem mc t v1 n val, n,
    ⟨v1.kl, v1.st, v1.cp, v1.nc, v1.cnt + 1#64, v1.keys, v1.nodes, v1.order, v1.root, v1.next,
      v1.free⟩, (fun i => if i = n.toNat then NodeKind.leaf else kind1 i),
    rfl, ?_, e1, e2, by show v1.cnt + 1#64 = _; rw [e3], e4,
    hn1, hn2, if_pos rfl, fun i hi hin => (if_neg hin).trans (hkold i hi hin), hnext, hwas,
    leafMem_n0 hlay1 hnle hok1.wf.cnt_le, hloc,
    fun i o w hi hin ho ho8 => ?_, ⟨pv', hp', hpH', hend', hpp⟩, fun A hT hP hB => ?_⟩
  · exact leaf_ok hok1 hn1 hn2 hkf hfl c hslot (if_pos rfl) (fun i hin => if_neg hin)
      (fun j hj => by
        show (if n.toNat = n.toNat then srcBit s.memory keyp else rep n.toNat) j = _
        rw [if_pos rfl]
        exact (hsrc j hj).symm) (fun i hin => if_neg hin) (fun i => Iff.rfl)
  · refine Iff.trans ?_ (hrd hok1 i o w hi ho ho8)
    show Rd (leafMem mc t v1 n val) (nodeField v1 i o) w ↔ _
    unfold Rd
    rw [leafMem_node hlay1 hnle hok1.wf.cnt_le hks c hslot (i := i) (by
      rcases hloc with ⟨a, b, c', d⟩ | hge
      · rw [d]; exact hi
      · exact Nat.le_trans hi hncle) hin ho]
  · rw [leafMem_frame hlay1 hnle hok1.wf.cnt_le hks c hslot A hT (by
      rcases hloc with ⟨a, b, c', d⟩ | hge
      · rw [a, c', d]
        exact hB
      · omega)]
    exact hfr A hT hP

end InitECandidate.Solver.GuestBound
