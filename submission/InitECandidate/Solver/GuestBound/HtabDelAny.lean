import InitECandidate.Solver.GuestBound.HtabSetCalls

/-!
# Hash tables: `htab_del` for an arbitrary key

Either the key is not stored and nothing changes, or its leaf is removed as
described by `DelRel`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

set_option maxHeartbeats 8000000 in
theorem htab_del_any_exec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_del" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t kp : Word) (v : HtabV) (kind : Nat → NodeKind) (rep : KeyRep)
    (ht : s.locals "t" = some (.word t)) (hkey : s.locals "key" = some (.word kp))
    (hok : HtabOK s.memory t v kind rep) (hk64 : kp.toNat + v.kl.toNat < 2 ^ 64)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', (r = .returned l s.globals m' s.ffi [.word 0#64] ∧ m' = s.memory) ∨
      ∃ Lw : Word, LiveN v kind Lw.toNat ∧ kind Lw.toNat = .leaf ∧
        r = .returned l s.globals m' s.ffi [.word 1#64] ∧ DelRel s.memory t v Lw m' := by
  have hbody := (fun_of_index 139 hE.functions (by guest_decl_at 139) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', (r = .returned l s.globals m' s.ffi [.word 0#64] ∧ m' = s.memory) ∨
      ∃ Lw : Word, LiveN v kind Lw.toNat ∧ kind Lw.toNat = .leaf ∧
        r = .returned l s.globals m' s.ffi [.word 1#64] ∧ DelRel s.memory t v Lw m')) r h
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨hkl, hst, -, hcnt, hkeys, hnd, hord, hroot, -, hfree, -⟩ := hwf.hdr
  have hkeyb : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs 8#64 s.memory kp j (srcBit s.memory kp j) :=
    fun j _ => KeyBitIs.of_byte (fun x hx => by unfold srcBit; rw [hx])
  refine WPs.dec (eval_load_rd hE (eval_addc hE 0#64 ht) hkl) ?_
  refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 8#64 (by lk [ht])) hst) ?_
  refine WPs.decCall_findpath hE (t := t) (kp := kp) (v := v) (kind := kind) (rep := rep)
    (κ := srcBit s.memory kp) (by lk [ht]) (by lk [hkey]) hwf hok.keys hkeyb (fun Lw hres => ?_)
  rcases hres with ⟨rfl, -⟩ | ⟨hL, hLk, -⟩
  · refine WPs.seqG (fun _ => False) ?_ (fun _ hF => hF.elim)
    refine WPs.ite (w := 1#64) (fun y hy => by
      rw [eval_cmp_inv hE (of_eval (w := (0 : Word)) (by lk [])) (of_eval (eval_const _ _)) y hy]
      simp [evalPanCmp]) ?_
    split
    · rename_i h10
      exact absurd h10 (by decide)
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    exact ⟨_, _, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨hL1, hL2, hL3⟩ := hL
  obtain ⟨p, value, pos, hp, -, hpos, -, hpar, hposlt, hordL⟩ := hwf.leaf_ok _ hL1 hL2 hLk
  have hnl := hwf.next_le
  have hcl := hwf.cnt_le
  have h1 : (1#64 : Word).toNat = 1 := by decide
  have hc1 : (v.cnt - 1#64).toNat = v.cnt.toNat - 1 := by
    rw [BitVec.toNat_sub, h1]
    have := v.cnt.isLt
    omega
  obtain ⟨moved, hmoved, hm1, hm2, hmk, hm16⟩ := hwf.order_ok (v.cnt.toNat - 1) (by omega)
  have hofc : BitVec.ofNat 64 (v.cnt.toNat - 1) = v.cnt - 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [hc1, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := v.cnt.isLt; omega)
  rw [hofc] at hm16
  have hLnc : Lw.toNat ≤ v.nc.toNat := by omega
  have hpnc : pos.toNat ≤ v.nc.toNat := by omega
  have hcnc : (v.cnt - 1#64).toNat ≤ v.nc.toNat := by omega
  have hmnc : moved.toNat ≤ v.nc.toNat := by omega
  have hL0 : Lw ≠ 0#64 := by
    intro h0
    rw [h0] at hL1
    exact absurd hL1 (by decide)
  -- facts for the unlink, on the original memory
  have hsp0 : ∃ g lc rc gl : Word, v.root ≠ Lw →
      p.toNat ≤ v.nc.toNat ∧ kind p.toNat = .internal ∧
      Rd s.memory (nodeField v p.toNat 0) g ∧ g.toNat ≤ v.nc.toNat ∧
      Rd s.memory (nodeField v p.toNat 8) lc ∧ Rd s.memory (nodeField v p.toNat 16) rc ∧
      (if lc = Lw then rc else lc).toNat ≤ v.nc.toNat ∧
      (g ≠ 0#64 → Rd s.memory (nodeField v g.toNat 8) gl) := by
    by_cases hr : v.root = Lw
    · exact ⟨0, 0, 0, 0, fun h => absurd hr h⟩
    rcases hpar with ⟨-, hroot'⟩ | ⟨hp1, hp2, hpk, -⟩
    · exact absurd (BitVec.eq_of_toNat_eq hroot') hr
    obtain ⟨g, lc, rc, b, hg, hlc, hrc, -, -, hgpar, hcl', hcr', -⟩ :=
      hwf.internal_ok _ hp1 hp2 hpk
    have hgnc : g.toNat ≤ v.nc.toNat := by
      rcases hgpar with ⟨h0, -⟩ | ⟨-, hg2, -⟩
      · rw [h0]
        show (0 : Nat) ≤ _
        omega
      · omega
    have hsnc : (if lc = Lw then rc else lc).toNat ≤ v.nc.toNat := by
      have := hcl'.2.1
      have := hcr'.2.1
      split <;> omega
    by_cases hg0 : g = 0#64
    · exact ⟨g, lc, rc, 0, fun _ => ⟨by omega, hpk, hg, hgnc, hlc, hrc, hsnc,
        fun h => absurd hg0 h⟩⟩
    · rcases hgpar with ⟨h0, -⟩ | ⟨hg1, hg2, hgk, -⟩
      · exact absurd h0 hg0
      obtain ⟨_, gl, _, _, -, hgl, -⟩ := hwf.internal_ok _ hg1 hg2 hgk
      exact ⟨g, lc, rc, gl, fun _ => ⟨by omega, hpk, hg, hgnc, hlc, hrc, hsnc, fun _ => hgl⟩⟩
  obtain ⟨g, lc, rc, gl, hsp⟩ := hsp0
  -- reads that survive the order fix and the count store
  have fA : ∀ a w, Rd s.memory a w → a ≠ orderSlot v pos.toNat →
      a ≠ nodeField v moved.toNat 16 → a ≠ t + 24#64 → Rd (delA s.memory t v pos moved) a w :=
    fun a w h h1 h2 h3 => ((h.frame _ h1).frame _ h2).frame _ h3
  have hdr_ord : ∀ k, k < 88 → t + BitVec.ofNat 64 k ≠ orderSlot v pos.toNat :=
    fun k hk h => (hdr_ne_ord hlay hpnc hk).mp h
  have hdr_node : ∀ k, k < 88 → t + BitVec.ofNat 64 k ≠ nodeField v moved.toNat 16 :=
    fun k hk h => (hdr_ne_node hlay hmnc (by omega) hk).mp h
  have hdr_hdr : ∀ k, k < 88 → k ≠ 24 → t + BitVec.ofNat 64 k ≠ t + 24#64 :=
    fun k hk hne h => hne ((hdr_eq_hdr hlay hk (by omega)).mp h)
  have node_fr : ∀ (i o : Nat) w, i ≤ v.nc.toNat → o < 32 → o % 8 = 0 →
      (i ≠ moved.toNat ∨ o ≠ 16) → Rd s.memory (nodeField v i o) w →
      Rd (delA s.memory t v pos moved) (nodeField v i o) w := by
    intro i o w hi ho ho8 hne hrd
    refine fA _ _ hrd (fun h => (node_ne_ord hlay hi ho hpnc).mp h) ?_
      (fun h => (node_ne_hdr hlay hi ho (by omega)).mp h)
    intro h
    have := (node_eq_node hlay hi hmnc ho (by omega) ho8 (by omega)).mp h
    omega
  have hrootA := fA _ _ hroot (hdr_ord 56 (by omega)) (hdr_node 56 (by omega))
    (hdr_hdr 56 (by omega) (by omega))
  have hfreeA := fA _ _ hfree (hdr_ord 72 (by omega)) (hdr_node 72 (by omega))
    (hdr_hdr 72 (by omega) (by omega))
  have hspA : v.root ≠ Lw → Rd (delA s.memory t v pos moved) (nodeField v Lw.toNat 0) p ∧
      p.toNat ≤ v.nc.toNat ∧
      Rd (delA s.memory t v pos moved) (nodeField v p.toNat 0) g ∧ g.toNat ≤ v.nc.toNat ∧
      Rd (delA s.memory t v pos moved) (nodeField v p.toNat 8) lc ∧
      Rd (delA s.memory t v pos moved) (nodeField v p.toNat 16) rc ∧
      (if lc = Lw then rc else lc).toNat ≤ v.nc.toNat ∧
      (g ≠ 0#64 → Rd (delA s.memory t v pos moved) (nodeField v g.toNat 8) gl) := by
    intro hr
    obtain ⟨hpn, hpk, hg, hgnc, hlc, hrc, hsnc, hgl⟩ := hsp hr
    have hpm : p.toNat ≠ moved.toNat := by
      intro heq
      rw [heq, hmk] at hpk
      cases hpk
    exact ⟨node_fr _ 0 _ hLnc (by omega) (by omega) (Or.inr (by omega)) hp, hpn,
      node_fr _ 0 _ hpn (by omega) (by omega) (Or.inr (by omega)) hg, hgnc,
      node_fr _ 8 _ hpn (by omega) (by omega) (Or.inr (by omega)) hlc,
      node_fr _ 16 _ hpn (by omega) (by omega) (Or.inl hpm) hrc, hsnc,
      fun h0 => node_fr _ 8 _ hgnc (by omega) (by omega) (Or.inr (by omega)) (hgl h0)⟩
  have hslotA : (v.keys + Lw * v.st).toNat + v.kl.toNat < 2 ^ 64 := by
    obtain ⟨e1, e2⟩ := keyptr_bounds hlay hLnc
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at e1
    have := hok.kl_st
    obtain ⟨-, -, -, l4⟩ := id hlay
    obtain ⟨-, -, l3, -⟩ := id hlay
    rw [e1]
    omega
  refine WPs.guard0 (guard_eq0 hE (of_eval (w := Lw) (by lk [])) hL0) ?_
  refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 32#64 (by lk [ht])) hkeys) ?_
  refine WPs.decCall_memeq_any hE (A := v.keys + Lw * v.st) (B := kp) (nW := v.kl)
    (by ev [evalPanOp]) (by lk [hkey]) (by lk []) hslotA hk64 (by have := hok.kl8; omega)
    (fun e _ => ?_)
  by_cases he0 : e = 0#64
  · refine WPs.seqG (fun _ => False) ?_ (fun _ hF => hF.elim)
    refine WPs.ite (w := 1#64) (fun y hy => by
      rw [eval_cmp_inv hE (of_eval (w := e) (by lk [])) (of_eval (eval_const _ _)) y hy]
      simp [evalPanCmp, he0]) ?_
    split
    · rename_i h10
      exact absurd h10 (by decide)
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    exact ⟨_, _, Or.inl ⟨rfl, rfl⟩⟩
  refine WPs.guard0 (guard_eq0 hE (of_eval (w := e) (by lk [])) he0) ?_
  refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 40#64 (by lk [ht])) hnd) ?_
  refine WPs.dec (eval_load_rd hE (eval_node hE hlay (idx := "leaf") hLnc (by lk []) (by lk [])
    16#64 (by decide)) hpos) ?_
  refine WPs.dec (w := v.cnt - 1#64) (eval_sub_inv hE (eval_load_rd hE
    (eval_addc hE (a := t) 24#64 (by lk [ht])) hcnt)) ?_
  refine WPs.seq_mem (fun m' => m' = setCell (setCell s.memory (orderSlot v pos.toNat) moved)
      (nodeField v moved.toNat 16) pos)
    (WPs.conseq (del_phaseA hE hlay (cnt1 := v.cnt - 1#64) (by lk [ht]) (by lk []) (by lk [])
      (by lk []) hpnc hcnc hmnc hord (by rw [hc1]; exact hmoved) (fun hpc => hpc ▸ hm16))
      (fun r hr => ⟨_, hr, rfl⟩)) ?_
  intro m' hm'
  subst hm'
  refine WPs.seq_store hE (eval_addc hE (a := t) 24#64 (by lk [ht]))
    (of_eval (w := v.cnt - 1#64) (by lk [])) ?_
  refine WPs.seq_mem (fun m' => m' = delB (delA s.memory t v pos moved) t v Lw v.root p g lc rc
      gl v.free)
    (WPs.conseq (del_phaseB hE hlay (by lk [ht]) (by lk []) (by lk []) hrootA hLnc hfreeA hspA)
      (fun r hr => ⟨_, hr, rfl⟩)) ?_
  intro m' hm'
  subst hm'
  have hfrB : Rd (delB (delA s.memory t v pos moved) t v Lw v.root p g lc rc gl v.free)
      (t + 72#64) (if v.root = Lw then v.free else p) := by
    unfold delB
    split
    · exact hfreeA.frame _ (fun h => by
        have := (hdr_eq_hdr hlay (k := 72) (k' := 56) (by omega) (by omega)).mp h
        omega)
    · exact Rd.here _ _ _
  refine WPs.seq_store hE (eval_node hE hlay (idx := "leaf") hLnc (by lk []) (by lk []) 0#64
    (by decide)) (eval_load_rd hE (eval_addc hE (a := t) 72#64 (by lk [ht])) hfrB) ?_
  refine WPs.seq_store hE (eval_addc hE (a := t) 72#64 (by lk [ht]))
    (of_eval (w := Lw) (by lk [])) ?_
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  refine ⟨_, _, Or.inr ⟨Lw, ⟨hL1, hL2, hL3⟩, hLk, rfl, pos, moved, p, g, lc, rc, gl, hpos, hmoved,
    ?_, rfl⟩⟩
  intro hr
  obtain ⟨-, -, hg, -, hlc, hrc, -, hgl⟩ := hsp hr
  exact ⟨hp, hg, hlc, hrc, hgl⟩

end InitECandidate.Solver.GuestBound
