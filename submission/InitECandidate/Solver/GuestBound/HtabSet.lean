import InitECandidate.Solver.GuestBound.HtabSetTail

/-!
# Hash tables: `htab_set`

`htab_set(t, key, value)` on a well-formed table leaves a well-formed table:
the first key becomes the root, a stored key gets its value overwritten, and a
new key is linked in at the first bit where it differs from its neighbours.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem SetPost.restore {m : Word → Option (PanValue Word)} {t pv : Word} {v : HtabV}
    {f : FfiState σ} {r : Result σ} {x : VarName} {old : Option (PanValue Word)}
    (h : SetPost m t pv v f r) : SetPost m t pv v f (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g', m', v', kind', rep', rfl, rest⟩ := h
  exact ⟨_, g', m', v', kind', rep', rfl, rest⟩

/-- From the first differing bit of the new key and a stored key: the stored
key's bits agree with the new key before that bit and differ at it. -/
theorem fd_key_bits {m : Word → Option (PanValue Word)} {keyp slot : Word} {n : Nat} {d : Word}
    {ρ : Word → Bool} (hfd : FdPost m keyp slot n d)
    (hneq : ¬ ∀ k, k < n → byteAt m (off slot k) = byteAt m (off keyp k))
    (hρ : ∀ j : Word, j.toNat < n * 8 → KeyBitIs 8#64 m slot j (ρ j)) :
    d.toNat < n * 8 ∧ ρ d = !srcBit m keyp d ∧
      ∀ j : Word, j.toNat < d.toNat → ρ j = srcBit m keyp j := by
  rcases hfd with ⟨-, hall⟩ | ⟨i, j, xa, xb, hi, hj, hdv, hpre, hxa, hxb, hbit, hbits⟩
  · exfalso
    apply hneq
    intro k hk
    obtain ⟨x, h1, h2⟩ := hall k hk
    rw [h1, h2]
  have hjw : ∀ (jw A : Word), A + (jw >>> (3 : Nat)) = off A (jw.toNat / 8) := by
    intro jw A
    unfold off
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by have := jw.isLt; omega)).symm
  have hρb : ∀ (jw x : Word), jw.toNat < n * 8 → byteAt m (off slot (jw.toNat / 8)) = some x →
      ρ jw = bitOf x (jw.toNat % 8) :=
    fun jw x h hx => (hρ jw h).bit_eq (by rw [hjw]; exact hx)
  have hκb : ∀ (jw x : Word), byteAt m (off keyp (jw.toNat / 8)) = some x →
      srcBit m keyp jw = bitOf x (jw.toNat % 8) := by
    intro jw x hx
    unfold srcBit
    rw [hjw, hx]
  have hd8 : d.toNat / 8 = i := by omega
  have hd8m : d.toNat % 8 = j := by omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [hρb d xb (by omega) (by rw [hd8]; exact hxb), hκb d xa (by rw [hd8]; exact hxa), hd8m]
    cases h1 : bitOf xa j <;> cases h2 : bitOf xb j <;> simp_all
  · intro jw hjlt
    by_cases hlt : jw.toNat / 8 < i
    · obtain ⟨x, h1, h2⟩ := hpre _ hlt
      rw [hρb jw x (by omega) h2, hκb jw x h1]
    · have e : jw.toNat / 8 = i := by omega
      rw [hρb jw xb (by omega) (by rw [e]; exact hxb), hκb jw xa (by rw [e]; exact hxa)]
      exact (hbits _ (by omega)).symm

set_option maxHeartbeats 32000000 in
theorem htab_set_exec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_set" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t keyp val pv : Word) (v : HtabV) (kind : Nat → NodeKind)
    (rep : KeyRep)
    (ht : s.locals "t" = some (.word t)) (hkp : s.locals "key" = some (.word keyp))
    (hv : s.locals "value" = some (.word val)) (hok : HtabOK s.memory t v kind rep)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (ht8 : t.toNat % 8 = 0)
    (hk64 : keyp.toNat + v.kl.toNat < 2 ^ 64)
    (hkT : keyp.toNat + v.kl.toNat ≤ t.toNat ∨ t.toNat + 88 ≤ keyp.toNat)
    (hkB : keyp.toNat + v.kl.toNat ≤ v.keys.toNat ∨
      v.order.toNat + (v.nc.toNat + 1) * 8 ≤ keyp.toNat)
    (hkP : keyp.toNat + v.kl.toNat ≤ pv.toNat ∨ 2952790016 ≤ keyp.toNat)
    (h : Runs E s body r) : Stopped r ∨ SetPost s.memory t pv v s.ffi r := by
  have hbody := (fun_of_index 138 hE.functions (by guest_decl_at 138) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (SetPost s.memory t pv v s.ffi)) r h
  have hwf := hok.wf
  have hk := hok.keys
  have hlay := hwf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  have hnxl := hwf.next_le
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  have ofn : ∀ x : Word, BitVec.ofNat 64 x.toNat = x := fun x => by simp
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have h8 : (8#64 : Word).toNat = 8 := by decide
  have hkl8 : (v.kl * 8#64).toNat = v.kl.toNat * 8 := by
    rw [BitVec.toNat_mul, h8]
    exact Nat.mod_eq_of_lt hok.kl8
  have hkey : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs 8#64 s.memory keyp j (srcBit s.memory keyp j) :=
    fun j _ => KeyBitIs.of_byte (fun x hx => by unfold srcBit; rw [hx])
  refine WPs.dec (eval_load_rd hE (eval_addc hE 0#64 ht) hkl) ?_
  refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 8#64 (by lk [ht])) hst) ?_
  refine WPs.decCall_findpath hE (t := t) (kp := keyp) (v := v) (kind := kind) (rep := rep)
    (κ := srcBit s.memory keyp) (by lk [ht]) (by lk [hkp]) hwf hk hkey (fun nv hres => ?_)
  refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 32#64 (by lk [ht])) hkeys) ?_
  rcases hres with ⟨rfl, hroot0⟩ | ⟨hL, hLk, hpa⟩
  · -- the first key
    refine WPs.seqG (fun _ => False) ?_ (fun _ hF => hF.elim)
    refine WPs.ite (w := 1#64) (fun y hy => by
      rw [eval_cmp_inv hE (of_eval (w := (0 : Word)) (by lk [])) (of_eval (eval_const _ _)) y hy]
      simp [evalPanCmp]) ?_
    split
    · rename_i h10
      exact absurd h10 (by decide)
    refine WPs.decCall_newleaf hE (t := t) (keyp := keyp) (val := val) (pv := pv) (v := v)
      (kind := kind) (rep := rep) (by lk [ht]) (by lk [hkp]) (by lk [hv]) hok.toDet hp hpH hend
      ht8 hk64 hkT hkB hkP (fun g1 m1 nl v1 kind1 P1 => ?_)
    obtain ⟨hok1, e1, e2, e3, e4, hnl1, hnl2, hk1, hkold1, hnext1, hwas1, hnl0, hloc1, hrd1,
      ⟨pv1, hp1, hpH1, hend1, hpp1⟩, hfr1⟩ := P1
    have hlay1 := hok1.wf.layout
    refine WPs.seq_store hE (eval_addc hE (a := t) 56#64 (by lk [ht]))
      (of_eval (w := nl) (by lk [])) ?_
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    refine ⟨_, g1, _, setRoot v1 nl, kind1, _, rfl,
      set_root_ok hok1 (fun i => ⟨fun h => h.elim id False.elim, Or.inl⟩) (e4.trans hroot0)
        ⟨hnl1, hnl2, by rw [hk1]; exact NodeKind.noConfusion⟩ hk1 hnl0, e1, hloc1,
      ⟨pv1, hp1, hpH1, hend1, hpp1⟩, fun A hT hP hB => ?_⟩
    show setCell m1 (t + 56#64) nl A = s.memory A
    rw [setCell_ne' _ (NE (by rw [hdr_toNat hlay1 (k := 56) (by omega)]; omega))]
    exact hfr1 A hT hP hB
  have hnv1 := hL.1
  have hnv0 : ¬ nv = 0#64 := fun e => by rw [e] at hnv1; exact absurd hnv1 (by decide)
  have hnvle : nv.toNat ≤ v.nc.toNat := by have := hL.2.1; omega
  refine WPs.guard0 (fun y hy => by
    rw [eval_cmp_inv hE (of_eval (w := nv) (by lk [])) (of_eval (eval_const _ _)) y hy]
    simp [evalPanCmp, hnv0]) ?_
  obtain ⟨hslot, hslot'⟩ := keyptr_bounds hlay hnvle
  rw [ofn] at hslot
  have hks := hok.kl_st
  have hkl8' := hok.kl8
  refine WPs.decCall_memeq_any hE (A := v.keys + nv * v.st) (B := keyp) (nW := v.kl)
    (by ev [evalPanOp]) (by lk [hkp]) (by lk []) (by rw [hslot]; omega) hk64 (by omega)
    (fun e he1 => ?_)
  by_cases he0 : e = 0#64
  · -- a new key
    refine WPs.guard0 (fun y hy => by
      rw [eval_cmp_inv hE (of_eval (w := e) (by lk [])) (of_eval (eval_const _ _)) y hy]
      simp [evalPanCmp, he0]) ?_
    have hneq : ¬ ∀ k, k < v.kl.toNat →
        byteAt s.memory (off (v.keys + nv * v.st) k) = byteAt s.memory (off keyp k) := by
      intro hb
      have := he1 hb
      rw [he0] at this
      exact absurd this (by decide)
    refine WPs.decCall_firstdiff hE (A := keyp) (B := v.keys + nv * v.st) (nW := v.kl)
      (by lk [hkp]) (by ev [evalPanOp]) (by lk []) ⟨hk64, by rw [hslot]; omega, hkl8'⟩
      (fun d hfd => ?_)
    obtain ⟨hdlt, hLd, hLlt⟩ := fd_key_bits (ρ := rep nv.toNat) hfd hneq (fun j hj => by
      have := hok.leaf_key nv.toNat hL.1 hL.2.1 hLk j (by rw [hkl8]; exact hj)
      rw [ofn] at this
      exact this)
    refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 40#64 (by lk [ht])) hnd) ?_
    refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
    refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 56#64 (by lk [ht])) hroot) ?_
    refine WPs.seq (fun a => a.globals = s.globals ∧ a.memory = s.memory ∧ a.ffi = s.ffi ∧
        a.locals "t" = some (.word t) ∧ a.locals "key" = some (.word keyp) ∧
        a.locals "value" = some (.word val) ∧ a.locals "d" = some (.word d) ∧
        a.locals "nodes" = some (.word v.nodes) ∧ ∃ nw pw bn, a.locals "n" = some (.word nw) ∧
        a.locals "p" = some (.word pw) ∧ WalkFacts s.memory v kind nv.toNat d nw pw ∧
        Rd s.memory (nodeField v nw.toNat 24) bn ∧ d.toNat ≤ bn.toNat) ?_ ?_
    · refine (set_walk hE (s := ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "klen" (.word v.kl)) "stride" (.word v.st)) "leaf" (.word nv)) "keys" (.word v.keys)) "eq" (.word e)) "d" (.word d)) "nodes" (.word v.nodes)) "p" (.word 0#64)) "n" (.word v.root)), s.globals, s.memory, s.ffi⟩) (t := t) (keyp := keyp) (d := d) (L := nv) (κ := srcBit s.memory keyp)
        hok hL hLk hpa (by rw [hkl8]; exact hdlt) hkey ?w1 ?w2 ?w3 ?w4 ?w5).conseq ?_
      case w1 => lk []
      case w2 => lk [hkp]
      case w3 => lk []
      case w4 => lk []
      case w5 => lk []
      rintro r ⟨l, nw, pw, bn, rfl, hkeep, hn, hpp, hW, hbn, hle⟩
      refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, nw, pw, bn, hn, hpp, hW, hbn, hle⟩
      · exact (hkeep "t" (by simp [walkKeep])).trans (by lk [ht])
      · exact (hkeep "key" (by simp [walkKeep])).trans (by lk [hkp])
      · exact (hkeep "value" (by simp [walkKeep])).trans (by lk [hv])
      · exact (hkeep "d" (by simp [walkKeep])).trans (by lk [])
      · exact (hkeep "nodes" (by simp [walkKeep])).trans (by lk [])
    · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, hta, hka, hva, hda, hna, nw, pw, bn, hn, hpp, hW, hbn,
        hle⟩
      simp only at hg hm hf hta hka hva hda hna hn hpp
      subst hg hm hf
      exact (set_link_tail hE (s := ⟨la, s.globals, s.memory, s.ffi⟩) hok hta hka hva hda hna hn hpp hp hpH hend ht8 hk64 hkT hkB hkP hL hLk
        hpa (by rw [hkl8]; exact hdlt) hLd hLlt hW hbn hle).conseq
        (fun r h => h.restore.restore.restore.restore.restore.restore.restore.restore.restore)
  · -- a stored key: overwrite the value
    refine WPs.seqG (fun _ => False) ?_ (fun _ hF => hF.elim)
    refine WPs.ite (w := 1#64) (fun y hy => by
      rw [eval_cmp_inv hE (of_eval (w := e) (by lk [])) (of_eval (eval_const _ _)) y hy]
      simp [evalPanCmp, he0]) ?_
    split
    · rename_i h10
      exact absurd h10 (by decide)
    refine WPs.seq_store_inv hE (addr := nodeField v nv.toNat 8) (w := val) ?ha ?hv ?_
    case ha =>
      exact eval_node_ld hE (s := ⟨(updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "klen" (.word v.kl)) "stride" (.word v.st)) "leaf" (.word nv)) "keys" (.word v.keys)) "eq" (.word e)), s.globals, s.memory, s.ffi⟩) hlay (idx := "leaf") hnvle (by lk [ht]) hnd (by lk []) 8#64
        (by decide)
    case hv =>
      dsimp only
      exact of_eval (by lk [hv])
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    refine ⟨_, s.globals, _, v, kind, rep, rfl, set_value_ok hok hL hLk, rfl,
      Or.inl ⟨rfl, rfl, rfl, rfl⟩, ⟨pv, hp, hpH, hend, Nat.le_refl _⟩, fun A hT hP hB => ?_⟩
    show setCell s.memory (nodeField v nv.toNat 8) val A = s.memory A
    rw [setCell_ne' _ (NE (by rw [node_toNat hlay hnvle (o := 8) (by omega)]; omega))]

/-- `htab_set(e1, e2, e3);` at a call site that discards the result. -/
theorem WPs.call_set (hE : GuestEnv E) {s : St σ} {Q : Result σ → Prop} {e1 e2 e3 : Exp Word}
    {t keyp val pv : Word} {v : HtabV} {kind : Nat → NodeKind} {rep : KeyRep}
    (h1 : ∀ y, E.eval s e1 = some y → y = .word t)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word keyp)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word val) (hok : HtabOK s.memory t v kind rep)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (ht8 : t.toNat % 8 = 0)
    (hk64 : keyp.toNat + v.kl.toNat < 2 ^ 64)
    (hkT : keyp.toNat + v.kl.toNat ≤ t.toNat ∨ t.toNat + 88 ≤ keyp.toNat)
    (hkB : keyp.toNat + v.kl.toNat ≤ v.keys.toNat ∨
      v.order.toNat + (v.nc.toNat + 1) * 8 ≤ keyp.toNat)
    (hkP : keyp.toNat + v.kl.toNat ≤ pv.toNat ∨ 2952790016 ≤ keyp.toNat)
    (h : ∀ l g' m', SetPost s.memory t pv v s.ffi (.returned l g' m' s.ffi [.word 0#64]) →
      Q (.normal s.locals g' m' s.ffi)) :
    WPs E s (.call (some (none, none)) "htab_set" [e1, e2, e3]) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 138 hE.functions (by guest_decl_at 138) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil] at hvalues
  cases he1 : E.eval s e1 with
  | none => rw [he1] at hvalues; simp at hvalues
  | some y1 =>
    have := h1 y1 he1
    subst this
    cases he2 : E.eval s e2 with
    | none => rw [he1, he2] at hvalues; simp at hvalues
    | some y2 =>
      have := h2 y2 he2
      subst this
      cases he3 : E.eval s e3 with
      | none => rw [he1, he2, he3] at hvalues; simp at hvalues
      | some y3 =>
        have := h3 y3 he3
        subst this
        rw [he1, he2, he3] at hvalues
        simp only [Option.map_some, Option.some.injEq] at hvalues
        subst hvalues
        rw [hparams] at hbind
        simp [bindPanValueParameters] at hbind
        have hpost := htab_set_exec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩
          rb t keyp val pv v kind rep
          (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
          (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
          (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
          hok hp hpH hend ht8 hk64 hkT hkB hkP hcallee
        rcases hpost with hst | hsp
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
        · obtain ⟨l, g', m', v', kind', rep', rfl, rest⟩ := hsp
          simp only [CallOutcome] at hout
          rcases hout with herr | ⟨l', g'', hassign, rfl⟩
          · exact Or.inl (Stopped.of_error herr)
          · simp only [assignPanValueCallResult, Option.some.injEq, Prod.mk.injEq] at hassign
            obtain ⟨rfl, rfl⟩ := hassign
            exact Or.inr (h l g' m' ⟨l, g', m', v', kind', rep', rfl, rest⟩)

end InitECandidate.Solver.GuestBound
