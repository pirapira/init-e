import InitECandidate.Solver.GuestBound.TrieWalkDefs
import InitECandidate.Solver.GuestBound.TrieCalls
import InitECandidate.Solver.GuestBound.TrieCollapse
import InitECandidate.Solver.GuestBound.TrieLoopBranch
import InitECandidate.Solver.GuestBound.Fq12InvInner

/-!
# The hashing walk: looking for a child to descend into

The first half of an iteration of `_node_rlp_fill`: for an extension whose
cursor is 0, the cursor becomes 1 and the child is examined; for a branch the
slots from the cursor on are examined until one needs its RLP.  Only the
cursor cell of the top frame changes.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A child worth descending into: registered, not a stub, deeper, cache empty. -/
def GoodCh (R : Reg) (m : Word → Option (PanValue Word)) (ℓ : Nat) (c : Word) : Prop :=
  ∃ kc ℓc, R.Kd c kc ∧ kc ≠ 0#64 ∧ R.Lv c ℓc ∧ ℓ < ℓc ∧ Rd m (c + 8#64) 0#64

theorem nodeSize_ge (k : Word) : 32 ≤ nodeSize k := by
  unfold nodeSize
  split <;> [omega; (split <;> [omega; (split <;> omega)])]

theorem good_of_needs {R : Reg} {g : VarName → Option (PanValue Word)}
    {m m1 : Word → Option (PanValue Word)} {c : Word} {ℓ ℓc : Nat} (hW : WorldTJ R g m)
    (hc : c = 0#64 ∨ ∃ k, R.Kd c k) (hl : c ≠ 0#64 → R.Lv c ℓc) (hlt : ℓ < ℓc)
    (hm : ∀ x : Word, x.toNat < 2952790016 → m1 x = m x)
    (h : c ≠ 0#64 ∧ ∃ kk, Rd m1 c kk ∧ kk ≠ 0#64 ∧ Rd m1 (c + 8#64) 0#64) :
    GoodCh R m ℓ c := by
  obtain ⟨hc0, kk, r0, hkk, r8⟩ := h
  rcases hc with rfl | ⟨k, hk⟩
  · exact absurd rfl hc0
  · obtain ⟨-, hRd, hlo, hhi, -⟩ := hW.kd hk
    have := nodeSize_ge k
    have e8 : (c + 8#64).toNat = c.toNat + 8 := by bv_omega
    unfold Rd at r0 r8
    rw [hm c (by omega)] at r0
    rw [hm _ (by omega)] at r8
    have : k = kk := Rd.inj hRd r0
    subst this
    exact ⟨k, ℓc, hk, hkk, hl hc0, hlt, r8⟩

theorem ofNat_add1 (j : Nat) : (BitVec.ofNat 64 j : Word) + 1#64 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

local notation "SCAN" => ((Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 2)))
                                (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))])) (Exp.const (BitVec.ofNat 64 0)))
                                  (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 1)))
                                    (Prog.seq
                                    (Prog.assign VarKind.local "child" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 48))])))
                                    (Prog.call (some ((some (VarKind.local, "found")), none)) "_node_needs_rlp" [(Exp.var VarKind.local "child")])))
                                  Prog.skip)
                                (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 3)))
                                  (Prog.dec "i" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]))
                                    (Prog.seq
                                      (Prog.while (Exp.op BinOp.and [(Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.less (Exp.var VarKind.local "i") (Exp.const (BitVec.ofNat 64 16)))), (Exp.cmp Cmp.notEqual (Exp.const (BitVec.ofNat 64 0)) (Exp.cmp Cmp.equal (Exp.var VarKind.local "found") (Exp.const (BitVec.ofNat 64 0))))])
                                        (Prog.seq
                                          (Prog.assign VarKind.local "child" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 8))])])))
                                          (Prog.seq
                                          (Prog.assign VarKind.local "i" (Exp.op BinOp.add [(Exp.var VarKind.local "i"), (Exp.const (BitVec.ofNat 64 1))]))
                                          (Prog.call (some ((some (VarKind.local, "found")), none)) "_node_needs_rlp" [(Exp.var VarKind.local "child")]))))
                                      (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.var VarKind.local "i"))))
                                  Prog.skip)) : Prog Word)

/-- The state after the scan. -/
def ScanQ (R : Reg) (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (ffi : FfiState σ) (topv nd : Word) (ℓ : Nat) (r : Result σ) : Prop :=
  ∃ L m1 c f cur', r = .normal L g m1 ffi ∧ L "top" = some (.word topv) ∧
    L "nd" = some (.word nd) ∧ L "child" = some (.word c) ∧ L "found" = some (.word f) ∧
    (∀ x, x ≠ topv + 16#64 → m1 x = m x) ∧ Rd m1 (topv + 16#64) cur' ∧ cur'.toNat ≤ 16 ∧
    (f ≠ 0#64 → GoodCh R m ℓ c)

/-- Invariant of the slot loop. -/
def BrI (R : Reg) (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (ffi : FfiState σ) (topv nd : Word) (ℓ : Nat) (a : St σ) : Prop :=
  a.globals = g ∧ a.memory = m ∧ a.ffi = ffi ∧ a.locals "top" = some (.word topv) ∧
    a.locals "nd" = some (.word nd) ∧ ∃ (jj : Nat) (c f : Word),
      a.locals "i" = some (.word (BitVec.ofNat 64 jj)) ∧ jj ≤ 16 ∧
      a.locals "child" = some (.word c) ∧ a.locals "found" = some (.word f) ∧
      (f ≠ 0#64 → GoodCh R m ℓ c)

set_option maxHeartbeats 8000000 in
theorem wk_scan (hE : GuestEnv E) (I : WalkIface E) {R : Reg} {topv nd k cur : Word} {ℓ : Nat}
    (hW : WorldTJ R s.globals s.memory) (hK : R.Kd nd k) (hLv : R.Lv nd ℓ)
    (qtop : s.locals "top" = some (.word topv)) (qnd : s.locals "nd" = some (.word nd))
    (qk : s.locals "k" = some (.word k)) (qch : s.locals "child" = some (.word 0#64))
    (qf : s.locals "found" = some (.word 0#64))
    (rc : Rd s.memory (topv + 16#64) cur) (hcur : cur.toNat ≤ 16)
    (htop : 2952790016 ≤ topv.toNat) (htl : topv.toNat + 48 < 2 ^ 64) :
    WPs E s SCAN (ScanQ R s.globals s.memory s.ffi topv nd ℓ) := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have e16 : (topv + 16#64).toNat = topv.toNat + 16 := by bv_omega
  obtain ⟨-, hRdk, hlo, hhi, -⟩ := hW.kd hK
  have hsz := nodeSize_ge k
  have stay : ScanQ R s.globals s.memory s.ffi topv nd ℓ
      (.normal s.locals s.globals s.memory s.ffi) :=
    ⟨s.locals, s.memory, 0#64, 0#64, cur, rfl, qtop, qnd, qch, qf, fun _ _ => rfl, rc,
      hcur, fun h => absurd rfl h⟩
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  simp only [evalF_local, qk, eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · refine WPs.ite_both (fun w2 hw2 => ?_)
    obtain ⟨x, y, hx, hy, hwv2⟩ := cmp_word_inv hE hw2
    simp only [evalF_local, qk, eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · exact WPs.skip stay
    · rename_i h3
      have hk3 : k = 3#64 := by
        by_contra hne
        apply h3
        rw [hwv2]
        simp [evalPanCmp, hne]
      subst hk3
      -- a branch: scan the slots from the cursor on
      refine WPs.dec (w := cur) (eval_load_rd hE (eval_addc hE 16#64 qtop) rc) ?_
      refine WPs.seqG (BrI R s.globals s.memory s.ffi topv nd ℓ)
        (WPs.loopG (I := BrI R s.globals s.memory s.ffi topv nd ℓ)
          ⟨rfl, rfl, rfl, by lk [qtop], by lk [qnd], cur.toNat, 0#64, 0#64,
            by rw [ofNat_toNat']; lk [], hcur, by lk [qch], by lk [qf],
            fun h => absurd rfl h⟩ ?_ (fun a k hI _ => hI)) ?_
      · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, qt, qn, jj, c, f, qi, hj, qc, qf', -⟩
          ⟨w, cc, hcond, hw⟩
        dsimp only at hg hm hf qt qn qi qc qf'
        subst hg hm hf
        obtain ⟨va, vb, w', ha, hb, hop, hxw⟩ := eval_op2_inv hE.word (cond_of_eval hcond)
        have h1 := eval_cmp_inv hE (op := .notEqual) (of_eval (eval_const _ 0#64))
          (eval_cmp_inv hE (op := .less) (of_eval (w := BitVec.ofNat 64 jj) (by lk [qi]))
            (of_eval (eval_const _ 16#64))) _ ha
        simp only [PanValue.word.injEq] at h1 hxw
        have hjlt : jj < 16 := by
          by_contra hge
          rw [less16 jj hj, if_neg hge] at h1
          subst h1 hxw
          simp [wordOp, evalPanCmp] at hop
          subst hop
          have hz : ∀ x : Word, (AndOp.and (0#64) x : Word) = 0#64 := fun x => by
            first
              | exact BitVec.zero_and
              | simp [AndOp.and]
          rw [hz] at hw
          exact absurd hw (by decide)
        have ej : (BitVec.ofNat 64 jj : Word).toNat = jj := by
          rw [BitVec.toNat_ofNat]
          omega
        obtain ⟨c', rs, hch⟩ := hW.slot hK (i := jj) hjlt
        refine WPs.seq_asg (old := c) (w := c') qc
          (eval_load_rd hE (eval_slot_idx hE qn qi (by omega)) (by rw [ej]; exact rs)) ?_
        refine WPs.seq_asg (old := BitVec.ofNat 64 jj) (w := BitVec.ofNat 64 (jj + 1))
          (by lk [qi]) (of_eval (by ev [qi, ofNat_add1])) ?_
        refine WPs.callA_ret (fun v g m ffi hret => ?_)
        obtain ⟨rfl, rfl, rfl, f', rfl, hf'⟩ := I.needs _ _ c' _ _ _ _ hret (by lk [])
        exact ⟨rfl, rfl, rfl, by lk [qt], by lk [qn], jj + 1, c', f', by lk [], by omega,
          by lk [], by lk [], fun h0 => good_of_needs hW hch
            (fun hc0 => hW.slot_lv hK (hW.cv_br hK hLv) hjlt rs hc0) (by omega)
            (fun _ _ => rfl) (hf' h0)⟩
      · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, qt, qn, jj, c, f, qi, hj, qc, qf', hgood⟩
        dsimp only at hg hm hf qt qn qi qc qf'
        subst hg hm hf
        have ej : (BitVec.ofNat 64 jj : Word).toNat = jj := by
          rw [BitVec.toNat_ofNat]
          omega
        refine WPs.store hE (addr := topv + 16#64) (w := BitVec.ofNat 64 jj)
          (eval_addc hE 16#64 qt) (of_eval (by lk [qi])) ?_
        simp only [restorePanValueFfiLocal]
        exact ⟨_, _, c, f, BitVec.ofNat 64 jj, rfl,
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qt],
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qn],
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qc],
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qf'],
          fun x hx => setCell_ne _ hx, Rd.here _ _ _, by rw [ej]; exact hj, hgood⟩
  · rename_i h2
    have hk2 : k = 2#64 := by
      by_contra hne
      apply h2
      rw [hwv]
      simp [evalPanCmp, hne]
    subst hk2
    obtain ⟨nl, cx, r40, hn1, r48, hch⟩ := hW.ext hK
    have hcv := hW.cv_ext hK hLv r40
    have hsz2 : nodeSize 2#64 = 56 := by decide
    have e48 : (nd + 48#64).toNat = nd.toNat + 48 := by bv_omega
    refine WPs.ite_both (fun w3 hw3 => ?_)
    obtain ⟨x, y, hx, hy, hwv3⟩ := cmp_word_inv hE hw3
    have hxc := eval_load_rd hE (eval_addc hE 16#64 qtop) rc _ hx
    simp only [eval_const, Option.some.injEq, PanValue.word.injEq] at hy hxc
    subst hy hxc
    split
    · exact WPs.skip stay
    · refine WPs.seq_store hE (addr := topv + 16#64) (w := 1#64) (eval_addc hE 16#64 qtop)
        (of_eval (eval_const _ _)) ?_
      refine WPs.seq_asg (old := 0#64) (w := cx) qch
        (eval_load_rd hE (eval_addc hE 48#64 qnd) (r48.frame _ (NE (by omega)))) ?_
      refine WPs.callA_ret (fun v g m ffi hret => ?_)
      obtain ⟨rfl, rfl, rfl, f, rfl, hf⟩ := I.needs _ _ cx _ _ _ _ hret (by lk [])
      exact ⟨_, _, cx, f, 1#64, rfl, by lk [qtop], by lk [qnd], by lk [], by lk [],
        fun x hx => setCell_ne _ hx, Rd.here _ _ _, by decide,
        fun h0 => good_of_needs hW hch (fun hc0 => hW.ext_lv hK hcv r48 hc0) (by omega)
          (fun x hx => setCell_ne _ (NE (by omega))) (hf h0)⟩

end InitECandidate.Solver.GuestBound
