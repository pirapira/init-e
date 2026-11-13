import InitECandidate.Solver.GuestBound.TrieDelBranch

/-!
# The descent loop of the delete walk

`dl_body`: one iteration keeps the descent invariant `DlI` and decreases the
measure `insMu` (the remaining key length while `go` is set).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

local notation "DGUARD" => ((Exp.cmp Cmp.notEqual (Exp.var VarKind.local "go") (Exp.const (BitVec.ofNat 64 0))) : Exp Word)

local notation "DBODY" => ((Prog.seq (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 0))) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "node") (Exp.const (BitVec.ofNat 64 0))) (Prog.assign VarKind.local "res" (Exp.const (BitVec.ofNat 64 0))) (Prog.dec "k" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 0))])) (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 0))) (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 2))]) Prog.skip) (Prog.seq (Prog.call (some (none, none)) "node_invalidate" [(Exp.var VarKind.local "node")]) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 1))) (Prog.seq (Prog.assign VarKind.local "res" (Exp.var VarKind.local "node")) (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 40))])) (Exp.op BinOp.sub [(Exp.var VarKind.local "klen"), (Exp.var VarKind.local "level")])) (Prog.decCall "eq" Shape.one "memeq" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 32))])), (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")]), (Exp.op BinOp.sub [(Exp.var VarKind.local "klen"), (Exp.var VarKind.local "level")])] (Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "eq") (Exp.const (BitVec.ofNat 64 0))) (Prog.assign VarKind.local "res" (Exp.const (BitVec.ofNat 64 0))) Prog.skip)) Prog.skip)) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 2))) (Prog.dec "seg" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 32))])) (Prog.dec "sl" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 40))])) (Prog.decCall "pl" Shape.one "common_prefix_length" [(Exp.var VarKind.local "seg"), (Exp.var VarKind.local "sl"), (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")]), (Exp.op BinOp.sub [(Exp.var VarKind.local "klen"), (Exp.var VarKind.local "level")])] (Prog.ite (Exp.cmp Cmp.lower (Exp.var VarKind.local "pl") (Exp.var VarKind.local "sl")) (Prog.assign VarKind.local "res" (Exp.var VarKind.local "node")) (Prog.decCall "fr" Shape.one "scratch_alloc" [(Exp.const (BitVec.ofNat 64 40))] (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr"), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "top")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "node")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 2))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr"), (Exp.const (BitVec.ofNat 64 24))]) (Exp.var VarKind.local "seg")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr"), (Exp.const (BitVec.ofNat 64 32))]) (Exp.var VarKind.local "sl")) (Prog.seq (Prog.assign VarKind.local "top" (Exp.var VarKind.local "fr")) (Prog.seq (Prog.assign VarKind.local "node" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 48))]))) (Prog.seq (Prog.assign VarKind.local "level" (Exp.op BinOp.add [(Exp.var VarKind.local "level"), (Exp.var VarKind.local "sl")])) (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 1)))))))))))))))) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "level") (Exp.var VarKind.local "klen")) (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 168))])) (Exp.const (BitVec.ofNat 64 0))) (Prog.assign VarKind.local "res" (Exp.var VarKind.local "node")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 160))]) (Exp.const (BitVec.ofNat 64 0))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 168))]) (Exp.const (BitVec.ofNat 64 0))) (Prog.call (some ((some (VarKind.local, "res")), none)) "_collapse_branch" [(Exp.var VarKind.local "node")])))) (Prog.dec "idx" Shape.one (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")])) (Prog.decCall "fr2" Shape.one "scratch_alloc" [(Exp.const (BitVec.ofNat 64 40))] (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr2"), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "top")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr2"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "node")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr2"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 3))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr2"), (Exp.const (BitVec.ofNat 64 32))]) (Exp.var VarKind.local "idx")) (Prog.seq (Prog.assign VarKind.local "top" (Exp.var VarKind.local "fr2")) (Prog.seq (Prog.assign VarKind.local "node" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "idx"), (Exp.const (BitVec.ofNat 64 8))])]))) (Prog.seq (Prog.assign VarKind.local "level" (Exp.op BinOp.add [(Exp.var VarKind.local "level"), (Exp.const (BitVec.ofNat 64 1))])) (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 1)))))))))))))))))))) : Prog Word)

/-- Invariant of the descent loop. -/
def DlI (Rg : Reg) (G : VarName → Option (PanValue Word)) (M : Word → Option (PanValue Word))
    (F : FfiState σ) (fv lim : Word) (ℓ0 : Nat) (key klen : Word) (a : St σ) : Prop :=
  a.ffi = F ∧ ∃ gw lv, DlS Rg G M fv lim ℓ0 key klen a.locals a.globals a.memory gw lv

/-- Leaving the scope of `k`. -/
theorem DlS.exit_k {Rg : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {fv lim : Word} {ℓ0 : Nat} {key klen : Word}
    {l g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)} {gw lv : Word}
    (old : Option (PanValue Word)) (h : DlS Rg G M fv lim ℓ0 key klen l g m gw lv) :
    DlS Rg G M fv lim ℓ0 key klen (restorePanValueLocal l "k" old) g m gw lv := by
  obtain ⟨R, topv, resv, nd, sp, ℓ, hle, hW, hg, hsp, hfv, hfs, hsl, hm, a1, a2, a3, a4, a5, a6,
    a7, rest⟩ := h
  exact ⟨R, topv, resv, nd, sp, ℓ, hle, hW, hg, hsp, hfv, hfs, hsl, hm,
    by simp (config := { decide := true }) [restorePanValueLocal, a1],
    by simp (config := { decide := true }) [restorePanValueLocal, a2],
    by simp (config := { decide := true }) [restorePanValueLocal, a3],
    by simp (config := { decide := true }) [restorePanValueLocal, a4],
    by simp (config := { decide := true }) [restorePanValueLocal, a5],
    by simp (config := { decide := true }) [restorePanValueLocal, a6],
    by simp (config := { decide := true }) [restorePanValueLocal, a7], rest⟩

set_option maxHeartbeats 32000000 in
/-- One iteration of the descent. -/
theorem dl_body (hE : GuestEnv E) {Rg : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {F : FfiState σ} {fv lim : Word} {ℓ0 : Nat}
    {key klen : Word} (hF : 2952790016 ≤ fv.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    {a : St σ} (hI : DlI Rg G M F fv lim ℓ0 key klen a) (hct : CondTrue E a DGUARD) :
    WPs E a DBODY (fun r => ∃ l g m f, r = .normal l g m f ∧
      DlI Rg G M F fv lim ℓ0 key klen ⟨l, g, m, f⟩ ∧ insMu ⟨l, g, m, f⟩ < insMu a) := by
  obtain ⟨la, ga, ma, fa⟩ := a
  obtain ⟨hf, gw, lv, R, topv, resv, nd, sp, ℓ, hle, hW, hg, hsp, hfv, hfs, hsl, hm, k1, k2, k3,
    k4, k5, k6, k7, hst, hgo, hres⟩ := hI
  obtain ⟨w, cc, hcond, hw⟩ := hct
  dsimp only at hf hW hg hsp hfv hm k1 k2 k3 k4 k5 k6 k7 hst
  subst hf
  have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := gw) (by lk [k7]))
    (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hcond)
  simp only [PanValue.word.injEq] at hcv
  have hgw : gw ≠ 0#64 := by
    rintro rfl
    rw [hcv] at hw
    simp [evalPanCmp] at hw
  obtain ⟨hℓ, hlv, hnd, hLn⟩ := hgo hgw
  subst hℓ
  have hkeyR : klen ≠ 0#64 → ∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat := by
    intro h0
    obtain ⟨lo, hi, hI', hr⟩ := hkey h0
    exact ⟨lo, hi, hle.Im _ _ hI', hr⟩
  have hPost : ∀ l' g' m' gw' lv', DlS Rg G M fv lim ℓ0 key klen l' g' m' gw' lv' →
      (gw' = 0#64 ∨ lv.toNat < lv'.toNat) →
      ∃ l g m f, (.normal l' g' m' fa : Result σ) = .normal l g m f ∧
        DlI Rg G M fa fv lim ℓ0 key klen ⟨l, g, m, f⟩ ∧
        insMu ⟨l, g, m, f⟩ < insMu ⟨la, ga, ma, fa⟩ := by
    intro l' g' m' gw' lv' hS hd
    refine ⟨l', g', m', fa, rfl, ⟨rfl, gw', lv', hS⟩, ?_⟩
    obtain ⟨R', topv', resv', nd', sp', ℓ', -, -, -, -, -, -, -, -, -, b2, b3, -, -, -, b7, -,
      hgo', -⟩ := hS
    refine insMu_lt (gw := gw) (lv := lv) (kl := klen) (gw' := gw') (lv' := lv') k7 k3 k2 b7 b3
      b2 hgw hlv ?_
    by_cases h0 : gw' = 0#64
    · exact Or.inl h0
    · rcases hd with hd | hd
      · exact absurd hd h0
      · exact Or.inr ⟨hd, (hgo' h0).2.1⟩
  refine WPs.seq_asg (old := gw) (w := 0#64) k7 (of_eval (eval_const _ _)) ?_
  have c : DlCtx Rg R G M fv lim sp ℓ0 key klen lv nd topv resv
      (⟨updatePanValueMap la "go" (.word 0#64), ga, ma, fa⟩ : St σ) :=
    ⟨⟨by lk [k1], by lk [k2], by lk [k3], by lk [k4], by lk [k5], by lk [k6], by lk []⟩, hle, hW,
      hg, hsp, hfv, hfs, hsl, hm, hst, hlv, hF⟩
  refine WPs.ite_both (fun w2 hw2 => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw2
  rw [eval_const] at hy
  rw [evalF_local] at hx
  simp (config := { decide := true }) [update_lookup, k4] at hx hy
  subst hx hy
  split
  · rename_i h0
    have hne : nd ≠ 0#64 := by
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    obtain ⟨k, hKd⟩ : ∃ k, R.Kd nd k := by
      rcases hnd with h | h
      · exact absurd h hne
      · exact h
    obtain ⟨hNd, hRd, hlo, htop, h8⟩ := hW.kd hKd
    obtain ⟨hk3, -, -, -⟩ := hW.node_kind hNd hRd
    refine WPs.dec (w := k) (eval_load_rd hE (eval_addc hE (a := nd) 0#64 (by lk [k4]))
      (by rw [BitVec.add_zero]; exact hRd)) ?_
    refine WPs.seqG (fun a' => a' = ⟨updatePanValueMap (updatePanValueMap la "go" (.word 0#64))
        "k" (.word k), ga, ma, fa⟩ ∧ k ≠ 0#64) (WPs.ite_both (fun w3 hw3 => ?_)) ?_
    · obtain ⟨x, y, hx, hy, hwv3⟩ := cmp_word_inv hE hw3
      rw [eval_const] at hy
      rw [evalF_local] at hx
      simp (config := { decide := true }) [update_lookup] at hx hy
      subst hx hy
      split
      · rename_i h2
        refine WPs.skip ⟨rfl, ?_⟩
        rintro rfl
        rw [h2] at hwv3
        simp [evalPanCmp] at hwv3
      · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
    rintro _ ⟨rfl, hk0⟩
    refine WPs.seqG (fun a' => ∃ m1, a' = ⟨updatePanValueMap (updatePanValueMap la "go"
        (.word 0#64)) "k" (.word k), ga, m1, fa⟩ ∧ WorldTJ R ga m1 ∧
        ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
          m1 addr = ma addr) (WPs.call_ret (fun vs g m ffi hret => ?_)) ?_
    · obtain ⟨rfl, rfl, hW1, hm1⟩ := node_invalidate_ret hE hret (a := nd) (k := k)
        (of_eval (by lk [k4])) hW hNd hRd hk0
      exact ⟨m, rfl, hW1, hm1⟩
    rintro _ ⟨m1, rfl, hW1, hm1⟩
    have c1 : DlCtx Rg R G M fv lim sp ℓ0 key klen lv nd topv resv
        (⟨updatePanValueMap (updatePanValueMap la "go" (.word 0#64)) "k" (.word k), ga, m1,
          fa⟩ : St σ) :=
      c.heap ⟨by lk [k1], by lk [k2], by lk [k3], by lk [k4], by lk [k5], by lk [k6], by lk []⟩
        rfl hW1 hm1
    have hQk : ∀ l' g' m' gw' lv', DlS Rg G M fv lim ℓ0 key klen l' g' m' gw' lv' →
        (gw' = 0#64 ∨ lv.toNat < lv'.toNat) →
        ∃ l g m f, restorePanValueFfiLocal "k"
            ((updatePanValueMap la "go" (.word 0#64)) "k") (.normal l' g' m' fa : Result σ) =
            .normal l g m f ∧ DlI Rg G M fa fv lim ℓ0 key klen ⟨l, g, m, f⟩ ∧
          insMu ⟨l, g, m, f⟩ < insMu ⟨la, ga, ma, fa⟩ := by
      intro l' g' m' gw' lv' hS hd
      simp only [restorePanValueFfiLocal]
      exact hPost _ _ _ gw' lv' (hS.exit_k _) hd
    have hk1ne : ∀ c : Word, k ≠ c → k.toNat ≠ c.toNat :=
      fun c hc he => hc (BitVec.eq_of_toNat_eq he)
    refine WPs.ite_both (fun w4 hw4 => ?_)
    obtain ⟨x, y, hx, hy, hwv4⟩ := cmp_word_inv hE hw4
    rw [eval_const] at hy
    rw [evalF_local] at hx
    simp (config := { decide := true }) [update_lookup] at hx hy
    subst hx hy
    split
    · rename_i h3
      have hk1 : k ≠ 1#64 := by
        rintro rfl
        rw [h3] at hwv4
        simp [evalPanCmp] at hwv4
      refine WPs.ite_both (fun w5 hw5 => ?_)
      obtain ⟨x, y, hx, hy, hwv5⟩ := cmp_word_inv hE hw5
      rw [eval_const] at hy
      rw [evalF_local] at hx
      simp (config := { decide := true }) [update_lookup] at hx hy
      subst hx hy
      split
      · rename_i h4
        have hk2 : k ≠ 2#64 := by
          rintro rfl
          rw [h4] at hwv5
          simp [evalPanCmp] at hwv5
        have hk3' : k = 3#64 := by
          have a0 := hk1ne 0#64 hk0
          have a1 := hk1ne 1#64 hk1
          have a2 := hk1ne 2#64 hk2
          simp at a0 a1 a2
          exact BitVec.eq_of_toNat_eq (by simp; omega)
        subst hk3'
        exact dl_branch hE c1 hKd (hLn hne) hkeyR hQk
      · rename_i h4
        have hk2 : k = 2#64 := by
          by_contra hne2
          exact h4 (by rw [hwv5]; simp [evalPanCmp, hne2])
        subst hk2
        exact dl_ext hE c1 hKd (hLn hne) hQk
    · rename_i h3
      have hk1 : k = 1#64 := by
        by_contra hne1
        exact h3 (by rw [hwv4]; simp [evalPanCmp, hne1])
      subst hk1
      exact dl_leaf hE c1 hKd (hLn hne) hQk
  · refine WPs.assign (old := resv) (w := 0#64) (by lk [k6]) (of_eval (eval_const _ _)) ?_
    exact hPost _ _ _ 0#64 lv (c.stop
      (l' := updatePanValueMap (updatePanValueMap la "go" (.word 0#64)) "res" (.word 0#64))
      (res' := 0#64) (nd' := nd) (Reg.Le.refl R) hW
      (fun _ _ => rfl) (fun _ _ => rfl) (by lk [k1]) (by lk [k2]) (by lk [k3]) (by lk [k4])
      (by lk [k5]) (by lk []) (by lk []) (Or.inl rfl)) (Or.inl rfl)

theorem dl_body_cost (hE : GuestEnv E) : Costs E DBODY (10 ^ 120) := by
  have h : ∃ B, Costs E DBODY B ∧ B ≤ 10 ^ 120 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

end InitECandidate.Solver.GuestBound
