import InitECandidate.Solver.GuestBound.TrieLoop
import InitECandidate.Solver.GuestBound.Fns.L4

/-!
# Step bound of `_mpt_insert_node`

The loop is not a counter loop: it ends because the level grows on every
iteration that continues, and the level stays within the key — which holds
only under the world invariant (`InsI`). `ins_body` is the loop body with the
decrease of the measure `insMu`; `mpt_insert_node_cost` is the step bound of
the function from an invariant state.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

local notation "IGUARD" => ((Exp.cmp Cmp.notEqual (Exp.var VarKind.local "go") (Exp.const (BitVec.ofNat 64 0))) : Exp Word)

local notation "IBODY" => ((Prog.dec "r" Shape.one (Exp.const (BitVec.ofNat 64 0)) (Prog.dec "next_node" Shape.one (Exp.const (BitVec.ofNat 64 0)) (Prog.dec "next_slot" Shape.one (Exp.const (BitVec.ofNat 64 0)) (Prog.dec "next_level" Shape.one (Exp.const (BitVec.ofNat 64 0)) (Prog.seq (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 0))) (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "node") (Exp.const (BitVec.ofNat 64 0))) (Prog.call (some ((some (VarKind.local, "r")), none)) "node_new_leaf" [(Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")]), (Exp.op BinOp.sub [(Exp.var VarKind.local "klen"), (Exp.var VarKind.local "level")]), (Exp.var VarKind.local "vptr"), (Exp.var VarKind.local "vlen")]) (Prog.dec "k" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 0))])) (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 0))) (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 2))]) Prog.skip) (Prog.seq (Prog.call (some (none, none)) "node_invalidate" [(Exp.var VarKind.local "node")]) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 1))) (Prog.call (some ((some (VarKind.local, "r")), none)) "_insert_into_leaf" [(Exp.var VarKind.local "node"), (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")]), (Exp.op BinOp.sub [(Exp.var VarKind.local "klen"), (Exp.var VarKind.local "level")]), (Exp.var VarKind.local "vptr"), (Exp.var VarKind.local "vlen")]) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 2))) (Prog.dec "seg" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 32))])) (Prog.dec "sl" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 40))])) (Prog.decCall "pl" Shape.one "common_prefix_length" [(Exp.var VarKind.local "seg"), (Exp.var VarKind.local "sl"), (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")]), (Exp.op BinOp.sub [(Exp.var VarKind.local "klen"), (Exp.var VarKind.local "level")])] (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "pl") (Exp.var VarKind.local "sl")) (Prog.seq (Prog.assign VarKind.local "r" (Exp.var VarKind.local "node")) (Prog.seq (Prog.assign VarKind.local "next_node" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 48))]))) (Prog.seq (Prog.assign VarKind.local "next_slot" (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 48))])) (Prog.seq (Prog.assign VarKind.local "next_level" (Exp.op BinOp.add [(Exp.var VarKind.local "level"), (Exp.var VarKind.local "pl")])) (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 1))))))) (Prog.decCall "br" Shape.one "_split_extension" [(Exp.var VarKind.local "node"), (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")]), (Exp.op BinOp.sub [(Exp.var VarKind.local "klen"), (Exp.var VarKind.local "level")]), (Exp.var VarKind.local "vptr"), (Exp.var VarKind.local "vlen"), (Exp.var VarKind.local "pl")] (Prog.ite (Exp.cmp Cmp.lower (Exp.const (BitVec.ofNat 64 0)) (Exp.var VarKind.local "pl")) (Prog.call (some ((some (VarKind.local, "r")), none)) "node_new_ext" [(Exp.var VarKind.local "seg"), (Exp.var VarKind.local "pl"), (Exp.var VarKind.local "br")]) (Prog.assign VarKind.local "r" (Exp.var VarKind.local "br")))))))) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "level") (Exp.var VarKind.local "klen")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 160))]) (Exp.var VarKind.local "vptr")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 168))]) (Exp.var VarKind.local "vlen")) (Prog.assign VarKind.local "r" (Exp.var VarKind.local "node")))) (Prog.dec "idx" Shape.one (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")])) (Prog.seq (Prog.assign VarKind.local "r" (Exp.var VarKind.local "node")) (Prog.seq (Prog.assign VarKind.local "next_node" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "idx"), (Exp.const (BitVec.ofNat 64 8))])]))) (Prog.seq (Prog.assign VarKind.local "next_slot" (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "idx"), (Exp.const (BitVec.ofNat 64 8))])])) (Prog.seq (Prog.assign VarKind.local "next_level" (Exp.op BinOp.add [(Exp.var VarKind.local "level"), (Exp.const (BitVec.ofNat 64 1))])) (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 1))))))))))))))) (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "slot") (Exp.const (BitVec.ofNat 64 0))) (Prog.assign VarKind.local "result" (Exp.var VarKind.local "r")) (Prog.store (Exp.var VarKind.local "slot") (Exp.var VarKind.local "r"))) (Prog.seq (Prog.assign VarKind.local "node" (Exp.var VarKind.local "next_node")) (Prog.seq (Prog.assign VarKind.local "slot" (Exp.var VarKind.local "next_slot")) (Prog.assign VarKind.local "level" (Exp.var VarKind.local "next_level"))))))))))) : Prog Word)

/-- The measure: zero once `go` is cleared, else the remaining key length plus one. -/
def insMu (a : St σ) : Nat :=
  match a.locals "go", a.locals "level", a.locals "klen" with
  | some (.word gw), some (.word lv), some (.word kl) =>
    if gw = 0#64 then 0 else kl.toNat - lv.toNat + 1
  | _, _, _ => 0

theorem insMu_lt {a b : St σ} {gw lv kl gw' lv' : Word}
    (a1 : a.locals "go" = some (.word gw)) (a2 : a.locals "level" = some (.word lv))
    (a3 : a.locals "klen" = some (.word kl)) (b1 : b.locals "go" = some (.word gw'))
    (b2 : b.locals "level" = some (.word lv')) (b3 : b.locals "klen" = some (.word kl))
    (hgw : gw ≠ 0#64) (hlv : lv.toNat ≤ kl.toNat)
    (h : gw' = 0#64 ∨ (lv.toNat < lv'.toNat ∧ lv'.toNat ≤ kl.toNat)) : insMu b < insMu a := by
  unfold insMu
  rw [a1, a2, a3, b1, b2, b3]
  simp only [if_neg hgw]
  rcases h with rfl | ⟨h1, h2⟩
  · simp
  · split <;> omega

theorem insMu_le (a : St σ) : insMu a ≤ 2 ^ 64 := by
  unfold insMu
  split
  · rename_i gw lv kl _ _ _
    have := kl.isLt
    split <;> omega
  · omega

set_option maxHeartbeats 32000000 in
/-- One iteration: the invariant is kept and the measure decreases. -/
theorem ins_body (hE : GuestEnv E) {Rg : Reg} {s : St σ} {key klen vptr vlen level : Word}
    (hblk : klen ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    {a : St σ} (hI : InsI Rg s key klen vptr vlen level a) (hct : CondTrue E a IGUARD) :
    WPs E a IBODY (fun r => ∃ l g m f, r = .normal l g m f ∧
      InsI Rg s key klen vptr vlen level ⟨l, g, m, f⟩ ∧ insMu ⟨l, g, m, f⟩ < insMu a) := by
  obtain ⟨la, ga, ma, fa⟩ := a
  obtain ⟨R, lv, nd, sl, res, gw, hle, hW', hf, hg, hm, k1, k2, k3, k4, k5,
    k6, k7, k8, k9, hres, hI⟩ := hI
  obtain ⟨w, cc, hcond, hw⟩ := hct
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  dsimp only at hW' hf hg hm k1 k2 k3 k4 k5 k6 k7 k8 k9
  subst hf
  have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := gw) (by lk [k9]))
    (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hcond)
  simp only [PanValue.word.injEq] at hcv
  have hgw : gw ≠ 0#64 := by
    rintro rfl
    rw [hcv] at hw
    simp [evalPanCmp] at hw
  obtain ⟨hlv', hnd', hLn', hsl'⟩ := hI hgw
  have hkeyR : klen ≠ 0#64 → ∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat := by
    intro h0
    obtain ⟨lo, hi, hI', hr⟩ := hblk h0
    exact ⟨lo, hi, by rw [hle.Im]; exact hI', hr⟩
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.seq_asg (old := gw) (w := 0#64) (by lk [k9]) (of_eval (eval_const _ _)) ?_
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have hLoc : InsLoc L key klen vptr vlen lv nd sl res :=
    ⟨by rw [hLL]; lk [k1], by rw [hLL]; lk [k2], by rw [hLL]; lk [k3], by rw [hLL]; lk [k4],
      by rw [hLL]; lk [k5], by rw [hLL]; lk [k6], by rw [hLL]; lk [k7], by rw [hLL]; lk [k8],
      by rw [hLL]; lk [], by rw [hLL]; lk [], by rw [hLL]; lk [], by rw [hLL]; lk [],
      by rw [hLL]; lk []⟩
  clear hLL
  refine WPs.seqG (fun a' => a'.ffi = s.ffi ∧
      InsMid R ga ma key klen vptr vlen lv sl res a'.locals a'.globals a'.memory)
    (ins_step hE (s := ⟨L, ga, ma, s.ffi⟩) hLoc hW' hnd' hLn' hlv' hkeyR
      (fun l' g' m' hmid => ⟨rfl, hmid⟩)) ?_
  rintro ⟨l2, g2, m2, f2⟩ ⟨hf2, R', rv, kk, gw', nn, ns, nlv, nd', hle', hW2, hg2, hm2, j1,
    j2, j3, j4, j5, j6, j7, j8, j9, j10, j11, j12, j13, hKr, hkk, hLr, hgo'⟩
  dsimp only at hf2 hW2 hg2 hm2 j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13
  subst hf2
  -- the result goes to the pending slot, or becomes the result
  refine WPs.seqG (fun a2 => a2.ffi = s.ffi ∧ a2.globals = g2 ∧ WorldTJ R' g2 a2.memory ∧
      (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        a2.memory addr = m2 addr) ∧
      (∃ res', a2.locals "result" = some (.word res') ∧
        ∃ k, R'.Kd res' k ∧ k ≠ 0#64 ∧ R'.Lv res' level.toNat) ∧
      ∀ x, x ≠ "result" → a2.locals x = l2 x) (WPs.ite_both (fun w2 hw2 => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw2
    rw [eval_const] at hy
    rw [evalF_local] at hx
    dsimp only at hx
    rw [j7] at hx
    simp only [Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i h0
      have hsl0 : sl ≠ 0#64 := by
        rintro rfl
        rw [h0] at hwv
        simp [evalPanCmp] at hwv
      have hSlot : SlotOf R' sl lv.toNat := (hsl'.resolve_left hsl0).mono hle'
      have hres' : ∃ k, R'.Kd res k ∧ k ≠ 0#64 ∧ R'.Lv res level.toNat := by
        rcases hres with ⟨⟨k, hk, hk0, hkl⟩, -⟩ | ⟨h1, -⟩
        · exact ⟨k, hle'.Kd _ _ hk, hk0, hle'.Lv _ _ hkl⟩
        · exact absurd h1 hsl0
      obtain ⟨W3, hb1, hb2⟩ := hW2.slot_store hSlot (c := rv) (Or.inr (hW2.kd hKr).1)
        (fun _ => hLr)
      refine WPs.store hE (addr := sl) (w := rv) (by rw [evalF_local]; exact j7)
        (of_eval (by rw [evalF_local]; exact j9)) ?_
      refine ⟨rfl, rfl, W3, fun addr ha => ?_, ⟨res, j8, hres'⟩, fun _ _ => rfl⟩
      show setCell m2 sl rv addr = _
      rw [setCell_ne _ (NE (by unfold HBASE at ha hb1; omega))]
    · rename_i h0
      have hsl0 : sl = 0#64 := by
        by_contra hne
        exact h0 (by rw [hwv]; simp [evalPanCmp, hne])
      have hlv0 : lv = level := by
        rcases hres with ⟨-, hns⟩ | ⟨-, -, h3⟩
        · exact absurd hsl0 (hns hgw)
        · exact h3
      refine WPs.assign (old := res) (w := rv) j8 (of_eval (by rw [evalF_local]; exact j9)) ?_
      exact ⟨rfl, rfl, hW2, fun _ _ => rfl,
        ⟨rv, by lk [], kk, hKr, hkk, by rw [← hlv0]; exact hLr⟩,
        fun x hx => by simp [update_lookup, hx]⟩
  rintro ⟨l3, g3, m3, f3⟩ ⟨hf3, hg3, hW3, hm3, ⟨res', hr3, k', hk', hk0', hkl'⟩, hfr⟩
  dsimp only at hf3 hg3 hW3 hm3 hr3 hfr
  subst hf3 hg3
  have p1 : l3 "key" = some (.word key) := by rw [hfr _ (by decide)]; exact j1
  have p2 : l3 "klen" = some (.word klen) := by rw [hfr _ (by decide)]; exact j2
  have p3 : l3 "vptr" = some (.word vptr) := by rw [hfr _ (by decide)]; exact j3
  have p4 : l3 "vlen" = some (.word vlen) := by rw [hfr _ (by decide)]; exact j4
  have p5 : l3 "level" = some (.word lv) := by rw [hfr _ (by decide)]; exact j5
  have p6 : l3 "node" = some (.word nd') := by rw [hfr _ (by decide)]; exact j6
  have p7 : l3 "slot" = some (.word sl) := by rw [hfr _ (by decide)]; exact j7
  have p10 : l3 "go" = some (.word gw') := by rw [hfr _ (by decide)]; exact j10
  have p11 : l3 "next_node" = some (.word nn) := by rw [hfr _ (by decide)]; exact j11
  have p12 : l3 "next_slot" = some (.word ns) := by rw [hfr _ (by decide)]; exact j12
  have p13 : l3 "next_level" = some (.word nlv) := by rw [hfr _ (by decide)]; exact j13
  refine WPs.seq_asg (old := nd') (w := nn) p6 (of_eval (by lk [p11])) ?_
  refine WPs.seq_asg (old := sl) (w := ns) (by lk [p7]) (of_eval (by lk [p12])) ?_
  refine WPs.assign (old := lv) (w := nlv) (by lk [p5]) (of_eval (by lk [p13])) ?_
  simp only [restorePanValueFfiLocal]
  refine ⟨_, _, _, _, rfl, ⟨R', nlv, nn, ns, res', gw', hle.trans hle', hW3, rfl,
    fun x hx => (hg2 x hx).trans (hg x hx),
    fun addr ha => ((hm3 addr ha).trans (hm2 addr ha)).trans (hm addr ha),
    by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p1],
    by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p2],
    by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p3],
    by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p4],
    by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
    by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
    by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
    by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hr3],
    by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p10],
    Or.inl ⟨⟨k', hk', hk0', hkl'⟩, fun hgw' => ?_⟩, fun hgw' => ?_⟩, ?_⟩
  · rcases hgo' with h0 | ⟨-, hnn, hnl, hns, hl1, hl2⟩
    · exact absurd h0 hgw'
    · exact hW3.slot_ne hns
  · rcases hgo' with h0 | ⟨-, hnn, hnl, hns, hl1, hl2⟩
    · exact absurd h0 hgw'
    · exact ⟨hl2, hnn, hnl, Or.inr hns⟩
  · refine insMu_lt (gw := gw) (lv := lv) (kl := klen) (gw' := gw') (lv' := nlv) k9 k5 k2
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p10])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, p2])
      hgw hlv' ?_
    rcases hgo' with h0 | ⟨-, hnn, hnl, hns, hl1, hl2⟩
    · exact Or.inl h0
    · exact Or.inr ⟨hl1, hl2⟩

theorem ins_body_cost (hE : GuestEnv E) :
    Costs E IBODY (10 ^ 120) := by
  have h : ∃ B, Costs E IBODY B ∧ B ≤ 10 ^ 120 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem ins_ret_cost (hE : GuestEnv E) :
    Costs E (Prog.return (Exp.var VarKind.local "result") : Prog Word) 10 := by
  have h : ∃ B, Costs E (Prog.return (Exp.var VarKind.local "result") : Prog Word) B ∧ B ≤ 10 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 4000000 in
/-- Step bound of `_mpt_insert_node` from a state satisfying the world invariant. -/
theorem mpt_insert_node_cost (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_mpt_insert_node" E.functions = some (parameters, body))
    (Rg : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat)
    (node key klen level vptr vlen : Word)
    (hnode : s.locals "node" = some (.word node)) (hkey : s.locals "key" = some (.word key))
    (hklen : s.locals "klen" = some (.word klen))
    (hlevel : s.locals "level" = some (.word level))
    (hvp : s.locals "vptr" = some (.word vptr)) (hvl : s.locals "vlen" = some (.word vlen))
    (hW : WorldTJ Rg s.globals s.memory) (hnd : node = 0#64 ∨ ∃ k, Rg.Kd node k)
    (hLn : node ≠ 0#64 → Rg.Lv node level.toNat) (hlv : level.toNat ≤ klen.toNat)
    (hblk : klen ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 141 := by
  have hbody := (fun_of_index 275 hE.functions (by guest_decl_at 275) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hloop : Triple E (fun a => InsI Rg s key klen vptr vlen level a ∧ insMu a ≤ 2 ^ 64)
      (.while IGUARD IBODY) ((2 ^ 64 + 1) * (expCost IGUARD + 10 ^ 120 + 1))
      (fun r => match r with
        | .normal _ _ _ _ => True
        | _ => True) := by
    refine (Triple.while_exit (I := InsI Rg s key klen vptr vlen level) (μ := insMu)
      (Q := fun _ => True) (2 ^ 64) (condCost_exp _) (fun _ _ _ => trivial) ?_).consequence
      (fun _ h => h) (Nat.le_refl _) (fun r _ => by cases r <;> trivial)
    intro k
    refine Triple.of_costs (ins_body_cost hE) ?_
    rintro fuel' a r' n' ⟨hI, hk, hct⟩ hrun' hne'
    rcases ins_body hE hblk hI hct r' (Runs.of_run hrun') with hst | ⟨l, g, m, f, rfl, hI', hlt⟩
    · cases r' with
      | error l g m f => cases hne'
      | raised l g m f ex val => trivial
      | finalFfi l g m f ev => trivial
      | _ => exact absurd hst (fun h => h)
    · exact ⟨hI', hk ▸ hlt⟩
  have hall := Triple.dec (E := E) (P := fun a => a = s)
    (P' := fun a => a = ⟨updatePanValueMap s.locals "result" (.word 0#64), s.globals, s.memory,
      s.ffi⟩) "result" Shape.one (Exp.const (BitVec.ofNat 64 0)) ?_
    (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap s.locals "result"
        (.word 0#64)) "slot" (.word 0#64), s.globals, s.memory, s.ffi⟩) "slot" Shape.one
      (Exp.const (BitVec.ofNat 64 0)) ?_
      (Triple.dec (P' := fun a => InsI Rg s key klen vptr vlen level a ∧ insMu a ≤ 2 ^ 64) "go"
        Shape.one (Exp.const (BitVec.ofNat 64 1)) ?_
        (Triple.seq (Mid := fun _ => True) (Q := fun _ => True) hloop (ins_ret_cost hE))))
  · have hn := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq] at hn
    refine Nat.le_trans hn ?_
    decide +kernel
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) a 0#64) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 0#64) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 1#64) val hval
    subst this
    exact ⟨⟨Rg, level, node, 0#64, 0#64, 1#64, Reg.Le.refl Rg, hW, rfl, fun _ _ => rfl,
      fun _ _ => rfl, by lk [hkey], by lk [hklen], by lk [hvp], by lk [hvl], by lk [hlevel],
      by lk [hnode], by lk [], by lk [], by lk [], Or.inr ⟨rfl, by decide, rfl⟩,
      fun _ => ⟨hlv, hnd, hLn, Or.inl rfl⟩⟩, insMu_le _⟩

end InitECandidate.Solver.GuestBound
