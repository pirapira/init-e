import InitECandidate.Solver.GuestBound.TrieDecDefs
import InitECandidate.Solver.GuestBound.TrieWalkStep
import InitECandidate.Solver.GuestBound.RlpTotal

/-!
# The witness decoder: invariant, and the iteration in mode 1

In mode 1 the decoder calls `_decode_step`; the result is a finished node
(mode 0) or a new record, which is linked to the stack (mode 2).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem DStk.top_in {R : Reg} {m : Word → Option (PanValue Word)} {lim ℓ0 sp : Nat}
    {top : Word} {ℓ : Nat} (h : DStk R m lim ℓ0 sp top ℓ) :
    top = 0#64 ∨ (sp ≤ top.toNat ∧ top.toNat + 88 ≤ lim) := by
  cases h with
  | nil => exact Or.inl rfl
  | ext h1 h2 h3 h4 => exact Or.inr ⟨h3, h4⟩
  | br h1 h2 h3 h4 => exact Or.inr ⟨h3, h4⟩

theorem icOf_congr {m m' : Word → Option (PanValue Word)} {t : Word}
    (h : t ≠ 0#64 → m' (t + 32#64) = m (t + 32#64)) : icOf m' t = icOf m t := by
  unfold icOf
  by_cases ht : t = 0#64
  · rw [if_pos ht, if_pos ht]
  · rw [if_neg ht, if_neg ht, h ht]

/-- Invariant of the decoder loop. `L0` is the level of the node being decoded. -/
def DcI (I : DecIface E) (R0 : Reg) (G : VarName → Option (PanValue Word))
    (M : Word → Option (PanValue Word)) (F : FfiState σ) (fv lim dbv : Word) (L0 : Nat)
    (a : St σ) : Prop :=
  ∃ (R : Reg) (sp topv resv cp cn md sl gv : Word) (ℓ : Nat),
    R0.Le R ∧ WorldTJ R a.globals a.memory ∧ a.ffi = F ∧
    (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → a.globals x = G x) ∧
    a.globals "scratch_ptr" = some (.word sp) ∧ fv.toNat ≤ sp.toNat ∧ sp.toNat ≤ lim.toNat ∧
    I.Pre R a.globals ∧
    a.locals "db" = some (.word dbv) ∧ a.locals "top" = some (.word topv) ∧
    a.locals "result" = some (.word resv) ∧ a.locals "cur_p" = some (.word cp) ∧
    a.locals "cur_n" = some (.word cn) ∧ a.locals "mode" = some (.word md) ∧
    a.locals "slot" = some (.word sl) ∧ a.locals "go" = some (.word gv) ∧
    DStk R a.memory lim.toNat L0 sp.toNat topv ℓ ∧
    (md ≠ 1#64 → md ≠ 2#64 → DRes R ℓ resv) ∧
    (gv = 0#64 → md ≠ 1#64 ∧ md ≠ 2#64 ∧ topv = 0#64) ∧ (md = 2#64 → topv ≠ 0#64) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ lim.toNat ≤ addr.toNat) → a.memory addr = M addr

/-- One iteration: the invariant is kept and the measure drops. -/
def DcPost (I : DecIface E) (R0 : Reg) (G : VarName → Option (PanValue Word))
    (M : Word → Option (PanValue Word)) (F : FfiState σ) (fv lim dbv : Word) (L0 : Nat)
    (a : St σ) (r : Result σ) : Prop :=
  ∃ l g m f, r = .normal l g m f ∧ DcI I R0 G M F fv lim dbv L0 ⟨l, g, m, f⟩ ∧
    dcMu ⟨l, g, m, f⟩ < dcMu a

local notation "M1PROG" => ((Prog.decCall "d" (Shape.comb [Shape.one, Shape.one]) "_decode_step" [(Exp.var VarKind.local "db"), (Exp.var VarKind.local "cur_p"), (Exp.var VarKind.local "cur_n")]
                              (Prog.ite (Exp.cmp Cmp.equal (Exp.rField 0 (Exp.var VarKind.local "d")) (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.seq
                                  (Prog.assign VarKind.local "result" (Exp.rField 1 (Exp.var VarKind.local "d")))
                                  (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 0))))
                                (Prog.seq
                                  (Prog.store (Exp.op BinOp.add [(Exp.rField 1 (Exp.var VarKind.local "d")), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "top"))
                                  (Prog.seq
                                  (Prog.assign VarKind.local "top" (Exp.rField 1 (Exp.var VarKind.local "d")))
                                  (Prog.seq
                                  (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 8))])) (Exp.const (BitVec.ofNat 64 1)))
                                    (Prog.assign VarKind.local "slot" (Exp.const (BitVec.ofNat 64 1)))
                                    (Prog.assign VarKind.local "slot" (Exp.const (BitVec.ofNat 64 0))))
                                  (Prog.assign VarKind.local "mode" (Exp.const (BitVec.ofNat 64 2)))))))) : Prog Word)

set_option maxHeartbeats 16000000 in
theorem dc_mode1 (hE : GuestEnv E) (I : DecIface E) {R0 : Reg}
    {G : VarName → Option (PanValue Word)} {M : Word → Option (PanValue Word)}
    {F : FfiState σ} {fv lim dbv : Word} {L0 : Nat}
    (hGfv : G "frame_mem_ptr" = some (.word fv)) (hFv : 2952790016 ≤ fv.toNat) {a : St σ}
    (hI : DcI I R0 G M F fv lim dbv L0 a) (hmd : a.locals "mode" = some (.word 1#64))
    (hgo : ∀ gv, a.locals "go" = some (.word gv) → gv ≠ 0#64) :
    WPs E a M1PROG (DcPost I R0 G M F fv lim dbv L0 a) := by
  obtain ⟨la, ga, ma, fa⟩ := a
  obtain ⟨R, sp, topv, resv, cp, cn, md, sl, gv, ℓ, hle, hW, hf, hg, hgs, hfs, hsl, hPre, qdb,
    qtop, qres, qcp, qcn, qmode, qslot, qgo, hst, hres, hfin, hm2t, hM⟩ := hI
  dsimp only at hW hf hg hgs hPre qdb qtop qres qcp qcn qmode qslot qgo hst hM hmd hgo
  subst hf
  have hmd1 : md = 1#64 := by
    rw [qmode] at hmd
    simpa using hmd
  subst hmd1
  have hgv := hgo gv qgo
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hlim := lim.isLt
  have hgfv : ga "frame_mem_ptr" = some (.word fv) :=
    (hg _ (by decide) (by decide)).trans hGfv
  have hmu0 := dcMu_eq (a := (⟨la, ga, ma, fa⟩ : St σ)) hgs qtop qmode qgo
  dsimp only at hmu0
  refine WPs.decCall_ret (fun v g1 m1 f1 hret => ?_)
  obtain ⟨hf1, R', d0, d1, sp', rfl, hle', hW', hg', hgs', hfs', hsp', hmem, hleaf, hrec⟩ :=
    I.decode R _ _ _ _ dbv cp cn sp fv ℓ _ _ _ _ hret (by lk [qdb]) (by lk [qcp])
      (by lk [qcn]) hW hPre hgs hgfv hfs hFv
  dsimp only at hf1 hg' hmem
  subst hf1
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qd : L "d" = some (.rStruct [.word d0, .word d1]) := by rw [hLL]; lk []
  have qdb' : L "db" = some (.word dbv) := by rw [hLL]; lk [qdb]
  have qtop' : L "top" = some (.word topv) := by rw [hLL]; lk [qtop]
  have qres' : L "result" = some (.word resv) := by rw [hLL]; lk [qres]
  have qcp' : L "cur_p" = some (.word cp) := by rw [hLL]; lk [qcp]
  have qcn' : L "cur_n" = some (.word cn) := by rw [hLL]; lk [qcn]
  have qmode' : L "mode" = some (.word 1#64) := by rw [hLL]; lk [qmode]
  have qslot' : L "slot" = some (.word sl) := by rw [hLL]; lk [qslot]
  have qgo' : L "go" = some (.word gv) := by rw [hLL]; lk [qgo]
  have hold : la "d" = none ∨ True := Or.inr trivial
  have ed0 : ∀ (L' : VarName → Option (PanValue Word)) (g' : VarName → Option (PanValue Word))
      (m' : Word → Option (PanValue Word)) (f' : FfiState σ),
      L' "d" = some (.rStruct [.word d0, .word d1]) →
      E.eval ⟨L', g', m', f'⟩ (.rField 0 (.var .local "d")) = some (.word d0) := by
    intro L' g' m' f' h
    rw [eval_rField _ 0 "d" _ h]
    rfl
  have ed1 : ∀ (L' : VarName → Option (PanValue Word)) (g' : VarName → Option (PanValue Word))
      (m' : Word → Option (PanValue Word)) (f' : FfiState σ),
      L' "d" = some (.rStruct [.word d0, .word d1]) →
      E.eval ⟨L', g', m', f'⟩ (.rField 1 (.var .local "d")) = some (.word d1) := by
    intro L' g' m' f' h
    rw [eval_rField _ 1 "d" _ h]
    rfl
  clear hLL
  have hglob : ∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g1 x = G x :=
    fun x h1 h2 => (hg' x h1 h2).trans (hg x h1 h2)
  have hPre' := I.pre_mono hPre hle' hg'
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  rw [ed0 _ _ _ _ qd] at hx
  simp only [eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · -- a record: link it and go to mode 2
    rename_i hw0
    have hd0 : d0 ≠ 0#64 := by
      rintro rfl
      rw [hwv] at hw0
      simp [evalPanCmp] at hw0
    obtain ⟨hsd, hq8, hq88, hnew⟩ := hrec hd0
    subst hsd
    have e0 : sp' + 0#64 = sp' := by simp
    have ea : E.eval ⟨L, g1, m1, f1⟩ (.op .add [.rField 1 (.var .local "d"), .const 0#64]) =
        some (.word (sp' + 0#64)) := by
      simp [evalF_op hE.word, evalArgs_cons, evalArgs_nil, ed1 _ _ _ _ qd, wordsProj_cons,
        wordsProj_nil, wordOp]
    refine WPs.seq_store hE (addr := sp' + 0#64) (w := topv) ea (of_eval (by lk [qtop'])) ?_
    rw [e0]
    refine WPs.seq_asg (old := topv) (w := sp') qtop' (of_eval (ed1 _ _ _ _ qd)) ?_
    have hmlow : ∀ x : Word, x ≠ sp' → setCell m1 sp' topv x = m1 x := fun x hx => setCell_ne _ hx
    have cell : ∀ (c : Nat) (w : Word), 8 ≤ c → c ≤ 80 → Rd m1 (sp' + BitVec.ofNat 64 c) w →
        Rd (setCell m1 sp' topv) (sp' + BitVec.ofNat 64 c) w := by
      intro c w hc1 hc2 hr
      have e : (sp' + BitVec.ofNat 64 c).toNat = sp'.toNat + c := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      exact hr.frame _ (NE (by omega))
    have hq0 : sp' ≠ 0#64 := by
      rintro rfl
      simp at hfs'
      omega
    have hst' : DStk R' (setCell m1 sp' topv) lim.toNat L0 (sp'.toNat + 88) topv ℓ :=
      (((hst.mono hle').frame hlim (fun x hx _ => hmem x (Or.inr hx))).frame hlim
        (fun x hx _ => hmlow x (NE (by omega)))).lower (by omega)
    have hW2 : WorldTJ R' g1 (setCell m1 sp' topv) :=
      hW'.scratch (fun x _ => rfl) (fun a ha => hmlow a (NE (by omega)))
    have hMM : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ lim.toNat ≤ addr.toNat) →
        setCell m1 sp' topv addr = M addr := fun addr ha =>
      (hmlow addr (NE (by unfold HBASE at ha; omega))).trans
        ((hmem addr (by omega)).trans (hM addr ha))
    refine WPs.seqG (fun a' => ∃ sv : Word, a' = ⟨updatePanValueMap (updatePanValueMap L "top"
        (.word sp')) "slot" (.word sv), g1, setCell m1 sp' topv, f1⟩)
      (WPs.ite_both (fun w2 _ => ?_)) ?_
    · split
      · exact WPs.assign (old := sl) (w := 0#64) (by lk [qslot']) (of_eval (eval_const _ _))
          ⟨0#64, rfl⟩
      · exact WPs.assign (old := sl) (w := 1#64) (by lk [qslot']) (of_eval (eval_const _ _))
          ⟨1#64, rfl⟩
    rintro _ ⟨sv, rfl⟩
    refine WPs.assign (old := 1#64) (w := 2#64) (by lk [qmode']) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    obtain ⟨ℓ', hstk⟩ : ∃ ℓ', DStk R' (setCell m1 sp' topv) lim.toNat L0 sp'.toNat sp' ℓ' := by
      rcases hnew with ⟨rk, seg, sgl, r64, r72, hs1, himm⟩ | ⟨kd, b, rk, hkd, r16, hKb, hLb, r32⟩
      · exact ⟨_, .ext hq0 hq8 (Nat.le_refl _) (by omega) (Rd.here _ _ _) (cell 8 _ (by omega)
          (by omega) rk) (cell 64 _ (by omega) (by omega) r64) (cell 72 _ (by omega) (by omega)
          r72) hs1 himm hst'⟩
      · exact ⟨_, .br hq0 hq8 (Nat.le_refl _) (by omega) (Rd.here _ _ _) (cell 8 _ (by omega)
          (by omega) rk) hkd (cell 16 _ (by omega) (by omega) r16) (cell 32 _ (by omega)
          (by omega) r32) (by decide) hKb hLb hst'⟩
    refine ⟨_, _, _, _, rfl, ⟨R', sp', sp', resv, cp, cn, 2#64, sv, gv, ℓ', hle.trans hle', hW2,
      rfl, hglob, hgs', hfs', by omega, hPre',
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qdb'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qres'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qcp'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qcn'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo'],
      hstk, fun _ h => absurd rfl h, fun h => absurd h hgv, fun _ => hq0, hMM⟩, ?_⟩
    rw [hmu0, dcMu_eq (sp := sp') (t := sp') (md := 2#64) (gv := gv) hgs'
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo'])]
    dsimp only
    have := tT_le sp'
    have := icOf_le (setCell m1 sp' topv) sp'
    have := rankOf_le (2#64 : Word)
    have := goOf_le gv
    omega
  · -- a finished node: mode 0
    rename_i hw0
    have hd0 : d0 = 0#64 := by
      by_contra hne
      apply hw0
      rw [hwv]
      simp [evalPanCmp, hne]
    refine WPs.seq_asg (old := resv) (w := d1) qres' (of_eval (ed1 _ _ _ _ qd)) ?_
    refine WPs.assign (old := 1#64) (w := 0#64) (by lk [qmode']) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    have hst' : DStk R' m1 lim.toNat L0 sp'.toNat topv ℓ :=
      ((hst.mono hle').frame hlim (fun x hx _ => hmem x (Or.inr hx))).lower hsp'
    refine ⟨_, _, _, _, rfl, ⟨R', sp', topv, d1, cp, cn, 0#64, sl, gv, ℓ, hle.trans hle', hW',
      rfl, hglob, hgs', hfs', by omega, hPre',
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qdb'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qtop'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qcp'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qcn'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qslot'],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo'],
      hst', fun _ _ => hleaf hd0, fun h => absurd h hgv, fun h => absurd h (by decide),
      fun addr ha => (hmem addr (by omega)).trans (hM addr ha)⟩, ?_⟩
    rw [hmu0, dcMu_eq (sp := sp') (t := topv) (md := 0#64) (gv := gv) hgs'
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qtop'])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo'])]
    dsimp only
    have hic : icOf m1 topv = icOf ma topv := icOf_congr (fun ht => by
      rcases hst.top_in with h0 | ⟨h1, h2⟩
      · exact absurd h0 ht
      · have e : (topv + 32#64).toNat = topv.toNat + 32 := by bv_omega
        exact hmem _ (Or.inr (by omega)))
    rw [hic]
    have h0 : rankOf (0#64 : Word) = 0 := by decide
    have h1 : rankOf (1#64 : Word) = 1 := by decide
    rw [h0, h1]
    have : sp'.toNat * 2 ^ 73 ≤ sp.toNat * 2 ^ 73 := Nat.mul_le_mul_right _ hsp'
    omega

end InitECandidate.Solver.GuestBound
