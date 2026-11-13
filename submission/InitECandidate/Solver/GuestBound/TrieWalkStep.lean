import InitECandidate.Solver.GuestBound.TrieWalkScan
import InitECandidate.Solver.GuestBound.TrieDelPush
import InitECandidate.Solver.GuestBound.ScratchFrame

/-!
# The hashing walk: one iteration

One iteration of the loop of `_node_rlp_fill` keeps the invariant `WkI` and
decreases the measure `wkMu`: either a child with an empty cache is pushed
(the scratch pointer drops), or the top node is finished (its cache is filled).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Writing the first three cells of a walk frame. -/
theorem rec3 (m : Word → Option (PanValue Word)) (q a0 a1 a2 : Word)
    (hq : q.toNat + 48 < 2 ^ 64) :
    Rd (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64) a2) q a0 ∧
      Rd (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64) a2)
        (q + 8#64) a1 ∧
      Rd (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64) a2)
        (q + 16#64) a2 ∧
      ∀ addr : Word, ¬ (q.toNat ≤ addr.toNat ∧ addr.toNat < q.toNat + 24) →
        setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64) a2 addr =
          m addr := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have e0 : q + 0#64 = q := by simp
  have e8 : (q + 8#64).toNat = q.toNat + 8 := by bv_omega
  have e16 : (q + 16#64).toNat = q.toNat + 16 := by bv_omega
  rw [e0]
  refine ⟨?_, ?_, Rd.here _ _ _, fun addr ha => ?_⟩
  · exact ((Rd.here m q a0).frame _ (NE (by omega))).frame _ (NE (by omega))
  · exact (Rd.here _ (q + 8#64) a1).frame _ (NE (by omega))
  · rw [setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]

/-- The cache cell of a registered node lies below the heap pointer. -/
theorem WorldTJ.cache_lt {R : Reg} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {x k pv : Word} (hW : WorldTJ R g m)
    (hp : g "heap_ptr" = some (.word pv)) (hk : R.Kd x k) :
    (x + 8#64).toNat = x.toNat + 8 ∧ x.toNat + 8 < pv.toNat ∧ pv.toNat ≤ 2952790016 := by
  have h1 := (hW.nd_below hp hk).1
  have h2 := nodeSize_ge k
  have h3 : pv.toNat ≤ 2952790016 := by
    obtain ⟨pv', T, N, J, C, n, hp', hpH, -⟩ := hW
    rw [hp] at hp'
    simp only [Option.some.injEq, PanValue.word.injEq] at hp'
    subst hp'
    exact hpH.1
  refine ⟨by bv_omega, by omega, h3⟩

local notation "WGUARD" => ((Exp.cmp Cmp.notEqual (Exp.var VarKind.local "top") (Exp.const (BitVec.ofNat 64 0))) : Exp Word)

local notation "WBODY" => ((Prog.dec "nd" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 8))]))
                      (Prog.dec "k" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 0))]))
                        (Prog.dec "child" Shape.one (Exp.const (BitVec.ofNat 64 0))
                          (Prog.dec "found" Shape.one (Exp.const (BitVec.ofNat 64 0))
                            (Prog.seq
                              (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 2)))
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
                                  Prog.skip))
                              (Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "found") (Exp.const (BitVec.ofNat 64 0)))
                                (Prog.decCall "cf" Shape.one "scratch_alloc" [(Exp.const (BitVec.ofNat 64 48))]
                                  (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "cf"), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "top"))
                                    (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "cf"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "child"))
                                    (Prog.seq
                                    (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "cf"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 0)))
                                    (Prog.seq
                                    (Prog.call (some (none, none)) "_node_rlp_begin" [(Exp.var VarKind.local "cf"), (Exp.var VarKind.local "child")])
                                    (Prog.assign VarKind.local "top" (Exp.var VarKind.local "cf")))))))
                                (Prog.seq
                                  (Prog.call (some (none, none)) "_node_rlp_finish" [(Exp.var VarKind.local "top"), (Exp.var VarKind.local "nd")])
                                  (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))])))))))))) : Prog Word)

/-- The RLP cache of `node` is filled. -/
def Filled (m : Word → Option (PanValue Word)) (node : Word) : Prop :=
  ∃ buf off, Rd m (node + 8#64) buf ∧ buf ≠ 0#64 ∧ Rd m (node + 16#64) off ∧
    off.toNat < 2 ^ 32

/-- Invariant of the loop of `_node_rlp_fill`; `node` is the node the walk started from. -/
def WkI (I : WalkIface E) (R : Reg) (G : VarName → Option (PanValue Word))
    (M : Word → Option (PanValue Word)) (F : FfiState σ) (fv lim pv0 node : Word) (a : St σ) :
    Prop :=
  ∃ (pv sp topv : Word) (S : List Word), WorldTJ R a.globals a.memory ∧ a.ffi = F ∧
    (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → a.globals x = G x) ∧
    a.globals "heap_ptr" = some (.word pv) ∧ pv0.toNat ≤ pv.toNat ∧
    a.globals "scratch_ptr" = some (.word sp) ∧ fv.toNat ≤ sp.toNat ∧ sp.toNat ≤ lim.toNat ∧
    I.Pre R a.globals ∧ a.locals "mark" = some (.word lim) ∧
    a.locals "top" = some (.word topv) ∧
    RStk R (I.FrOK R pv a.memory) a.memory lim.toNat sp.toNat topv S ∧
    ((S = [] ∧ Filled a.memory node) ∨ ∃ S0, S = S0 ++ [node]) ∧
    (∀ addr : Word, lim.toNat ≤ addr.toNat → a.memory addr = M addr) ∧
    ∀ addr : Word, addr.toNat < pv0.toNat → ¬ CacheC R addr → ¬ I.K addr →
      a.memory addr = M addr

set_option maxHeartbeats 16000000 in
theorem wk_body (hE : GuestEnv E) (I : WalkIface E) {R : Reg}
    {G : VarName → Option (PanValue Word)} {M : Word → Option (PanValue Word)}
    {F : FfiState σ} {fv lim pv0 node : Word} (hGfv : G "frame_mem_ptr" = some (.word fv))
    (hFv : 2952790016 ≤ fv.toNat) {a : St σ} (hI : WkI I R G M F fv lim pv0 node a)
    (hct : CondTrue E a WGUARD) :
    WPs E a WBODY (fun r => ∃ l g m f, r = .normal l g m f ∧
      WkI I R G M F fv lim pv0 node ⟨l, g, m, f⟩ ∧ wkMu R ⟨l, g, m, f⟩ < wkMu R a) := by
  obtain ⟨la, ga, ma, fa⟩ := a
  obtain ⟨pv, sp, topv, S, hW, hf, hg, hgp, hpv0, hgs, hfs, hsl, hPre, qmark, qtop, hst, hbot, hM, hM0⟩ := hI
  obtain ⟨w, cc, hcond, hw⟩ := hct
  dsimp only at hW hf hg hgp hgs hPre qmark qtop hst hbot hM hM0
  subst hf
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have hlim := lim.isLt
  have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := topv) (by lk [qtop]))
    (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hcond)
  simp only [PanValue.word.injEq] at hcv
  have ht0 : topv ≠ 0#64 := by
    rintro rfl
    rw [hcv] at hw
    simp [evalPanCmp] at hw
  have hgfv : ga "frame_mem_ptr" = some (.word fv) :=
    (hg _ (by decide) (by decide)).trans hGfv
  cases hst with
  | nil => exact absurd rfl ht0
  | @cons _ _ prev nd cur k ℓ S' h1 h2 h3 h4 r0 r1 r2 hcu hK hk0 hLv hc0 hFr hS htail =>
  have e8 : (topv + 8#64).toNat = topv.toNat + 8 := by bv_omega
  have e16 : (topv + 16#64).toNat = topv.toNat + 16 := by bv_omega
  obtain ⟨-, hRdk, -, -, -⟩ := hW.kd hK
  obtain ⟨end8, endlt, hpvE⟩ := hW.cache_lt hgp hK
  have cl : ∀ {x k' : Word}, R.Kd x k' →
      (x + 8#64).toNat = x.toNat + 8 ∧ x.toNat + 8 < pv.toNat := fun hk' =>
    ⟨(hW.cache_lt hgp hk').1, (hW.cache_lt hgp hk').2.1⟩
  refine WPs.dec (w := nd) (eval_load_rd hE (eval_addc hE 8#64 qtop) r1) ?_
  refine WPs.dec (w := k) (eval_load_rd hE (eval_addc hE (a := nd) 0#64 (by lk []))
    (by rw [BitVec.add_zero]; exact hRdk)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.seq (fun a' => ScanQ R ga ma fa topv nd lim ℓ
      (.normal a'.locals a'.globals a'.memory a'.ffi))
    ((wk_scan hE I (topv := topv) (nd := nd) (k := k) (cur := cur) (ℓ := ℓ) (mk := lim)
      (by lk [qmark]) hW hK hLv
      (by lk [qtop]) (by lk []) (by lk []) (by lk []) (by lk []) r2 hcu (by omega)
      (by omega)).conseq (fun r hr => by
        obtain ⟨L, m1, c, f, cur', hr, rest⟩ := hr
        exact ⟨L, ga, m1, fa, hr, L, m1, c, f, cur', rfl, rest⟩)) ?_
  rintro ⟨L, g', m1, f'⟩ ⟨L', m1', c, f, cur', heq, qmk, qt, qn, qc, qfd, hm1, rc', hcu', hgood⟩
  injection heq with e1 e2 e3 e4
  have e2' := e2.symm
  have e4' := e4.symm
  subst e1 e2' e3 e4'
  dsimp only at qmk qt qn qc qfd hm1 rc' hgood
  have hmh : ∀ x : Word, x.toNat < 2952790016 → m1 x = ma x :=
    fun x hx => hm1 x (NE (by omega))
  have hW1 : WorldTJ R ga m1 := hW.scratch (fun x _ => rfl) hmh
  have frTop1 : I.FrOK R pv m1 topv nd := I.stable hFr (Nat.le_refl _)
    ⟨fun a ha _ _ => hmh a (by omega), fun a h1 h2 => hm1 a (NE (by omega))⟩
  have tail1 : RStk R (I.FrOK R pv m1) m1 lim.toNat (topv.toNat + 48) prev S' :=
    htail.step hlim (fun x hx _ => hm1 x (NE (by omega)))
      (fun x hx => by
        obtain ⟨ℓ', k', -, -, hk'⟩ := hS x hx
        have := cl hk'
        exact hmh _ (by omega))
      (fun fr nd' hfr hfr' hF => I.stable hF (Nat.le_refl _)
        ⟨fun a ha _ _ => hmh a (by omega), fun a h1 h2 => hm1 a (NE (by omega))⟩)
  have r0' : Rd m1 topv prev := by
    unfold Rd at r0 ⊢
    rw [hm1 _ (NE (by omega))]
    exact r0
  have r1' : Rd m1 (topv + 8#64) nd := by
    unfold Rd at r1 ⊢
    rw [hm1 _ (NE (by omega))]
    exact r1
  have hc0' : Rd m1 (nd + 8#64) 0#64 := by
    unfold Rd at hc0 ⊢
    rw [hmh _ (by omega)]
    exact hc0
  refine WPs.ite_both (fun w2 hw2 => ?_)
  obtain ⟨x, y, hx, hy, hwv2⟩ := cmp_word_inv hE hw2
  simp only [evalF_local, qfd, eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · -- nothing to descend into: finish the top node and pop
    refine WPs.seq_call_ret (fun vs g3 m3 ffi3 hret => ?_)
    obtain ⟨rfl, pv', hgp', hpv', hg3, hW3, ⟨buf, off, rb, hb0, ro, hoff⟩, hheap, hcache, hscr⟩ :=
      I.finish R _ _ _ topv nd k pv _ _ _ _ hret (by lk [qt]) (by lk [qn]) hW1 hPre hgp hK hk0
        frTop1
    dsimp only at hgp' hg3 hheap hcache hscr
    refine WPs.assign (old := topv) (w := prev) qt
      (eval_load_rd hE (eval_addc hE 0#64 qt) (by
        rw [BitVec.add_zero]
        show Rd m3 topv prev
        unfold Rd
        rw [hscr _ (by omega)]
        exact r0')) ?_
    simp only [restorePanValueFfiLocal]
    have hsp3 : g3 "scratch_ptr" = some (.word sp) := (hg3 _ (by decide)).trans hgs
    refine ⟨_, _, _, _, rfl, ⟨pv', sp, prev, S', hW3, rfl,
      fun x h1 h2 => (hg3 x h1).trans (hg x h1 h2), hgp', by omega, hsp3, hfs, hsl,
      I.pre_glob hPre (fun x h1 _ => hg3 x h1),
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qmk, qmark],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      (tail1.step hlim (fun x hx _ => hscr x (by omega))
        (fun x hx => by
          obtain ⟨ℓ', k', hl', hlt, hk'⟩ := hS x hx
          exact hcache x k' hk' (by
            rintro rfl
            have := hW.lv_unique hl' hLv
            omega))
        (fun fr nd' hfr hfr' hF => I.stable hF hpv'
          ⟨hheap, fun a h1 h2 => hscr a (by omega)⟩)).lower (by omega),
      (by
        rcases hbot with ⟨hnil, -⟩ | ⟨S0, hS0⟩
        · cases hnil
        · cases S0 with
          | nil =>
            simp only [List.nil_append, List.cons.injEq] at hS0
            obtain ⟨rfl, rfl⟩ := hS0
            exact Or.inl ⟨rfl, buf, off, rb, hb0, ro, hoff⟩
          | cons x S0' =>
            simp only [List.cons_append, List.cons.injEq] at hS0
            obtain ⟨rfl, rfl⟩ := hS0
            exact Or.inr ⟨S0', rfl⟩),
      fun addr ha => (hscr addr (by omega)).trans ((hm1 addr (NE (by omega))).trans (hM addr ha)),
      fun addr ha h1 h2 => (hheap addr (by omega) h1 h2).trans
        ((hmh addr (by omega)).trans (hM0 addr ha h1 h2))⟩, ?_⟩
    have hU := Uset.pop (m := ma) (m' := m3) hK hk0 hc0 rb hb0 (fun x k' hk' hne => by
      have := cl hk'
      exact (hcache x k' hk' hne).trans (hmh _ (by omega)))
    unfold wkMu spOf
    dsimp only
    rw [hsp3, hgs]
    omega
  · -- a child needs its RLP: push a frame for it
    rename_i hf0
    have hfne : f ≠ 0#64 := by
      rintro rfl
      apply hf0
      rw [hwv2]
      simp [evalPanCmp]
    obtain ⟨kc, ℓc, hKc, hkc0, hLc, hlt, rc8⟩ := hgood hfne
    obtain ⟨cend8, cendlt⟩ := cl hKc
    refine WPs.decCall_ret (fun vq g1 mq f1 hret1 => ?_)
    obtain ⟨hmq, hfq, q, rfl, rfl, hq1, hq2, hq8⟩ := scratchalloc_ret hE hret1 (pv := sp)
      (fv := fv) (nv := 48#64) (eval_const _ _) hgs hgfv hfs
    have hmq' : m1 = mq := hmq.symm
    have hfq' : fa = f1 := hfq.symm
    subst hmq' hfq'
    have hq2' : q.toNat + 48 ≤ sp.toNat := by simpa using hq2
    obtain ⟨c0, c1, c2, hfr⟩ := rec3 m1 q topv c 0#64 (by omega)
    have hq0 : q ≠ 0#64 := by
      rintro rfl
      simp at hq1
      omega
    refine WPs.seq_store hE (addr := q + 0#64) (w := topv) (eval_addc hE 0#64 (by lk []))
      (of_eval (by lk [qt])) ?_
    refine WPs.seq_store hE (addr := q + 8#64) (w := c) (eval_addc hE 8#64 (by lk []))
      (of_eval (by lk [qc])) ?_
    refine WPs.seq_store hE (addr := q + 16#64) (w := 0#64) (eval_addc hE 16#64 (by lk []))
      (of_eval (eval_const _ _)) ?_
    have hW2 := hW1.scratch (g' := updatePanValueMap ga "scratch_ptr" (.word q))
      (fun x hx => by simp [update_lookup, hx]) (fun a ha => hfr a (by omega))
    refine WPs.seq_call_ret (fun vs g3 m3 ffi3 hret => ?_)
    obtain ⟨rfl, pv', hgp', hpv', hg3, hW3, hFr3, hheap, hscr⟩ :=
      I.begin R _ _ _ q c kc pv _ _ _ _ hret (by lk []) (by lk [qc]) hW2
        (I.pre_glob hPre (fun x h1 h2 => by simp [update_lookup, h2]))
        (by simp (config := { decide := true }) [update_lookup, hgp]) hKc hkc0 (by omega) hq8
        (by omega)
    dsimp only at hgp' hg3 hheap hscr
    refine WPs.assign (old := topv) (w := q) (by lk [qt]) (of_eval (by lk [])) ?_
    simp only [restorePanValueFfiLocal]
    have hsp3 : g3 "scratch_ptr" = some (.word q) :=
      (hg3 _ (by decide)).trans (by simp [update_lookup])
    have hlow : ∀ x : Word, x.toNat < pv.toNat → m3 x = ma x := fun x hx =>
      (hheap x hx).trans ((hfr x (by omega)).trans (hmh x (by omega)))
    have stk1 : RStk R (I.FrOK R pv m1) m1 lim.toNat sp.toNat topv (nd :: S') :=
      .cons h1 h2 h3 h4 r0' r1' rc' hcu' hK hk0 hLv hc0' frTop1 hS tail1
    have hhigh : ∀ x : Word, sp.toNat ≤ x.toNat → m3 x = m1 x := fun x hx =>
      (hscr x (by omega) (by omega)).trans (hfr x (by omega))
    refine ⟨_, _, _, _, rfl, ⟨pv', q, q, c :: nd :: S', hW3, rfl,
      fun x h1 h2 => (hg3 x h1).trans (by simp [update_lookup, h2]; exact hg x h1 h2),
      hgp', by omega, hsp3, hq1, by omega,
      I.pre_glob hPre (fun x h1 h2 => (hg3 x h1).trans (by simp [update_lookup, h2])),
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qmk, qmark],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      .cons (cur := 0#64) (prev := topv) hq0 hq8 (Nat.le_refl _) (by omega)
        (by unfold Rd; dsimp only; rw [hscr q (by omega) (by omega)]; exact c0)
        (by
          have e : (q + 8#64).toNat = q.toNat + 8 := by bv_omega
          unfold Rd
          dsimp only
          rw [hscr _ (by omega) (by omega)]
          exact c1)
        (by
          have e : (q + 16#64).toNat = q.toNat + 16 := by bv_omega
          unfold Rd
          dsimp only
          rw [hscr _ (by omega) (by omega)]
          exact c2)
        (by decide) hKc hkc0 hLc
        (by unfold Rd; dsimp only; rw [hlow _ (by omega)]; exact rc8) hFr3
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact ⟨ℓ, k, hLv, hlt, hK⟩
          · obtain ⟨ℓ', k', hl', hlt', hk'⟩ := hS x hx'
            exact ⟨ℓ', k', hl', by omega, hk'⟩)
        ((stk1.step hlim (fun x hx _ => hhigh x hx)
          (fun x hx => by
            have hk' : ∃ k', R.Kd x k' := by
              rcases List.mem_cons.mp hx with rfl | hx'
              · exact ⟨k, hK⟩
              · obtain ⟨ℓ', k', -, -, hk'⟩ := hS x hx'
                exact ⟨k', hk'⟩
            obtain ⟨k', hk'⟩ := hk'
            have := cl hk'
            exact (hheap _ (by omega)).trans (hfr _ (by omega)))
          (fun fr nd' hfr1 hfr' hF => I.stable hF hpv'
            ⟨fun a ha _ _ => (hheap a ha).trans (hfr a (by omega)),
              fun a h1 h2 => hhigh a (by omega)⟩)).lower (by omega)),
      (by
        rcases hbot with ⟨hnil, -⟩ | ⟨S0, hS0⟩
        · cases hnil
        · exact Or.inr ⟨c :: S0, by rw [hS0]; rfl⟩),
      fun addr ha => (hhigh addr (by omega)).trans
        ((hm1 addr (NE (by omega))).trans (hM addr ha)),
      fun addr ha h1 h2 => (hlow addr (by omega)).trans (hM0 addr ha h1 h2)⟩, ?_⟩
    have hU : Uset R m3 = Uset R ma := Uset.same (fun x k' hk' => by
      have := cl hk'
      exact hlow _ (by omega))
    unfold wkMu spOf
    dsimp only
    rw [hsp3, hgs, hU]
    show (Uset R ma).ncard + q.toNat < (Uset R ma).ncard + sp.toNat
    omega

end InitECandidate.Solver.GuestBound
