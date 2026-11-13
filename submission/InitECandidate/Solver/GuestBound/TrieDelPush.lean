import InitECandidate.Solver.GuestBound.TrieDelDown

/-!
# The descent loop of the delete walk: pushing a record; the extension case
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The top record lies at or above the scratch pointer. -/
theorem DelStack.top_ge {R : Reg} {m : Word → Option (PanValue Word)} {sp lim top : Word}
    {ℓ0 ℓ : Nat} (h : DelStack R m sp lim ℓ0 top ℓ) (h0 : top ≠ 0#64) :
    sp.toNat ≤ top.toNat := by
  cases h with
  | nil => exact absurd rfl h0
  | ext h1 h2 h3 => exact h3
  | br h1 h2 h3 => exact h3

/-- The stack below a record pushed at `q`, after writes confined to the record. -/
theorem DlCtx.below {Rg R R' : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {fv lim sp : Word} {ℓ0 : Nat}
    {key klen lv nd topv resv : Word} {b : St σ}
    (c : DlCtx Rg R G M fv lim sp ℓ0 key klen lv nd topv resv b) (hle : R.Le R') {q : Word}
    (hq2 : q.toNat + 40 ≤ sp.toNat) {m' : Word → Option (PanValue Word)}
    (hm' : ∀ addr : Word, ¬ (q.toNat ≤ addr.toNat ∧ addr.toNat < q.toNat + 40) →
      m' addr = b.memory addr) :
    DelStack R' m' q lim ℓ0 topv lv.toNat ∧ (topv = 0#64 ∨ q.toNat + 40 ≤ topv.toNat) := by
  refine ⟨((c.st.mono hle).frame (fun x hx _ => hm' x (by omega))).lower (by omega), ?_⟩
  by_cases h0 : topv = 0#64
  · exact Or.inl h0
  · have := c.st.top_ge h0
    exact Or.inr (by omega)

/-- The iteration pushed a record at `q` and descends. -/
theorem DlCtx.push {Rg R R' : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {fv lim sp : Word} {ℓ0 : Nat}
    {key klen lv nd topv resv : Word} {b : St σ}
    (c : DlCtx Rg R G M fv lim sp ℓ0 key klen lv nd topv resv b) (hle : R.Le R') {q : Word}
    (hq1 : fv.toNat ≤ q.toNat) (hq2 : q.toNat + 40 ≤ sp.toNat)
    {l' g' : VarName → Option (PanValue Word)} {m' : Word → Option (PanValue Word)}
    {nd' lv' res' : Word}
    (hW' : WorldTJ R' g' m') (hg' : ∀ x, x ≠ "scratch_ptr" → g' x = b.globals x)
    (hsp' : g' "scratch_ptr" = some (.word q))
    (hm' : ∀ addr : Word, ¬ (q.toNat ≤ addr.toNat ∧ addr.toNat < q.toNat + 40) →
      m' addr = b.memory addr)
    (l1 : l' "key" = some (.word key)) (l2 : l' "klen" = some (.word klen))
    (l3 : l' "level" = some (.word lv')) (l4 : l' "node" = some (.word nd'))
    (l5 : l' "top" = some (.word q)) (l6 : l' "res" = some (.word res'))
    (l7 : l' "go" = some (.word 1#64))
    (hst' : DelStack R' m' q lim ℓ0 q lv'.toNat) (hlv' : lv'.toNat ≤ klen.toNat)
    (hnd' : nd' = 0#64 ∨ ∃ k, R'.Kd nd' k) (hl' : nd' ≠ 0#64 → R'.Lv nd' lv'.toNat) :
    DlS Rg G M fv lim ℓ0 key klen l' g' m' 1#64 lv' := by
  have hF := c.hF
  have hfs := c.fs
  have hsl := c.sl
  refine ⟨R', q, res', nd', q, lv'.toNat, c.le.trans hle, hW',
    fun x h1 h2 => (hg' x h2).trans (c.g x h1 h2), hsp',
    by rw [hg' _ (by decide)]; exact c.gfv, hq1, by omega, fun addr ha => ?_, l1, l2, l3, l4, l5,
    l6, l7, hst', fun _ => ⟨rfl, hlv', hnd', hl'⟩, fun h => absurd h (by decide)⟩
  rw [hm' addr (by unfold HBASE at ha; rcases ha with ha | ha <;> omega)]
  exact c.m addr ha

/-- The world invariant after a scratch allocation and writes above the heap. -/
theorem WorldTJ.scratch {Rg : Reg} {g g' : VarName → Option (PanValue Word)}
    {m m' : Word → Option (PanValue Word)} (h : WorldTJ Rg g m)
    (hg : ∀ x, x ≠ "scratch_ptr" → g' x = g x)
    (hm : ∀ a : Word, a.toNat < 2952790016 → m' a = m a) : WorldTJ Rg g' m' :=
  (h.frame_heap (fun a _ _ hlt => hm a hlt)).of_globals hg

/-- Writing the five cells of an extension record. -/
theorem rec5 (m : Word → Option (PanValue Word)) (q a0 a1 a2 a3 a4 : Word)
    (hq : q.toNat + 40 < 2 ^ 64) :
    Rd (setCell (setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64)
        a2) (q + 24#64) a3) (q + 32#64) a4) q a0 ∧
      Rd (setCell (setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1)
        (q + 16#64) a2) (q + 24#64) a3) (q + 32#64) a4) (q + 8#64) a1 ∧
      Rd (setCell (setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1)
        (q + 16#64) a2) (q + 24#64) a3) (q + 32#64) a4) (q + 16#64) a2 ∧
      Rd (setCell (setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1)
        (q + 16#64) a2) (q + 24#64) a3) (q + 32#64) a4) (q + 24#64) a3 ∧
      Rd (setCell (setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1)
        (q + 16#64) a2) (q + 24#64) a3) (q + 32#64) a4) (q + 32#64) a4 ∧
      ∀ addr : Word, ¬ (q.toNat ≤ addr.toNat ∧ addr.toNat < q.toNat + 40) →
        setCell (setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64)
          a2) (q + 24#64) a3) (q + 32#64) a4 addr = m addr := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have e0 : q + 0#64 = q := by simp
  have e8 : (q + 8#64).toNat = q.toNat + 8 := by bv_omega
  have e16 : (q + 16#64).toNat = q.toNat + 16 := by bv_omega
  have e24 : (q + 24#64).toNat = q.toNat + 24 := by bv_omega
  have e32 : (q + 32#64).toNat = q.toNat + 32 := by bv_omega
  rw [e0]
  refine ⟨?_, ?_, ?_, ?_, Rd.here _ _ _, fun addr ha => ?_⟩
  · exact ((((Rd.here m q a0).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))
  · exact (((Rd.here _ (q + 8#64) a1).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))
  · exact ((Rd.here _ (q + 16#64) a2).frame _ (NE (by omega))).frame _ (NE (by omega))
  · exact (Rd.here _ (q + 24#64) a3).frame _ (NE (by omega))
  · rw [setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]

/-- Writing the four cells of a branch record. -/
theorem rec4 (m : Word → Option (PanValue Word)) (q a0 a1 a2 a4 : Word)
    (hq : q.toNat + 40 < 2 ^ 64) :
    Rd (setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64) a2)
        (q + 32#64) a4) q a0 ∧
      Rd (setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64) a2)
        (q + 32#64) a4) (q + 8#64) a1 ∧
      Rd (setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64) a2)
        (q + 32#64) a4) (q + 16#64) a2 ∧
      Rd (setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64) a2)
        (q + 32#64) a4) (q + 32#64) a4 ∧
      ∀ addr : Word, ¬ (q.toNat ≤ addr.toNat ∧ addr.toNat < q.toNat + 40) →
        setCell (setCell (setCell (setCell m (q + 0#64) a0) (q + 8#64) a1) (q + 16#64) a2)
          (q + 32#64) a4 addr = m addr := by
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have e0 : q + 0#64 = q := by simp
  have e8 : (q + 8#64).toNat = q.toNat + 8 := by bv_omega
  have e16 : (q + 16#64).toNat = q.toNat + 16 := by bv_omega
  have e32 : (q + 32#64).toNat = q.toNat + 32 := by bv_omega
  rw [e0]
  refine ⟨?_, ?_, ?_, Rd.here _ _ _, fun addr ha => ?_⟩
  · exact (((Rd.here m q a0).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))
  · exact ((Rd.here _ (q + 8#64) a1).frame _ (NE (by omega))).frame _ (NE (by omega))
  · exact (Rd.here _ (q + 16#64) a2).frame _ (NE (by omega))
  · rw [setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega))]

set_option maxHeartbeats 16000000 in
/-- An extension: the walk stops when the key leaves the segment, and otherwise
pushes a record and descends to the child. -/
theorem dl_ext (hE : GuestEnv E) {Rg R : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {fv lim sp : Word} {ℓ0 : Nat}
    {key klen lv nd topv resv : Word}
    (c : DlCtx Rg R G M fv lim sp ℓ0 key klen lv nd topv resv s)
    (hK : R.Kd nd 2#64) (hLn : R.Lv nd lv.toNat)
    (hQ : ∀ l' g' m' gw' lv', DlS Rg G M fv lim ℓ0 key klen l' g' m' gw' lv' →
      (gw' = 0#64 ∨ lv.toNat < lv'.toNat) → Q (.normal l' g' m' s.ffi)) :
    WPs E s (.dec "seg" .one (.load .one (.op .add [.var .local "node", .const 32#64]))
      (.dec "sl" .one (.load .one (.op .add [.var .local "node", .const 40#64]))
        (.decCall "pl" .one "common_prefix_length"
          [.var .local "seg", .var .local "sl",
            .op .add [.var .local "key", .var .local "level"],
            .op .sub [.var .local "klen", .var .local "level"]]
          (.ite (.cmp .lower (.var .local "pl") (.var .local "sl"))
            (.assign .local "res" (.var .local "node"))
            (.decCall "fr" .one "scratch_alloc" [.const 40#64]
              (.seq (.store (.op .add [.var .local "fr", .const 0#64]) (.var .local "top"))
                (.seq (.store (.op .add [.var .local "fr", .const 8#64]) (.var .local "node"))
                  (.seq (.store (.op .add [.var .local "fr", .const 16#64]) (.const 2#64))
                    (.seq (.store (.op .add [.var .local "fr", .const 24#64])
                        (.var .local "seg"))
                      (.seq (.store (.op .add [.var .local "fr", .const 32#64])
                          (.var .local "sl"))
                        (.seq (.assign .local "top" (.var .local "fr"))
                          (.seq (.assign .local "node"
                              (.load .one (.op .add [.var .local "node", .const 48#64])))
                            (.seq (.assign .local "level"
                                (.op .add [.var .local "level", .var .local "sl"]))
                              (.assign .local "go" (.const 1#64))))))))))))))) Q := by
  have hL := c.loc
  have hW := c.w
  have hF := c.hF
  have hfs := c.fs
  have hsl := c.sl
  have hlim := lim.isLt
  have hlvk := c.lv
  have hklen := klen.isLt
  obtain ⟨hNd, hRd, hlo, htop, h8⟩ := hW.kd hK
  have hsz2 : nodeSize 2#64 = 56 := by decide
  obtain ⟨sg0, nl0, r1, r2', -⟩ := hW.seg hNd hRd (Or.inr rfl)
  obtain ⟨sgl, cx, r2, hn1, r3, hch⟩ := hW.ext hK
  have e1 : sgl = nl0 := Rd.inj r2 r2'
  subst e1
  have ekl : (klen - lv).toNat = klen.toNat - lv.toNat := by
    rw [BitVec.toNat_sub]
    omega
  have e48 : (nd + 48#64).toNat = nd.toNat + 48 := by bv_omega
  refine WPs.dec (w := sg0) (eval_load_rd hE (eval_addc hE 32#64 hL.node) r1) ?_
  refine WPs.dec (w := sgl) (eval_load_rd hE (eval_addc hE 40#64 (by lk [hL.node])) r2) ?_
  refine WPs.decCall_ret (fun vp g m ffi hret => ?_)
  obtain ⟨p, rfl, rfl, rfl, rfl, hp1, hp2⟩ := common_prefix_ret hE hret (a := sg0) (al := sgl)
    (b := key + lv) (bl := klen - lv) (of_eval (by lk [])) (of_eval (by lk []))
    (of_eval (by ev [hL.key, hL.level])) (of_eval (by ev [hL.klen, hL.level]))
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qkey : L "key" = some (.word key) := by rw [hLL]; lk [hL.key]
  have qklen : L "klen" = some (.word klen) := by rw [hLL]; lk [hL.klen]
  have qlv : L "level" = some (.word lv) := by rw [hLL]; lk [hL.level]
  have qnode : L "node" = some (.word nd) := by rw [hLL]; lk [hL.node]
  have qtop : L "top" = some (.word topv) := by rw [hLL]; lk [hL.top]
  have qres : L "res" = some (.word resv) := by rw [hLL]; lk [hL.res]
  have qgo : L "go" = some (.word 0#64) := by rw [hLL]; lk [hL.go]
  have qseg : L "seg" = some (.word sg0) := by rw [hLL]; lk []
  have qsl : L "sl" = some (.word sgl) := by rw [hLL]; lk []
  have qpl : L "pl" = some (.word p) := by rw [hLL]; lk []
  clear hLL
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  simp only [evalF_local, qpl, qsl, Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · rename_i h0
    -- the whole segment matches: push a record and descend
    have hpe : p.toNat = sgl.toNat := by
      by_contra hne
      have hl : p < sgl := by rw [BitVec.lt_def]; omega
      rw [h0] at hwv
      simp [evalPanCmp, hl] at hwv
    have elv : (lv + sgl).toNat = lv.toNat + sgl.toNat := by
      rw [BitVec.toNat_add]
      omega
    refine WPs.decCall_ret (fun vq g1 m1 f1 hret1 => ?_)
    obtain ⟨rfl, rfl, q, rfl, rfl, hq1, hq2, hq8⟩ := scratchalloc_ret hE hret1 (pv := sp)
      (fv := fv) (nv := 40#64) (eval_const _ _) c.gsp c.gfv c.fs
    have hq2' : q.toNat + 40 ≤ sp.toNat := by simpa using hq2
    obtain ⟨c0, c1, c2, c3, c4, hfr⟩ := rec5 s.memory q topv nd 2#64 sg0 sgl (by omega)
    obtain ⟨hbelow, hprev⟩ := c.below (Reg.Le.addSg R nd sg0 sgl) hq2' hfr
    have W5 := (hW.learn_sg hK (Or.inr rfl) r1 r2).scratch
      (g' := updatePanValueMap s.globals "scratch_ptr" (.word q))
      (fun x hx => by simp [update_lookup, hx]) (fun a ha => hfr a (by omega))
    have rcx5 := r3
    unfold Rd at rcx5
    rw [← hfr (nd + 48#64) (by omega)] at rcx5
    have hq0 : q ≠ 0#64 := by
      rintro rfl
      simp at hq1
      omega
    have hst5 := DelStack.ext (R := R.addSg nd sg0 sgl) (sp := q) (lim := lim) (ℓ0 := ℓ0) hq0 hq8
      (Nat.le_refl _) (by omega) hprev c0 c1 c2 c3 c4 hK hLn (Or.inr ⟨rfl, rfl, rfl⟩) hbelow
    rw [← elv] at hst5
    refine WPs.seq_store hE (addr := q + 0#64) (w := topv) (eval_addc hE 0#64 (by lk []))
      (of_eval (by lk [qtop])) ?_
    refine WPs.seq_store hE (addr := q + 8#64) (w := nd) (eval_addc hE 8#64 (by lk []))
      (of_eval (by lk [qnode])) ?_
    refine WPs.seq_store hE (addr := q + 16#64) (w := 2#64) (eval_addc hE 16#64 (by lk []))
      (of_eval (eval_const _ _)) ?_
    refine WPs.seq_store hE (addr := q + 24#64) (w := sg0) (eval_addc hE 24#64 (by lk []))
      (of_eval (by lk [qseg])) ?_
    refine WPs.seq_store hE (addr := q + 32#64) (w := sgl) (eval_addc hE 32#64 (by lk []))
      (of_eval (by lk [qsl])) ?_
    refine WPs.seq_asg (old := topv) (w := q) (by lk [qtop]) (of_eval (by lk [])) ?_
    refine WPs.seq_asg (old := nd) (w := cx) (by lk [qnode])
      (eval_load_rd hE (eval_addc hE 48#64 (by lk [qnode])) rcx5) ?_
    refine WPs.seq_asg (old := lv) (w := lv + sgl) (by lk [qlv]) (of_eval (by ev [qlv, qsl])) ?_
    refine WPs.assign (old := 0#64) (w := 1#64) (by lk [qgo]) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact hQ _ _ _ 1#64 (lv + sgl) (c.push (R' := R.addSg nd sg0 sgl) (Reg.Le.addSg R nd sg0 sgl)
      (q := q) (nd' := cx) (res' := resv) hq1 hq2' W5
      (fun x hx => by simp [update_lookup, hx]) (by simp [update_lookup]) hfr
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qkey])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qklen])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qres])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      hst5 (by omega) hch
      (fun hc0 => by
        rw [elv]
        exact hW.ext_lv hK (hW.cv_ext hK hLn r2) r3 hc0)) (Or.inr (by omega))
  · -- the key leaves the segment: nothing to delete
    refine WPs.assign (old := resv) (w := nd) qres (of_eval (by lk [qnode])) ?_
    simp only [restorePanValueFfiLocal]
    exact hQ _ _ _ 0#64 lv (c.stop (res' := nd) (nd' := nd) (Reg.Le.refl R) hW (fun _ _ => rfl)
      (fun _ _ => rfl)
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qkey])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qklen])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qlv])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qnode])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qtop])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
      (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, qgo])
      (Or.inr ⟨2#64, hK, by decide, hLn⟩)) (Or.inl rfl)

end InitECandidate.Solver.GuestBound
