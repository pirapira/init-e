import InitECandidate.Solver.GuestBound.TrieDelUnwind
import InitECandidate.Solver.GuestBound.TrieLoopCost

/-!
# The descent loop of the delete walk: state and the leaf case

`DlS` is the state of the descent after an iteration; `DlCtx` is what an
iteration starts from (after `go = 0`). An iteration either stops with a
result at the current level, or pushes a record and moves to a child one or
more levels down.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem Reg.Le.addSg (Rg : Reg) (a sp nl : Word) : Rg.Le (Rg.addSg a sp nl) :=
  ⟨rfl, rfl, fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ _ h => h, fun _ _ h => h,
    fun _ _ h => h, fun _ _ _ h => Or.inl h, fun _ h => h⟩

/-- The locals of the descent at the start of the conditional. -/
structure DlLoc (l : VarName → Option (PanValue Word)) (key klen lv nd topv resv : Word) :
    Prop where
  key : l "key" = some (.word key)
  klen : l "klen" = some (.word klen)
  level : l "level" = some (.word lv)
  node : l "node" = some (.word nd)
  top : l "top" = some (.word topv)
  res : l "res" = some (.word resv)
  go : l "go" = some (.word 0#64)

/-- The state of the delete descent. -/
def DlS (Rg : Reg) (G : VarName → Option (PanValue Word)) (M : Word → Option (PanValue Word))
    (fv lim : Word) (ℓ0 : Nat) (key klen : Word) (l g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (gw lv : Word) : Prop :=
  ∃ R topv resv nd sp ℓ, Rg.Le R ∧ WorldTJ R g m ∧
    (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = G x) ∧
    g "scratch_ptr" = some (.word sp) ∧ g "frame_mem_ptr" = some (.word fv) ∧
    fv.toNat ≤ sp.toNat ∧ sp.toNat ≤ lim.toNat ∧
    (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ lim.toNat ≤ addr.toNat) → m addr = M addr) ∧
    l "key" = some (.word key) ∧ l "klen" = some (.word klen) ∧ l "level" = some (.word lv) ∧
    l "node" = some (.word nd) ∧ l "top" = some (.word topv) ∧ l "res" = some (.word resv) ∧
    l "go" = some (.word gw) ∧ DelStack R m sp lim ℓ0 topv ℓ ∧
    (gw ≠ 0#64 → ℓ = lv.toNat ∧ lv.toNat ≤ klen.toNat ∧ (nd = 0#64 ∨ ∃ k, R.Kd nd k) ∧
      (nd ≠ 0#64 → R.Lv nd lv.toNat)) ∧
    (gw = 0#64 → resv = 0#64 ∨ ∃ k, R.Kd resv k ∧ k ≠ 0#64 ∧ R.Lv resv ℓ)

/-- What an iteration starts from. -/
structure DlCtx (Rg R : Reg) (G : VarName → Option (PanValue Word))
    (M : Word → Option (PanValue Word)) (fv lim sp : Word) (ℓ0 : Nat)
    (key klen lv nd topv resv : Word) (b : St σ) : Prop where
  loc : DlLoc b.locals key klen lv nd topv resv
  le : Rg.Le R
  w : WorldTJ R b.globals b.memory
  g : ∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → b.globals x = G x
  gsp : b.globals "scratch_ptr" = some (.word sp)
  gfv : b.globals "frame_mem_ptr" = some (.word fv)
  fs : fv.toNat ≤ sp.toNat
  sl : sp.toNat ≤ lim.toNat
  m : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ lim.toNat ≤ addr.toNat) → b.memory addr = M addr
  st : DelStack R b.memory sp lim ℓ0 topv lv.toNat
  lv : lv.toNat ≤ klen.toNat
  hF : 2952790016 ≤ fv.toNat

/-- The iteration stops: only the heap changed, the registry grew, and the
result sits at the current level. -/
theorem DlCtx.stop {Rg R R' : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {fv lim sp : Word} {ℓ0 : Nat}
    {key klen lv nd topv resv : Word} {b : St σ}
    (c : DlCtx Rg R G M fv lim sp ℓ0 key klen lv nd topv resv b)
    {l' g' : VarName → Option (PanValue Word)} {m' : Word → Option (PanValue Word)}
    {res' nd' : Word} (hle : R.Le R') (hW' : WorldTJ R' g' m')
    (hg' : ∀ x, x ≠ "heap_ptr" → g' x = b.globals x)
    (hm' : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = b.memory addr)
    (l1 : l' "key" = some (.word key)) (l2 : l' "klen" = some (.word klen))
    (l3 : l' "level" = some (.word lv)) (l4 : l' "node" = some (.word nd'))
    (l5 : l' "top" = some (.word topv)) (l6 : l' "res" = some (.word res'))
    (l7 : l' "go" = some (.word 0#64))
    (hres : res' = 0#64 ∨ ∃ k, R'.Kd res' k ∧ k ≠ 0#64 ∧ R'.Lv res' lv.toNat) :
    DlS Rg G M fv lim ℓ0 key klen l' g' m' 0#64 lv := by
  have hF := c.hF
  have hfs := c.fs
  have hsl := c.sl
  refine ⟨R', topv, res', nd', sp, lv.toNat, c.le.trans hle, hW',
    fun x h1 h2 => (hg' x h1).trans (c.g x h1 h2), by rw [hg' _ (by decide)]; exact c.gsp,
    by rw [hg' _ (by decide)]; exact c.gfv, c.fs, c.sl, fun addr ha => ?_, l1, l2, l3, l4, l5, l6,
    l7, (c.st.mono hle).frame (fun x hx _ => hm' x (Or.inr (by omega))),
    fun h => absurd rfl h, fun _ => hres⟩
  rcases ha with ha | ha
  · exact (hm' addr (Or.inl ha)).trans (c.m addr (Or.inl ha))
  · exact (hm' addr (Or.inr (by omega))).trans (c.m addr (Or.inr ha))

/-- The context after a change of the heap only (and of locals other than the loop's). -/
theorem DlCtx.heap {Rg R : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {fv lim sp : Word} {ℓ0 : Nat}
    {key klen lv nd topv resv : Word} {b b' : St σ}
    (c : DlCtx Rg R G M fv lim sp ℓ0 key klen lv nd topv resv b)
    (hl : DlLoc b'.locals key klen lv nd topv resv) (hg : b'.globals = b.globals)
    (hW' : WorldTJ R b'.globals b'.memory)
    (hm' : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      b'.memory addr = b.memory addr) :
    DlCtx Rg R G M fv lim sp ℓ0 key klen lv nd topv resv b' := by
  have hF := c.hF
  have hfs := c.fs
  have hsl := c.sl
  refine ⟨hl, c.le, hW', by rw [hg]; exact c.g, by rw [hg]; exact c.gsp, by rw [hg]; exact c.gfv,
    c.fs, c.sl, fun addr ha => ?_, c.st.frame (fun x hx _ => hm' x (Or.inr (by omega))), c.lv,
    c.hF⟩
  rcases ha with ha | ha
  · exact (hm' addr (Or.inl ha)).trans (c.m addr (Or.inl ha))
  · exact (hm' addr (Or.inr (by omega))).trans (c.m addr (Or.inr ha))

set_option maxHeartbeats 8000000 in
/-- A leaf: it stays, or disappears when its key is the remaining key. -/
theorem dl_leaf (hE : GuestEnv E) {Rg R : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {fv lim sp : Word} {ℓ0 : Nat}
    {key klen lv nd topv resv : Word}
    (c : DlCtx Rg R G M fv lim sp ℓ0 key klen lv nd topv resv s)
    (hK : R.Kd nd 1#64) (hLn : R.Lv nd lv.toNat)
    (hQ : ∀ l' g' m' gw' lv', DlS Rg G M fv lim ℓ0 key klen l' g' m' gw' lv' →
      (gw' = 0#64 ∨ lv.toNat < lv'.toNat) → Q (.normal l' g' m' s.ffi)) :
    WPs E s (.seq (.assign .local "res" (.var .local "node"))
      (.ite (.cmp .equal (.load .one (.op .add [.var .local "node", .const 40#64]))
          (.op .sub [.var .local "klen", .var .local "level"]))
        (.decCall "eq" .one "memeq"
          [.load .one (.op .add [.var .local "node", .const 32#64]),
            .op .add [.var .local "key", .var .local "level"],
            .op .sub [.var .local "klen", .var .local "level"]]
          (.ite (.cmp .notEqual (.var .local "eq") (.const 0#64))
            (.assign .local "res" (.const 0#64)) .skip))
        .skip)) Q := by
  have hL := c.loc
  have hkeep : (0#64 : Word) = 0#64 ∨ ∃ k, R.Kd (0#64 : Word) k ∧ k ≠ 0#64 ∧
      R.Lv (0#64 : Word) lv.toNat := Or.inl rfl
  have hnode : nd = 0#64 ∨ ∃ k, R.Kd nd k ∧ k ≠ 0#64 ∧ R.Lv nd lv.toNat :=
    Or.inr ⟨1#64, hK, by decide, hLn⟩
  refine WPs.seq_asg (old := resv) (w := nd) hL.res (of_eval (by lk [hL.node])) ?_
  refine WPs.ite_both (fun w _ => ?_)
  split
  · exact WPs.skip (hQ _ _ _ 0#64 lv (c.stop (res' := nd) (nd' := nd) (Reg.Le.refl R) c.w (fun _ _ => rfl)
      (fun _ _ => rfl) (by lk [hL.key]) (by lk [hL.klen]) (by lk [hL.level]) (by lk [hL.node])
      (by lk [hL.top]) (by lk []) (by lk [hL.go]) hnode) (Or.inl rfl))
  · refine WPs.decCall_word (fun e g m ffi hret => ?_)
    obtain ⟨rfl, rfl, rfl⟩ := CalleeRet.quiet
      (keepFn_sound (quietKeeper E) hE.functions 1 "memeq" memeq_quiet) hret
    refine WPs.ite_both (fun w2 _ => ?_)
    split
    · refine WPs.skip ?_
      simp only [restorePanValueFfiLocal]
      exact hQ _ _ _ 0#64 lv (c.stop (res' := nd) (nd' := nd) (Reg.Le.refl R) c.w (fun _ _ => rfl)
        (fun _ _ => rfl)
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.key])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.klen])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.level])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.node])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.top])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.go])
        hnode) (Or.inl rfl)
    · refine WPs.assign (old := nd) (w := 0#64) (by lk []) (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      exact hQ _ _ _ 0#64 lv (c.stop (res' := 0#64) (nd' := nd) (Reg.Le.refl R) c.w
        (fun _ _ => rfl) (fun _ _ => rfl)
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.key])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.klen])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.level])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.node])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.top])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup])
        (by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL.go])
        hkeep) (Or.inl rfl)

end InitECandidate.Solver.GuestBound
