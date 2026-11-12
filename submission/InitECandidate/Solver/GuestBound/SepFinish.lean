import InitECandidate.Solver.GuestBound.SepChain

/-!
# The end-of-frame block of `run_frames`

`rfEnd` is `frame_epilogue(); if kind == 0 { leave the loop } else { finish_child }`.
Proved here: the epilogue (given that `state_restore` keeps the world
assertion) and the exit branch. The `finish_child` branch is a hypothesis
(`ChildSpec`), stated on the chain invariant.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The test `kind == 0` on the continuation record. -/
def rfKindCond : Exp Word :=
  (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "cur_cont"), (Exp.const (BitVec.ofNat 64 16))])) (Exp.const (BitVec.ofNat 64 0)))

/-- Leave the loop: restore `ev` and `cur_cont`, clear `go`. -/
def rfExit : Prog Word :=
  (Prog.seq (Prog.assign VarKind.global "ev" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "cur_cont"), (Exp.const (BitVec.ofNat 64 0))]))) (Prog.seq (Prog.assign VarKind.global "cur_cont" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "cur_cont"), (Exp.const (BitVec.ofNat 64 8))]))) (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 0)))))

/-- End a child frame; `EvmErr` is handled by `frame_exception` on the parent. -/
def rfChild : Prog Word :=
  (Prog.dec "err2" Shape.one (Exp.const (BitVec.ofNat 64 0)) (Prog.call (some (none, (some ("EvmErr", "err2", (Prog.call (some (none, none)) "frame_exception" [(Exp.var VarKind.local "err2")]))))) "finish_child" []))

theorem rfEnd_eq : rfEnd = .seq .skip (.seq (.call (some (none, none)) "frame_epilogue" [])
    (.ite rfKindCond rfExit rfChild)) := rfl

/-- `state_restore(snap)` keeps the world assertion `W` and touches nothing else. -/
def RestoreSpec (E : Env σ) (W : Assn) : Prop :=
  ∀ parameters body, lookupPanFunction "state_restore" E.functions = some (parameters, body) →
    ∀ (s : St σ) (R : Assn), (W ⋆ R).holds s →
      WPr E s body (fun r => Trap r ∨ ∃ l g m, r = .returned l g m s.ffi [.word 0#64] ∧
        (W ⋆ R).holds (⟨l, g, m, s.ffi⟩ : St σ))

/-- The `finish_child` branch re-establishes the chain invariant at a smaller measure. -/
def ChildSpec (E : Env σ) (W : Assn) (D : Word → Prop) : Prop :=
  ∀ (a : St σ) (n : Nat) (F : Fr) (ps : List Fr) (R : Assn), ChainOk D F ps →
    F.gas + gasSum ps < 2 ^ 64 - 1 → F.mu + muSum ps ≤ n → F.C.kind ≠ 0#64 →
    (F.full ⋆ suspA ps ⋆ W ⋆ R).holds a →
    WPr E a rfChild (fun r => Trap r ∨ ∃ l g m, r = .normal l g m a.ffi ∧
      l "go" = a.locals "go" ∧ ∃ n', n' < n ∧ chainInv W D n' g m)

/-- A local assignment, whatever the value. -/
theorem WPr.assign_local_any {x : VarName} {e : Exp Word}
    (h : ∀ v, E.eval s e = some v →
      Q (.normal (updatePanValueMap s.locals x v) s.globals s.memory s.ffi)) :
    WPr E s (.assign .local x e) Q := by
  intro r hr
  rw [runs_assign_local] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl rfl
  | some y =>
    rw [hv] at hr
    simp only at hr
    split at hr
    · subst hr; exact Or.inr (h _ hv)
    · subst hr; exact Or.inl rfl

/-- `frame_epilogue(); rest`: the world assertion and its frame are kept. -/
theorem frame_epilogue_seq (hE : GuestEnv E) {W A : Assn} (hW : RestoreSpec E W) {q : Prog Word}
    (h : (W ⋆ A).holds s) (htrap : ∀ r, Trap r → Q r)
    (hq : ∀ g m, (W ⋆ A).holds (⟨s.locals, g, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, g, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "frame_epilogue" []) q) Q := by
  refine WPr.seq (fun s' => ∃ g m, s' = ⟨s.locals, g, m, s.ffi⟩ ∧ (W ⋆ A).holds s')
    (WPr.call_spec (fun r => Trap r ∨ ∃ l g m, r = .returned l g m s.ffi [.word 0#64] ∧
        (W ⋆ A).holds (⟨l, g, m, s.ffi⟩ : St σ)) ?_ ?_ ?_ ?_) ?_
  · intro parameters cbody values cl hlk _ _
    have hbody := (fun_of_index 582 hE.functions (by guest_decl_at 582) (by decide +kernel)
      hlk).1
    subst hbody
    refine WPr.seq (fun s' => ∃ g m, s' = ⟨cl, g, m, s.ffi⟩ ∧ (W ⋆ A).holds s')
      (WPr.ite_both (fun w _ => ?_)) ?_
    · split
      · exact WPr.skip ⟨_, _, rfl, Assn.holds_congr rfl rfl h⟩
      · refine WPr.call_spec (fun r => Trap r ∨ ∃ l g m, r = .returned l g m s.ffi [.word 0#64] ∧
          (W ⋆ A).holds (⟨l, g, m, s.ffi⟩ : St σ)) ?_ ?_ ?_ ?_
        · intro parameters2 cbody2 values2 cl2 hlk2 _ _
          exact hW parameters2 cbody2 hlk2 ⟨cl2, s.globals, s.memory, s.ffi⟩ A
            (Assn.holds_congr rfl rfl h)
        · rintro l g m ffi vs (ht | ⟨l', g', m', hC, hh⟩)
          · exact ht.elim
          · injection hC with _ hg hm hf _
            subst hg hm hf
            exact ⟨_, _, rfl, Assn.holds_congr rfl rfl hh⟩
        · rintro l g m ffi exc v (ht | ⟨_, _, _, hC, -⟩)
          · exact Or.inl ht
          · cases hC
        · rintro l g m ffi ev _
          exact Or.inl trivial
    · rintro _ ⟨g, m, rfl, hh⟩
      exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
        (Or.inr ⟨_, _, _, rfl, Assn.holds_congr rfl rfl hh⟩)
  · rintro l g m ffi vs (ht | ⟨l', g', m', hC, hh⟩)
    · exact ht.elim
    · injection hC with _ hg hm hf _
      subst hg hm hf
      exact ⟨_, _, rfl, Assn.holds_congr rfl rfl hh⟩
  · rintro l g m ffi exc v (ht | ⟨_, _, _, hC, -⟩)
    · exact htrap _ ht
    · cases hC
  · rintro l g m ffi ev _
    exact htrap _ trivial
  · rintro _ ⟨g, m, rfl, hh⟩
    exact hq g m hh

/-- The kind field read by the test of `rfEnd`. -/
theorem rfKind_eval (hE : GuestEnv E) {F : Fr} {A : Assn}
    (h : (F.full ⋆ A).holds s) (w : Word) (hc : E.eval s rfKindCond = some (.word w)) :
    (w = 0#64 ↔ F.C.kind ≠ 0#64) := by
  have h1 : (ExcExtraM F.e F.Z ⋆ (FrameOp F.M F.K F.e F.fv F.X ⋆ MemExtra F.e F.Y ⋆
      RecCells F.Z.cc F.C ⋆ AccCells F.e F.A) ⋆ A).holds s :=
    Assn.holds_perm h (by unfold Fr.full; ac_rfl)
  unfold ExcExtraM at h1
  have hcc : s.globals "cur_cont" = some (.word F.Z.cc) := Assn.glob_at h1 (by look)
  have h2 : (RecCells F.Z.cc F.C ⋆ (FrameOp F.M F.K F.e F.fv F.X ⋆ MemExtra F.e F.Y ⋆
      ExcExtraM F.e F.Z ⋆ AccCells F.e F.A) ⋆ A).holds s :=
    Assn.holds_perm h (by unfold Fr.full; ac_rfl)
  unfold RecCells at h2
  have hcv := eval_cmp_inv hE (op := .equal)
    (eval_load_at hE (addr := F.Z.cc + 16#64) (v := .word F.C.kind)
      (of_eval (by ev [eval_global, hcc])) h2 (by look))
    (of_eval (w := 0#64) (eval_const _ _)) _ hc
  simp only [PanValue.word.injEq] at hcv
  by_cases hk : F.C.kind = 0#64
  · rw [hk] at hcv
    simp [evalPanCmp] at hcv
    simp [hcv, hk]
  · simp [evalPanCmp, hk] at hcv
    simp [hcv, hk]

/-- The end-of-frame block on a chain of frames. -/
theorem finish_chain (hE : GuestEnv E) {W : Assn} {D : Word → Prop} (hW : RestoreSpec E W)
    (hC : ChildSpec E W D) (a : St σ) (n : Nat) (hI : chainInv W D n a.globals a.memory) :
    WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
      (l "go" = some (.word 0#64) ∨
        (l "go" = a.locals "go" ∧ ∃ n', n' < n ∧ chainInv W D n' g m))) := by
  obtain ⟨F, ps, R, hch, hgas, hmu, hh⟩ := hI
  have h0 : (F.full ⋆ suspA ps ⋆ W ⋆ R).holds a := by
    unfold Assn.holds
    rw [view_eq]
    exact hh
  refine WPr.wps (Q' := fun r => Trap r ∨ ∃ l g m, r = .normal l g m a.ffi ∧
      (l "go" = some (.word 0#64) ∨
        (l "go" = a.locals "go" ∧ ∃ n', n' < n ∧ chainInv W D n' g m))) ?_ ?_
  rotate_left
  · rintro r (ht | ⟨l, g, m, rfl, hr⟩)
    · exact Or.inl ht.stopped
    · exact Or.inr ⟨l, g, m, a.ffi, rfl, hr⟩
  rw [rfEnd_eq]
  refine WPr.seq (IsState a) (WPr.skip rfl) ?_
  intro a' ha
  have ha' : a' = a := ha
  rw [ha']
  clear ha ha' a'
  refine frame_epilogue_seq hE hW (A := F.full ⋆ suspA ps ⋆ R)
    (Assn.holds_perm h0 (by ac_rfl)) (fun r ht => Or.inl ht) (fun g m h1 => ?_)
  have h2 : (F.full ⋆ suspA ps ⋆ W ⋆ R).holds (⟨a.locals, g, m, a.ffi⟩ : St σ) :=
    Assn.holds_perm h1 (by ac_rfl)
  refine WPr.ite_both (fun w hw => ?_)
  have hk := rfKind_eval hE h2 w hw
  split
  · rename_i hw0
    refine WPr.conseq (hC ⟨a.locals, g, m, a.ffi⟩ n F ps R hch hgas hmu (hk.mp hw0) h2) ?_
    rintro r (ht | ⟨l, g', m', rfl, hgo, hn⟩)
    · exact Or.inl ht
    · exact Or.inr ⟨l, g', m', rfl, Or.inr ⟨hgo, hn⟩⟩
  · unfold rfExit
    refine WPr.seq (fun s' => ∃ g', s' = ⟨a.locals, g', m, a.ffi⟩)
      (WPr.assign_global_any (fun g' => ⟨g', rfl⟩)) ?_
    rintro _ ⟨g1, rfl⟩
    refine WPr.seq (fun s' => ∃ g', s' = ⟨a.locals, g', m, a.ffi⟩)
      (WPr.assign_global_any (fun g' => ⟨g', rfl⟩)) ?_
    rintro _ ⟨g2, rfl⟩
    refine WPr.assign_local_any (fun v hv => ?_)
    rw [eval_const] at hv
    cases hv
    exact Or.inr ⟨_, _, _, rfl, Or.inl (by simp [update_lookup])⟩

/-- `run_frames` from a chain of frames of measure at most `k`: the step bound,
given the remaining handlers, the two cost bounds, `state_restore` and the
`finish_child` branch. -/
theorem run_frames_bound_world (W : Assn) (D : Word → Prop) (hE : GuestEnv E)
    (hrest : ∀ f, f ∈ restOpsM → HandlerSpecM E f) (BD BF : Nat)
    (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (hW : RestoreSpec E W) (hC : ChildSpec E W D)
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "run_frames" E.functions = some (parameters, body))
    (s : St σ) (k : Nat) (hI : chainInv W D k s.globals s.memory) (fuel : Nat) (r : Result σ)
    (n : Nat) (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ (k + 1 + 1) * (expCost rfCond + (BD + BF + 200) + 1) + 10 :=
  run_frames_bound_chain W D hE hrest BD BF costD costF
    (fun a n hI => finish_chain hE hW hC a n hI) parameters body hlookup s k hI fuel r n hrun hne

end InitECandidate.Solver.GuestBound
