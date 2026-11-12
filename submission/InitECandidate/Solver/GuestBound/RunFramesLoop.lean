import InitECandidate.Solver.GuestBound.SepFrameOp2

/-!
# The interpreter loop, against two obligations

`run_frames` is `var go = 1; while go != 0 { BODY }; return 0`. Each iteration
either dispatches one opcode (`rfDispatch`: `op_dispatch` with the `EvmErr`
handler `frame_exception`) or ends the current frame (`rfEnd`:
`frame_epilogue`, then leave the loop or `finish_child`).

`rf_loop` proves the step bound of the loop from an abstract machine invariant
`Inv` with a measure `μ`, given for the two blocks
* a cost bound, and
* that from an `Inv` state they stop, or end normally in an `Inv` state with a
  smaller measure (the end block may instead clear `go`).

What remains for the interpreter is to supply `Inv`, `μ` and these facts.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- `go != 0`. -/
def rfCond : Exp Word := 
  (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "go") (Exp.const (BitVec.ofNat 64 0)))

/-- The continuation record says the frame was ended by an exception. -/
def rfC1 : Exp Word := 
  (Exp.cmp Cmp.notEqual (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "cur_cont"), (Exp.const (BitVec.ofNat 64 32))])) (Exp.const (BitVec.ofNat 64 0)))

/-- The frame's running flag is clear. -/
def rfC2 : Exp Word := 
  (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ev"), (Exp.const (BitVec.ofNat 64 104))])) (Exp.const (BitVec.ofNat 64 0)))

/-- The program counter of the frame. -/
def rfPc : Exp Word := 
  (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ev"), (Exp.const (BitVec.ofNat 64 0))]))

/-- The program counter is past the code. -/
def rfC3 : Exp Word := 
  (Exp.cmp Cmp.notLower (Exp.var VarKind.local "pc") (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ev"), (Exp.const (BitVec.ofNat 64 56))])))

/-- `done != 0`. -/
def rfDoneCond : Exp Word := 
  (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "done") (Exp.const (BitVec.ofNat 64 0)))

/-- Dispatch one opcode; `EvmErr` is handled by `frame_exception`. -/
def rfDispatch : Prog Word := 
  (Prog.call (some (none, (some ("EvmErr", "err", (Prog.call (some (none, none)) "frame_exception" [(Exp.var VarKind.local "err")]))))) "op_dispatch" [(Exp.loadByte (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ev"), (Exp.const (BitVec.ofNat 64 48))])), (Exp.var VarKind.local "pc")]))])

/-- End the current frame. -/
def rfEnd : Prog Word := 
  (Prog.seq Prog.skip (Prog.seq (Prog.call (some (none, none)) "frame_epilogue" []) (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "cur_cont"), (Exp.const (BitVec.ofNat 64 16))])) (Exp.const (BitVec.ofNat 64 0))) (Prog.seq (Prog.assign VarKind.global "ev" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "cur_cont"), (Exp.const (BitVec.ofNat 64 0))]))) (Prog.seq (Prog.assign VarKind.global "cur_cont" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "cur_cont"), (Exp.const (BitVec.ofNat 64 8))]))) (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 0))))) (Prog.dec "err2" Shape.one (Exp.const (BitVec.ofNat 64 0)) (Prog.call (some (none, (some ("EvmErr", "err2", (Prog.call (some (none, none)) "frame_exception" [(Exp.var VarKind.local "err2")]))))) "finish_child" [])))))

/-- One iteration of the loop. -/
def rfBody : Prog Word :=
  .dec "done" .one (.const 0#64)
    (.seq
      (.ite rfC1 (.assign .local "done" (.const 1#64))
        (.ite rfC2 (.assign .local "done" (.const 1#64))
          (.dec "pc" .one rfPc
            (.ite rfC3 (.assign .local "done" (.const 1#64))
              (.dec "err" .one (.const 0#64) rfDispatch)))))
      (.ite rfDoneCond rfEnd .skip))

/-- The body of `run_frames`. -/
def rfProg : Prog Word :=
  .dec "go" .one (.const 1#64) (.seq (.while rfCond rfBody) (.return (.const 0#64)))

/-- What the loop needs of the two blocks. -/
structure RfSpec (E : Env σ) where
  /-- The machine invariant, on globals, memory and FFI state. -/
  Inv : (VarName → Option (PanValue Word)) → (Word → Option (PanValue Word)) → FfiState σ → Prop
  /-- The measure. -/
  μ : (VarName → Option (PanValue Word)) → (Word → Option (PanValue Word)) → Nat
  /-- What is known when an opcode is dispatched. -/
  DispatchPre : St σ → Prop
  BD : Nat
  BF : Nat
  costD : Costs E rfDispatch BD
  costF : Costs E rfEnd BF
  /-- The three tests that precede a dispatch came out false. -/
  pre : ∀ (a : St σ) (pcv : PanValue Word),
    E.eval ⟨updatePanValueMap a.locals "done" (.word 0#64), a.globals, a.memory, a.ffi⟩ rfC1 =
      some (.word 0#64) →
    E.eval ⟨updatePanValueMap a.locals "done" (.word 0#64), a.globals, a.memory, a.ffi⟩ rfC2 =
      some (.word 0#64) →
    E.eval ⟨updatePanValueMap a.locals "done" (.word 0#64), a.globals, a.memory, a.ffi⟩ rfPc =
      some pcv →
    E.eval ⟨updatePanValueMap (updatePanValueMap a.locals "done" (.word 0#64)) "pc" pcv,
      a.globals, a.memory, a.ffi⟩ rfC3 = some (.word 0#64) →
    DispatchPre ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap a.locals "done"
      (.word 0#64)) "pc" pcv) "err" (.word 0#64), a.globals, a.memory, a.ffi⟩
  /-- A dispatch keeps the invariant and lowers the measure. -/
  dispatch : ∀ a : St σ, Inv a.globals a.memory a.ffi → DispatchPre a →
    WPs E a rfDispatch (fun r => ∃ l g m f, r = .normal l g m f ∧ Inv g m f ∧
      μ g m < μ a.globals a.memory ∧ l "go" = a.locals "go" ∧ l "done" = a.locals "done")
  /-- Ending a frame leaves the loop, or keeps the invariant and lowers the measure. -/
  finish : ∀ a : St σ, Inv a.globals a.memory a.ffi →
    WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
      (l "go" = some (.word 0#64) ∨
        (l "go" = a.locals "go" ∧ Inv g m f ∧ μ g m < μ a.globals a.memory)))

/-- One iteration from an invariant state with `go = 1`. -/
theorem rf_body_wps (hE : GuestEnv E) (S : RfSpec E) (a : St σ)
    (hI : S.Inv a.globals a.memory a.ffi) (hgo : a.locals "go" = some (.word 1#64)) :
    WPs E a rfBody (fun r => ∃ l g m f, r = .normal l g m f ∧
      (l "go" = some (.word 0#64) ∨
        (l "go" = some (.word 1#64) ∧ S.Inv g m f ∧ S.μ g m < S.μ a.globals a.memory))) := by
  unfold rfBody
  refine WPs.dec_ev (fun v hv => ?_)
  rw [eval_const] at hv
  cases hv
  refine WPs.seqG (fun s' => ∃ l g m f, s' = ⟨l, g, m, f⟩ ∧ l "go" = some (.word 1#64) ∧
      S.Inv g m f ∧
      ((l "done" = some (.word 1#64) ∧ S.μ g m ≤ S.μ a.globals a.memory) ∨
        (l "done" = some (.word 0#64) ∧ S.μ g m < S.μ a.globals a.memory))) ?_ ?_
  · -- up to the dispatch
    have hset : ∀ (l : VarName → Option (PanValue Word)), l "go" = some (.word 1#64) →
        l "done" = some (.word 0#64) → ∀ Q' : Result σ → Prop,
        Q' (.normal (updatePanValueMap l "done" (.word 1#64)) a.globals a.memory a.ffi) →
        WPs E ⟨l, a.globals, a.memory, a.ffi⟩ (.assign .local "done" (.const 1#64)) Q' :=
      fun l _ hd Q' hq => WPs.assign (old := 0#64) (w := 1#64) hd (of_eval (eval_const _ _)) hq
    refine WPs.ite_both (fun w1 hw1 => ?_)
    split
    · rename_i hz1
      rw [hz1] at hw1
      refine WPs.ite_both (fun w2 hw2 => ?_)
      split
      · rename_i hz2
        rw [hz2] at hw2
        refine WPs.dec_ev (fun pcv hpc => ?_)
        refine WPs.ite_both (fun w3 hw3 => ?_)
        split
        · rename_i hz3
          rw [hz3] at hw3
          refine WPs.dec_ev (fun ev0 hev0 => ?_)
          rw [eval_const] at hev0
          cases hev0
          refine WPs.conseq (S.dispatch _ hI (S.pre a pcv hw1 hw2 hpc hw3)) ?_
          rintro r ⟨l, g, m, f, rfl, hI', hμ, hgo', hdone'⟩
          simp only [restorePanValueFfiLocal]
          refine ⟨_, _, _, _, rfl, ?_, hI', Or.inr ⟨?_, hμ⟩⟩
          · simp (config := { decide := true }) [restorePanValueLocal, hgo', update_lookup, hgo]
          · simp (config := { decide := true }) [restorePanValueLocal, hdone', update_lookup]
        · refine hset _ (by simp (config := { decide := true }) [update_lookup, hgo])
            (by simp (config := { decide := true }) [update_lookup]) _ ?_
          simp only [restorePanValueFfiLocal]
          refine ⟨_, _, _, _, rfl, ?_, hI, Or.inl ⟨?_, Nat.le_refl _⟩⟩
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hgo]
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      · refine hset _ (by simp (config := { decide := true }) [update_lookup, hgo])
          (by simp (config := { decide := true }) [update_lookup]) _ ?_
        refine ⟨_, _, _, _, rfl, ?_, hI, Or.inl ⟨?_, Nat.le_refl _⟩⟩
        · simp (config := { decide := true }) [update_lookup, hgo]
        · simp (config := { decide := true }) [update_lookup]
    · refine hset _ (by simp (config := { decide := true }) [update_lookup, hgo])
        (by simp (config := { decide := true }) [update_lookup]) _ ?_
      refine ⟨_, _, _, _, rfl, ?_, hI, Or.inl ⟨?_, Nat.le_refl _⟩⟩
      · simp (config := { decide := true }) [update_lookup, hgo]
      · simp (config := { decide := true }) [update_lookup]
  · -- after it
    rintro _ ⟨l, g, m, f, rfl, hgo1, hI1, hcase⟩
    refine WPs.ite_both (fun w hw => ?_)
    rcases hcase with ⟨hd, hμ⟩ | ⟨hd, hμ⟩
    · have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := 1#64) (by lk [hd]))
        (of_eval (w := 0#64) (eval_const _ _)) _ hw
      simp only [PanValue.word.injEq] at hcv
      split
      · rename_i hz
        rw [hz] at hcv
        simp [evalPanCmp] at hcv
      · refine WPs.conseq (S.finish _ hI1) ?_
        rintro r ⟨l', g', m', f', rfl, hout⟩
        simp only [restorePanValueFfiLocal]
        refine ⟨_, _, _, _, rfl, ?_⟩
        rcases hout with h0 | ⟨hg, hI', hμ'⟩
        · left
          simp (config := { decide := true }) [restorePanValueLocal, h0]
        · right
          refine ⟨?_, hI', Nat.lt_of_lt_of_le hμ' hμ⟩
          simp (config := { decide := true }) [restorePanValueLocal, hg, hgo1]
    · have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := 0#64) (by lk [hd]))
        (of_eval (w := 0#64) (eval_const _ _)) _ hw
      simp only [PanValue.word.injEq] at hcv
      split
      · refine WPs.skip ?_
        simp only [restorePanValueFfiLocal]
        refine ⟨_, _, _, _, rfl, Or.inr ⟨?_, hI1, hμ⟩⟩
        simp (config := { decide := true }) [restorePanValueLocal, hgo1]
      · rename_i hnz
        exact absurd (by rw [hcv]; simp [evalPanCmp]) hnz

/-- The cost of one iteration. -/
theorem rf_body_cost (S : RfSpec E) : Costs E rfBody (S.BD + S.BF + 200) := by
  have hA := Costs.assignLocal (E := E) "done" (.const 1#64)
  have hS := Costs.skip (E := E)
  have h := Costs.dec "done" .one (.const 0#64) (Costs.seq
    (Costs.ite rfC1 hA (Costs.ite rfC2 hA (Costs.dec "pc" .one rfPc (Costs.ite rfC3 hA
      (Costs.dec "err" .one (.const 0#64) S.costD)))))
    (Costs.ite rfDoneCond S.costF hS))
  refine Triple.consequence h (fun _ h => h) ?_ (fun _ h => h)
  simp only [stepCost_eq, rfC1, rfC2, rfC3, rfPc, rfDoneCond, expCost, expsCost]
  omega

/-- The variant of the loop: zero once `go` is cleared. -/
def rfNu (S : RfSpec E) (a : St σ) : Nat :=
  match a.locals "go" with
  | some (.word w) => if w = 0#64 then 0 else S.μ a.globals a.memory + 1
  | _ => 0

/-- The loop of `run_frames` from an invariant state: its step bound. -/
theorem rf_loop (hE : GuestEnv E) (S : RfSpec E) (s : St σ)
    (hI : S.Inv s.globals s.memory s.ffi) (hgo : s.locals "go" = some (.word 1#64)) :
    WPc E s (.while rfCond rfBody)
      ((S.μ s.globals s.memory + 1 + 1) * (expCost rfCond + (S.BD + S.BF + 200) + 1))
      (fun _ => True) := by
  refine WPc.while (I := fun a => a.locals "go" = some (.word 0#64) ∨
      (a.locals "go" = some (.word 1#64) ∧ S.Inv a.globals a.memory a.ffi)) (μ := rfNu S)
    (S.μ s.globals s.memory + 1) (Or.inr ⟨hgo, hI⟩) (by simp [rfNu, hgo]) ?_
    (fun _ _ _ _ => trivial)
  intro a hIa hct
  rcases hIa with h0 | ⟨h1, hIa⟩
  · obtain ⟨v, k, hc, hv⟩ := hct
    rw [cond_eq] at hc
    simp [rfCond, evalF_cmp hE.word, h0, eval_const, evalPanCmp] at hc
    obtain ⟨rfl, -⟩ := hc
    simp at hv
  · refine WPc.of_costs (rf_body_cost S) (WPs.conseq (rf_body_wps hE S a hIa h1) ?_)
    rintro r ⟨l, g, m, f, rfl, hout⟩
    rcases hout with h | ⟨h, hI', hμ⟩
    · exact ⟨Or.inl h, by simp [rfNu, h, h1]⟩
    · exact ⟨Or.inr ⟨h, hI'⟩, by simp [rfNu, h, h1]; omega⟩

/-- `run_frames` from an invariant state takes at most this many steps. -/
theorem run_frames_bound (hE : GuestEnv E) (S : RfSpec E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "run_frames" E.functions = some (parameters, body))
    (s : St σ) (hI : S.Inv s.globals s.memory s.ffi) (fuel : Nat) (r : Result σ) (n : Nat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ (S.μ s.globals s.memory + 1 + 1) * (expCost rfCond + (S.BD + S.BF + 200) + 1) + 10 := by
  have hbody := (fun_of_index 584 hE.functions (by guest_decl_at 584) (by decide +kernel)
    hlookup).1
  subst hbody
  have hw : WPc E s rfProg (panValueExpStepCost (.const 1#64 : Exp Word) +
      ((S.μ s.globals s.memory + 1 + 1) * (expCost rfCond + (S.BD + S.BF + 200) + 1) +
        (panValueExpStepCost (.const 0#64 : Exp Word) + 1) + 1) + 1) (fun _ => True) := by
    unfold rfProg
    refine WPc.dec (fun v hv => ?_)
    rw [eval_const] at hv
    cases hv
    refine WPc.seq (fun _ => True)
      ((rf_loop hE S (⟨updatePanValueMap s.locals "go" (.word 1#64), s.globals, s.memory,
          s.ffi⟩ : St σ) hI (by simp (config := { decide := true }) [update_lookup])).mono
        (Nat.le_refl _) (fun r _ => by cases r <;> exact True.intro))
      (fun s' _ => WPc.of_costs (Costs.return _) (WPs.of_true (fun _ => trivial)))
  have := hw.steps hrun hne
  simp only [stepCost_eq, expCost] at this
  omega

end InitECandidate.Solver.GuestBound
