import InitECandidate.Solver.GuestBound.TrieMptNew
import InitECandidate.Solver.GuestBound.DecCallAt
import InitECandidate.Solver.GuestBound.Fns.L0C1
import InitECandidate.Solver.GuestBound.Fns.L2C6
import InitECandidate.Solver.GuestBound.Fns.L2C7
import InitECandidate.Solver.GuestBound.Fns.L1C0
import InitECandidate.Solver.GuestBound.Fns.L0C10

/-!
# Step bounds of `decode_witness_to_mpt` and `mpt_from_witness`
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A statement with an unconditional cost whose normal results satisfy `Mid`. -/
theorem Triple.of_wps_mid {P Mid : St σ → Prop} {Q : Result σ → Prop} {p : Prog Word} {B : Nat}
    (hc : Costs E p B) (hQ : ∀ r, Q r)
    (hp : ∀ s, P s → WPs E s p (fun r => match r with
      | .normal l g m f => Mid ⟨l, g, m, f⟩
      | r => Q r)) :
    Triple E P p B (fun r => match r with
      | .normal l g m f => Mid ⟨l, g, m, f⟩
      | r => Q r) := by
  intro fuel s r n hP hrun hne
  refine ⟨(hc fuel s r n trivial hrun hne).1, ?_⟩
  rcases hp s hP r (Runs.of_run hrun) with hst | hq
  · cases r with
    | normal l g m f => exact absurd hst Stopped.not_normal
    | _ => exact hQ _
  · exact hq

local notation "DW_ITE1" => ((Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "is_empty") (Exp.const (BitVec.ofNat 64 0)))
              (Prog.return (Exp.const (BitVec.ofNat 64 0)))
              Prog.skip) : Prog Word)

local notation "DW_ITE2" => ((Prog.ite (Exp.cmp Cmp.equal (Exp.rField 0 (Exp.var VarKind.local "r")) (Exp.const (BitVec.ofNat 64 0)))
                  (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 1))])
                  Prog.skip) : Prog Word)

local notation "DW_TAIL" => ((Prog.seq
                    (Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "nd") (Exp.const (BitVec.ofNat 64 0)))
                      (Prog.decCall "h" Shape.one "alloc" [(Exp.const (BitVec.ofNat 64 32))]
                        (Prog.seq
                          (Prog.call (some (none, none)) "memcpy" [(Exp.var VarKind.local "h"), (Exp.var VarKind.local "root_hash"), (Exp.const (BitVec.ofNat 64 32))])
                          (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "nd"), (Exp.const (BitVec.ofNat 64 24))]) (Exp.var VarKind.local "h"))))
                      Prog.skip)
                    (Prog.return (Exp.var VarKind.local "nd"))) : Prog Word)

theorem dw_ite1_cost (hE : GuestEnv E) : Costs E DW_ITE1 100 := by
  have h : ∃ B, Costs E DW_ITE1 B ∧ B ≤ 100 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem dw_ite2_cost (hE : GuestEnv E) : Costs E DW_ITE2 100 := by
  have h : ∃ B, Costs E DW_ITE2 B ∧ B ≤ 100 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem dw_tail_cost (hE : GuestEnv E) : Costs E DW_TAIL (10 ^ 30) := by
  have h : ∃ B, Costs E DW_TAIL B ∧ B ≤ 10 ^ 30 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 16000000 in
/-- Step bound of `decode_witness_to_mpt` from a world-invariant state. -/
theorem decode_witness_to_mpt_cost (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "decode_witness_to_mpt" E.functions = some (parameters, body))
    (R0 : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (dbv rh sp0 fv : Word)
    (hdb : s.locals "db" = some (.word dbv)) (hrh : s.locals "root_hash" = some (.word rh))
    (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 185 := by
  have hbody := (fun_of_index 265 hE.functions (by guest_decl_at 265) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hall := Triple.decCallRun (E := E) (P := fun a => a = s)
    (P' := fun a => ∃ v, a = ⟨updatePanValueMap s.locals "is_empty" v, s.globals, s.memory,
      s.ffi⟩) "is_empty" Shape.one
    [Exp.var VarKind.local "root_hash", Exp.var VarKind.global "empty_trie_root",
      Exp.const (BitVec.ofNat 64 32)] (Fn.memeq hE) ?_
    (Triple.seq (Mid := fun a => ∃ v, a = ⟨updatePanValueMap s.locals "is_empty" v, s.globals,
        s.memory, s.ffi⟩) (Q := fun _ => True)
      (Triple.of_wps_mid (Q := fun _ => True) (Mid := fun a => ∃ v, a = ⟨updatePanValueMap s.locals
        "is_empty" v, s.globals, s.memory, s.ffi⟩) (dw_ite1_cost hE) (fun _ => trivial) ?_)
      (Triple.decCallRun (P' := fun a => ∃ (v : PanValue Word) (q0 q1 q2 : Word),
          a = ⟨updatePanValueMap (updatePanValueMap s.locals "is_empty" v) "r"
            (.rStruct [.word q0, .word q1, .word q2]), s.globals, s.memory, s.ffi⟩) "r"
        (Shape.comb [Shape.one, Shape.one, Shape.one])
        [Exp.var VarKind.local "db", Exp.var VarKind.local "root_hash"]
        (Fn.nodedb_lookup hE) ?_
        (Triple.seq (Mid := fun a => ∃ (v : PanValue Word) (q0 q1 q2 : Word),
            a = ⟨updatePanValueMap (updatePanValueMap s.locals "is_empty" v) "r"
              (.rStruct [.word q0, .word q1, .word q2]), s.globals, s.memory, s.ffi⟩)
          (Q := fun _ => True)
          (Triple.of_wps_mid (Q := fun _ => True) (Mid := fun a => ∃ (v : PanValue Word)
            (q0 q1 q2 : Word), a = ⟨updatePanValueMap (updatePanValueMap s.locals "is_empty" v) "r"
            (.rStruct [.word q0, .word q1, .word q2]), s.globals, s.memory, s.ffi⟩)
            (dw_ite2_cost hE) (fun _ => trivial) ?_)
          (Triple.decCallAt (f := "_decode_witness_node") (P' := fun _ => True) (B := 10 ^ 184) "nd"
            Shape.one
            [Exp.var VarKind.local "db", Exp.rField 1 (Exp.var VarKind.local "r"),
              Exp.rField 2 (Exp.var VarKind.local "r")] ?_ (fun _ _ _ _ _ _ _ _ => trivial)
            (Triple.of_costs (dw_tail_cost hE) (fun _ _ _ _ _ _ _ => trivial))))))
  · have hn' := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq, stepsCost_eq] at hn'
    refine Nat.le_trans hn' ?_
    decide +kernel
  · rintro a v g m ffi rfl hret -
    obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet
      (keepFn_sound (quietKeeper E) hE.functions 1 "memeq" memeq_quiet) hret.ret
    subst g m ffi
    exact ⟨v, rfl⟩
  · rintro a ⟨v, rfl⟩
    refine WPs.ite_both (fun w _ => ?_)
    split
    · exact WPs.skip ⟨v, rfl⟩
    · exact WPs.ret_ev (fun _ _ => trivial)
  · rintro a v g m ffi ⟨v0, rfl⟩ hret hsh
    obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet (nodedb_lookup_quiet hE) hret.ret
    subst g m ffi
    obtain ⟨q0, q1, q2, rfl⟩ := struct3_of_shape hsh
    exact ⟨v0, q0, q1, q2, rfl⟩
  · rintro a ⟨v, q0, q1, q2, rfl⟩
    refine WPs.ite_both (fun w _ => ?_)
    split
    · exact WPs.skip ⟨v, q0, q1, q2, rfl⟩
    · refine WPs.call_ret (fun vs g m ffi hret => ?_)
      obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet (mpt_fail_quiet hE) hret
      subst g m ffi
      exact ⟨v, q0, q1, q2, rfl⟩
  · rintro a ⟨v, q0, q1, q2, rfl⟩
    intro ps cbody values cl hlk hvalues hbind fuel' r' n' hrun' hne'
    have hparams := (fun_of_index 264 hE.functions (by guest_decl_at 264) (by decide +kernel)
      hlk).2
    have e1 : E.eval (⟨updatePanValueMap (updatePanValueMap s.locals "is_empty" v) "r"
        (.rStruct [.word q0, .word q1, .word q2]), s.globals, s.memory, s.ffi⟩ : St σ)
        (.rField 1 (.var .local "r")) = some (.word q1) := by
      rw [eval_rField _ 1 "r" [.word q0, .word q1, .word q2] (by lk [])]
      rfl
    have e2 : E.eval (⟨updatePanValueMap (updatePanValueMap s.locals "is_empty" v) "r"
        (.rStruct [.word q0, .word q1, .word q2]), s.globals, s.memory, s.ffi⟩ : St σ)
        (.rField 2 (.var .local "r")) = some (.word q2) := by
      rw [eval_rField _ 2 "r" [.word q0, .word q1, .word q2] (by lk [])]
      rfl
    have e0 : E.eval (⟨updatePanValueMap (updatePanValueMap s.locals "is_empty" v) "r"
        (.rStruct [.word q0, .word q1, .word q2]), s.globals, s.memory, s.ffi⟩ : St σ)
        (.var .local "db") = some (.word dbv) := by lk [hdb]
    simp only [evalArgs_cons, evalArgs_nil, e0, e1, e2, Option.map_some, Option.some.injEq]
      at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact decode_node_cost hE ps cbody hlk R0 fuel' ⟨cl, s.globals, s.memory, s.ffi⟩ r' n'
      dbv q1 q2 sp0 fv 0
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hW hsp hfv hfs hF hrun' hne'

theorem mfw_tail_cost (hE : GuestEnv E) :
    Costs E (Prog.call none "mpt_new" [(Exp.var VarKind.local "root"),
      (Exp.var VarKind.local "secured")] : Prog Word) 1000 := by
  have h : ∃ B, Costs E (Prog.call none "mpt_new" [(Exp.var VarKind.local "root"),
      (Exp.var VarKind.local "secured")] : Prog Word) B ∧ B ≤ 1000 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 8000000 in
/-- Step bound of `mpt_from_witness` from a world-invariant state. -/
theorem mpt_from_witness_cost (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "mpt_from_witness" E.functions = some (parameters, body))
    (R0 : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (dbv rh sp0 fv : Word)
    (hdb : s.locals "db" = some (.word dbv)) (hrh : s.locals "root_hash" = some (.word rh))
    (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 186 := by
  have hbody := (fun_of_index 269 hE.functions (by guest_decl_at 269) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hall := Triple.decCallAt (E := E) (f := "decode_witness_to_mpt") (P := fun a => a = s)
    (P' := fun _ => True) (B := 10 ^ 185) "root" Shape.one
    [Exp.var VarKind.local "db", Exp.var VarKind.local "root_hash"] ?_
    (fun _ _ _ _ _ _ _ _ => trivial)
    (Triple.of_costs (mfw_tail_cost hE) (fun _ _ _ _ _ _ _ => trivial))
  · have hn' := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq, stepsCost_eq] at hn'
    refine Nat.le_trans hn' ?_
    decide +kernel
  · rintro a rfl
    intro ps cbody values cl hlk hvalues hbind fuel' r' n' hrun' hne'
    have hparams := (fun_of_index 265 hE.functions (by guest_decl_at 265) (by decide +kernel)
      hlk).2
    simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local, hdb, hrh]
      at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact decode_witness_to_mpt_cost hE ps cbody hlk R0 fuel' ⟨cl, a.globals, a.memory, a.ffi⟩
      r' n' dbv rh sp0 fv
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hW hsp hfv hfs hF hrun' hne'

end InitECandidate.Solver.GuestBound
