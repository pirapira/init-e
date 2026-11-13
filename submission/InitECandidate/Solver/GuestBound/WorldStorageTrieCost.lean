import InitECandidate.Solver.GuestBound.WorldStorageTrie
import InitECandidate.Solver.GuestBound.TrieMptCost
import InitECandidate.Solver.GuestBound.Fns.L1C4
import InitECandidate.Solver.GuestBound.Fns.L5C0

/-!
# Step bound of `ws_storage_trie` under the world invariant
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

local notation "WS_ITE" => ((Prog.ite (Exp.cmp Cmp.notEqual (Exp.rField 0 (Exp.var VarKind.local "m")) (Exp.const (BitVec.ofNat 64 0)))
                (Prog.return (Exp.op BinOp.sub [(Exp.rField 1 (Exp.var VarKind.local "m")), (Exp.const (BitVec.ofNat 64 1))]))
                Prog.skip) : Prog Word)

local notation "WS_TAIL" => ((Prog.seq
                  (Prog.call (some (none, none)) "htab_set" [(Exp.var VarKind.local "t"), (Exp.var VarKind.local "root"), (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 1))])])
                  (Prog.return (Exp.var VarKind.local "node"))) : Prog Word)

theorem ws_ite_cost (hE : GuestEnv E) : Costs E WS_ITE 100 := by
  have h : ∃ B, Costs E WS_ITE B ∧ B ≤ 100 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

theorem ws_tail_cost (hE : GuestEnv E) : Costs E WS_TAIL (10 ^ 60) := by
  have h : ∃ B, Costs E WS_TAIL B ∧ B ≤ 10 ^ 60 := ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 16000000 in
/-- Step bound of `ws_storage_trie` from a world-invariant state. -/
theorem ws_storage_trie_cost (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "ws_storage_trie" E.functions = some (parameters, body))
    (R0 : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (root wsv t dbv sp0 fv : Word)
    (hroot : s.locals "root" = some (.word root)) (hws : s.globals "ws" = some (.word wsv))
    (hct : R0.Cn (wsv + 32#64) t) (hcd : R0.Cn (wsv + 0#64) dbv)
    (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 186 := by
  have hbody := (fun_of_index 368 hE.functions (by guest_decl_at 368) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hall := Triple.dec (E := E) (P := fun a => a = s)
    (P' := fun a => a = ⟨updatePanValueMap s.locals "t" (.word t), s.globals, s.memory, s.ffi⟩)
    "t" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ws"),
      (Exp.const (BitVec.ofNat 64 32))])) ?_
    (Triple.decCallRun (P' := fun a => ∃ o0 o1 : Word, a = ⟨updatePanValueMap
        (updatePanValueMap s.locals "t" (.word t)) "m" (.rStruct [.word o0, .word o1]), s.globals,
        s.memory, s.ffi⟩) "m" (Shape.comb [Shape.one, Shape.one])
      [Exp.var VarKind.local "t", Exp.var VarKind.local "root"] (Fn.htab_get hE) ?_
      (Triple.seq (Mid := fun a => ∃ o0 o1 : Word, a = ⟨updatePanValueMap
          (updatePanValueMap s.locals "t" (.word t)) "m" (.rStruct [.word o0, .word o1]),
          s.globals, s.memory, s.ffi⟩) (Q := fun _ => True)
        (Triple.of_wps_mid (Q := fun _ => True) (Mid := fun a => ∃ o0 o1 : Word,
          a = ⟨updatePanValueMap (updatePanValueMap s.locals "t" (.word t)) "m"
            (.rStruct [.word o0, .word o1]), s.globals, s.memory, s.ffi⟩)
          (ws_ite_cost hE) (fun _ => trivial) ?_)
        (Triple.decCallAt (f := "decode_witness_to_mpt") (P' := fun _ => True) (B := 10 ^ 185)
          "node" Shape.one
          [Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ws"),
            (Exp.const (BitVec.ofNat 64 0))]), Exp.var VarKind.local "root"] ?_
          (fun _ _ _ _ _ _ _ _ => trivial)
          (Triple.of_costs (ws_tail_cost hE) (fun _ _ _ _ _ _ _ => trivial)))))
  · have hn' := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq, stepsCost_eq] at hn'
    refine Nat.le_trans hn' ?_
    decide +kernel
  · rintro a v rfl hval -
    have := eval_load_rd hE (eval_gaddc hE 32#64 hws) (hW.cell hct) v hval
    subst this
    rfl
  · rintro a v g m ffi rfl hret hsh
    obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet (htab_get_quiet hE) hret.ret
    subst g m ffi
    obtain ⟨o0, o1, rfl⟩ := struct2_of_shape hsh
    exact ⟨o0, o1, rfl⟩
  · rintro a ⟨o0, o1, rfl⟩
    refine WPs.ite_both (fun w _ => ?_)
    split
    · exact WPs.skip ⟨o0, o1, rfl⟩
    · exact WPs.ret_ev (fun _ _ => trivial)
  · rintro a ⟨o0, o1, rfl⟩
    intro ps cbody values cl hlk hvalues hbind fuel' r' n' hrun' hne'
    have hparams := (fun_of_index 265 hE.functions (by guest_decl_at 265) (by decide +kernel)
      hlk).2
    obtain ⟨v1, v2, g1, g2, rfl⟩ := evalArgs2_inv hvalues
    have h1 := eval_load_rd hE (s := (⟨updatePanValueMap (updatePanValueMap s.locals "t"
      (.word t)) "m" (.rStruct [.word o0, .word o1]), s.globals, s.memory, s.ffi⟩ : St σ))
      (eval_gaddc hE 0#64 hws) (hW.cell hcd) v1 g1
    subst h1
    have h2 := of_eval (w := root) (by lk [hroot]) v2 g2
    subst h2
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact decode_witness_to_mpt_cost hE ps cbody hlk R0 fuel' ⟨cl, s.globals, s.memory, s.ffi⟩
      r' n' dbv root sp0 fv
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hW hsp hfv hfs hF hrun' hne'

end InitECandidate.Solver.GuestBound
