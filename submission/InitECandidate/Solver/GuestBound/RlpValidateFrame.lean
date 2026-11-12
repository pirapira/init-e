import InitECandidate.Solver.GuestBound.ScratchFrame
import InitECandidate.Solver.GuestBound.Fq12InvTail

/-!
# `_rlp_validate_items_body` writes only free scratch memory

The loop keeps `ScrKeep` relative to the entry state: its only stores go to
24-byte records it has just taken from the scratch arena.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Loop invariant: the frame relation, and the four loop variables are words. -/
def VbI (pv fv : Word) (s a : St σ) : Prop :=
  ScrKeep pv fv s a.globals a.memory a.ffi ∧
    ∃ tw pw ew gw : Word, a.locals "top" = some (.word tw) ∧ a.locals "pos" = some (.word pw) ∧
      a.locals "end" = some (.word ew) ∧ a.locals "go" = some (.word gw)

set_option maxHeartbeats 8000000 in
theorem rlp_validate_body_frame (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_rlp_validate_items_body" E.functions =
      some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv pw0 : Word) (hpw : s.locals "p" = some (.word pw0))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l g m, r = .returned l g m s.ffi [.word 0#64] ∧ ScrKeep pv fv s g m s.ffi := by
  have hbody := (fun_of_index 110 hE.functions (by guest_decl_at 110) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g m, r = .returned l g m s.ffi [.word 0#64] ∧
    ScrKeep pv fv s g m s.ffi)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := pw0) (of_eval (by lk [hpw])) ?_
  refine WPs.dec_ev (fun ve hve => ?_)
  obtain ⟨_, _, ew0, -, -, -, rfl⟩ := eval_op2_inv hE.word hve
  refine WPs.dec (w := 1#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l g m, r = .returned l g m s.ffi [.word 0#64] ∧
    ScrKeep pv fv s g m s.ffi) ?_ (by rintro r ⟨l, g, m, rfl, hk⟩; exact ⟨_, g, m, rfl, hk⟩)
  refine WPs.seqG (fun a => VbI pv fv s a) (WPs.loopG (I := VbI pv fv s)
    ⟨⟨rfl, fun _ _ => rfl, ⟨pv, hp, hfp, Nat.le_refl _⟩, fun _ _ => rfl⟩, 0#64, pw0, ew0, 1#64,
      by lk [], by lk [], by lk [], by lk []⟩ ?_ (fun a k hI _ => hI)) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨⟨hfa, hgl, ⟨qv, hq, hq1, hq2⟩, hfr⟩, tw, pw, ew, gw, htop, hpos,
      hend, hgo⟩ -
    simp only at hfa hgl hq hfr htop hpos hend hgo
    subst hfa
    have hfmp : ga "frame_mem_ptr" = some (.word fv) := by rw [hgl _ (by decide)]; exact hf
    refine WPs.ite_both (fun w _ => ?_)
    split
    · -- an item: read its header
      refine WPs.decCall_ret (fun v g m ffi hret => ?_)
      obtain ⟨hg, hm, hf', a, b, c, rfl⟩ := rlpheader_ret hE hret (lenv := ew - pw)
        (by ev [hend, hpos])
      subst g m ffi
      try dsimp only
      refine WPs.dec (w := pw + a) (of_eval (by ev [hpos, evalF_rField])) ?_
      try dsimp only
      refine WPs.dec (w := pw + a + b) (of_eval (by ev [hpos, evalF_rField])) ?_
      try dsimp only
      refine WPs.ite_both (fun w2 _ => ?_)
      split
      · refine WPs.assign (old := pw) (by lk [hpos]) (of_eval (w := pw + a + b) (by lk [])) ?_
        simp only [restorePanValueFfiLocal]
        exact ⟨⟨rfl, hgl, ⟨qv, hq, hq1, hq2⟩, hfr⟩, tw, pw + a + b, ew, gw,
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, htop],
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hend],
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hgo]⟩
      · -- a nested list: push a continuation record
        refine WPs.decCall_ret (fun v g m ffi hret => ?_)
        obtain ⟨hm, hf', rv, rfl, hg, r1, r2, r3⟩ := scratchalloc_ret hE hret (nv := 24#64)
          (eval_const _ _) hq hfmp hq1
        subst g m ffi
        rw [show (24#64 : Word).toNat = 24 by decide] at r2
        try dsimp only
        refine WPs.seq_store hE (addr := rv) (by lk []) (of_eval (w := pw + a + b) (by lk [])) ?_
        try dsimp only
        refine WPs.seq_store hE (addr := rv + 8#64) (by ev []) (of_eval (w := ew) (by lk [hend]))
          ?_
        try dsimp only
        refine WPs.seq_store hE (addr := rv + 16#64) (by ev [])
          (of_eval (w := tw) (by lk [htop])) ?_
        try dsimp only
        refine WPs.seq_assign (old := tw) (by lk [htop]) (of_eval (w := rv) (by lk [])) ?_
        try dsimp only
        refine WPs.seq_assign (old := pw) (by lk [hpos]) (of_eval (w := pw + a) (by lk [])) ?_
        try dsimp only
        refine WPs.assign (old := ew) (by lk [hend]) (of_eval (w := pw + a + b) (by lk [])) ?_
        simp only [restorePanValueFfiLocal]
        have hqv := qv.isLt
        have e8 : (rv + 8#64).toNat = rv.toNat + 8 := by
          rw [BitVec.toNat_add, show (8#64 : Word).toNat = 8 by decide]
          omega
        have e16 : (rv + 16#64).toNat = rv.toNat + 16 := by
          rw [BitVec.toNat_add, show (16#64 : Word).toNat = 16 by decide]
          omega
        refine ⟨⟨rfl, fun x hx => ?_, ⟨rv, by simp [update_lookup], r1, by omega⟩, fun x hx => ?_⟩,
          rv, pw + a, pw + a + b, gw,
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
          by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hgo]⟩
        · dsimp only
          rw [update_lookup, if_neg (by simpa using hx)]
          exact hgl x hx
        · dsimp only
          rw [setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [e16] at this; omega),
            setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [e8] at this; omega),
            setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; omega)]
          exact hfr x hx
    · -- the range is consumed: stop, or resume the enclosing list
      refine WPs.ite_both (fun w2 _ => ?_)
      split
      · refine WPs.seq (fun a' => ∃ w1 : Word, a' = ⟨updatePanValueMap la "pos" (.word w1), ga,
            ma, s.ffi⟩) (WPs.assign_load hE hpos (fun w1 => ⟨_, _, _, _, rfl, w1, rfl⟩)) ?_
        rintro _ ⟨w1, rfl⟩
        refine WPs.seq (fun a' => ∃ w3 : Word, a' = ⟨updatePanValueMap
            (updatePanValueMap la "pos" (.word w1)) "end" (.word w3), ga, ma, s.ffi⟩)
          (WPs.assign_load hE (old := ew) (by lk [hend])
            (fun w3 => ⟨_, _, _, _, rfl, w3, rfl⟩)) ?_
        rintro _ ⟨w3, rfl⟩
        refine WPs.assign_load hE (old := tw) (by lk [htop]) (fun w4 => ?_)
        exact ⟨⟨rfl, hgl, ⟨qv, hq, hq1, hq2⟩, hfr⟩, w4, w1, w3, gw, by lk [], by lk [], by lk [],
          by lk [hgo]⟩
      · refine WPs.assign (old := gw) hgo (of_eval (w := 0#64) (eval_const _ _)) ?_
        exact ⟨⟨rfl, hgl, ⟨qv, hq, hq1, hq2⟩, hfr⟩, tw, pw, ew, 0#64, by lk [htop],
          by lk [hpos], by lk [hend], by lk []⟩
  · rintro a ⟨hk, -⟩
    refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
    obtain ⟨k1, k2, k3, k4⟩ := hk
    exact ⟨_, a.globals, a.memory, by rw [k1], rfl, k2, k3, k4⟩

end InitECandidate.Solver.GuestBound
