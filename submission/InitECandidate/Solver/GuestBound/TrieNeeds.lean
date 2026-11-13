import InitECandidate.Solver.GuestBound.TrieWalkDefs
import InitECandidate.Solver.GuestBound.TrieCalls
import InitECandidate.Solver.GuestBound.WorldRestore

/-!
# `_node_needs_rlp`: the `needs` field of the walk interface

The function reads two cells and changes nothing; it answers 1 only for a
non-null node that is not a stub and whose RLP cache is empty.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- What `_node_needs_rlp` returns. -/
def NeedsQ (s : St σ) (c : Word) (r : Result σ) : Prop :=
  ∃ l f, r = .returned l s.globals s.memory s.ffi [.word f] ∧
    (f ≠ 0#64 → c ≠ 0#64 ∧ ∃ kk, Rd s.memory c kk ∧ kk ≠ 0#64 ∧ Rd s.memory (c + 8#64) 0#64)

set_option maxHeartbeats 4000000 in
theorem node_needs_rlp_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_node_needs_rlp" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (c : Word) (hc : s.locals "child" = some (.word c))
    (h : Runs E s body r) : Stopped r ∨ NeedsQ s c r := by
  have hbody := (fun_of_index 283 hE.functions (by guest_decl_at 283) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (NeedsQ s c)) r h
  have zero : NeedsQ s c (.returned (fun _ => none) s.globals s.memory s.ffi [.word 0#64]) :=
    ⟨_, 0#64, rfl, fun h => absurd rfl h⟩
  refine WPs.seqG (fun a => a = s ∧ c ≠ 0#64) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    simp only [evalF_local, hc, eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i hw0
      exact WPs.skip ⟨rfl, by
        rintro rfl
        rw [hwv] at hw0
        simp [evalPanCmp] at hw0⟩
    · exact WPs.ret (w := 0#64) (of_eval (eval_const _ _)) zero
  intro a ha
  obtain ⟨ha, hc0⟩ := ha
  rw [ha]
  clear ha a
  refine WPs.seqG (fun a => a = s ∧ ∃ kk, Rd s.memory c kk ∧ kk ≠ 0#64)
    (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    obtain ⟨addr, v, ha, hv, hm⟩ := eval_load_one hE.mem hx
    rw [eval_addc hE 0#64 hc] at ha
    simp only [Option.some.injEq, PanValue.word.injEq, eval_const] at ha hv hy
    subst ha hv hy
    rw [BitVec.add_zero] at hm
    split
    · rename_i hw0
      exact WPs.skip ⟨rfl, x, hm, by
        rintro rfl
        rw [hwv] at hw0
        simp [evalPanCmp] at hw0⟩
    · exact WPs.ret (w := 0#64) (of_eval (eval_const _ _)) zero
  intro a ha
  obtain ⟨ha, kk, hk, hkk⟩ := ha
  rw [ha]
  clear ha a
  refine WPs.seqG (fun a => a = s ∧ Rd s.memory (c + 8#64) 0#64)
    (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    obtain ⟨addr, v, ha, hv, hm⟩ := eval_load_one hE.mem hx
    rw [eval_addc hE 8#64 hc] at ha
    simp only [Option.some.injEq, PanValue.word.injEq, eval_const] at ha hv hy
    subst ha hv hy
    split
    · rename_i hw0
      have hv0 : x = 0#64 := by
        by_contra hne
        rw [hwv] at hw0
        simp [evalPanCmp, hne] at hw0
      subst hv0
      exact WPs.skip ⟨rfl, hm⟩
    · exact WPs.ret (w := 0#64) (of_eval (eval_const _ _)) zero
  intro a ha
  obtain ⟨ha, h8⟩ := ha
  rw [ha]
  clear ha a
  exact WPs.ret (w := 1#64) (of_eval (eval_const _ _))
    ⟨_, 1#64, rfl, fun _ => ⟨hc0, kk, hk, hkk, h8⟩⟩

/-- The `needs` field of `WalkIface`. -/
theorem needs_spec (hE : GuestEnv E) (s : St σ) (e : Exp Word) (c : Word) (v : PanValue Word)
    (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (ffi : FfiState σ)
    (hret : CalleeRet E s "_node_needs_rlp" [e] [v] g m ffi) (he : E.eval s e = some (.word c)) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ f : Word, v = .word f ∧
      (f ≠ 0#64 → c ≠ 0#64 ∧ ∃ kk, Rd s.memory c kk ∧ kk ≠ 0#64 ∧
        Rd s.memory (c + 8#64) 0#64) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := hret
  have hparams := (fun_of_index 283 hE.functions (by guest_decl_at 283) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, he, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases node_needs_rlp_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ c
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hrun
    with hst | ⟨l', f, heq, hf⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, f, rfl, hf⟩

end InitECandidate.Solver.GuestBound
