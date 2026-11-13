import InitECandidate.Solver.GuestBound.RlpItemRange
import InitECandidate.Solver.GuestBound.TrieCalls

/-!
# `rlp_read_length` computes a function of the bytes it reads

`RL m p k v`: folding the `k` bytes at `p` big-endian gives `v`.  The relation
is functional and depends only on those bytes, so two reads of the same
unchanged bytes agree (issue #30).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- One step of the big-endian fold, in the form the evaluator produces. -/
def rlStep (v b : Word) : Word := OrOp.or (v <<< (8#64).toNat) (OrOp.or b 0#64)

/-- The big-endian value of the `k` bytes at `p`. -/
inductive RL (m : Word → Option (PanValue Word)) (p : Word) : Nat → Word → Prop
  | zero : RL m p 0 0#64
  | step {k : Nat} {v b : Word} : RL m p k v → byteAt m (p + BitVec.ofNat 64 k) = some b →
      RL m p (k + 1) (rlStep v b)

theorem RL.fn {m : Word → Option (PanValue Word)} {p : Word} {k : Nat} {v v' : Word}
    (h : RL m p k v) (h' : RL m p k v') : v = v' := by
  induction h generalizing v' with
  | zero => cases h'; rfl
  | step _ hb ih =>
    cases h' with
    | step h1 hb' =>
      have := ih h1
      subst this
      rw [hb] at hb'
      simp only [Option.some.injEq] at hb'
      subst hb'
      rfl

theorem RL.frame {m m' : Word → Option (PanValue Word)} {p : Word} {k : Nat} {v : Word}
    (h : RL m p k v) (hb : ∀ j, j < k → byteAt m' (p + BitVec.ofNat 64 j) =
      byteAt m (p + BitVec.ofNat 64 j)) : RL m' p k v := by
  induction h with
  | zero => exact .zero
  | step _ hbt ih =>
    exact .step (ih (fun j hj => hb j (by omega))) (by rw [hb _ (by omega)]; exact hbt)

/-- An assignment followed by the rest, which may use that the value evaluated. -/
theorem WPs.seq_asg_some {x : VarName} {e : Exp Word} {q : Prog Word} {w old : Word}
    (hx : s.locals x = some (.word old)) (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : E.eval s e = some (.word w) →
      WPs E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩ q Q) :
    WPs E s (.seq (.assign .local x e) q) Q := by
  intro r hr
  cases hv : E.eval s e with
  | none =>
    have h1 : WPs E s (.assign .local x e) (fun _ => False) := by
      intro r1 hr1
      rw [runs_assign_local, hv] at hr1
      simp only at hr1
      subst hr1
      exact Or.inl (Stopped.err s)
    exact (WPs.seqG (fun _ => False) (h1.conseq (fun r hf => hf.elim)) (fun _ hf => hf.elim)) r hr
  | some y =>
    have := he y hv
    subst this
    exact WPs.seq_asg hx he (h hv) r hr

/-- Loop invariant of `rlp_read_length`. -/
def RlI (s : St σ) (pw nw : Word) (a : St σ) : Prop :=
  a.globals = s.globals ∧ a.memory = s.memory ∧ a.ffi = s.ffi ∧
    a.locals "p" = some (.word pw) ∧ a.locals "n" = some (.word nw) ∧
    ∃ (k : Nat) (v : Word), a.locals "i" = some (.word (BitVec.ofNat 64 k)) ∧ k ≤ nw.toNat ∧
      a.locals "v" = some (.word v) ∧ RL s.memory pw k v

set_option maxHeartbeats 8000000 in
theorem rlp_read_length_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_read_length" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pw nw : Word) (hp : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw)) (h : Runs E s body r) :
    Stopped r ∨ ∃ l v, r = .returned l s.globals s.memory s.ffi [.word v] ∧
      RL s.memory pw nw.toNat v := by
  have hbody := (fun_of_index 106 hE.functions (by guest_decl_at 106) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l v, r = .returned l s.globals s.memory s.ffi [.word v] ∧
    RL s.memory pw nw.toNat v)) r h
  have hnl := nw.isLt
  refine WPs.guard_quiet (rlp_fail_quiet hE) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.seqG (fun a => RlI s pw nw a ∧ a.locals "i" = some (.word nw))
    (WPs.loopG (I := RlI s pw nw)
      ⟨rfl, rfl, rfl, by lk [hp], by lk [hn], 0, 0#64, by lk [], Nat.zero_le _, by lk [], .zero⟩
      ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, qp, qn, k, v, qi, hk, qv, hrl⟩ ⟨w, cc, hcond, hw⟩
    dsimp only at hg hm hf qp qn qi qv
    subst hg hm hf
    have ek : (BitVec.ofNat 64 k : Word).toNat = k := by
      rw [BitVec.toNat_ofNat]
      omega
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 k) (by lk [qi]))
      (of_eval (w := nw) (by lk [qn])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hlt : k < nw.toNat := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 k : Word) < nw := by rw [BitVec.lt_def, ek]; omega
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    cases hbt : byteAt s.memory (pw + BitVec.ofNat 64 k) with
    | none =>
      have habs : ∀ y, E.eval (⟨la, s.globals, s.memory, s.ffi⟩ : St σ)
          (.op .or [.shift .lsl (.var .local "v") (.const 8#64),
            .loadByte (.op .add [.var .local "p", .var .local "i"])]) = some y → False := by
        intro y hy
        obtain ⟨va, vb, w1, ha, hb, hop, rfl⟩ := eval_op2_inv hE.word hy
        obtain ⟨b', -, hbb⟩ := loadByte_byteAt hE hb (addr := pw + BitVec.ofNat 64 k)
          (of_eval (by ev [qp, qi]))
        rw [hbt] at hbb
        cases hbb
      exact WPs.seq_asg_some (old := v) (w := 0#64) qv (fun y hy => (habs y hy).elim)
        (fun hy => (habs _ hy).elim)
    | some b =>
      refine WPs.seq_asg_some (old := v) (w := rlStep v b) qv (fun y hy => ?_) (fun _ => ?_)
      · obtain ⟨va, vb, w1, ha, hb, hop, rfl⟩ := eval_op2_inv hE.word hy
        obtain ⟨b', hx, hbb⟩ := loadByte_byteAt hE hb (addr := pw + BitVec.ofNat 64 k)
          (of_eval (by ev [qp, qi]))
        rw [hbt] at hbb
        simp only [Option.some.injEq, PanValue.word.injEq] at hbb hx
        subst hbb hx
        rw [evalF_shift hE.word, evalF_local] at ha
        dsimp only at ha
        rw [qv, eval_const] at ha
        simp only [RiscV.panRiscVShift] at ha
        rw [if_pos (by decide)] at ha
        simp only [Option.map_some, Option.some.injEq, PanValue.word.injEq] at ha
        simp [wordOp] at hop
        subst ha hop
        rfl
      · refine WPs.assign (old := BitVec.ofNat 64 k) (w := BitVec.ofNat 64 (k + 1))
          (by lk [qi]) (of_eval (by ev [qi, ofNat_succ])) ?_
        exact ⟨rfl, rfl, rfl, by lk [qp], by lk [qn], k + 1, rlStep v b, by lk [], by omega,
          by lk [], .step hrl hbt⟩
  · rintro a kk ⟨hg, hm, hf, qp, qn, k, v, qi, hk, qv, hrl⟩ hcond
    have ek : (BitVec.ofNat 64 k : Word).toNat = k := by
      rw [BitVec.toNat_ofNat]
      omega
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 k) (by lk [qi]))
      (of_eval (w := nw) (by lk [qn])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge : ¬ k < nw.toNat := by
      intro hlt
      have hl : (BitVec.ofNat 64 k : Word) < nw := by rw [BitVec.lt_def, ek]; exact hlt
      simp [evalPanCmp, hl] at hcv
    have hkn : k = nw.toNat := by omega
    have heq : (BitVec.ofNat 64 k : Word) = nw := BitVec.eq_of_toNat_eq (by rw [ek, hkn])
    rw [heq] at qi
    exact ⟨⟨hg, hm, hf, qp, qn, k, v, by rw [heq]; exact qi, hk, qv, hrl⟩, qi⟩
  · rintro ⟨la, ga, ma, fa⟩ ⟨⟨hg, hm, hf, qp, qn, k, v, qi, hk, qv, hrl⟩, qin⟩
    dsimp only at hg hm hf qp qn qi qv qin
    subst hg hm hf
    have hkn : k = nw.toNat := by
      rw [qi] at qin
      simp only [Option.some.injEq, PanValue.word.injEq] at qin
      have := congrArg BitVec.toNat qin
      rw [BitVec.toNat_ofNat] at this
      omega
    subst hkn
    refine WPs.ret (w := v) (of_eval (by lk [qv])) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, v, rfl, hrl⟩

end InitECandidate.Solver.GuestBound
