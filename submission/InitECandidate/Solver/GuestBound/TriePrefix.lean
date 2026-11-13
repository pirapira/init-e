import InitECandidate.Solver.GuestBound.TrieCalls

/-!
# `min` and `common_prefix_length`

Both change nothing. `common_prefix_length(a, al, b, bl)` returns a length at
most `al` and at most `bl`, whatever the bytes are (a failing byte load ends
the run).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem min_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "min" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a b : Word) (ha : s.locals "a" = some (.word a))
    (hb : s.locals "b" = some (.word b)) (h : Runs E s body r) :
    Stopped r ∨ ∃ l w, r = .returned l s.globals s.memory s.ffi [.word w] ∧
      w.toNat ≤ a.toNat ∧ w.toNat ≤ b.toNat := by
  have hbody := (fun_of_index 31 hE.functions (by guest_decl_at 31) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l w, r = .returned l s.globals s.memory s.ffi [.word w] ∧
    w.toNat ≤ a.toNat ∧ w.toNat ≤ b.toNat)) r h
  refine WPs.seqG (fun s' => s' = s ∧ b.toNat ≤ a.toNat) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    rw [evalF_local, ha] at hx
    rw [evalF_local, hb] at hy
    simp only [Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i h0
      refine WPs.skip ⟨rfl, ?_⟩
      by_contra hc
      have hl : a < b := by rw [BitVec.lt_def]; omega
      rw [h0] at hwv
      simp [evalPanCmp, hl] at hwv
    · rename_i h0
      have hl : a.toNat < b.toNat := by
        by_contra hc
        have hl : ¬ a < b := by rw [BitVec.lt_def]; exact hc
        exact h0 (by rw [hwv]; simp [evalPanCmp, hl])
      exact WPs.ret (w := a) (of_eval (by lk [ha])) ⟨_, a, rfl, Nat.le_refl _, by omega⟩
  · rintro _ ⟨rfl, hle⟩
    exact WPs.ret (w := b) (of_eval (by lk [hb])) ⟨_, b, rfl, hle, Nat.le_refl _⟩

/-- Loop invariant of `common_prefix_length`. -/
def CplI (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (n : Word) (a : St σ) : Prop :=
  a.globals = g ∧ a.memory = m ∧ a.ffi = f ∧ a.locals "n" = some (.word n) ∧
    ∃ i : Word, a.locals "i" = some (.word i) ∧ i.toNat ≤ n.toNat

set_option maxHeartbeats 2000000 in
theorem common_prefix_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "common_prefix_length" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (al bl : Word) (hal : s.locals "al" = some (.word al))
    (hbl : s.locals "bl" = some (.word bl)) (h : Runs E s body r) :
    Stopped r ∨ ∃ l p, r = .returned l s.globals s.memory s.ffi [.word p] ∧
      p.toNat ≤ al.toNat ∧ p.toNat ≤ bl.toNat := by
  have hbody := (fun_of_index 251 hE.functions (by guest_decl_at 251) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l p, r = .returned l s.globals s.memory s.ffi [.word p] ∧
    p.toNat ≤ al.toNat ∧ p.toNat ≤ bl.toNat)) r h
  refine WPs.decCall_word (fun n g m ffi hret => ?_)
  obtain ⟨ps, cbody, values, cl, l, hlk, hvalues, hbind, hrun⟩ := hret
  have hparams := (fun_of_index 31 hE.functions (by guest_decl_at 31) (by decide +kernel)
    hlk).2
  simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local, hal, hbl]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases min_spec hE ps cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ _ al bl
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hrun with
    hst | ⟨l', w, heq, hna, hnb⟩
  · exact absurd hst (fun h => h)
  cases heq
  refine WPs.conseq (Q' := fun r => ∃ l p, r = .returned l s.globals s.memory s.ffi [.word p] ∧
    p.toNat ≤ al.toNat ∧ p.toNat ≤ bl.toNat) ?_
    (by rintro r ⟨l, p, rfl, hq⟩; exact ⟨_, p, rfl, hq⟩)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l p, r = .returned l s.globals s.memory s.ffi [.word p] ∧
    p.toNat ≤ al.toNat ∧ p.toNat ≤ bl.toNat) ?_
    (by rintro r ⟨l, p, rfl, hq⟩; exact ⟨_, p, rfl, hq⟩)
  refine WPs.seqG (fun a => CplI s.globals s.memory s.ffi n a)
    (WPs.loopG (I := CplI s.globals s.memory s.ffi n)
      ⟨rfl, rfl, rfl, by lk [], 0#64, by lk [], Nat.zero_le _⟩ ?_ (fun a k hI _ => hI)) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, hN, i, hI, hin⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hm hf hN hI
    subst hg hm hf
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := i) (by lk [hI]))
      (of_eval (w := n) (by lk [hN])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hlt : i.toNat < n.toNat := by
      by_contra hge
      have hl : ¬ i < n := by rw [BitVec.lt_def]; omega
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
      have := n.isLt
      omega
    refine WPs.seqG (fun a' => a' = ⟨la, s.globals, s.memory, s.ffi⟩)
      (WPs.ite_both (fun w' hw' => ?_)) ?_
    · split
      · exact WPs.skip rfl
      · exact WPs.ret (w := i) (of_eval (by lk [hI])) ⟨_, i, rfl, by omega, by omega⟩
    · rintro _ rfl
      refine WPs.assign (old := i) (by lk [hI]) (of_eval (w := i + 1#64) (by ev [hI])) ?_
      exact ⟨rfl, rfl, rfl, by lk [hN], i + 1#64, by lk [], by omega⟩
  · rintro a ⟨hg, hm, hf, hN, i, hI, hin⟩
    refine WPs.ret (w := n) (of_eval (by lk [hN])) ?_
    exact ⟨_, n, by rw [hg, hm, hf], hna, hnb⟩

end InitECandidate.Solver.GuestBound
