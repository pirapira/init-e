import InitECandidate.Solver.GuestBound.MemZero

/-!
# `memzero` on an aligned block whose length is a multiple of 8

`memzero_spec` asks for a multiple of 32; a branch node is 176 bytes. Here the
second (word-stride) loop runs too.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Invariant of the word-stride loop. -/
def MzK (g : VarName → Option (PanValue Word)) (m0 : Word → Option (PanValue Word))
    (f : FfiState σ) (dst nW : Word) (k : Nat) (a : St σ) : Prop :=
  a.globals = g ∧ a.ffi = f ∧ a.locals "dst" = some (.word dst) ∧
    a.locals "n" = some (.word nW) ∧ a.locals "i" = some (.word (BitVec.ofNat 64 (8 * k))) ∧
    8 * k ≤ nW.toNat ∧ ZeroRel m0 a.memory dst (8 * k)

/-- After the aligned loops: everything is zeroed and `i = n`. -/
def MzE (g : VarName → Option (PanValue Word)) (m0 : Word → Option (PanValue Word))
    (f : FfiState σ) (dst nW : Word) (a : St σ) : Prop :=
  a.globals = g ∧ a.ffi = f ∧ a.locals "dst" = some (.word dst) ∧
    a.locals "n" = some (.word nW) ∧ a.locals "i" = some (.word nW) ∧
    ZeroRel m0 a.memory dst nW.toNat

set_option maxHeartbeats 4000000 in
theorem memzero_spec8 (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "memzero" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (dst nW : Word)
    (hd : s.locals "dst" = some (.word dst)) (hn : s.locals "n" = some (.word nW))
    (hal : dst.toNat % 8 = 0) (hn8 : nW.toNat % 8 = 0)
    (h64 : dst.toNat + nW.toNat + 32 < 2 ^ 64) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      ZeroRel s.memory m' dst nW.toNat := by
  have hbody := (fun_of_index 17 hE.functions (by guest_decl_at 17) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    ZeroRel s.memory m' dst nW.toNat)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    ZeroRel s.memory m' dst nW.toNat) ?_
    (by rintro r ⟨l, m', rfl, hrel⟩; exact ⟨_, m', rfl, hrel⟩)
  have hN64 := nW.isLt
  have hjt : ∀ j : Nat, 32 * j ≤ nW.toNat + 32 →
      (BitVec.ofNat 64 (32 * j) : Word).toNat = 32 * j := by
    intro j hj
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hkt : ∀ k : Nat, 8 * k ≤ nW.toNat + 32 →
      (BitVec.ofNat 64 (8 * k) : Word).toNat = 8 * k := by
    intro k hk
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have h32 : (32#64 : Word).toNat = 32 := by decide
  have h8 : (8#64 : Word).toNat = 8 := by decide
  have h1 : (1#64 : Word).toNat = 1 := by decide
  -- value of the guards once `i = n`
  have hfin : ∀ (a : St σ) (k : Word), k.toNat ≤ 32 → 1 ≤ k.toNat →
      a.locals "n" = some (.word nW) → a.locals "i" = some (.word nW) →
      ∀ x, E.eval a (.cmp .notLower (.var .local "n")
        (.op .add [.var .local "i", .const k])) = some x → x = .word 0#64 := by
    intro a k hk hk1 hN hI x hx
    have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := nW) (by lk [hN]))
      (of_eval (w := nW + k) (by ev [hI])) _ hx
    have hl : nW < nW + k := by
      rw [BitVec.lt_def, BitVec.toNat_add]
      omega
    rw [hc]
    simp [evalPanCmp, hl]
  refine WPs.seqG (fun a => MzE s.globals s.memory s.ffi dst nW a) ?_ ?_
  · refine WPs.ite (w := 1#64) ?_ ?_
    · intro x hx
      have hc := eval_cmp_inv hE (op := .equal) (of_eval (w := dst &&& 7#64) (by ev [hd]; exact congrArg (AndOp.and dst) (by decide)))
        (of_eval (w := 0#64) (eval_const _ _)) _ hx
      rw [hc, and7_zero hal]
      rfl
    rw [if_neg (by decide)]
    refine WPs.seqG (fun a => MzI s.globals s.memory s.ffi dst nW (nW.toNat / 32) a)
      (WPs.loopG (I := fun a => ∃ j, MzI s.globals s.memory s.ffi dst nW j a)
        ⟨0, rfl, rfl, by lk [hd], by lk [hn], by lk [], Nat.zero_le _, fun x => by
          rw [if_neg (by omega)]⟩ ?_ ?_) ?_
    · rintro ⟨la, ga, ma, fa⟩ ⟨j, hg, hf, hD, hN, hI, hjn, hzr⟩ ⟨w, cc, hcond, hw⟩
      simp only at hg hf hD hN hI hzr
      subst hg hf
      have hi32 : (BitVec.ofNat 64 (32 * j) : Word) + 32#64 = BitVec.ofNat 64 (32 * (j + 1)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := nW) (by lk [hN]))
        (of_eval (w := BitVec.ofNat 64 (32 * (j + 1))) (by ev [hI, hi32])) _ (cond_of_eval hcond)
      simp only [PanValue.word.injEq] at hc
      have hjD : 32 * (j + 1) ≤ nW.toNat := by
        by_contra hgt
        have hl : nW < (BitVec.ofNat 64 (32 * (j + 1)) : Word) := by
          rw [BitVec.lt_def, hjt (j + 1) (by omega)]
          omega
        rw [hc] at hw
        simp [evalPanCmp, hl] at hw
      have hij := hjt j (by omega)
      have a0 : (dst + BitVec.ofNat 64 (32 * j)).toNat = dst.toNat + 32 * j := by
        rw [BitVec.toNat_add, hij]
        omega
      have a1 : (dst + BitVec.ofNat 64 (32 * j) + 8#64).toNat = dst.toNat + 32 * j + 8 := by
        rw [BitVec.toNat_add, a0, h8]
        omega
      have a2 : (dst + BitVec.ofNat 64 (32 * j) + 16#64).toNat = dst.toNat + 32 * j + 16 := by
        rw [BitVec.toNat_add, a0, show (16#64 : Word).toNat = 16 by decide]
        omega
      have a3 : (dst + BitVec.ofNat 64 (32 * j) + 24#64).toNat = dst.toNat + 32 * j + 24 := by
        rw [BitVec.toNat_add, a0, show (24#64 : Word).toNat = 24 by decide]
        omega
      refine WPs.seq_store_inv hE (addr := dst + BitVec.ofNat 64 (32 * j)) (w := 0#64)
        (of_eval (by ev [hD, hI])) (of_eval (eval_const _ _)) ?_
      refine WPs.seq_store_inv hE (addr := dst + BitVec.ofNat 64 (32 * j) + 8#64) (w := 0#64)
        (of_eval (by ev [hD, hI, BitVec.add_assoc])) (of_eval (eval_const _ _)) ?_
      refine WPs.seq_store_inv hE (addr := dst + BitVec.ofNat 64 (32 * j) + 16#64) (w := 0#64)
        (of_eval (by ev [hD, hI, BitVec.add_assoc])) (of_eval (eval_const _ _)) ?_
      refine WPs.seq_store_inv hE (addr := dst + BitVec.ofNat 64 (32 * j) + 24#64) (w := 0#64)
        (of_eval (by ev [hD, hI, BitVec.add_assoc])) (of_eval (eval_const _ _)) ?_
      refine WPs.assign (old := BitVec.ofNat 64 (32 * j)) (by lk [hI])
        (of_eval (w := BitVec.ofNat 64 (32 * (j + 1))) (by ev [hI, hi32])) ?_
      refine ⟨j + 1, rfl, rfl, by lk [hD], by lk [hN], by lk [], hjD, ?_⟩
      intro x
      have e : ∀ a : Word, (x = a) ↔ x.toNat = a.toNat := fun a => BitVec.toNat_inj.symm
      show setCell (setCell (setCell (setCell ma _ _) _ _) _ _) _ _ x = _
      simp only [setCell, beq_iff_eq, e, a0, a1, a2, a3, hzr x]
      split_ifs <;> first | rfl | omega
    · rintro a k ⟨j, hg, hf, hD, hN, hI, hjn, hzr⟩ hcond
      have hi32 : (BitVec.ofNat 64 (32 * j) : Word) + 32#64 = BitVec.ofNat 64 (32 * (j + 1)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := nW) (by lk [hN]))
        (of_eval (w := BitVec.ofNat 64 (32 * (j + 1))) (by ev [hI, hi32])) _ (cond_of_eval hcond)
      simp only [PanValue.word.injEq] at hc
      have hgt : nW.toNat < 32 * (j + 1) := by
        by_contra hle
        have hl : ¬ nW < (BitVec.ofNat 64 (32 * (j + 1)) : Word) := by
          rw [BitVec.lt_def, hjt (j + 1) (by omega)]
          omega
        simp [evalPanCmp, hl] at hc
      have : j = nW.toNat / 32 := by omega
      subst this
      exact ⟨hg, hf, hD, hN, hI, hjn, hzr⟩
    · rintro a ⟨hg, hf, hD, hN, hI, hjn, hzr⟩
      refine WPs.loopG (I := fun a => ∃ k, MzK s.globals s.memory s.ffi dst nW k a)
        ⟨4 * (nW.toNat / 32), hg, hf, hD, hN, by
          rw [hI]
          congr 3
          omega, by omega, by
          have e4 : 8 * (4 * (nW.toNat / 32)) = 32 * (nW.toNat / 32) := by omega
          rw [e4]
          exact hzr⟩ ?_ ?_
      · rintro ⟨la, ga, ma, fa⟩ ⟨k, hg, hf, hD, hN, hI, hkn, hzr⟩ ⟨w, cc, hcond, hw⟩
        simp only at hg hf hD hN hI hzr
        subst hg hf
        have hi8 : (BitVec.ofNat 64 (8 * k) : Word) + 8#64 = BitVec.ofNat 64 (8 * (k + 1)) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := nW) (by lk [hN]))
          (of_eval (w := BitVec.ofNat 64 (8 * (k + 1))) (by ev [hI, hi8])) _ (cond_of_eval hcond)
        simp only [PanValue.word.injEq] at hc
        have hkD : 8 * (k + 1) ≤ nW.toNat := by
          by_contra hgt
          have hl : nW < (BitVec.ofNat 64 (8 * (k + 1)) : Word) := by
            rw [BitVec.lt_def, hkt (k + 1) (by omega)]
            omega
          rw [hc] at hw
          simp [evalPanCmp, hl] at hw
        have hik := hkt k (by omega)
        have a0 : (dst + BitVec.ofNat 64 (8 * k)).toNat = dst.toNat + 8 * k := by
          rw [BitVec.toNat_add, hik]
          omega
        refine WPs.seq_store_inv hE (addr := dst + BitVec.ofNat 64 (8 * k)) (w := 0#64)
          (of_eval (by ev [hD, hI])) (of_eval (eval_const _ _)) ?_
        refine WPs.assign (old := BitVec.ofNat 64 (8 * k)) (by lk [hI])
          (of_eval (w := BitVec.ofNat 64 (8 * (k + 1))) (by ev [hI, hi8])) ?_
        refine ⟨k + 1, rfl, rfl, by lk [hD], by lk [hN], by lk [], hkD, ?_⟩
        intro x
        have e : ∀ a : Word, (x = a) ↔ x.toNat = a.toNat := fun a => BitVec.toNat_inj.symm
        show setCell ma _ _ x = _
        simp only [setCell, beq_iff_eq, e, a0, hzr x]
        split_ifs <;> first | rfl | omega
      · rintro a k' ⟨k, hg, hf, hD, hN, hI, hkn, hzr⟩ hcond
        have hi8 : (BitVec.ofNat 64 (8 * k) : Word) + 8#64 = BitVec.ofNat 64 (8 * (k + 1)) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := nW) (by lk [hN]))
          (of_eval (w := BitVec.ofNat 64 (8 * (k + 1))) (by ev [hI, hi8])) _ (cond_of_eval hcond)
        simp only [PanValue.word.injEq] at hc
        have hgt : nW.toNat < 8 * (k + 1) := by
          by_contra hle
          have hl : ¬ nW < (BitVec.ofNat 64 (8 * (k + 1)) : Word) := by
            rw [BitVec.lt_def, hkt (k + 1) (by omega)]
            omega
          simp [evalPanCmp, hl] at hc
        have hkn' : 8 * k = nW.toNat := by omega
        refine ⟨hg, hf, hD, hN, ?_, ?_⟩
        · rw [hI]
          congr 2
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_ofNat]
          omega
        · rw [← hkn']
          exact hzr
  · rintro a ⟨hg, hf, hD, hN, hI', hzr⟩
    refine WPs.seqG (fun a' => a' = a)
      (WPs.while_false (hfin a 8#64 (by rw [h8]; omega) (by rw [h8]; omega) hN hI') rfl) ?_
    intro a' ha'
    rw [ha']
    refine WPs.seqG (fun a' => a' = a) (WPs.while_false ?_ rfl) ?_
    · intro x hx
      have hc := eval_cmp_inv hE (op := .lower) (of_eval (w := nW) (by lk [hI']))
        (of_eval (w := nW) (by lk [hN])) _ hx
      rw [hc]
      simp [evalPanCmp]
    intro a'' ha''
    rw [ha'']
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    exact ⟨_, a.memory, by rw [hg, hf], hzr⟩


end InitECandidate.Solver.GuestBound
