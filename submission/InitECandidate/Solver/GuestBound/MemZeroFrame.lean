import InitECandidate.Solver.GuestBound.MemZero
import InitECandidate.Solver.GuestBound.HtabDelInv

/-!
# `memzero` on a word-aligned block writes only that block

`memzero_spec` covers lengths that are multiples of 32. The trie code clears a
176-byte branch node, so this is the frame fact for any multiple of 8: memory
outside `[dst, dst + n)` is unchanged, globals and FFI state are unchanged.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Loop invariant: `i = 8 j ≤ n` and memory outside the block is as in `m0`. -/
def FzI (g : VarName → Option (PanValue Word)) (m0 : Word → Option (PanValue Word))
    (f : FfiState σ) (dst nW : Word) (a : St σ) : Prop :=
  a.globals = g ∧ a.ffi = f ∧ a.locals "dst" = some (.word dst) ∧
    a.locals "n" = some (.word nW) ∧
    (∀ x : Word, (x.toNat < dst.toNat ∨ dst.toNat + nW.toNat ≤ x.toNat) → a.memory x = m0 x) ∧
    ∃ j : Nat, a.locals "i" = some (.word (BitVec.ofNat 64 (8 * j))) ∧ 8 * j ≤ nW.toNat

set_option maxHeartbeats 4000000 in
theorem memzero_frame8 (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "memzero" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (dst nW : Word)
    (hd : s.locals "dst" = some (.word dst)) (hn : s.locals "n" = some (.word nW))
    (hal : dst.toNat % 8 = 0) (hn8 : nW.toNat % 8 = 0)
    (h64 : dst.toNat + nW.toNat + 32 < 2 ^ 64) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      ∀ x : Word, (x.toNat < dst.toNat ∨ dst.toNat + nW.toNat ≤ x.toNat) →
        m' x = s.memory x := by
  have hbody := (fun_of_index 17 hE.functions (by guest_decl_at 17) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    ∀ x : Word, (x.toNat < dst.toNat ∨ dst.toNat + nW.toNat ≤ x.toNat) →
      m' x = s.memory x)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    ∀ x : Word, (x.toNat < dst.toNat ∨ dst.toNat + nW.toNat ≤ x.toNat) → m' x = s.memory x) ?_
    (by rintro r ⟨l, m', rfl, hrel⟩; exact ⟨_, m', rfl, hrel⟩)
  have hN64 := nW.isLt
  have hjt : ∀ j : Nat, 8 * j ≤ nW.toNat + 32 →
      (BitVec.ofNat 64 (8 * j) : Word).toNat = 8 * j := by
    intro j hj
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have h8 : (8#64 : Word).toNat = 8 := by decide
  -- one round of either word loop: `k` cells of 8 bytes
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
  have hinit : FzI s.globals s.memory s.ffi dst nW
      ⟨updatePanValueMap s.locals "i" (.word 0#64), s.globals, s.memory, s.ffi⟩ :=
    ⟨rfl, rfl, by lk [hd], by lk [hn], fun _ _ => rfl, 0, by lk [], Nat.zero_le _⟩
  -- after the word loops `i = n`
  refine WPs.seqG (fun a => FzI s.globals s.memory s.ffi dst nW a ∧
      a.locals "i" = some (.word nW)) ?_ ?_
  · refine WPs.ite (w := 1#64) ?_ ?_
    · intro x hx
      have hc := eval_cmp_inv hE (op := .equal) (of_eval (w := dst &&& 7#64)
        (by ev [hd]; exact congrArg (AndOp.and dst) (by decide)))
        (of_eval (w := 0#64) (eval_const _ _)) _ hx
      rw [hc, and7_zero hal]
      rfl
    rw [if_neg (by decide)]
    refine WPs.seqG (fun a => FzI s.globals s.memory s.ffi dst nW a)
      (WPs.loopG (I := fun a => FzI s.globals s.memory s.ffi dst nW a) hinit ?_
        (fun a k hI _ => hI)) ?_
    · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hD, hN, hfr, j, hI, hjn⟩ ⟨w, cc, hcond, hw⟩
      simp only at hg hf hD hN hI hfr
      subst hg hf
      have hi32 : (BitVec.ofNat 64 (8 * j) : Word) + 32#64 = BitVec.ofNat 64 (8 * (j + 4)) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        omega
      have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := nW) (by lk [hN]))
        (of_eval (w := BitVec.ofNat 64 (8 * (j + 4))) (by ev [hI, hi32])) _ (cond_of_eval hcond)
      simp only [PanValue.word.injEq] at hc
      have hjD : 8 * (j + 4) ≤ nW.toNat := by
        by_contra hgt
        have hl : nW < (BitVec.ofNat 64 (8 * (j + 4)) : Word) := by
          rw [BitVec.lt_def, hjt (j + 4) (by omega)]
          omega
        rw [hc] at hw
        simp [evalPanCmp, hl] at hw
      have hij := hjt j (by omega)
      have a0 : (dst + BitVec.ofNat 64 (8 * j)).toNat = dst.toNat + 8 * j := by
        rw [BitVec.toNat_add, hij]
        omega
      have a1 : (dst + BitVec.ofNat 64 (8 * j) + 8#64).toNat = dst.toNat + 8 * j + 8 := by
        rw [BitVec.toNat_add, a0, h8]
        omega
      have a2 : (dst + BitVec.ofNat 64 (8 * j) + 16#64).toNat = dst.toNat + 8 * j + 16 := by
        rw [BitVec.toNat_add, a0, show (16#64 : Word).toNat = 16 by decide]
        omega
      have a3 : (dst + BitVec.ofNat 64 (8 * j) + 24#64).toNat = dst.toNat + 8 * j + 24 := by
        rw [BitVec.toNat_add, a0, show (24#64 : Word).toNat = 24 by decide]
        omega
      refine WPs.seq_store_inv hE (addr := dst + BitVec.ofNat 64 (8 * j)) (w := 0#64)
        (of_eval (by ev [hD, hI])) (of_eval (eval_const _ _)) ?_
      refine WPs.seq_store_inv hE (addr := dst + BitVec.ofNat 64 (8 * j) + 8#64) (w := 0#64)
        (of_eval (by ev [hD, hI, BitVec.add_assoc])) (of_eval (eval_const _ _)) ?_
      refine WPs.seq_store_inv hE (addr := dst + BitVec.ofNat 64 (8 * j) + 16#64) (w := 0#64)
        (of_eval (by ev [hD, hI, BitVec.add_assoc])) (of_eval (eval_const _ _)) ?_
      refine WPs.seq_store_inv hE (addr := dst + BitVec.ofNat 64 (8 * j) + 24#64) (w := 0#64)
        (of_eval (by ev [hD, hI, BitVec.add_assoc])) (of_eval (eval_const _ _)) ?_
      refine WPs.assign (old := BitVec.ofNat 64 (8 * j)) (by lk [hI])
        (of_eval (w := BitVec.ofNat 64 (8 * (j + 4))) (by ev [hI, hi32])) ?_
      refine ⟨rfl, rfl, by lk [hD], by lk [hN], fun x hx => ?_, j + 4, by lk [], hjD⟩
      show setCell (setCell (setCell (setCell ma _ _) _ _) _ _) _ _ x = _
      rw [setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [a3] at this; omega),
        setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [a2] at this; omega),
        setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [a1] at this; omega),
        setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [a0] at this; omega)]
      exact hfr x hx
    · intro a hIa
      refine WPs.loopG (I := fun a => FzI s.globals s.memory s.ffi dst nW a) hIa ?_ ?_
      · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hD, hN, hfr, j, hI, hjn⟩ ⟨w, cc, hcond, hw⟩
        simp only at hg hf hD hN hI hfr
        subst hg hf
        have hi8 : (BitVec.ofNat 64 (8 * j) : Word) + 8#64 = BitVec.ofNat 64 (8 * (j + 1)) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := nW) (by lk [hN]))
          (of_eval (w := BitVec.ofNat 64 (8 * (j + 1))) (by ev [hI, hi8])) _
          (cond_of_eval hcond)
        simp only [PanValue.word.injEq] at hc
        have hjD : 8 * (j + 1) ≤ nW.toNat := by
          by_contra hgt
          have hl : nW < (BitVec.ofNat 64 (8 * (j + 1)) : Word) := by
            rw [BitVec.lt_def, hjt (j + 1) (by omega)]
            omega
          rw [hc] at hw
          simp [evalPanCmp, hl] at hw
        have hij := hjt j (by omega)
        have a0 : (dst + BitVec.ofNat 64 (8 * j)).toNat = dst.toNat + 8 * j := by
          rw [BitVec.toNat_add, hij]
          omega
        refine WPs.seq_store_inv hE (addr := dst + BitVec.ofNat 64 (8 * j)) (w := 0#64)
          (of_eval (by ev [hD, hI])) (of_eval (eval_const _ _)) ?_
        refine WPs.assign (old := BitVec.ofNat 64 (8 * j)) (by lk [hI])
          (of_eval (w := BitVec.ofNat 64 (8 * (j + 1))) (by ev [hI, hi8])) ?_
        refine ⟨rfl, rfl, by lk [hD], by lk [hN], fun x hx => ?_, j + 1, by lk [], hjD⟩
        show setCell ma _ _ x = _
        rw [setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; rw [a0] at this; omega)]
        exact hfr x hx
      · rintro a k ⟨hg, hf, hD, hN, hfr, j, hI, hjn⟩ hcond
        have hi8 : (BitVec.ofNat 64 (8 * j) : Word) + 8#64 = BitVec.ofNat 64 (8 * (j + 1)) := by
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
          omega
        have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := nW) (by lk [hN]))
          (of_eval (w := BitVec.ofNat 64 (8 * (j + 1))) (by ev [hI, hi8])) _
          (cond_of_eval hcond)
        simp only [PanValue.word.injEq] at hc
        have hgt : nW.toNat < 8 * (j + 1) := by
          by_contra hle
          have hl : ¬ nW < (BitVec.ofNat 64 (8 * (j + 1)) : Word) := by
            rw [BitVec.lt_def, hjt (j + 1) (by omega)]
            omega
          simp [evalPanCmp, hl] at hc
        refine ⟨⟨hg, hf, hD, hN, hfr, j, hI, hjn⟩, ?_⟩
        show a.locals "i" = _
        rw [hI]
        congr 2
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        omega
  · rintro a ⟨⟨hg, hf, hD, hN, hfr, -⟩, hI'⟩
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
    exact ⟨_, a.memory, by rw [hg, hf], hfr⟩

end InitECandidate.Solver.GuestBound
