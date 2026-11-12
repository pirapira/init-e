import InitECandidate.Solver.GuestBound.EcpLine

/-!
# `memcpy` of an aligned block onto itself

`memcpy(a, a, n)` changes nothing: every store writes back the word it loaded.
`ecp_add` does this when its output is its first operand and the second is
the point at infinity.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Storing the word just loaded from the same address. -/
theorem WPs.seq_store_load_same (hE : GuestEnv E) {a b : Exp Word} {q : Prog Word} {addr : Word}
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hb : ∀ y, E.eval s b = some y → y = .word addr) (h : WPs E s q Q) :
    WPs E s (.seq (.store a (.load .one b)) q) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  obtain ⟨fuel, n, hrun⟩ := h1
  rcases store_word_inv hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · cases r1 with
    | error l g m f => simp only at hrest; subst hrest; exact Or.inl trivial
    | _ => cases herr
  obtain ⟨ab, w, hb', rfl, hmem⟩ := eval_load_one hE.mem hy
  have e1 := ha _ ha'
  have e2 := hb _ hb'
  simp only [PanValue.word.injEq] at e1 e2
  subst e1
  subst e2
  rw [hm w rfl, setCell_same hmem] at hrest
  exact h r hrest

def CpSelfI (s : St σ) (A nW : Word) (j : Nat) (a : St σ) : Prop :=
  a.globals = s.globals ∧ a.memory = s.memory ∧ a.ffi = s.ffi ∧
    a.locals "dst" = some (.word A) ∧ a.locals "src" = some (.word A) ∧
    a.locals "n" = some (.word nW) ∧ a.locals "i" = some (.word (BitVec.ofNat 64 (32 * j))) ∧
    32 * j ≤ nW.toNat

set_option maxHeartbeats 8000000 in
theorem memcpy_self (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "memcpy" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A nW : Word)
    (hd : s.locals "dst" = some (.word A)) (hs : s.locals "src" = some (.word A))
    (hn : s.locals "n" = some (.word nW))
    (hal : A.toNat % 8 = 0) (hn32 : nW.toNat % 32 = 0)
    (h64 : A.toNat + nW.toNat + 32 < 2 ^ 64) (h : Runs E s body r) :
    Stopped r ∨ ∃ l, r = .returned l s.globals s.memory s.ffi [.word 0#64] := by
  have hbody := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l, r = .returned l s.globals s.memory s.ffi
    [.word 0#64])) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l, r = .returned l s.globals s.memory s.ffi
    [.word 0#64]) ?_ (by rintro r ⟨l, rfl⟩; exact ⟨_, rfl⟩)
  have hN64 := nW.isLt
  have hjt : ∀ j : Nat, 32 * j ≤ nW.toNat + 32 →
      (BitVec.ofNat 64 (32 * j) : Word).toNat = 32 * j := by
    intro j hj
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have h8 : (8#64 : Word).toNat = 8 := by decide
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
  refine WPs.seqG (fun a => CpSelfI s A nW (nW.toNat / 32) a) ?_ ?_
  · refine WPs.ite (w := 1#64) ?_ ?_
    · intro x hx
      have hc := eval_cmp_inv hE (op := .equal) (of_eval (w := (A ||| A) &&& 7#64)
        (by
          ev [hd, hs]
          show (A ||| (A ||| 0#64)) &&& (7#64 &&& 18446744073709551615#64) = A &&& 7#64
          rw [BitVec.or_zero, BitVec.or_self,
            show (7#64 &&& 18446744073709551615#64 : Word) = 7#64 by decide]))
        (of_eval (w := 0#64) (eval_const _ _)) _ hx
      rw [hc, BitVec.or_self, and7_zero hal]
      rfl
    rw [if_neg (by decide)]
    refine WPs.seqG (fun a => CpSelfI s A nW (nW.toNat / 32) a)
      (WPs.loopG (I := fun a => ∃ j, CpSelfI s A nW j a)
        ⟨0, rfl, rfl, rfl, by lk [hd], by lk [hs], by lk [hn], by lk [], Nat.zero_le _⟩ ?_ ?_) ?_
    · rintro ⟨la, ga, ma, fa⟩ ⟨j, hg, hm, hf, hD, hS, hN, hI, hjn⟩ ⟨w, cc, hcond, hw⟩
      simp only at hg hm hf hD hS hN hI
      subst ga ma fa
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
      refine WPs.seq_store_load_same hE (addr := A + BitVec.ofNat 64 (32 * j))
        (of_eval (by ev [hD, hI])) (of_eval (by ev [hS, hI])) ?_
      refine WPs.seq_store_load_same hE (addr := A + BitVec.ofNat 64 (32 * j) + 8#64)
        (of_eval (by ev [hD, hI, BitVec.add_assoc])) (of_eval (by ev [hS, hI, BitVec.add_assoc]))
        ?_
      refine WPs.seq_store_load_same hE (addr := A + BitVec.ofNat 64 (32 * j) + 16#64)
        (of_eval (by ev [hD, hI, BitVec.add_assoc])) (of_eval (by ev [hS, hI, BitVec.add_assoc]))
        ?_
      refine WPs.seq_store_load_same hE (addr := A + BitVec.ofNat 64 (32 * j) + 24#64)
        (of_eval (by ev [hD, hI, BitVec.add_assoc])) (of_eval (by ev [hS, hI, BitVec.add_assoc]))
        ?_
      refine WPs.assign (old := BitVec.ofNat 64 (32 * j)) (by lk [hI])
        (of_eval (w := BitVec.ofNat 64 (32 * (j + 1))) (by ev [hI, hi32])) ?_
      exact ⟨j + 1, rfl, rfl, rfl, by lk [hD], by lk [hS], by lk [hN], by lk [], hjD⟩
    · rintro a k ⟨j, hg, hm, hf, hD, hS, hN, hI, hjn⟩ hcond
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
      exact ⟨hg, hm, hf, hD, hS, hN, hI, hjn⟩
    · rintro a ⟨hg, hm, hf, hD, hS, hN, hI, hjn⟩
      have hI' : a.locals "i" = some (.word nW) := by
        rw [hI]
        congr 2
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat]
        omega
      exact WPs.while_false (hfin a 8#64 (by rw [h8]; omega) (by rw [h8]; omega) hN hI')
        ⟨hg, hm, hf, hD, hS, hN, hI, hjn⟩
  · rintro a ⟨hg, hm, hf, hD, hS, hN, hI, hjn⟩
    have hI' : a.locals "i" = some (.word nW) := by
      rw [hI]
      congr 2
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      omega
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
    exact ⟨_, by rw [hg, hm, hf]⟩

end InitECandidate.Solver.GuestBound
