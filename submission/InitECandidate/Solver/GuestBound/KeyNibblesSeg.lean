import InitECandidate.Solver.GuestBound.NibStore

/-!
# `key_to_nibbles` writes nibbles

`key_to_nibbles_frame` with the content of the output: every byte of
`[out, out + 2 n)` is below 16 afterwards (`Nibs m out (2 n)`), which is what
`NibSeg` asks of a trie node's segment. Derived from the text of
`KeyNibbles.lean` (the loop invariant gains the written prefix).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Loop invariant: nibbles of bytes `0 .. i` are written, nothing else. -/
def KnJ (g : VarName → Option (PanValue Word)) (m0 : Word → Option (PanValue Word))
    (f : FfiState σ) (kw nw ow0 : Word) (a : St σ) : Prop :=
  a.globals = g ∧ a.ffi = f ∧ a.locals "key" = some (.word kw) ∧
    a.locals "n" = some (.word nw) ∧ a.locals "out" = some (.word ow0) ∧
    ∃ iw : Word, a.locals "i" = some (.word iw) ∧
      ow0.toNat + 2 * iw.toNat < 33806089704 + 16 ∧ iw.toNat ≤ nw.toNat ∧ Nibs a.memory ow0 (2 * iw.toNat) ∧
      ∀ x : Word, (x.toNat < ow0.toNat / 8 * 8 ∨ ow0.toNat + 2 * iw.toNat ≤ x.toNat) →
        a.memory x = m0 x

set_option maxHeartbeats 16000000 in
theorem key_to_nibbles_nib (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "key_to_nibbles" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (kw nw ow0 : Word) (hk : s.locals "key" = some (.word kw))
    (hn : s.locals "n" = some (.word nw)) (ho : s.locals "out" = some (.word ow0))
    (hob : ow0.toNat < 33806089704 + 16) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m, r = .returned l s.globals m s.ffi [.word 0#64] ∧
      ow0.toNat + 2 * nw.toNat < 33806089704 + 16 ∧
      Nibs m ow0 (2 * nw.toNat) ∧
      ∀ x : Word, (x.toNat < ow0.toNat / 8 * 8 ∨ ow0.toNat + 2 * nw.toNat ≤ x.toNat) →
        m x = s.memory x := by
  have hbody := (fun_of_index 248 hE.functions (by guest_decl_at 248) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m, r = .returned l s.globals m s.ffi [.word 0#64] ∧
      ow0.toNat + 2 * nw.toNat < 33806089704 + 16 ∧
      Nibs m ow0 (2 * nw.toNat) ∧
      ∀ x : Word, (x.toNat < ow0.toNat / 8 * 8 ∨ ow0.toNat + 2 * nw.toNat ≤ x.toNat) →
        m x = s.memory x)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l m, r = .returned l s.globals m s.ffi [.word 0#64] ∧
      ow0.toNat + 2 * nw.toNat < 33806089704 + 16 ∧
      Nibs m ow0 (2 * nw.toNat) ∧
      ∀ x : Word, (x.toNat < ow0.toNat / 8 * 8 ∨ ow0.toNat + 2 * nw.toNat ≤ x.toNat) →
        m x = s.memory x) ?_
    (by rintro r ⟨l, m, rfl, hq⟩; exact ⟨_, m, rfl, hq⟩)
  refine WPs.seqG (fun a => KnJ s.globals s.memory s.ffi kw nw ow0 a)
    (WPs.loopG (I := KnJ s.globals s.memory s.ffi kw nw ow0)
      ⟨rfl, rfl, by lk [hk], by lk [hn], by lk [ho], 0#64, by lk [], by simpa using hob,
        Nat.zero_le _, (by intro j hj; simp at hj), fun _ _ => rfl⟩ ?_ (fun a k hI _ => hI)) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hfa, hK, hN, hO, iw, hI, d1, d2, hnb, hfr⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hfa hK hN hO hI hfr
    subst hg hfa
    have hi4 : (iw + 4#64).toNat = iw.toNat + 4 := by
      rw [BitVec.toNat_add, show (4#64 : Word).toNat = 4 by decide]
      omega
    have hcv := eval_cmp_inv hE (op := .notLower) (of_eval (w := nw) (by lk [hN]))
      (of_eval (w := iw + 4#64) (by ev [hI])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hle : iw.toNat + 4 ≤ nw.toNat := by
      by_contra hgt
      have hl : nw < iw + 4#64 := by rw [BitVec.lt_def, hi4]; omega
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have hmul : (2#64 * iw).toNat = 2 * iw.toNat := by
      rw [BitVec.toNat_mul, show (2#64 : Word).toNat = 2 by decide]
      omega
    have ad0 : (ow0 + 2#64 * iw).toNat = ow0.toNat + 2 * iw.toNat := by
      rw [BitVec.toNat_add, hmul]
      omega
    have ad1 : (ow0 + (2#64 * iw + 1#64)).toNat = ow0.toNat + 2 * iw.toNat + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hmul, show (1#64 : Word).toNat = 1 by decide]
      omega
    have ad2 : (ow0 + (2#64 * iw + 2#64)).toNat = ow0.toNat + 2 * iw.toNat + 2 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hmul, show (2#64 : Word).toNat = 2 by decide]
      omega
    have ad3 : (ow0 + (2#64 * iw + 3#64)).toNat = ow0.toNat + 2 * iw.toNat + 3 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hmul, show (3#64 : Word).toNat = 3 by decide]
      omega
    have ad4 : (ow0 + (2#64 * iw + 4#64)).toNat = ow0.toNat + 2 * iw.toNat + 4 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hmul, show (4#64 : Word).toNat = 4 by decide]
      omega
    have ad5 : (ow0 + (2#64 * iw + 5#64)).toNat = ow0.toNat + 2 * iw.toNat + 5 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hmul, show (5#64 : Word).toNat = 5 by decide]
      omega
    have ad6 : (ow0 + (2#64 * iw + 6#64)).toNat = ow0.toNat + 2 * iw.toNat + 6 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hmul, show (6#64 : Word).toNat = 6 by decide]
      omega
    have ad7 : (ow0 + (2#64 * iw + 7#64)).toNat = ow0.toNat + 2 * iw.toNat + 7 := by
      rw [BitVec.toNat_add, BitVec.toNat_add, hmul, show (7#64 : Word).toNat = 7 by decide]
      omega
    refine WPs.dec_ev (fun vb0 hvb0 => ?_)
    obtain ⟨bvb0, rfl, hbvb0⟩ := loadByte_lt hE hvb0
    try dsimp only
    refine WPs.seq_storeByte_nib hE (addr := ow0 + 2#64 * iw) (of_eval (by ev [hO, hI]))
      (nib_lsr4 hE (b := bvb0) (by lk []) hbvb0) (fun m0 w0 hd0 hf0 hw0 hy0 => ?_)
    try dsimp only
    refine WPs.seq_storeByte_nib hE (addr := ow0 + (2#64 * iw + 1#64)) (of_eval (by ev [hO, hI]))
      (nib_and15 hE (b := bvb0) (by lk [])) (fun m1 w1 hd1 hf1 hw1 hy1 => ?_)
    try dsimp only
    refine WPs.dec_ev (fun vb1 hvb1 => ?_)
    obtain ⟨bvb1, rfl, hbvb1⟩ := loadByte_lt hE hvb1
    try dsimp only
    refine WPs.seq_storeByte_nib hE (addr := ow0 + (2#64 * iw + 2#64)) (of_eval (by ev [hO, hI]))
      (nib_lsr4 hE (b := bvb1) (by lk []) hbvb1) (fun m2 w2 hd2 hf2 hw2 hy2 => ?_)
    try dsimp only
    refine WPs.seq_storeByte_nib hE (addr := ow0 + (2#64 * iw + 3#64)) (of_eval (by ev [hO, hI]))
      (nib_and15 hE (b := bvb1) (by lk [])) (fun m3 w3 hd3 hf3 hw3 hy3 => ?_)
    try dsimp only
    refine WPs.dec_ev (fun vb2 hvb2 => ?_)
    obtain ⟨bvb2, rfl, hbvb2⟩ := loadByte_lt hE hvb2
    try dsimp only
    refine WPs.seq_storeByte_nib hE (addr := ow0 + (2#64 * iw + 4#64)) (of_eval (by ev [hO, hI]))
      (nib_lsr4 hE (b := bvb2) (by lk []) hbvb2) (fun m4 w4 hd4 hf4 hw4 hy4 => ?_)
    try dsimp only
    refine WPs.seq_storeByte_nib hE (addr := ow0 + (2#64 * iw + 5#64)) (of_eval (by ev [hO, hI]))
      (nib_and15 hE (b := bvb2) (by lk [])) (fun m5 w5 hd5 hf5 hw5 hy5 => ?_)
    try dsimp only
    refine WPs.dec_ev (fun vb3 hvb3 => ?_)
    obtain ⟨bvb3, rfl, hbvb3⟩ := loadByte_lt hE hvb3
    try dsimp only
    refine WPs.seq_storeByte_nib hE (addr := ow0 + (2#64 * iw + 6#64)) (of_eval (by ev [hO, hI]))
      (nib_lsr4 hE (b := bvb3) (by lk []) hbvb3) (fun m6 w6 hd6 hf6 hw6 hy6 => ?_)
    try dsimp only
    refine WPs.seq_storeByte_nib hE (addr := ow0 + (2#64 * iw + 7#64)) (of_eval (by ev [hO, hI]))
      (nib_and15 hE (b := bvb3) (by lk [])) (fun m7 w7 hd7 hf7 hw7 hy7 => ?_)
    try dsimp only
    refine WPs.assign (old := iw) (by lk [hI]) (of_eval (w := iw + 4#64) (by ev [hI])) ?_
    simp only [restorePanValueFfiLocal]
    rw [ad7] at hd7
    refine ⟨rfl, rfl,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hK],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hN],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hO],
      iw + 4#64,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by rw [hi4]; omega, by rw [hi4]; omega, ?_, fun x hx => ?_⟩
    rotate_left
    dsimp only at hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 ⊢
    rw [hi4] at hx
    rw [hf7 x (by rw [ad7]; omega)]
    rw [hf6 x (by rw [ad6]; omega)]
    rw [hf5 x (by rw [ad5]; omega)]
    rw [hf4 x (by rw [ad4]; omega)]
    rw [hf3 x (by rw [ad3]; omega)]
    rw [hf2 x (by rw [ad2]; omega)]
    rw [hf1 x (by rw [ad1]; omega)]
    rw [hf0 x (by rw [ad0]; omega)]
    exact hfr x (by omega)
    have n0 := hnb.snoc (by omega) ad0 hw0 hy0
    have n1 := n0.snoc (by omega) (by rw [ad1]; omega) hw1 hy1
    have n2 := n1.snoc (by omega) (by rw [ad2]; omega) hw2 hy2
    have n3 := n2.snoc (by omega) (by rw [ad3]; omega) hw3 hy3
    have n4 := n3.snoc (by omega) (by rw [ad4]; omega) hw4 hy4
    have n5 := n4.snoc (by omega) (by rw [ad5]; omega) hw5 hy5
    have n6 := n5.snoc (by omega) (by rw [ad6]; omega) hw6 hy6
    have n7 := n6.snoc (by omega) (by rw [ad7]; omega) hw7 hy7
    have e : 2 * (iw + 4#64).toNat = 2 * iw.toNat + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
      rw [hi4]; omega
    rw [e]
    exact n7
  · intro a hIa
    refine WPs.seqG (fun a => KnJ s.globals s.memory s.ffi kw nw ow0 a ∧
        a.locals "i" = some (.word nw))
      (WPs.loopG (I := KnJ s.globals s.memory s.ffi kw nw ow0) hIa ?_ ?_) ?_
    · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hfa, hK, hN, hO, iw, hI, d1, d2, hnb, hfr⟩ ⟨w, cc, hcond, hw⟩
      simp only at hg hfa hK hN hO hI hfr
      subst hg hfa
      have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := iw) (by lk [hI]))
        (of_eval (w := nw) (by lk [hN])) _ (cond_of_eval hcond)
      simp only [PanValue.word.injEq] at hcv
      have hlt : iw.toNat < nw.toNat := by
        by_contra hge
        have hl : ¬ iw < nw := by rw [BitVec.lt_def]; omega
        rw [hcv] at hw
        simp [evalPanCmp, hl] at hw
      have hi1 : (iw + 1#64).toNat = iw.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
        omega
      have hmul : (2#64 * iw).toNat = 2 * iw.toNat := by
        rw [BitVec.toNat_mul, show (2#64 : Word).toNat = 2 by decide]
        omega
      have ad0 : (ow0 + 2#64 * iw).toNat = ow0.toNat + 2 * iw.toNat := by
        rw [BitVec.toNat_add, hmul]
        omega
      have ad1 : (ow0 + (2#64 * iw + 1#64)).toNat = ow0.toNat + 2 * iw.toNat + 1 := by
        rw [BitVec.toNat_add, BitVec.toNat_add, hmul, show (1#64 : Word).toNat = 1 by decide]
        omega
      refine WPs.dec_ev (fun vb hvb => ?_)
      obtain ⟨bvb, rfl, hbvb⟩ := loadByte_lt hE hvb
      try dsimp only
      refine WPs.seq_storeByte_nib hE (addr := ow0 + 2#64 * iw) (of_eval (by ev [hO, hI]))
        (nib_lsr4 hE (b := bvb) (by lk []) hbvb) (fun m0 w0 hd0 hf0 hw0 hy0 => ?_)
      try dsimp only
      refine WPs.seq_storeByte_nib hE (addr := ow0 + (2#64 * iw + 1#64)) (of_eval (by ev [hO, hI]))
        (nib_and15 hE (b := bvb) (by lk [])) (fun m1 w1 hd1 hf1 hw1 hy1 => ?_)
      try dsimp only
      refine WPs.assign (old := iw) (by lk [hI]) (of_eval (w := iw + 1#64) (by ev [hI])) ?_
      simp only [restorePanValueFfiLocal]
      rw [ad1] at hd1
      refine ⟨rfl, rfl,
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hK],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hN],
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hO],
        iw + 1#64,
        by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
        by rw [hi1]; omega, by rw [hi1]; omega, ?_, fun x hx => ?_⟩
      rotate_left
      dsimp only at hf0 hf1 ⊢
      rw [hi1] at hx
      rw [hf1 x (by rw [ad1]; omega)]
      rw [hf0 x (by rw [ad0]; omega)]
      exact hfr x (by omega)
      have n0 := hnb.snoc (by omega) ad0 hw0 hy0
      have n1 := n0.snoc (by omega) (by rw [ad1]; omega) hw1 hy1
      have e : 2 * (iw + 1#64).toNat = 2 * iw.toNat + 1 + 1 := by
        rw [hi1]; omega
      rw [e]
      exact n1
    · rintro a k ⟨hg, hfa, hK, hN, hO, iw, hI, d1, d2, hnb, hfr⟩ hcond
      have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := iw) (by lk [hI]))
        (of_eval (w := nw) (by lk [hN])) _ (cond_of_eval hcond)
      simp only [PanValue.word.injEq] at hcv
      have hge : ¬ iw.toNat < nw.toNat := by
        intro hlt
        have hl : iw < nw := by rw [BitVec.lt_def]; exact hlt
        simp [evalPanCmp, hl] at hcv
      have heq : iw = nw := BitVec.eq_of_toNat_eq (by omega)
      subst heq
      exact ⟨⟨hg, hfa, hK, hN, hO, iw, hI, d1, d2, hnb, hfr⟩, hI⟩
    · rintro a ⟨⟨hg, hfa, hK, hN, hO, iw, hI, d1, d2, hnb, hfr⟩, hin⟩
      have : iw = nw := by
        rw [hI] at hin
        simpa using hin
      subst this
      refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
      exact ⟨_, a.memory, by rw [hg, hfa], d1, hnb, hfr⟩

end InitECandidate.Solver.GuestBound
