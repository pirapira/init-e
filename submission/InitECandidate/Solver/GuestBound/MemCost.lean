import InitECandidate.Solver.GuestBound.CostSpecs

/-!
# `extend_memory_cost1`

For an access of `size` bytes at `start` it returns `<cost, expand>`. Unless
`cost` is `2^64 - 1` (which no gas balance can pay), `expand` is a multiple of
32 below `2^37` and, when the access is not empty, the access ends at or
before `len + expand`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- `return <e1, e2>` for two word-valued expressions. -/
theorem WPr.ret_pair {s : St σ} {Q : Result σ → Prop} {e1 e2 : Exp Word} {w1 w2 : Word}
    (h1 : ∀ y, E.eval s e1 = some y → y = .word w1)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word w2)
    (h : Q (.returned (fun _ => none) s.globals s.memory s.ffi [.rStruct [.word w1, .word w2]])) :
    WPr E s (.return (.rStruct [e1, e2])) Q := by
  refine WPr.ret_any (fun v hv => ?_)
  rw [evalF_rStruct] at hv
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hv
  obtain ⟨v1, v2, g1, g2, rfl⟩ := evalArgs2_inv hvs
  have := h1 _ g1
  subst this
  have := h2 _ g2
  subst this
  exact h

/-- What `extend_memory_cost1` guarantees about `<cost, expand>`. -/
def CostOk (s n len cost x : Word) : Prop :=
  cost = 18446744073709551615#64 ∨
    (x.toNat % 32 = 0 ∧ x.toNat < 2 ^ 37 ∧ (n = 0#64 ∨ s.toNat + n.toNat ≤ len.toNat + x.toNat))

set_option maxHeartbeats 4000000 in
theorem extend_memory_cost1_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "extend_memory_cost1" E.functions = some (parameters, body))
    (c : St σ) (a0 a1 a2 a3 b0 b1 b2 b3 e len : Word)
    (hst : c.locals "start" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hsz : c.locals "size" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hev : c.globals "ev" = some (.word e)) (hlen : c.memory (e + 32#64) = some (.word len))
    (hl32 : len.toNat % 32 = 0) (hlb : len.toNat ≤ 2 ^ 62) :
    WPr E c body (fun r => ∃ l cost x, r = .returned l c.globals c.memory c.ffi
      [.rStruct [.word cost, .word x]] ∧
        CostOk (satW a0 a1 a2 a3) (satW b0 b1 b2 b3) len cost x) := by
  have hbody := (fun_of_index 458 hE.functions (by guest_decl_at 458) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  generalize hsd : satW a0 a1 a2 a3 = s
  generalize hnd : satW b0 b1 b2 b3 = n
  -- z = u256_is_zero(size)
  refine WPr.decCall_spec (fun rb => ∃ l z, rb = .returned l c.globals c.memory c.ffi [.word z] ∧
      (z ≠ 0#64 ↔ (b0 = 0#64 ∧ b1 = 0#64 ∧ b2 = 0#64 ∧ b3 = 0#64))) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 42 hE.functions (by guest_decl_at 42) (by decide +kernel)
      hlk).2
    have hvals : values = [.rStruct [.word b0, .word b1, .word b2, .word b3]] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local, hsz]
        at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact u256_is_zero_runs hE parameters cbody hlk ⟨cl, c.globals, c.memory, c.ffi⟩ b0 b1 b2 b3
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  rotate_left
  · rintro l g m ffi exc v ⟨l', z, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', z, hC, -⟩
    cases hC
  rintro l g m ffi v ⟨l', z, hC, hz⟩
  injection hC with _ hg hm hf hv'
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap c.locals "z" (.word z), c.globals, c.memory,
      c.ffi⟩ ∧ z = 0#64) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := z) (by lk []))
      (of_eval (w := 0#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      refine WPr.skip ⟨rfl, ?_⟩
      by_contra hne
      simp [evalPanCmp, hne] at hcv
    · rename_i h0
      have hzn : z ≠ 0#64 := by
        intro hz0
        exact h0 (by rw [hcv, hz0]; simp [evalPanCmp])
      obtain ⟨hb0, hb1, hb2, hb3⟩ := hz.mp hzn
      refine WPr.ret_pair (w1 := 0#64) (w2 := 0#64) (of_eval (eval_const _ _))
        (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨_, _, _, rfl, Or.inr ⟨by simp, by simp, Or.inl ?_⟩⟩
      rw [← hnd]
      simp [satW, hb0, hb1, hb2, hb3]
  rintro _ ⟨rfl, hz0⟩
  -- s = sat_word(start)
  refine WPr.decCall_spec (fun rb => ∃ l, rb = .returned l c.globals c.memory c.ffi
      [.word (satW a0 a1 a2 a3)]) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 440 hE.functions (by guest_decl_at 440) (by decide +kernel)
      hlk).2
    have hvals : values = [.rStruct [.word a0, .word a1, .word a2, .word a3]] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        update_lookup, hst] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact sat_word_runs hE parameters cbody hlk ⟨cl, c.globals, c.memory, c.ffi⟩ a0 a1 a2 a3
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  rotate_left
  · rintro l g m ffi exc v ⟨l', hC⟩
    cases hC
  · rintro l g m ffi ev ⟨l', hC⟩
    cases hC
  rintro l1 g m ffi v ⟨l', hC⟩
  injection hC with _ hg hm hf hv'
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  rw [hsd]
  -- n = sat_word(size)
  refine WPr.decCall_spec (fun rb => ∃ l, rb = .returned l c.globals c.memory c.ffi
      [.word (satW b0 b1 b2 b3)]) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 440 hE.functions (by guest_decl_at 440) (by decide +kernel)
      hlk).2
    have hvals : values = [.rStruct [.word b0, .word b1, .word b2, .word b3]] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        update_lookup, hsz] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact sat_word_runs hE parameters cbody hlk ⟨cl, c.globals, c.memory, c.ffi⟩ b0 b1 b2 b3
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  rotate_left
  · rintro l g m ffi exc v ⟨l', hC⟩
    cases hC
  · rintro l g m ffi ev ⟨l', hC⟩
    cases hC
  rintro l2 g m ffi v ⟨l', hC⟩
  injection hC with _ hg hm hf hv'
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  rw [hnd]
  -- endp = add_sat(s, n)
  refine WPr.decCall_spec (fun rb => ∃ l t, rb = .returned l c.globals c.memory c.ffi [.word t] ∧
      ((s.toNat + n.toNat < 2 ^ 64 ∧ t.toNat = s.toNat + n.toNat) ∨
        (2 ^ 64 ≤ s.toNat + n.toNat ∧ t = 18446744073709551615#64))) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 441 hE.functions (by guest_decl_at 441) (by decide +kernel)
      hlk).2
    have hvals : values = [.word s, .word n] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        update_lookup] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact add_sat_exact hE parameters cbody hlk ⟨cl, c.globals, c.memory, c.ffi⟩ s n
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  rotate_left
  · rintro l g m ffi exc v ⟨l', t, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', t, hC, -⟩
    cases hC
  rintro l3 g m ffi v ⟨l', endp, hC, hend⟩
  injection hC with _ hg hm hf hv'
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
      (updatePanValueMap c.locals "z" (.word z)) "s" (.word s)) "n" (.word n)) "endp"
      (.word endp), c.globals, c.memory, c.ffi⟩ ∧ endp ≠ 18446744073709551615#64)
    (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .equal) (of_eval (w := endp) (by lk []))
      (of_eval (w := 18446744073709551615#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      refine WPr.skip ⟨rfl, fun hmax => ?_⟩
      rw [hmax] at hcv
      simp [evalPanCmp] at hcv
    · refine WPr.ret_pair (w1 := 18446744073709551615#64) (w2 := 0#64)
        (of_eval (eval_const _ _)) (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      exact ⟨_, _, _, rfl, Or.inl rfl⟩
  rintro _ ⟨rfl, hendmax⟩
  have hendp : endp.toNat = s.toNat + n.toNat := by
    rcases hend with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h hendmax
  have hendlt : endp.toNat < 2 ^ 64 - 1 := by
    have := endp.isLt
    have : endp.toNat ≠ 2 ^ 64 - 1 := fun h => hendmax (by bv_omega)
    omega
  -- cur = lds 1 (ev + 32)
  refine WPr.dec_ev (fun v hv => ?_)
  have hcur := eval_load_inv2 hE (s := (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
    (updatePanValueMap c.locals "z" (.word z)) "s" (.word s)) "n" (.word n)) "endp" (.word endp),
    c.globals, c.memory, c.ffi⟩ : St σ)) (addr := e + 32#64)
    (w := len) (of_eval (by ev [eval_global, hev])) hlen v hv
  subst hcur
  -- before = ceil32(cur)
  refine WPr.decCall_spec (fun rb => ∃ l t, rb = .returned l c.globals c.memory c.ffi [.word t] ∧
      ((t = 18446744073709551615#64 ∧ 2 ^ 64 < len.toNat + 32) ∨
        (t.toNat % 32 = 0 ∧ len.toNat ≤ t.toNat ∧ t.toNat < len.toNat + 32))) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 442 hE.functions (by guest_decl_at 442) (by decide +kernel)
      hlk).2
    have hvals : values = [.word len] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        update_lookup] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact ceil32_runs hE parameters cbody hlk ⟨cl, c.globals, c.memory, c.ffi⟩ len
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  rotate_left
  · rintro l g m ffi exc v ⟨l', t, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', t, hC, -⟩
    cases hC
  rintro l4 g m ffi v ⟨l', before, hC, hbef⟩
  injection hC with _ hg hm hf hv'
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  have hbl : before.toNat = len.toNat := by
    rcases hbef with ⟨-, h⟩ | ⟨h1, h2, h3⟩ <;> omega
  -- after = ceil32(endp)
  refine WPr.decCall_spec (fun rb => ∃ l t, rb = .returned l c.globals c.memory c.ffi [.word t] ∧
      ((t = 18446744073709551615#64 ∧ 2 ^ 64 < endp.toNat + 32) ∨
        (t.toNat % 32 = 0 ∧ endp.toNat ≤ t.toNat ∧ t.toNat < endp.toNat + 32))) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 442 hE.functions (by guest_decl_at 442) (by decide +kernel)
      hlk).2
    have hvals : values = [.word endp] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        update_lookup] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact ceil32_runs hE parameters cbody hlk ⟨cl, c.globals, c.memory, c.ffi⟩ endp
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  rotate_left
  · rintro l g m ffi exc v ⟨l', t, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', t, hC, -⟩
    cases hC
  rintro l5 g m ffi v ⟨l', after, hC, haft⟩
  injection hC with _ hg hm hf hv'
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
      (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap c.locals "z"
        (.word z)) "s" (.word s)) "n" (.word n)) "endp" (.word endp)) "cur" (.word len))
        "before" (.word before)) "after" (.word after), c.globals, c.memory, c.ffi⟩ ∧
      before.toNat < after.toNat) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .notLower) (of_eval (w := before) (by lk []))
      (of_eval (w := after) (by lk [])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      exact WPr.skip ⟨rfl, BitVec.lt_def.mp (cmp_notLower_zero hcv.symm)⟩
    · rename_i h0
      have hge : ¬ before < after := cmp_notLower_ne (by rw [← hcv]; exact h0)
      have hge' : after.toNat ≤ before.toNat := Nat.le_of_not_lt (fun h => hge (BitVec.lt_def.mpr h))
      refine WPr.ret_pair (w1 := 0#64) (w2 := 0#64) (of_eval (eval_const _ _))
        (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨_, _, _, rfl, Or.inr ⟨by simp, by simp, Or.inr ?_⟩⟩
      rcases haft with ⟨h1, -⟩ | ⟨h1, h2, h3⟩
      · rw [h1] at hge'
        simp at hge'
        omega
      · simp
        omega
  rintro _ ⟨rfl, hba⟩
  -- ca = memory_gas_cost(after)
  refine WPr.decCall_spec (fun rb => ∃ l t, rb = .returned l c.globals c.memory c.ffi [.word t] ∧
      (t ≠ 18446744073709551615#64 → after.toNat < 2 ^ 37)) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 457 hE.functions (by guest_decl_at 457) (by decide +kernel)
      hlk).2
    have hvals : values = [.word after] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        update_lookup] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact memory_gas_cost_runs hE parameters cbody hlk ⟨cl, c.globals, c.memory, c.ffi⟩ after
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  rotate_left
  · rintro l g m ffi exc v ⟨l', t, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', t, hC, -⟩
    cases hC
  rintro l6 g m ffi v ⟨l', ca, hC, hca⟩
  injection hC with _ hg hm hf hv'
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  -- cb = memory_gas_cost(before)
  refine WPr.decCall_spec (fun rb => ∃ l t, rb = .returned l c.globals c.memory c.ffi [.word t])
    ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 457 hE.functions (by guest_decl_at 457) (by decide +kernel)
      hlk).2
    have hvals : values = [.word before] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        update_lookup] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact WPr.conseq (memory_gas_cost_runs hE parameters cbody hlk
      ⟨cl, c.globals, c.memory, c.ffi⟩ before
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]))
      (fun r ⟨l, t, hr, _⟩ => ⟨l, t, hr⟩)
  rotate_left
  · rintro l g m ffi exc v ⟨l', t, hC⟩
    cases hC
  · rintro l g m ffi ev ⟨l', t, hC⟩
    cases hC
  rintro l7 g m ffi v ⟨l', cb, hC⟩
  injection hC with _ hg hm hf hv'
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
      (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap
        (updatePanValueMap (updatePanValueMap c.locals "z" (.word z)) "s" (.word s)) "n"
        (.word n)) "endp" (.word endp)) "cur" (.word len)) "before" (.word before)) "after"
        (.word after)) "ca" (.word ca)) "cb" (.word cb), c.globals, c.memory, c.ffi⟩ ∧
      ca ≠ 18446744073709551615#64) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .equal) (of_eval (w := ca) (by lk []))
      (of_eval (w := 18446744073709551615#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      refine WPr.skip ⟨rfl, fun hmax => ?_⟩
      rw [hmax] at hcv
      simp [evalPanCmp] at hcv
    · refine WPr.ret_pair (w1 := 18446744073709551615#64) (w2 := 0#64)
        (of_eval (eval_const _ _)) (of_eval (eval_const _ _)) ?_
      simp only [restorePanValueFfiLocal]
      exact ⟨_, _, _, rfl, Or.inl rfl⟩
  rintro _ ⟨rfl, hcamax⟩
  have hasmall := hca hcamax
  refine WPr.ret_pair (w1 := ca - cb) (w2 := after - before) (of_eval (by ev []))
    (of_eval (by ev [])) ?_
  simp only [restorePanValueFfiLocal]
  refine ⟨_, _, _, rfl, Or.inr ?_⟩
  have hx : (after - before).toNat = after.toNat - before.toNat := by bv_omega
  rcases haft with ⟨h1, -⟩ | ⟨h1, h2, h3⟩
  · rw [h1] at hasmall
    simp at hasmall
  · refine ⟨by omega, by omega, Or.inr (by omega)⟩

end InitECandidate.Solver.GuestBound
