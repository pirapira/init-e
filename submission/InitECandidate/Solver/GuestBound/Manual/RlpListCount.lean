import InitECandidate.Solver.GuestBound.RlpTotal

/-!
# The loop of `rlp_list_count`

`while off <+ len { var total = rlp_item_total(p + off, len - off); off = off + total; … }`.
By `rlp_item_total_spec`, `1 ≤ total ≤ len - off`, so `off` advances without
wrapping and `len - off` strictly decreases.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

theorem totalVals_inv {len : Word} {values : List (PanValue Word)} (h : totalVals len values) :
    ∃ t, values = [.word t] ∧ 1 ≤ t.toNat ∧ t.toNat ≤ len.toNat := by
  unfold totalVals at h
  split at h
  · rename_i t
    exact ⟨t, rfl, h⟩
  · exact h.elim

namespace Manual

theorem rlp_list_count.loop0 {σ : Type} {E : Env σ} (hE : GuestEnv E) (b : Nat)
    (hbody : Costs E (loopBody 113 0) b) :
    Costs E (.while (loopGuard 113 0) (loopBody 113 0))
      (18446744073709551616 * (expCost (loopGuard 113 0) + b + 1)) := by
  revert hbody
  loop_reduce 113 0
  intro hbody
  let μ : St σ → Nat := fun s =>
    match s.locals "off", s.locals "len" with
    | some (.word o), some (.word l) => l.toNat - o.toNat
    | _, _ => 0
  refine (Triple.while (E := E) (I := fun _ => True) (μ := μ) (Q := fun _ => True)
    (e := expCost (.cmp .lower (.var .local "off") (.var .local "len"))) (b := b) (2 ^ 64 - 1)
    (by rw [← stepCost_eq]; exact condCost _ _) (fun _ _ => trivial) ?_).consequence ?_
    (Nat.mul_le_mul_right _ (by decide)) (fun _ h => h)
  · intro k fuel s r n hP hrun hne
    obtain ⟨-, hμ, hc⟩ := hP
    refine ⟨(hbody fuel s r n trivial hrun hne).1, ?_⟩
    obtain ⟨v, kc, hcond, hv⟩ := hc
    obtain ⟨ov, lv, hoff, hlen, hx⟩ := cmp_inv hE.word (cond_of_eval hcond)
    simp only [eval_local] at hoff hlen
    have hlt : ov < lv := by
      apply cmp_lower_ne
      intro h0
      rw [hx, h0] at hv
      simp at hv
    have hltn := BitVec.lt_def.mp hlt
    have hμs : μ s = lv.toNat - ov.toNat := by simp [μ, hoff, hlen]
    rcases decCall_run_inv hrun with herr | ⟨f1, params', calleeBody, values, calleeLocals, rb, nb,
      hlookup', hvalues, hbind, hcallee, hout⟩
    · rw [herr] at hne; cases hne
    have hparams := (fun_of_index 112 hE.functions (by guest_decl_at 112) (by decide +kernel)
      hlookup').2
    obtain ⟨v₁, v₂, -, hv₂, rfl⟩ := evalArgs2_inv hvalues
    obtain ⟨sa, sb, hsa, hsb, rfl⟩ := eval_sub hE.word hv₂
    simp only [eval_local] at hsa hsb
    rw [hlen] at hsa
    rw [hoff] at hsb
    simp only [Option.some.injEq, PanValue.word.injEq] at hsa hsb
    subst hsa hsb
    rw [hparams] at hbind
    have hclen : calleeLocals "len" = some (.word (lv - ov)) := bind2 hbind
    have hspec := rlp_item_total_spec hE params' calleeBody hlookup' f1
      ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb nb (lv - ov) hcallee hclen
    have hsubn : (lv - ov).toNat = lv.toNat - ov.toNat := by
      rw [BitVec.toNat_sub]
      have := lv.isLt
      have := ov.isLt
      omega
    cases rb with
    | returned l g m ffi values' =>
      obtain ⟨t, rfl, ht1, htle⟩ := totalVals_inv hspec
      obtain ⟨f2, r', n', -, hrun', rfl⟩ := hout
      obtain ⟨f3, r₁, n₁, h₁, hrest⟩ := seq_run_inv hrun'
      rcases assign_local_inv h₁ with herr | ⟨va, hva, rfl⟩
      · cases r₁ with
        | error l' g' m' f' =>
          simp only at hrest
          subst hrest
          exact Bool.noConfusion hne
        | _ => cases herr
      obtain ⟨xa, xb, hxa, hxb, rfl⟩ := eval_add hE.word hva
      have hoff2 : (updatePanValueMap s.locals "total" (PanValue.word t)) "off" =
          some (.word ov) := by simp [updatePanValueMap, hoff]
      have htot2 : (updatePanValueMap s.locals "total" (PanValue.word t)) "total" =
          some (.word t) := by simp [updatePanValueMap]
      simp only [eval_local] at hxa hxb
      rw [hoff2] at hxa
      rw [htot2] at hxb
      simp only [Option.some.injEq, PanValue.word.injEq] at hxa hxb
      subst hxa hxb
      simp only at hrest
      obtain ⟨n₂, hrun₂⟩ := hrest
      rcases assign_local_inv hrun₂ with herr | ⟨vc, -, rfl⟩
      · cases r' with
        | error l' g' m' f' => exact Bool.noConfusion hne
        | _ => cases herr
      simp only [restorePanValueFfiLocal, loopBodyPost, true_and]
      have hoffF : restorePanValueLocal (updatePanValueMap (updatePanValueMap
          (updatePanValueMap s.locals "total" (PanValue.word t)) "off" (PanValue.word (ov + t)))
          "count" vc) "total" (s.locals "total") "off" = some (.word (ov + t)) := by
        simp [restorePanValueLocal, updatePanValueMap]
      have hlenF : restorePanValueLocal (updatePanValueMap (updatePanValueMap
          (updatePanValueMap s.locals "total" (PanValue.word t)) "off" (PanValue.word (ov + t)))
          "count" vc) "total" (s.locals "total") "len" = some (.word lv) := by
        simp [restorePanValueLocal, updatePanValueMap, hlen]
      have hadd : (ov + t).toNat = ov.toNat + t.toNat := by
        rw [BitVec.toNat_add]
        have := lv.isLt
        omega
      simp only [μ, hoffF, hlenF, hadd]
      omega
    | raised l g m ffi exception value =>
      simp only at hout
      subst hout
      simp only [loopBodyPost]
    | finalFfi l g m ffi event =>
      simp only at hout
      subst hout
      simp only [loopBodyPost]
    | _ => exact hout.elim
  · intro s _
    refine ⟨trivial, ?_⟩
    simp only [μ]
    split
    · rename_i o l _ _
      have := l.isLt
      omega
    · omega

end Manual
end InitECandidate.Solver.GuestBound
