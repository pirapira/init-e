import InitECandidate.Solver.GuestBound.TripleRules
import InitECandidate.Solver.GuestBound.RlpHeader
import InitECandidate.Solver.GuestBound.HalvingLoop

/-!
# `input_blob`

The copy loop `while i <+ len { …; i = i + 8 }` is bounded because the
function traps unless `len` is at most the host input capacity, so `i + 8`
does not wrap.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Close a cost inequality between closed expression costs. -/
macro "cost_le" : tactic => `(tactic| (
  simp only [stepCost_eq, stepsCost_eq, expCost, expsCost]
  omega))

namespace Manual

/-- `len` holds a word at most the input capacity. -/
def LenOk (s : St σ) : Prop :=
  ∃ w : Word, s.locals "len" = some (.word w) ∧ w.toNat ≤ 1073741808

/-- Bytes left to copy. -/
def lenMu (s : St σ) : Nat :=
  match s.locals "i", s.locals "len" with
  | some (.word i), some (.word l) => l.toNat - i.toNat
  | _, _ => 0

theorem LenOk.update {s : St σ} {x : VarName} {v : PanValue Word}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {f : FfiState σ} (h : LenOk s) (hx : (("len" : VarName) == x) = false) :
    LenOk ⟨updatePanValueMap s.locals x v, g, m, f⟩ := by
  obtain ⟨w, hw, hle⟩ := h
  exact ⟨w, by simp [updatePanValueMap, hx, hw], hle⟩

theorem «input_blob».cost (hE : GuestEnv E) {T A : Nat} (htrap : FunCost E "trap_with" T)
    (halloc : FunCost E "alloc" A) :
    FunCost E "input_blob" (T + A + 1073741809 * 128 + 256) := by
  refine FunCost.mono (funCost_of_index 29 hE.functions (by guest_decl_at 29)
    (by decide +kernel) (B := T + A + 1073741809 * 128 + 256) ?_) (Nat.le_refl _)
  reduce_body
  refine (Triple.dec (B := T + A + 1073741809 * 128 + 250) (P' := fun _ => True) _ _ _
    (fun _ _ _ _ _ => trivial) ?_).consequence (fun _ h => h) (by cost_le) (fun _ h => h)
  refine (Triple.seq (B₁ := 8) (B₂ := T + A + 1073741809 * 128 + 240)
    (Mid := fun s => ∃ w : Word, s.locals "len" = some (.word w)) (Q := fun _ => True) ?_
    ?_).consequence (fun _ h => h) (by omega) (fun _ h => h)
  · refine Triple.of_costs ((X.shMemLoad σ E _ _ _ _).consequence (fun _ h => h) (by cost_le)
      (fun _ h => h)) ?_
    intro fuel s r n _ hrun hne
    rcases shMemLoad_local_inv hrun with herr | ⟨g, m, ffi, ev, rfl⟩ | ⟨w, ffi, rfl⟩
    · rw [herr] at hne; cases hne
    · trivial
    · exact ⟨w, by simp [updatePanValueMap]⟩
  refine (Triple.seq (B₁ := T + 20) (B₂ := A + 1073741809 * 128 + 200) (Mid := LenOk)
    (Q := fun _ => True) ?_ ?_).consequence (fun _ h => h) (by omega) (fun _ h => h)
  · refine Triple.of_costs ((X.ite σ E _ _ _ _ _ (X.callDest σ E _ _ _ _ htrap)
      (X.skip σ E)).consequence (fun _ h => h) (by cost_le) (fun _ h => h)) ?_
    intro fuel s r n hP hrun hne
    obtain ⟨w, hw⟩ := hP
    rcases ite_run_inv hrun with herr | ⟨fuel', v, n', hc, hbranch⟩
    · rw [herr] at hne; cases hne
    rcases hbranch with ⟨-, hthen⟩ | ⟨hv, helse⟩
    · have hnr := call_noReturn (trap_with_noReturn hE) (some none) hthen
      cases r with
      | normal l g m f => cases hnr.2
      | _ => trivial
    · have hr := skip_inv helse
      subst hr
      obtain ⟨va, vb, ha, hb, hx⟩ := cmp_inv hE.word hc
      simp only [eval_const, eval_local] at ha hb
      rw [hw] at hb
      simp only [Option.some.injEq, PanValue.word.injEq] at ha hb
      subst ha hb
      have hnot : ¬ BitVec.ofNat 64 1073741808 < w := cmp_lower_zero (by rw [← hx, hv])
      have hmax : (BitVec.ofNat 64 1073741808).toNat = 1073741808 := by decide
      refine ⟨w, hw, ?_⟩
      rw [BitVec.lt_def, hmax] at hnot
      omega
  refine (Triple.decCall (C := 1073741809 * 128 + 150) (P' := LenOk) _ _ _ halloc
    (fun s v g m ffi (hP : LenOk s) _ => hP.update (by decide)) ?_).consequence (fun _ h => h)
    (by cost_le) (fun _ h => h)
  refine (Triple.dec (B := 1073741809 * 128 + 100) (P' := LenOk) _ _ _
    (fun s v (hP : LenOk s) _ _ => hP.update (by decide)) ?_).consequence (fun _ h => h)
    (by cost_le) (fun _ h => h)
  refine (Triple.dec (B := 1073741809 * 128 + 50) (P' := LenOk) _ _ _
    (fun s v (hP : LenOk s) _ _ => hP.update (by decide)) ?_).consequence (fun _ h => h)
    (by cost_le) (fun _ h => h)
  refine (Triple.seq (B₁ := 1073741809 * 128) (Mid := fun _ => True) (Q := fun _ => True) ?_
    (X.ret σ E _)).consequence (fun _ h => h) (by cost_le) (fun _ h => h)
  refine (Triple.while (I := LenOk) (μ := lenMu) (Q := fun _ => True)
    (e := panValueExpStepCost _) (b := 64) 1073741808 (condCost _ _) (fun _ _ => trivial)
    ?_).consequence ?_ (by cost_le) (fun r _ => by cases r <;> trivial)
  · intro k
    refine Triple.of_costs ((X.seq σ E _ _ _ _ (X.shMemLoad σ E _ _ _ _)
      (X.seq σ E _ _ _ _ (X.store σ E _ _) (X.assign σ E _ _ _))).consequence
        (fun _ h => h) (by decide +kernel) (fun _ h => h)) ?_
    intro fuel s r n hP hrun hne
    obtain ⟨⟨lv, hlen, hle⟩, hμ, v, kc, hcond, hv⟩ := hP
    obtain ⟨ov, lv', hoff, hlen', hx⟩ := cmp_inv hE.word (cond_of_eval hcond)
    simp only [eval_local] at hoff hlen'
    rw [hlen] at hlen'
    simp only [Option.some.injEq, PanValue.word.injEq] at hlen'
    subst hlen'
    have hlt : ov < lv := by
      apply cmp_lower_ne
      intro h0
      rw [hx, h0] at hv
      simp at hv
    have hltn := BitVec.lt_def.mp hlt
    have hμs : lenMu s = lv.toNat - ov.toNat := by simp [lenMu, hoff, hlen]
    obtain ⟨f1, r₁, n₁, h₁, hrest⟩ := seq_run_inv hrun
    rcases shMemLoad_local_inv h₁ with herr | ⟨g, m, ffi, ev, rfl⟩ | ⟨w, ffi, rfl⟩
    · cases r₁ with
      | error l' g' m' f' =>
        simp only at hrest
        subst hrest
        exact Bool.noConfusion hne
      | _ => cases herr
    · simp only at hrest
      subst hrest
      trivial
    simp only at hrest
    obtain ⟨n₂, hrun₂⟩ := hrest
    obtain ⟨f2, r₂, n₃, h₂, hrest₂⟩ := seq_run_inv hrun₂
    rcases store_inv h₂ with herr | ⟨m', rfl⟩
    · cases r₂ with
      | error l' g' m' f' =>
        simp only at hrest₂
        subst hrest₂
        exact Bool.noConfusion hne
      | _ => cases herr
    simp only at hrest₂
    obtain ⟨n₄, hrun₃⟩ := hrest₂
    rcases assign_local_inv hrun₃ with herr | ⟨va, hva, rfl⟩
    · cases r with
      | error l' g' m' f' => exact Bool.noConfusion hne
      | _ => cases herr
    obtain ⟨xa, xb, hxa, hxb, rfl⟩ := eval_add hE.word hva
    simp only [eval_local, eval_const] at hxa hxb
    have hi2 : updatePanValueMap s.locals "w" (PanValue.word w) "i" = some (.word ov) := by
      simp [updatePanValueMap, hoff]
    rw [hi2] at hxa
    simp only [Option.some.injEq, PanValue.word.injEq] at hxa hxb
    subst hxa hxb
    simp only [loopBodyPost]
    have hlenF : updatePanValueMap (updatePanValueMap s.locals "w" (PanValue.word w)) "i"
        (PanValue.word (ov + BitVec.ofNat 64 8)) "len" = some (.word lv) := by
      simp [updatePanValueMap, hlen]
    have hiF : updatePanValueMap (updatePanValueMap s.locals "w" (PanValue.word w)) "i"
        (PanValue.word (ov + BitVec.ofNat 64 8)) "i" =
          some (.word (ov + BitVec.ofNat 64 8)) := by
      simp [updatePanValueMap]
    have h8 : (BitVec.ofNat 64 8).toNat = 8 := by decide
    have hadd : (ov + BitVec.ofNat 64 8).toNat = ov.toNat + 8 := by
      rw [BitVec.toNat_add, h8]
      omega
    refine ⟨⟨lv, hlenF, hle⟩, ?_⟩
    simp only [lenMu, hiF, hlenF, hadd]
    omega
  · intro s h
    refine ⟨h, ?_⟩
    obtain ⟨w, hw, hle⟩ := h
    unfold lenMu
    split
    · rename_i i l _ hl
      rw [hw] at hl
      simp only [Option.some.injEq, PanValue.word.injEq] at hl
      subst hl
      omega
    · omega

end Manual
end InitECandidate.Solver.GuestBound
