import InitECandidate.Solver.GuestBound.Heap

/-!
# `scratch_alloc`: where the block is

`ScratchPost` (in `ScratchAlloc.lean`) only says the arena rank drops. For
frame arguments the location matters: when the scratch pointer `p` is not
below the frame-memory pointer `fmp`, a returning `scratch_alloc(n)` returns
an aligned `q` with `fmp ≤ q` and `q + n ≤ p`, sets `scratch_ptr` to `q`, and
changes nothing else.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- What a returning `scratch_alloc(nv)` did, for scratch pointer `pv` and
frame-memory pointer `fv`. -/
def ScratchAllocPost (pv fv nv : Word) (s : St σ) : Result σ → Prop
  | .returned _ g m f vs =>
      m = s.memory ∧ f = s.ffi ∧
        ∃ qv : Word, vs = [.word qv] ∧
          g = updatePanValueMap s.globals "scratch_ptr" (.word qv) ∧
          fv.toNat ≤ qv.toNat ∧ qv.toNat + nv.toNat ≤ pv.toNat ∧ qv.toNat % 8 = 0
  | .normal _ _ _ _ | .continued _ _ _ _ | .broke _ _ _ _ => False
  | _ => True

set_option maxHeartbeats 2000000 in
theorem scratch_alloc_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "scratch_alloc" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv nv : Word) (hn : s.locals "n" = some (.word nv))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (h : Runs E s body r) : ScratchAllocPost pv fv nv s r := by
  have hbody := (fun_of_index 13 hE.functions (by guest_decl_at 13) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  rw [runs_dec] at h
  simp only [eval_global, hp, shape_word, shape_matches_self, if_true] at h
  obtain ⟨rb, hb, rfl⟩ := h
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp hb
  have ft := trapIte_guard hE h₁
  cases r₁ with
  | normal l1 g1 m1 f1 =>
    obtain ⟨rfl, rfl, rfl, rfl, hg1⟩ := ft
    simp only at hrest
    simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_op hE.word,
      evalArgs_cons, evalArgs_nil, evalF_local, eval_global, hf, eval_const, update_lookup,
      if_true, if_false, hn, wordsProj_cons, wordsProj_nil, wordOp, Option.map_some,
      Option.some.injEq, PanValue.word.injEq] at hg1
    rw [runs_dec] at hrest
    simp (config := { decide := true }) only [evalF_op hE.word, evalArgs_cons, evalArgs_nil,
      evalF_local, eval_const, update_lookup, if_true, if_false, hn, wordsProj_cons,
      wordsProj_nil, wordOp, List.foldr, Option.map_some, shape_word, shape_matches_self]
      at hrest
    obtain ⟨rb2, hb2, rfl⟩ := hrest
    obtain ⟨r₂, h₂, hrest₂⟩ := runs_seq.mp hb2
    have ft2 := trapIte_guard hE h₂
    cases r₂ with
    | normal l2 g2 m2 f2 =>
      obtain ⟨rfl, rfl, rfl, rfl, hg2⟩ := ft2
      simp only at hrest₂
      simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, eval_global, hf,
        eval_const, update_lookup, if_true, Option.some.injEq, PanValue.word.injEq] at hg2
      obtain ⟨r₃, h₃, hrest₃⟩ := runs_seq.mp hrest₂
      rw [runs_assign_global] at h₃
      simp (config := { decide := true }) only [evalF_local, update_lookup, if_true,
        panValueAssignmentValid, hp, shape_word, shape_matches_self] at h₃
      subst h₃
      simp only at hrest₃
      rw [runs_return] at hrest₃
      simp (config := { decide := true }) only [evalF_local, update_lookup, if_true, if_false,
        payload_word] at hrest₃
      subst hrest₃
      simp only [restorePanValueFfiLocal, ScratchAllocPost]
      refine ⟨trivial, trivial, _, rfl, rfl, ?_⟩
      have h1 := lower_zero hg1
      have h2 := lower_zero hg2
      have hpl := pv.isLt
      have hnl := nv.isLt
      have hsub : (pv - fv).toNat = pv.toNat - fv.toNat := by
        rw [BitVec.toNat_sub]
        have := fv.isLt
        omega
      rw [BitVec.lt_def, hsub] at h1
      have hsub2 : (pv - nv).toNat = pv.toNat - nv.toNat := by
        rw [BitVec.toNat_sub]
        omega
      have hq := and_m8 (pv - nv)
      rw [hsub2] at hq
      rw [BitVec.lt_def, hq] at h2
      rw [hq]
      omega
    | continued l2 g2 m2 f2 => exact ft2.elim
    | broke l2 g2 m2 f2 => exact ft2.elim
    | returned l2 g2 m2 f2 vs => exact ft2.elim
    | _ =>
      simp only at hrest₂
      subst hrest₂
      simp only [restorePanValueFfiLocal, ScratchAllocPost]
  | continued l1 g1 m1 f1 => exact ft.elim
  | broke l1 g1 m1 f1 => exact ft.elim
  | returned l1 g1 m1 f1 vs => exact ft.elim
  | _ =>
    simp only at hrest
    subst hrest
    simp only [restorePanValueFfiLocal, ScratchAllocPost]

end InitECandidate.Solver.GuestBound
