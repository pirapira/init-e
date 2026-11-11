import InitECandidate.Solver.GuestBound.NoReturn

/-!
# Specification of `scratch_alloc`

When `scratch_alloc(n)` returns with `n ≥ 1`, it has changed only the global
`scratch_ptr`, and a rank of the scratch arena has strictly decreased. The
rank is wrap-aware: `scratch_ptr` when it is at or above `frame_mem_ptr`, and
`2^64 + scratch_ptr` otherwise (a state the guest never reaches, but one the
specification must cover).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A value whose shape is a single word is a word. -/
theorem word_of_shape_one {structs : StructContext} {v : PanValue Word}
    (h : panShapeMatches (panValueShape structs v) .one = true) : ∃ w, v = .word w := by
  cases v with
  | word w => exact ⟨w, rfl⟩
  | rStruct fields => simp [panValueShape, panShapeMatches] at h
  | nStruct name fields => simp [panValueShape, panShapeMatches] at h

/-- `skip` finishes normally in the same state. -/
theorem skip_inv {fuel : Nat} {s : St σ} {r : Result σ} {n : Nat}
    (h : E.run fuel s .skip = some (r, n)) : r = .normal s.locals s.globals s.memory s.ffi := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
  | succ fuel =>
    simp only [Env.run, evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm

/-- Progress measure of the scratch arena. -/
def scratchRank (globals : VarName → Option (PanValue Word)) : Nat :=
  match globals "scratch_ptr", globals "frame_mem_ptr" with
  | some (.word p), some (.word fmp) => if fmp ≤ p then p.toNat else 2 ^ 64 + p.toNat
  | _, _ => 0

/-- What a returning `scratch_alloc` guarantees, relative to the entry state. -/
def ScratchPost (s : St σ) : Result σ → Prop
  | .returned _ g m f _ =>
      scratchRank g < scratchRank s.globals ∧ m = s.memory ∧ f = s.ffi ∧
        g "frame_mem_ptr" = s.globals "frame_mem_ptr"
  | _ => True

theorem ScratchPost.of_not_returned {s : St σ} {r : Result σ} (h : r.leaves = false) :
    ScratchPost s r := by
  cases r <;> trivial

theorem ScratchPost.of_error {s : St σ} {r : Result σ} (h : r.isError = true) :
    ScratchPost s r := by
  cases r <;> trivial

theorem ScratchPost.restore {s : St σ} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : ScratchPost s r) : ScratchPost s (restorePanValueFfiLocal x old r) := by
  cases r <;> exact h

/-- The body of `scratch_alloc` satisfies `ScratchPost` when its argument is at least one. -/
theorem scratch_alloc_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "scratch_alloc" E.functions = some (parameters, body))
    (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (nv : Word)
    (hrun : E.run fuel s body = some (r, n)) (hn : s.locals "n" = some (.word nv))
    (hn1 : 1 ≤ nv.toNat) : ScratchPost s r := by
  have hbody := (fun_of_index 13 hE.functions (by guest_decl_at 13) (by decide +kernel)
    hlookup).1
  subst hbody
  have hW := hE.word
  -- var p = scratch_ptr
  rcases dec_run_inv hrun with herr | ⟨f1, vp, r1, n1, hvp, hshape, hrun1, rfl⟩
  · exact ScratchPost.of_error herr
  refine ScratchPost.restore ?_
  obtain ⟨pw, rfl⟩ := word_of_shape_one hshape
  simp only [eval_global] at hvp
  -- if n >+ p - frame_mem_ptr { trap_with(7) }
  obtain ⟨f2, ra, na, hra, hrest⟩ := seq_run_inv hrun1
  have hafter : ra = .normal (updatePanValueMap s.locals "p" (.word pw)) s.globals s.memory s.ffi ∨
      ra.leaves = false ∧ ra.isNormal = false := by
    rcases ite_run_inv hra with herr | ⟨f3, v1, n', -, hbranch⟩
    · right
      cases ra <;> first | exact ⟨rfl, rfl⟩ | cases herr
    · rcases hbranch with ⟨-, hcall⟩ | ⟨-, hskip⟩
      · exact Or.inr (call_noReturn (trap_with_noReturn hE) (some none) hcall)
      · exact Or.inl (skip_inv hskip)
  rcases hafter with rfl | ⟨hleaves, hnormal⟩
  swap
  · cases ra with
    | normal l g m f => cases hnormal
    | _ =>
      simp only at hrest
      subst hrest
      exact ScratchPost.of_not_returned hleaves
  -- the guard was false: n ≤ p - frame_mem_ptr
  have hguard1 : ∃ fmp, s.globals "frame_mem_ptr" = some (.word fmp) ∧ ¬ (pw - fmp) < nv := by
    rcases ite_run_inv hra with herr | ⟨f3, v1, n', hc1, hbranch⟩
    · cases herr
    · obtain ⟨a, b, hl, hr, hx⟩ := cmp_eval hW hc1
      obtain ⟨va, vb, w, hva, hvb, hop, hw⟩ := eval_op2_inv hW hl
      simp only [eval_local, eval_global] at hva hvb
      have hpl : (updatePanValueMap s.locals "p" (PanValue.word pw)) "p" = some (.word pw) := by
        simp [updatePanValueMap]
      rw [hpl] at hva
      simp only [Option.some.injEq, PanValue.word.injEq] at hva
      subst hva
      have hr' : E.eval ⟨updatePanValueMap s.locals "p" (.word pw), s.globals, s.memory, s.ffi⟩
          (.var .local "n") = some (.word b) := hr
      simp only [eval_local] at hr'
      have hnl : (updatePanValueMap s.locals "p" (PanValue.word pw)) "n" = some (.word nv) := by
        simp [updatePanValueMap, hn]
      rw [hnl] at hr'
      simp only [Option.some.injEq, PanValue.word.injEq] at hr' hw
      subst hr' hw
      simp only [wordOp, Option.some.injEq] at hop
      subst hop
      simp only [PanValue.word.injEq] at hx
      refine ⟨vb, hvb, ?_⟩
      rcases hbranch with ⟨hne, hcall⟩ | ⟨hz, -⟩
      · have := (call_noReturn (trap_with_noReturn hE) (some none) hcall).2
        cases this
      · intro hlt
        rw [hx] at hz
        simp [evalPanCmp, hlt] at hz
  obtain ⟨fmp, hfmp, hge1⟩ := hguard1
  simp only at hrest
  obtain ⟨n2, hrun2⟩ := hrest
  -- var q = (p - n) & (0 - 8)
  rcases dec_run_inv hrun2 with herr | ⟨f4, vq, r4, n4, hvq, hshapeq, hrun4, rfl⟩
  · exact ScratchPost.of_error herr
  refine ScratchPost.restore ?_
  obtain ⟨qw, rfl⟩ := word_of_shape_one hshapeq
  have hqle : qw.toNat ≤ (pw - nv).toNat := by
    obtain ⟨va, vb, w, hva, hvb, hop, hw⟩ := eval_op2_inv hW hvq
    obtain ⟨xa, xb, xw, hxa, hxb, hxop, hxw⟩ := eval_op2_inv hW hva
    simp only [eval_local] at hxa hxb
    have hpl : (updatePanValueMap s.locals "p" (PanValue.word pw)) "p" = some (.word pw) := by
      simp [updatePanValueMap]
    have hnl : (updatePanValueMap s.locals "p" (PanValue.word pw)) "n" = some (.word nv) := by
      simp [updatePanValueMap, hn]
    rw [hpl] at hxa
    rw [hnl] at hxb
    simp only [Option.some.injEq, PanValue.word.injEq] at hxa hxb hxw hw
    subst hxa hxb hxw hw
    simp only [wordOp, Option.some.injEq] at hxop
    subst hxop
    simp only [wordOp, Option.some.injEq, List.foldr] at hop
    subst hop
    show (AndOp.and (pw - nv) (AndOp.and vb (Complement.complement 0))).toNat ≤ (pw - nv).toNat
    exact Nat.and_le_left
  -- if q <+ frame_mem_ptr { trap_with(7) }
  obtain ⟨f5, rb, nb, hrb, hrest2⟩ := seq_run_inv hrun4
  have hafter2 : (rb = .normal (updatePanValueMap (updatePanValueMap s.locals "p" (.word pw)) "q"
        (.word qw)) s.globals s.memory s.ffi ∧ ¬ qw < fmp) ∨
      rb.leaves = false ∧ rb.isNormal = false := by
    rcases ite_run_inv hrb with herr | ⟨f6, v2, n'', hc2, hbranch⟩
    · right
      cases rb <;> first | exact ⟨rfl, rfl⟩ | cases herr
    · rcases hbranch with ⟨-, hcall⟩ | ⟨hz, hskip⟩
      · exact Or.inr (call_noReturn (trap_with_noReturn hE) (some none) hcall)
      · refine Or.inl ⟨skip_inv hskip, ?_⟩
        obtain ⟨a, b, hl, hr, hx⟩ := cmp_eval hW hc2
        have hl' : E.eval ⟨updatePanValueMap (updatePanValueMap s.locals "p" (.word pw)) "q"
            (.word qw), s.globals, s.memory, s.ffi⟩ (.var .local "q") = some (.word a) := hl
        have hr' : E.eval ⟨updatePanValueMap (updatePanValueMap s.locals "p" (.word pw)) "q"
            (.word qw), s.globals, s.memory, s.ffi⟩ (.var .global "frame_mem_ptr") =
            some (.word b) := hr
        simp only [eval_local, eval_global] at hl' hr'
        have hql : (updatePanValueMap (updatePanValueMap s.locals "p" (PanValue.word pw)) "q"
            (PanValue.word qw)) "q" = some (.word qw) := by
          simp [updatePanValueMap]
        rw [hql] at hl'
        rw [hfmp] at hr'
        simp only [Option.some.injEq, PanValue.word.injEq] at hl' hr' hx
        subst hl' hr'
        intro hlt
        rw [hx] at hz
        simp [evalPanCmp, hlt] at hz
  rcases hafter2 with ⟨rfl, hge2⟩ | ⟨hleaves, hnormal⟩
  swap
  · cases rb with
    | normal l g m f => cases hnormal
    | _ =>
      simp only at hrest2
      subst hrest2
      exact ScratchPost.of_not_returned hleaves
  simp only at hrest2
  obtain ⟨n3, hrun5⟩ := hrest2
  -- scratch_ptr = q; return q
  obtain ⟨f7, rc, nc, hrc, hrest3⟩ := seq_run_inv hrun5
  rcases assign_global_inv hrc with herr | ⟨vg, hvg, rfl⟩
  · cases rc with
    | error l g m f =>
      simp only at hrest3
      subst hrest3
      trivial
    | _ => cases herr
  simp only [eval_local] at hvg
  have hql : (updatePanValueMap (updatePanValueMap s.locals "p" (PanValue.word pw)) "q"
      (PanValue.word qw)) "q" = some (.word qw) := by
    simp [updatePanValueMap]
  rw [hql] at hvg
  simp only [Option.some.injEq] at hvg
  subst hvg
  simp only at hrest3
  obtain ⟨n4', hrun6⟩ := hrest3
  rcases return_inv hrun6 with herr | ⟨vr, -, rfl⟩
  · exact ScratchPost.of_error herr
  -- the returned state
  have hsp : updatePanValueMap s.globals "scratch_ptr" (PanValue.word qw) "scratch_ptr" =
      some (.word qw) := by simp [updatePanValueMap]
  have hfp : updatePanValueMap s.globals "scratch_ptr" (PanValue.word qw) "frame_mem_ptr" =
      s.globals "frame_mem_ptr" := by simp [updatePanValueMap]
  refine ⟨?_, rfl, rfl, hfp⟩
  have hfmpq : fmp ≤ qw := BitVec.not_lt.mp hge2
  simp only [scratchRank, hsp, hfp, hfmp, hvp, if_pos hfmpq]
  have hpwlt := pw.isLt
  have hqlt := qw.isLt
  by_cases hreg : fmp ≤ pw
  · rw [if_pos hreg]
    have h1 : nv.toNat ≤ (pw - fmp).toNat := by
      have := BitVec.not_lt.mp hge1
      exact BitVec.le_def.mp this
    have h2 : fmp.toNat ≤ pw.toNat := BitVec.le_def.mp hreg
    have h3 : (pw - fmp).toNat = pw.toNat - fmp.toNat := by
      rw [BitVec.toNat_sub]
      have := fmp.isLt
      omega
    have h4 : (pw - nv).toNat = pw.toNat - nv.toNat := by
      rw [BitVec.toNat_sub]
      have := nv.isLt
      omega
    omega
  · rw [if_neg hreg]
    omega

end InitECandidate.Solver.GuestBound
