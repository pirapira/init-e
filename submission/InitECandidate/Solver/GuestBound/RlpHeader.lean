import InitECandidate.Solver.GuestBound.Guards

/-!
# Specification of `rlp_item_header`

When `rlp_item_header(p, len)` returns `<a, b, flag>`, then
`1 ≤ a + b ≤ len` as natural numbers. This is what makes the offset in
`rlp_list_count` advance without wrapping.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-! ### Reading comparisons -/

theorem cmp_inv (hE : WordEnv E) {s : St σ} {operator : Cmp} {a b : Exp Word} {v : Word}
    (h : E.eval s (.cmp operator a b) = some (.word v)) :
    ∃ va vb, E.eval s a = some (.word va) ∧ E.eval s b = some (.word vb) ∧
      v = evalPanCmp operator va vb := by
  obtain ⟨va, vb, ha, hb, hx⟩ := cmp_eval hE h
  simp only [PanValue.word.injEq] at hx
  exact ⟨va, vb, ha, hb, hx⟩

theorem cmp_equal_zero {a b : Word} (h : evalPanCmp .equal a b = 0) : a ≠ b := by
  intro hab
  simp [evalPanCmp, hab] at h

theorem cmp_lower_zero {a b : Word} (h : evalPanCmp .lower a b = 0) : ¬ a < b := by
  intro hab
  simp [evalPanCmp, hab] at h

theorem cmp_lower_ne {a b : Word} (h : evalPanCmp .lower a b ≠ 0) : a < b := by
  by_cases hab : a < b
  · exact hab
  · simp [evalPanCmp, hab] at h

theorem cmp_notLower_zero {a b : Word} (h : evalPanCmp .notLower a b = 0) : a < b := by
  by_cases hab : a < b
  · exact hab
  · simp [evalPanCmp, hab] at h

theorem cmp_notLower_ne {a b : Word} (h : evalPanCmp .notLower a b ≠ 0) : ¬ a < b := by
  intro hab
  simp [evalPanCmp, hab] at h

/-- A subtraction of two word expressions. -/
theorem eval_sub (hE : WordEnv E) {s : St σ} {a b : Exp Word} {x : PanValue Word}
    (h : E.eval s (.op .sub [a, b]) = some x) :
    ∃ va vb, E.eval s a = some (.word va) ∧ E.eval s b = some (.word vb) ∧
      x = .word (va - vb) := by
  obtain ⟨va, vb, w, ha, hb, hop, hw⟩ := eval_op2_inv hE h
  simp only [wordOp, Option.some.injEq] at hop
  subst hop
  exact ⟨va, vb, ha, hb, hw⟩

/-- An addition of two word expressions. -/
theorem eval_add (hE : WordEnv E) {s : St σ} {a b : Exp Word} {x : PanValue Word}
    (h : E.eval s (.op .add [a, b]) = some x) :
    ∃ va vb, E.eval s a = some (.word va) ∧ E.eval s b = some (.word vb) ∧
      x = .word (va + vb) := by
  obtain ⟨va, vb, w, ha, hb, hop, hw⟩ := eval_op2_inv hE h
  simp only [wordOp, Option.some.injEq, List.foldr] at hop
  subst hop
  refine ⟨va, vb, ha, hb, ?_⟩
  rw [hw]
  simp

/-! ### The postcondition -/

/-- The returned values are a header `<a, b, _>` with `1 ≤ a + b ≤ len`. -/
def headerVals (len : Word) : List (PanValue Word) → Prop
  | [.rStruct [.word a, .word b, _]] => 1 ≤ a.toNat + b.toNat ∧ a.toNat + b.toNat ≤ len.toNat
  | _ => False

/-- A returned header `<a, b, _>` satisfies `1 ≤ a + b ≤ len`. -/
def HeaderPost (len : Word) : Result σ → Prop
  | .returned _ _ _ _ values => headerVals len values
  | _ => True

theorem HeaderPost.of_stops {len : Word} {r : Result σ} (h : Stops r) : HeaderPost len r := by
  obtain ⟨hl, -⟩ := h
  cases r <;> trivial

theorem HeaderPost.of_error {len : Word} {r : Result σ} (h : r.isError = true) :
    HeaderPost len r := HeaderPost.of_stops (Stops.of_error h)

theorem HeaderPost.restore {len : Word} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : HeaderPost len r) :
    HeaderPost len (restorePanValueFfiLocal x old r) := by
  cases r <;> exact h

theorem isNormal_restore {x : VarName} {old : Option (PanValue Word)} {r : Result σ}
    (h : r.isNormal = false) : (restorePanValueFfiLocal x old r).isNormal = false := by
  cases r <;> first | rfl | cases h

/-- `return <e₁, e₂, e₃>` fails or returns the three values. -/
theorem return3_inv {fuel : Nat} {s : St σ} {e₁ e₂ e₃ : Exp Word} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.return (.rStruct [e₁, e₂, e₃])) = some (r, n)) :
    r.isError = true ∨ ∃ v₁ v₂ v₃, E.eval s e₁ = some v₁ ∧ E.eval s e₂ = some v₂ ∧
      E.eval s e₃ = some v₃ ∧
      r = .returned (fun _ => none) s.globals s.memory s.ffi [.rStruct [v₁, v₂, v₃]] := by
  rcases return_inv h with herr | ⟨v, hv, rfl⟩
  · exact Or.inl herr
  · obtain ⟨v₁, v₂, v₃, h₁, h₂, h₃, rfl⟩ := eval_rStruct3_inv hv
    exact Or.inr ⟨v₁, v₂, v₃, h₁, h₂, h₃, rfl⟩

theorem isNormal_of_error {r : Result σ} (h : r.isError = true) : r.isNormal = false := by
  cases r <;> first | rfl | cases h

/-- What a block that always returns or stops gives. -/
def BlockPost (len : Word) (r : Result σ) : Prop := r.isNormal = false ∧ HeaderPost len r

theorem BlockPost.of_error {len : Word} {r : Result σ} (h : r.isError = true) :
    BlockPost len r := ⟨isNormal_of_error h, HeaderPost.of_error h⟩

theorem BlockPost.of_stops {len : Word} {r : Result σ} (h : Stops r) : BlockPost len r :=
  ⟨h.2, HeaderPost.of_stops h⟩

theorem BlockPost.restore {len : Word} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : BlockPost len r) : BlockPost len (restorePanValueFfiLocal x old r) :=
  ⟨isNormal_restore h.1, HeaderPost.restore h.2⟩

/-- The final `return <1, n, flag>` of a short block. -/
theorem short_return (flag : Word) {fuel : Nat} {s : St σ} {r : Result σ} {n : Nat}
    {nw lenv : Word} (hn : s.locals "n" = some (.word nw)) (hle : nw.toNat + 1 ≤ lenv.toNat)
    (h : E.run fuel s (.return (.rStruct [.const 1, .var .local "n", .const flag])) =
      some (r, n)) : BlockPost lenv r := by
  rcases return3_inv h with herr | ⟨v₁, v₂, v₃, h₁, h₂, h₃, rfl⟩
  · exact BlockPost.of_error herr
  simp only [eval_const, eval_local, Option.some.injEq] at h₁ h₂ h₃
  rw [hn] at h₂
  simp only [Option.some.injEq] at h₂
  subst h₁ h₂ h₃
  refine ⟨rfl, ?_⟩
  show 1 ≤ (1 : Word).toNat + nw.toNat ∧ (1 : Word).toNat + nw.toNat ≤ lenv.toNat
  simp only [show (1 : Word).toNat = 1 from rfl]
  omega

/-- The bound `n ≤ len - 1` read from the guard `len - 1 <+ n`. -/
theorem len_guard (hE : WordEnv E) {s : St σ} {x : VarName} {xw lenv : Word}
    (hx : s.locals x = some (.word xw)) (hlen : s.locals "len" = some (.word lenv))
    (hlen1 : 1 ≤ lenv.toNat)
    (hc : E.eval s (.cmp .lower (.op .sub [.var .local "len", .const 1]) (.var .local x)) =
      some (.word 0)) : xw.toNat + 1 ≤ lenv.toNat := by
  obtain ⟨ca, cb, hca, hcb, hz⟩ := cmp_inv hE hc
  obtain ⟨va, vb, hva, hvb, hsub⟩ := eval_sub hE hca
  simp only [eval_local, eval_const, Option.some.injEq, PanValue.word.injEq] at hva hvb hcb
  rw [hlen] at hva
  rw [hx] at hcb
  simp only [Option.some.injEq, PanValue.word.injEq] at hva hcb hsub
  subst hva hvb hcb hsub
  have hnot := cmp_lower_zero hz.symm
  have hle := BitVec.le_def.mp (BitVec.not_lt.mp hnot)
  have h1 : (lenv - 1).toNat = lenv.toNat - 1 := by
    rw [BitVec.toNat_sub]
    simp only [show (1 : Word).toNat = 1 from rfl]
    have := lenv.isLt
    omega
  omega

/-- A short header block: `var n = b - k; if len - 1 <+ n { fail }; return <1, n, flag>`. -/
theorem short_block (hE : GuestEnv E) (k flag : Word) {fuel : Nat} {s : St σ} {r : Result σ}
    {n : Nat} {lenv : Word}
    (hlen : s.locals "len" = some (.word lenv)) (hlen1 : 1 ≤ lenv.toNat)
    (h : E.run fuel s (.dec "n" .one (.op .sub [.var .local "b", .const k])
      (.seq (.ite (.cmp .lower (.op .sub [.var .local "len", .const 1]) (.var .local "n"))
          (.call (some (none, none)) "rlp_fail" [.const 3]) .skip)
        (.return (.rStruct [.const 1, .var .local "n", .const flag])))) = some (r, n)) :
    BlockPost lenv r := by
  rcases dec_run_inv h with herr | ⟨f1, v, r1, n1, hv, -, hrun1, rfl⟩
  · exact BlockPost.of_error herr
  refine BlockPost.restore ?_
  obtain ⟨va, vb, -, -, rfl⟩ := eval_sub hE.word hv
  have hn2 : (updatePanValueMap s.locals "n" (PanValue.word (va - vb))) "n" =
      some (.word (va - vb)) := by simp [updatePanValueMap]
  have hlen2 : (updatePanValueMap s.locals "n" (PanValue.word (va - vb))) "len" =
      some (.word lenv) := by simp [updatePanValueMap, hlen]
  rcases guard_fail_inv (rlp_fail_noReturn hE) hrun1 with hstop | ⟨hc, f2, n2, hrun2⟩
  · exact BlockPost.of_stops hstop
  exact short_return (s := ⟨updatePanValueMap s.locals "n" (PanValue.word (va - vb)), s.globals, s.memory, s.ffi⟩)
    flag hn2 (len_guard (s := ⟨updatePanValueMap s.locals "n" (PanValue.word (va - vb)), s.globals, s.memory, s.ffi⟩) hE.word hn2 hlen2 hlen1 hc) hrun2

/-- `if c₁ { if c₂ { fail } }` stops or changes nothing. -/
theorem extra_guard_inv (hE : GuestEnv E) {fuel : Nat} {s : St σ} {c₁ c₂ : Exp Word}
    {arguments : List (Exp Word)} {r : Result σ} {n : Nat}
    (h : E.run fuel s (.ite c₁ (.ite c₂ (.call (some (none, none)) "rlp_fail" arguments) .skip)
      .skip) = some (r, n)) :
    Stops r ∨ r = .normal s.locals s.globals s.memory s.ffi := by
  rcases ite_run_inv h with herr | ⟨f1, v, n', -, hbranch⟩
  · exact Or.inl (Stops.of_error herr)
  rcases hbranch with ⟨-, hin⟩ | ⟨-, hskip⟩
  · rcases ite_run_inv hin with herr | ⟨f2, v2, n'', -, hbranch2⟩
    · exact Or.inl (Stops.of_error herr)
    rcases hbranch2 with ⟨-, hcall⟩ | ⟨-, hskip⟩
    · exact Or.inl (call_noReturn (rlp_fail_noReturn hE) (some none) hcall)
    · exact Or.inr (skip_inv hskip)
  · exact Or.inr (skip_inv hskip)

/-- A short header block with the extra single-byte check. -/
theorem short_block_extra (hE : GuestEnv E) (k flag : Word) {c₁ c₂ : Exp Word}
    {arguments : List (Exp Word)} {fuel : Nat} {s : St σ} {r : Result σ}
    {n : Nat} {lenv : Word}
    (hlen : s.locals "len" = some (.word lenv)) (hlen1 : 1 ≤ lenv.toNat)
    (h : E.run fuel s (.dec "n" .one (.op .sub [.var .local "b", .const k])
      (.seq (.ite (.cmp .lower (.op .sub [.var .local "len", .const 1]) (.var .local "n"))
          (.call (some (none, none)) "rlp_fail" [.const 3]) .skip)
        (.seq (.ite c₁ (.ite c₂ (.call (some (none, none)) "rlp_fail" arguments) .skip) .skip)
          (.return (.rStruct [.const 1, .var .local "n", .const flag]))))) = some (r, n)) :
    BlockPost lenv r := by
  rcases dec_run_inv h with herr | ⟨f1, v, r1, n1, hv, -, hrun1, rfl⟩
  · exact BlockPost.of_error herr
  refine BlockPost.restore ?_
  obtain ⟨va, vb, -, -, rfl⟩ := eval_sub hE.word hv
  have hn2 : (updatePanValueMap s.locals "n" (PanValue.word (va - vb))) "n" =
      some (.word (va - vb)) := by simp [updatePanValueMap]
  have hlen2 : (updatePanValueMap s.locals "n" (PanValue.word (va - vb))) "len" =
      some (.word lenv) := by simp [updatePanValueMap, hlen]
  rcases guard_fail_inv (rlp_fail_noReturn hE) hrun1 with hstop | ⟨hc, f2, n2, hrun2⟩
  · exact BlockPost.of_stops hstop
  obtain ⟨f3, rx, nx, hrx, hrest⟩ := seq_run_inv hrun2
  rcases extra_guard_inv hE hrx with hstop | rfl
  · cases rx with
    | normal l g m f => exact absurd hstop.2 (by simp [PanValueFfiControlResult.isNormal])
    | _ =>
      simp only at hrest
      subst hrest
      exact BlockPost.of_stops hstop
  · simp only at hrest
    obtain ⟨n3, hrun3⟩ := hrest
    exact short_return (s := ⟨updatePanValueMap s.locals "n" (PanValue.word (va - vb)), s.globals, s.memory, s.ffi⟩)
      flag hn2 (len_guard (s := ⟨updatePanValueMap s.locals "n" (PanValue.word (va - vb)), s.globals, s.memory, s.ffi⟩) hE.word hn2 hlen2 hlen1 hc) hrun3

end InitECandidate.Solver.GuestBound
