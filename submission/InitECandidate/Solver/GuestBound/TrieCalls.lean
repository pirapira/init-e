import InitECandidate.Solver.GuestBound.TrieBranch
import InitECandidate.Solver.GuestBound.TrieKey

/-!
# Calling the node constructors; branch cells

* `Reg.Le` – the registry grew by nodes only.
* `node_new_branch_ret`, `node_new_leaf_ret`, `node_new_ext_ret` – the world
  lemmas of the constructors, for a returned call (`CalleeRet`).
* `loadByte_byteAt`, `eval_slot_addr` – the address `br + 32 + (ld8 k) * 8` of
  a branch slot, when the byte at `k` is a nibble.
* `branch_val_cell` – the value cells `+160`, `+168` of a branch.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `Rg'` has the tables, blocks and cells of `Rg`, and at least its nodes. -/
structure Reg.Le (Rg Rg' : Reg) : Prop where
  D : Rg'.D = Rg.D
  B : Rg'.B = Rg.B
  Cn : Rg'.Cn = Rg.Cn
  Im : Rg'.Im = Rg.Im
  Nd : ∀ a, Rg.Nd a → Rg'.Nd a
  Kd : ∀ a k, Rg.Kd a k → Rg'.Kd a k

theorem Reg.Le.refl (Rg : Reg) : Rg.Le Rg := ⟨rfl, rfl, rfl, rfl, fun _ h => h, fun _ _ h => h⟩

theorem Reg.Le.trans {R1 R2 R3 : Reg} (h1 : R1.Le R2) (h2 : R2.Le R3) : R1.Le R3 :=
  ⟨h2.D.trans h1.D, h2.B.trans h1.B, h2.Cn.trans h1.Cn, h2.Im.trans h1.Im,
    fun a h => h2.Nd a (h1.Nd a h), fun a k h => h2.Kd a k (h1.Kd a k h)⟩

theorem Reg.Le.addNd (Rg : Reg) (a k : Word) : Rg.Le (Rg.addNd a k) :=
  ⟨rfl, rfl, rfl, rfl, fun _ h => Or.inl h, fun _ _ h => Or.inl h⟩

theorem Reg.addNd_kd (Rg : Reg) (a k : Word) : (Rg.addNd a k).Kd a k := Or.inr ⟨rfl, rfl⟩

section rets

variable {v : PanValue Word} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ} {Rg : Reg}

theorem node_new_branch_ret (hE : GuestEnv E)
    (h : CalleeRet E s "node_new_branch" [] [v] g m ffi) (hW : WorldTJ Rg s.globals s.memory) :
    ∃ a, v = .word a ∧ ffi = s.ffi ∧ WorldTJ (Rg.addNd a 3#64) g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  rcases node_new_branch_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    hW hrun with hst | ⟨l', g', m', a, heq, hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, rfl, rfl, hw, hg, hm⟩

theorem node_new_leaf_ret (hE : GuestEnv E) {e1 e2 e3 e4 : Exp Word} {nib nlen vptr vlen : Word}
    (h : CalleeRet E s "node_new_leaf" [e1, e2, e3, e4] [v] g m ffi)
    (h1 : ∀ y, E.eval s e1 = some y → y = .word nib)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word nlen)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word vptr)
    (h4 : ∀ y, E.eval s e4 = some y → y = .word vlen)
    (hW : WorldTJ Rg s.globals s.memory)
    (hseg : nlen = 0#64 ∨ ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ nib.toNat ∧
      nib.toNat + nlen.toNat ≤ hi.toNat ∧ NibSeg s.memory nib nlen) :
    ∃ a, v = .word a ∧ ffi = s.ffi ∧ WorldTJ (Rg.addNd a 1#64) g m ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m addr = s.memory addr := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 256 hE.functions (by guest_decl_at 256) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil] at hvalues
  cases g1 : E.eval s e1 with
  | none => rw [g1] at hvalues; simp at hvalues
  | some y1 =>
  cases g2 : E.eval s e2 with
  | none => rw [g1, g2] at hvalues; simp at hvalues
  | some y2 =>
  cases g3 : E.eval s e3 with
  | none => rw [g1, g2, g3] at hvalues; simp at hvalues
  | some y3 =>
  cases g4 : E.eval s e4 with
  | none => rw [g1, g2, g3, g4] at hvalues; simp at hvalues
  | some y4 =>
  rw [g1, g2, g3, g4] at hvalues
  have := h1 _ g1
  subst this
  have := h2 _ g2
  subst this
  have := h3 _ g3
  subst this
  have := h4 _ g4
  subst this
  simp only [Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases node_new_leaf_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    nib nlen vptr vlen
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hW hseg hrun with hst | ⟨l', g', m', a, heq, hw, hg, hm⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨a, rfl, rfl, hw, hg, hm⟩

end rets

/-- A byte load, in terms of `byteAt`. -/
theorem loadByte_byteAt (hE : GuestEnv E) {a : Exp Word} {x : PanValue Word} {addr : Word}
    (h : E.eval s (.loadByte a) = some x) (ha : ∀ y, E.eval s a = some y → y = .word addr) :
    ∃ b : Word, x = .word b ∧ byteAt s.memory addr = some b := by
  obtain ⟨addr', cell, h1, h2, rfl⟩ := eval_loadByte hE.mem h
  have := ha _ h1
  simp only [PanValue.word.injEq] at this
  subst this
  rw [hE.bytes] at h2 ⊢
  refine ⟨_, rfl, ?_⟩
  unfold byteAt
  rw [show al8 addr' = RiscV.panRiscVByteAlign 8#64 addr' from rfl, h2]

theorem slot_off_eq (b : Word) (h16 : b.toNat < 16) :
    32#64 + b * 8#64 = BitVec.ofNat 64 (32 + 8 * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem slot_word_eq (br b : Word) (h16 : b.toNat < 16) :
    br + (32#64 + b * 8#64) = br + BitVec.ofNat 64 (32 + 8 * b.toNat) := by
  rw [slot_off_eq b h16]

/-- `br + 32 + (ld8 ea) * 8`, when the byte at the address is a nibble: a child slot. -/
theorem eval_slot_addr (hE : GuestEnv E) {x : VarName} {ea : Exp Word} {br k b0 : Word}
    (hbr : s.locals x = some (.word br)) (hk : ∀ y, E.eval s ea = some y → y = .word k)
    (hb : byteAt s.memory k = some b0) (h16 : b0.toNat < 16) :
    ∀ y, E.eval s (.op .add [.var .local x, .const 32#64,
        .panOp .mul [.loadByte ea, .const 8#64]]) = some y →
      y = .word (br + BitVec.ofNat 64 (32 + 8 * b0.toNat)) := by
  intro y hy
  cases hl : E.eval s (.loadByte ea) with
  | none =>
    simp (config := { decide := true }) [evalF_op hE.word, evalF_panOp, evalArgs_cons,
      evalArgs_nil, evalF_local, hbr, hl, eval_const] at hy
  | some xb =>
    obtain ⟨b, rfl, hb'⟩ := loadByte_byteAt hE hl (addr := k) hk
    rw [hb] at hb'
    simp only [Option.some.injEq] at hb'
    subst hb'
    simp (config := { decide := true }) [evalF_op hE.word, evalF_panOp, evalArgs_cons,
      evalArgs_nil, evalF_local, hbr, hl, eval_const, wordsProj_cons, wordsProj_nil,
      wordOp] at hy
    subst hy
    rw [slot_word_eq br b0 h16]

/-- `br + 32 + idx * 8` for a nibble `idx`: a child slot. -/
theorem eval_slot_idx (hE : GuestEnv E) {x ix : VarName} {br b : Word}
    (hbr : s.locals x = some (.word br)) (hix : s.locals ix = some (.word b))
    (h16 : b.toNat < 16) :
    E.eval s (.op .add [.var .local x, .const 32#64,
        .panOp .mul [.var .local ix, .const 8#64]]) =
      some (.word (br + BitVec.ofNat 64 (32 + 8 * b.toNat))) := by
  simp (config := { decide := true }) [evalF_op hE.word, evalF_panOp, evalArgs_cons,
    evalArgs_nil, evalF_local, hbr, hix, eval_const, wordsProj_cons, wordsProj_nil, wordOp]
  exact slot_off_eq b h16

/-- Word-valued locals, as a list. -/
def Has (l : VarName → Option (PanValue Word)) (xs : List (VarName × Word)) : Prop :=
  ∀ x w, (x, w) ∈ xs → l x = some (.word w)

/-- The value cells of a branch are inside it and not structural. -/
theorem branch_val_cell {a : Word} {c : Nat} (hc : c = 160 ∨ c = 168)
    (htop : a.toNat + 176 ≤ 2952790016) :
    (a.toNat ≤ (a + BitVec.ofNat 64 c).toNat ∧
      (a + BitVec.ofNat 64 c).toNat + 8 ≤ a.toNat + nodeSize 3#64) ∧
      ¬ StructCell a 3#64 (a + BitVec.ofNat 64 c) := by
  have hsz : nodeSize 3#64 = 176 := by decide
  have e : (a + BitVec.ofNat 64 c).toNat = a.toNat + c := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rintro (h | ⟨hk, -⟩ | ⟨-, i, hi, h⟩)
  · have := congrArg BitVec.toNat h
    omega
  · exact absurd hk (by decide)
  · have := congrArg BitVec.toNat h
    have ei : (a + BitVec.ofNat 64 (32 + 8 * i)).toNat = a.toNat + (32 + 8 * i) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    omega

end InitECandidate.Solver.GuestBound
