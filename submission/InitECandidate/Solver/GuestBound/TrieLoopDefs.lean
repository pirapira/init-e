import InitECandidate.Solver.GuestBound.TrieInsRets

/-!
# The insertion loop: definitions and the two leaf cases

One iteration of `_mpt_insert_node` computes `r` (the node that replaces the
current one) and, when it descends, the next node, the slot that will receive
the next `r`, and the next level. `InsMid` is the state after that block;
`ins_null` and `ins_leaf` are the cases of a null node and of a leaf.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A child slot of a registered extension or branch. -/
def SlotOf (R : Reg) (x : Word) : Prop :=
  (∃ a, R.Kd a 2#64 ∧ x = a + 48#64) ∨
    (∃ a i, R.Kd a 3#64 ∧ i < 16 ∧ x = a + BitVec.ofNat 64 (32 + 8 * i))

theorem SlotOf.mono {R R' : Reg} {x : Word} (h : R.Le R') (hs : SlotOf R x) : SlotOf R' x := by
  rcases hs with ⟨a, hk, rfl⟩ | ⟨a, i, hk, hi, rfl⟩
  · exact Or.inl ⟨a, h.Kd _ _ hk, rfl⟩
  · exact Or.inr ⟨a, i, h.Kd _ _ hk, hi, rfl⟩

/-- The locals of the loop body at the start of the big conditional. -/
structure InsLoc (l : VarName → Option (PanValue Word))
    (key klen vptr vlen lv nd sl res : Word) : Prop where
  key : l "key" = some (.word key)
  klen : l "klen" = some (.word klen)
  vptr : l "vptr" = some (.word vptr)
  vlen : l "vlen" = some (.word vlen)
  level : l "level" = some (.word lv)
  node : l "node" = some (.word nd)
  slot : l "slot" = some (.word sl)
  result : l "result" = some (.word res)
  r : l "r" = some (.word 0#64)
  go : l "go" = some (.word 0#64)
  nn : l "next_node" = some (.word 0#64)
  ns : l "next_slot" = some (.word 0#64)
  nl : l "next_level" = some (.word 0#64)

/-- After the big conditional of one iteration. -/
def InsMid (R0 : Reg) (g0 : VarName → Option (PanValue Word))
    (m0 : Word → Option (PanValue Word)) (key klen vptr vlen lv sl res : Word)
    (l' : VarName → Option (PanValue Word)) (g' : VarName → Option (PanValue Word))
    (m' : Word → Option (PanValue Word)) : Prop :=
  ∃ R rv kk gw nn ns nlv nd', R0.Le R ∧ WorldTJ R g' m' ∧
    (∀ x, x ≠ "heap_ptr" → g' x = g0 x) ∧
    (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) → m' addr = m0 addr) ∧
    l' "key" = some (.word key) ∧ l' "klen" = some (.word klen) ∧
    l' "vptr" = some (.word vptr) ∧ l' "vlen" = some (.word vlen) ∧
    l' "level" = some (.word lv) ∧ l' "node" = some (.word nd') ∧
    l' "slot" = some (.word sl) ∧ l' "result" = some (.word res) ∧
    l' "r" = some (.word rv) ∧ l' "go" = some (.word gw) ∧
    l' "next_node" = some (.word nn) ∧ l' "next_slot" = some (.word ns) ∧
    l' "next_level" = some (.word nlv) ∧ R.Kd rv kk ∧ kk ≠ 0#64 ∧
    (gw = 0#64 ∨ (gw = 1#64 ∧ (nn = 0#64 ∨ ∃ k, R.Kd nn k) ∧ SlotOf R ns ∧
      lv.toNat < nlv.toNat ∧ nlv.toNat ≤ klen.toNat))

/-- The remaining key `[key + lv, key + klen)`, when it is not empty. -/
theorem key_rest {R : Reg} {key klen lv : Word} (hlv : lv.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat) :
    (klen - lv).toNat = klen.toNat - lv.toNat ∧
      (klen - lv ≠ 0#64 → ∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ (key + lv).toNat ∧
        (key + lv).toNat + (klen - lv).toNat ≤ hi.toNat ∧
        (key + lv).toNat = key.toNat + lv.toNat) := by
  have e : (klen - lv).toNat = klen.toNat - lv.toNat := by
    rw [BitVec.toNat_sub]
    omega
  refine ⟨e, fun hne => ?_⟩
  have hk0 : klen ≠ 0#64 := by
    rintro rfl
    exact hne (BitVec.eq_of_toNat_eq (by rw [e]; simp))
  obtain ⟨lo, hi, hI, h1, h2⟩ := hkey hk0
  have := hi.isLt
  have e2 : (key + lv).toNat = key.toNat + lv.toNat := by
    rw [BitVec.toNat_add]
    omega
  exact ⟨lo, hi, hI, by omega, by omega, e2⟩

set_option maxHeartbeats 2000000 in
/-- A null node: `r` is a new leaf with the remaining key. -/
theorem ins_null (hE : GuestEnv E) {R0 : Reg} {key klen vptr vlen lv nd sl res : Word}
    (hL : InsLoc s.locals key klen vptr vlen lv nd sl res)
    (hW : WorldTJ R0 s.globals s.memory) (hlv : lv.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, R0.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hQ : ∀ l' g' m', InsMid R0 s.globals s.memory key klen vptr vlen lv sl res l' g' m' →
      Q (.normal l' g' m' s.ffi)) :
    WPs E s (.call (some (some (.local, "r"), none)) "node_new_leaf"
      [.op .add [.var .local "key", .var .local "level"],
        .op .sub [.var .local "klen", .var .local "level"], .var .local "vptr",
        .var .local "vlen"]) Q := by
  obtain ⟨e, hrest⟩ := key_rest hlv hkey
  refine WPs.callA_ret (fun v g m ffi hret => ?_)
  obtain ⟨a, rfl, rfl, hW1, hg1, hm1⟩ := node_new_leaf_ret hE hret (nib := key + lv)
    (nlen := klen - lv) (vptr := vptr) (vlen := vlen) (of_eval (by ev [hL.key, hL.level]))
    (of_eval (by ev [hL.klen, hL.level])) (of_eval (by lk [hL.vptr]))
    (of_eval (by lk [hL.vlen])) hW (by
      by_cases h0 : klen - lv = 0#64
      · exact Or.inl h0
      · obtain ⟨lo, hi, hI, h1, h2, h3⟩ := hrest h0
        exact Or.inr ⟨lo, hi, hI, h1, h2,
          hW.im_nibs hI (p := key + lv) (c := (klen - lv).toNat) h1 h2⟩)
  exact hQ _ _ _ ⟨R0.addNd a 1#64, a, 1#64, 0#64, 0#64, 0#64, 0#64, nd, Reg.Le.addNd R0 a 1#64,
    hW1, hg1, hm1, by lk [hL.key], by lk [hL.klen], by lk [hL.vptr], by lk [hL.vlen],
    by lk [hL.level], by lk [hL.node], by lk [hL.slot], by lk [hL.result], by lk [],
    by lk [hL.go], by lk [hL.nn], by lk [hL.ns], by lk [hL.nl], Reg.addNd_kd R0 a 1#64,
    by decide, Or.inl rfl⟩

set_option maxHeartbeats 2000000 in
/-- A leaf: `r` is what `_insert_into_leaf` returns. -/
theorem ins_leaf (hE : GuestEnv E) {R0 : Reg} {key klen vptr vlen lv nd sl res : Word}
    (hL : InsLoc s.locals key klen vptr vlen lv nd sl res)
    (hW : WorldTJ R0 s.globals s.memory) (hK : R0.Kd nd 1#64) (hlv : lv.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, R0.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hQ : ∀ l' g' m', InsMid R0 s.globals s.memory key klen vptr vlen lv sl res l' g' m' →
      Q (.normal l' g' m' s.ffi)) :
    WPs E s (.call (some (some (.local, "r"), none)) "_insert_into_leaf"
      [.var .local "node", .op .add [.var .local "key", .var .local "level"],
        .op .sub [.var .local "klen", .var .local "level"], .var .local "vptr",
        .var .local "vlen"]) Q := by
  obtain ⟨e, hrest⟩ := key_rest hlv hkey
  refine WPs.callA_ret (fun v g m ffi hret => ?_)
  obtain ⟨a, R', k, rfl, rfl, hle, hk, hk0, hW1, hg1, hm1⟩ := insert_leaf_ret hE hret
    (node := nd) (rk := key + lv) (rl := klen - lv) (vptr := vptr) (vlen := vlen)
    (of_eval (by lk [hL.node])) (of_eval (by ev [hL.key, hL.level]))
    (of_eval (by ev [hL.klen, hL.level])) (of_eval (by lk [hL.vptr]))
    (of_eval (by lk [hL.vlen])) hW hK (fun h0 => by
      obtain ⟨lo, hi, hI, h1, h2, h3⟩ := hrest h0
      exact ⟨lo, hi, hI, h1, h2⟩)
  exact hQ _ _ _ ⟨R', a, k, 0#64, 0#64, 0#64, 0#64, nd, hle,
    hW1, hg1, hm1, by lk [hL.key], by lk [hL.klen], by lk [hL.vptr], by lk [hL.vlen],
    by lk [hL.level], by lk [hL.node], by lk [hL.slot], by lk [hL.result], by lk [],
    by lk [hL.go], by lk [hL.nn], by lk [hL.ns], by lk [hL.nl], hk, hk0, Or.inl rfl⟩

end InitECandidate.Solver.GuestBound
