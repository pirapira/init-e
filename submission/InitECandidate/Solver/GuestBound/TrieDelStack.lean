import InitECandidate.Solver.GuestBound.TrieCollapse
import InitECandidate.Solver.GuestBound.ScratchFrame

/-!
# The stack of the delete walk

`_mpt_delete_node_body` records every extension and branch it descends through
in a 40-byte scratch record, linked through its first cell; the scratch arena
grows downward, so an older record lies above a newer one. `DelStack` is that
linked list: each record names a registered, levelled node, and the level the
record expects for the result of the subtree below (the extension's child
level, or the branch's level plus one). The predicate only reads scratch
cells in `[sp, lim)`, which no trie operation touches.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {Rg : Reg} {g g' : VarName → Option (PanValue Word)}
  {m m' : Word → Option (PanValue Word)}

/-- The world invariant only reads the heap. -/
theorem WorldTJ.frame_heap (h : WorldTJ Rg g m)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → HBASE ≤ a.toNat → a.toNat < 2952790016 → m' a = m a) :
    WorldTJ Rg g m' := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd, hIm⟩ := h
  have hpE := hpH.1
  refine ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng,
    hW.frame (fun a h8 hb hlt => hm a h8 hb (by omega)), hD, hB, fun x w hc => ?_, hNd,
    hIm.frame (Nat.le_refl _) (fun x hx => by
      obtain ⟨b1, b2, b3⟩ := hIm.cell_bounds hW hx
      exact hm x b1 b2 (by omega))⟩
  obtain ⟨hr, h8, hi, hhi, hf⟩ := hCn x w hc
  refine ⟨?_, h8, hi, hhi, hf⟩
  have := hf.lo_
  have := hf.hi_
  unfold Rd at hr ⊢
  rw [hm x h8 (by omega) (by omega)]
  exact hr

/-- The world invariant does not read the scratch pointer. -/
theorem WorldTJ.of_globals (h : WorldTJ Rg g m) (hg : ∀ x, x ≠ "scratch_ptr" → g' x = g x) :
    WorldTJ Rg g' m := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, rest⟩ := h
  exact ⟨pv, T, N, J, C, n, by rw [hg _ (by decide)]; exact hp, hpH,
    by rw [hg _ (by decide)]; exact hJg, by rw [hg _ (by decide)]; exact hCg,
    by rw [hg _ (by decide)]; exact hng, rest⟩

/-- The records of the delete walk, newest first: `DelStack R m sp lim ℓ0 top ℓ`
says that the stack starting at `top` expects a result at level `ℓ`, and that
the oldest record's node is at level `ℓ0`. -/
inductive DelStack (R : Reg) (m : Word → Option (PanValue Word)) (sp lim : Word) (ℓ0 : Nat) :
    Word → Nat → Prop
  | nil : DelStack R m sp lim ℓ0 0#64 ℓ0
  | ext {top prev node seg sl : Word} {ℓ : Nat} :
      top ≠ 0#64 → top.toNat % 8 = 0 → sp.toNat ≤ top.toNat → top.toNat + 40 ≤ lim.toNat →
      (prev = 0#64 ∨ top.toNat + 40 ≤ prev.toNat) →
      Rd m top prev → Rd m (top + 8#64) node → Rd m (top + 16#64) 2#64 →
      Rd m (top + 24#64) seg → Rd m (top + 32#64) sl →
      R.Kd node 2#64 → R.Lv node ℓ → R.Sg node seg sl →
      DelStack R m sp lim ℓ0 prev ℓ → DelStack R m sp lim ℓ0 top (ℓ + sl.toNat)
  | br {top prev node idx kd : Word} {ℓ : Nat} :
      top ≠ 0#64 → top.toNat % 8 = 0 → sp.toNat ≤ top.toNat → top.toNat + 40 ≤ lim.toNat →
      (prev = 0#64 ∨ top.toNat + 40 ≤ prev.toNat) →
      Rd m top prev → Rd m (top + 8#64) node → Rd m (top + 16#64) kd → kd ≠ 2#64 →
      Rd m (top + 32#64) idx → idx.toNat < 16 →
      R.Kd node 3#64 → R.Lv node ℓ →
      DelStack R m sp lim ℓ0 prev ℓ → DelStack R m sp lim ℓ0 top (ℓ + 1)

theorem DelStack.mono {R R' : Reg} {sp lim top : Word} {ℓ0 ℓ : Nat} (hle : R.Le R')
    (h : DelStack R m sp lim ℓ0 top ℓ) : DelStack R' m sp lim ℓ0 top ℓ := by
  induction h with
  | nil => exact .nil
  | ext h1 h2 h3 h4 h5 r0 r1 r2 r3 r4 hk hl hs _ ih =>
    exact .ext h1 h2 h3 h4 h5 r0 r1 r2 r3 r4 (hle.Kd _ _ hk) (hle.Lv _ _ hl) (hle.Sg _ _ _ hs) ih
  | br h1 h2 h3 h4 h5 r0 r1 r2 hk2 r4 hi hk hl _ ih =>
    exact .br h1 h2 h3 h4 h5 r0 r1 r2 hk2 r4 hi (hle.Kd _ _ hk) (hle.Lv _ _ hl) ih

/-- Offsets inside a record. -/
theorem rec_off {top lim : Word} (h : top.toNat + 40 ≤ lim.toNat) (c : Nat) (hc : c ≤ 32) :
    (top + BitVec.ofNat 64 c).toNat = top.toNat + c := by
  have := lim.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem DelStack.frame {R : Reg} {sp lim top : Word} {ℓ0 ℓ : Nat}
    (hm : ∀ x : Word, sp.toNat ≤ x.toNat → x.toNat < lim.toNat → m' x = m x)
    (h : DelStack R m sp lim ℓ0 top ℓ) : DelStack R m' sp lim ℓ0 top ℓ := by
  have rd : ∀ {top : Word}, sp.toNat ≤ top.toNat → top.toNat + 40 ≤ lim.toNat →
      ∀ (c : Nat) (w : Word), c ≤ 32 → Rd m (top + BitVec.ofNat 64 c) w →
        Rd m' (top + BitVec.ofNat 64 c) w := by
    intro top h3 h4 c w hc hr
    have e := rec_off h4 c hc
    unfold Rd at hr ⊢
    rw [hm _ (by omega) (by omega)]
    exact hr
  have rd0 : ∀ {top : Word}, sp.toNat ≤ top.toNat → top.toNat + 40 ≤ lim.toNat →
      ∀ w : Word, Rd m top w → Rd m' top w := by
    intro top h3 h4 w hr
    unfold Rd at hr ⊢
    rw [hm _ h3 (by omega)]
    exact hr
  induction h with
  | nil => exact .nil
  | ext h1 h2 h3 h4 h5 r0 r1 r2 r3 r4 hk hl hs _ ih =>
    exact .ext h1 h2 h3 h4 h5 (rd0 h3 h4 _ r0) (rd h3 h4 8 _ (by omega) r1)
      (rd h3 h4 16 _ (by omega) r2) (rd h3 h4 24 _ (by omega) r3) (rd h3 h4 32 _ (by omega) r4)
      hk hl hs ih
  | br h1 h2 h3 h4 h5 r0 r1 r2 hk2 r4 hi hk hl _ ih =>
    exact .br h1 h2 h3 h4 h5 (rd0 h3 h4 _ r0) (rd h3 h4 8 _ (by omega) r1)
      (rd h3 h4 16 _ (by omega) r2) hk2 (rd h3 h4 32 _ (by omega) r4) hi hk hl ih

/-- A lower scratch pointer. -/
theorem DelStack.lower {R : Reg} {sp sp' lim top : Word} {ℓ0 ℓ : Nat}
    (hsp : sp'.toNat ≤ sp.toNat) (h : DelStack R m sp lim ℓ0 top ℓ) :
    DelStack R m sp' lim ℓ0 top ℓ := by
  induction h with
  | nil => exact .nil
  | ext h1 h2 h3 h4 h5 r0 r1 r2 r3 r4 hk hl hs _ ih =>
    exact .ext h1 h2 (by omega) h4 h5 r0 r1 r2 r3 r4 hk hl hs ih
  | br h1 h2 h3 h4 h5 r0 r1 r2 hk2 r4 hi hk hl _ ih =>
    exact .br h1 h2 (by omega) h4 h5 r0 r1 r2 hk2 r4 hi hk hl ih

/-- The empty stack expects the entry level. -/
theorem DelStack.zero {R : Reg} {sp lim : Word} {ℓ0 ℓ : Nat}
    (h : DelStack R m sp lim ℓ0 0#64 ℓ) : ℓ = ℓ0 := by
  cases h with
  | nil => rfl
  | ext h1 => exact absurd rfl h1
  | br h1 => exact absurd rfl h1

end InitECandidate.Solver.GuestBound
