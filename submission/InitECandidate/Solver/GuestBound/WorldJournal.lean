import InitECandidate.Solver.GuestBound.HtabFrame
import InitECandidate.Solver.GuestBound.HtabDelAny
import InitECandidate.Solver.GuestBound.OnlyKeeper

/-!
# The journal next to the tables

`TabStep`: what one table operation (`htab_set`, `htab_del`) does to the heap,
in the form the other heap structures need: the heap pointer does not go
down, the key length stays, the blocks stay or move to fresh heap, cells
outside the old footprint and below the old heap pointer are unchanged, and
nothing outside the heap changes.

`JournalOK`: the journal block lies in the heap below the heap pointer, off
every table; each of its `journal_n` entries names a live table and a key
copy that lies below the heap pointer and off every table. That is all
`state_restore` needs to replay the entries with `htab_set` / `htab_del`.
Both invariants survive a `TabStep` (`TabsOK.step`, `JournalOK.step`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {m m' : Word → Option (PanValue Word)} {t : Word} {v v' : HtabV}
  {pv pv' : Word} {T : Word → Option HtabV}

/-- One operation on the live table `t`. -/
structure TabStep (m : Word → Option (PanValue Word)) (pv : Word) (T : Word → Option HtabV)
    (t : Word) (v : HtabV) (m' : Word → Option (PanValue Word)) (pv' : Word) (v' : HtabV) :
    Prop where
  hT : T t = some v
  pv_le : pv.toNat ≤ pv'.toNat
  kl : v'.kl = v.kl
  loc : (v'.keys = v.keys ∧ v'.nodes = v.nodes ∧ v'.order = v.order ∧ v'.nc = v.nc) ∨
    pv.toNat ≤ v'.keys.toNat
  new : TabAt m' pv' t v'
  frame : ∀ a : Word, a.toNat % 8 = 0 → ¬ TabFoot t v a → a.toNat < pv.toNat → m' a = m a
  out : ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m' a = m a

open Classical in
/-- The tables after a step. -/
noncomputable def stepT (T : Word → Option HtabV) (t : Word) (v' : HtabV) : Word → Option HtabV :=
  fun x => if x = t then some v' else T x

theorem TabStep.foot (h : TabStep m pv T t v m' pv' v') :
    ∀ a, TabFoot t v' a → TabFoot t v a ∨ pv.toNat ≤ a.toNat := by
  intro a ha
  rcases ha.2 with hh | hb
  · exact Or.inl ⟨ha.1, Or.inl hh⟩
  · rcases h.loc with ⟨e1, -, e3, e4⟩ | hge
    · exact Or.inl ⟨ha.1, Or.inr (by rw [← e1, ← e3, ← e4]; exact hb)⟩
    · exact Or.inr (by omega)

theorem TabsOK.step (hT : TabsOK m pv T) (h : TabStep m pv T t v m' pv' v') :
    TabsOK m' pv' (stepT T t v') :=
  hT.update h.hT h.pv_le h.new h.foot h.frame

/-- `htab_set` as a step. -/
theorem TabStep.of_set (hT : TabsOK m pv T) (hTt : T t = some v) (hpH : InHeap pv)
    {f : FfiState σ} {l g' : VarName → Option (PanValue Word)}
    (hpost : SetPost m t pv v f (.returned l g' m' f [.word 0#64])) :
    ∃ pv' v', g' "heap_ptr" = some (.word pv') ∧ InHeap pv' ∧ TabStep m pv T t v m' pv' v' := by
  obtain ⟨l0, g0, m0, v', kind', rep', heq, hok', hkl, hloc, ⟨pv', hp', hpH', hend', hpp'⟩, hfr⟩ :=
    hpost
  injection heq with _ hg hm _ _
  subst hg hm
  have hat := hT.at_ t v hTt
  obtain ⟨kind, rep, hok⟩ := hat.ok
  have hk8 := hok.keys8
  have ho8 := hok.order8
  obtain ⟨l1, l2, l3, l4⟩ := hok.wf.layout
  have hkn : v.keys.toNat ≤ v.nodes.toNat := Nat.le_trans (Nat.le_add_right _ _) l2
  have ht8 := hat.t8
  have hlo := hat.lo
  have hfin := hat.fin
  have hp8 := hpH.2
  have hpE := hpH.1
  refine ⟨pv', v', hp', hpH', hTt, hpp', hkl, hloc, ⟨⟨kind', rep', hok'⟩, ht8, hlo, hend'⟩,
    fun a ha8 hna hlt => ?_, fun a ha => ?_⟩
  · refine hfr a ?_ (Or.inl (by omega)) ?_
    · by_contra hc
      exact hna ⟨ha8, Or.inl (by omega)⟩
    · by_contra hc
      exact hna ⟨ha8, Or.inr (by omega)⟩
  · unfold HBASE at ha hlo
    refine hfr a ?_ ?_ ?_ <;> omega

/-- `htab_del` of a stored key as a step. -/
theorem TabStep.of_del (hT : TabsOK m pv T) (hTt : T t = some v) {kind : Nat → NodeKind}
    {rep : KeyRep} (hok : HtabOK m t v kind rep) {Lw : Word} (hL : LiveN v kind Lw.toNat)
    (hLk : kind Lw.toNat = .leaf) (hrel : DelRel m t v Lw m') :
    ∃ v', TabStep m pv T t v m' pv v' := by
  obtain ⟨v', kind', hok', hs⟩ := htab_del_ok hok hL hLk hrel
  obtain ⟨e1, -, -, e4, e5, e6, e7, -, -⟩ := hs
  have hat := hT.at_ t v hTt
  obtain ⟨l1, l2, l3, l4⟩ := hok.wf.layout
  have hkn : v.keys.toNat ≤ v.nodes.toNat := Nat.le_trans (Nat.le_add_right _ _) l2
  have hlo := hat.lo
  have hfin := hat.fin
  have hfr := del_frame hok hL hLk hrel
  refine ⟨v', hTt, Nat.le_refl _, e1, Or.inl ⟨e5, e6, e7, e4⟩,
    ⟨⟨kind', rep, hok'⟩, hat.t8, hlo, by rw [e7, e4]; exact hfin⟩,
    fun a ha8 hna hlt => hfr a ⟨?_, ?_⟩, fun a ha => hfr a ⟨?_, ?_⟩⟩
  · by_contra hc
    exact hna ⟨ha8, Or.inl (by omega)⟩
  · by_contra hc
    exact hna ⟨ha8, Or.inr (by omega)⟩
  · unfold HBASE at ha hlo
    omega
  · unfold HBASE at ha hlo
    omega

/-- A key copy `[kc, kc + kl)` below the heap pointer and off every table. -/
def KeyFree (pv : Word) (T : Word → Option HtabV) (kc kl : Word) : Prop :=
  kc.toNat + kl.toNat ≤ pv.toNat ∧ ∀ u w, T u = some w →
    (kc.toNat + kl.toNat ≤ u.toNat ∨ u.toNat + 88 ≤ kc.toNat) ∧
      (kc.toNat + kl.toNat ≤ w.keys.toNat ∨ w.order.toNat + (w.nc.toNat + 1) * 8 ≤ kc.toNat)

/-- Entry `i` of the journal at `J`: a live table and a free key copy. -/
def JEntry (m : Word → Option (PanValue Word)) (pv : Word) (T : Word → Option HtabV) (J : Word)
    (i : Nat) : Prop :=
  ∃ (t kc fl val : Word) (v : HtabV), Rd m (J + BitVec.ofNat 64 (32 * i)) t ∧
    Rd m (J + BitVec.ofNat 64 (32 * i) + 8#64) kc ∧
    Rd m (J + BitVec.ofNat 64 (32 * i) + 16#64) fl ∧
    Rd m (J + BitVec.ofNat 64 (32 * i) + 24#64) val ∧ T t = some v ∧ KeyFree pv T kc v.kl

/-- The journal: block `[J, J + 32·C)` with `n` entries. -/
structure JournalOK (m : Word → Option (PanValue Word)) (pv : Word) (T : Word → Option HtabV)
    (J C n : Word) : Prop where
  n_le : n.toNat ≤ C.toNat
  al : J.toNat % 8 = 0
  lo : HBASE ≤ J.toNat
  hi : J.toNat + 32 * C.toNat ≤ pv.toNat
  off : ∀ t v, T t = some v → ∀ a, TabFoot t v a →
    a.toNat < J.toNat ∨ J.toNat + 32 * C.toNat ≤ a.toNat
  entry : ∀ i, i < n.toNat → JEntry m pv T J i

theorem KeyFree.step {kc kl : Word} (hk : KeyFree pv T kc kl)
    (h : TabStep m pv T t v m' pv' v') : KeyFree pv' (stepT T t v') kc kl := by
  classical
  refine ⟨by have := hk.1; have := h.pv_le; omega, fun u w hu => ?_⟩
  unfold stepT at hu
  by_cases e : u = t
  · subst e
    simp only [if_true, Option.some.injEq] at hu
    subst hu
    obtain ⟨a1, a2⟩ := hk.2 u v h.hT
    refine ⟨a1, ?_⟩
    rcases h.loc with ⟨e1, -, e3, e4⟩ | hge
    · rw [e1, e3, e4]; exact a2
    · exact Or.inl (by have := hk.1; omega)
  · simp only [if_neg e] at hu
    exact hk.2 u w hu

/-- The journal after a table step, with any smaller entry count. -/
theorem JournalOK.step {J C n n' : Word} (hJ : JournalOK m pv T J C n)
    (hT : TabsOK m pv T) (h : TabStep m pv T t v m' pv' v') (hn : n'.toNat ≤ n.toNat) :
    JournalOK m' pv' (stepT T t v') J C n' := by
  classical
  have hpp := h.pv_le
  have hJhi := hJ.hi
  have hal := hJ.al
  refine ⟨by have := hJ.n_le; omega, hal, hJ.lo, by omega, fun u w hu a ha => ?_,
    fun i hi => ?_⟩
  · unfold stepT at hu
    by_cases e : u = t
    · subst e
      simp only [if_true, Option.some.injEq] at hu
      subst hu
      rcases h.foot a ha with hold | hge
      · exact hJ.off u v h.hT a hold
      · exact Or.inr (by omega)
    · simp only [if_neg e] at hu
      exact hJ.off u w hu a ha
  · obtain ⟨t0, kc, fl, val, v0, r0, r1, r2, r3, hT0, hkf⟩ := hJ.entry i (by omega)
    have hC := hJ.n_le
    have hbase : (J + BitVec.ofNat 64 (32 * i)).toNat = J.toNat + 32 * i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have := pv.isLt
      omega
    have keep : ∀ (c : Nat) (a : Word), a.toNat = J.toNat + 32 * i + c → c % 8 = 0 → c < 32 →
        ∀ w, Rd m a w → Rd m' a w := by
      intro c a ha hc8 hc w hr
      unfold Rd at hr ⊢
      rw [h.frame a (by omega) (fun hf => ?_) (by omega)]
      · exact hr
      · rcases hJ.off t v h.hT a hf with h1 | h1 <;> omega
    have hpvlt := pv.isLt
    have b1 : (J + BitVec.ofNat 64 (32 * i) + 8#64).toNat = J.toNat + 32 * i + 8 := by
      rw [BitVec.toNat_add, hbase]
      simp
      omega
    have b2 : (J + BitVec.ofNat 64 (32 * i) + 16#64).toNat = J.toNat + 32 * i + 16 := by
      rw [BitVec.toNat_add, hbase]
      simp
      omega
    have b3 : (J + BitVec.ofNat 64 (32 * i) + 24#64).toNat = J.toNat + 32 * i + 24 := by
      rw [BitVec.toNat_add, hbase]
      simp
      omega
    by_cases e : t0 = t
    · subst e
      have hv0 : v0 = v := Option.some.inj (hT0.symm.trans h.hT)
      subst hv0
      refine ⟨t0, kc, fl, val, v', keep 0 _ (by rw [hbase]; omega) (by omega) (by omega) _ r0,
        keep 8 _ b1 (by omega) (by omega) _ r1, keep 16 _ b2 (by omega) (by omega) _ r2,
        keep 24 _ b3 (by omega) (by omega) _ r3, by simp [stepT], ?_⟩
      rw [h.kl]
      exact hkf.step h
    · refine ⟨t0, kc, fl, val, v0, keep 0 _ (by rw [hbase]; omega) (by omega) (by omega) _ r0,
        keep 8 _ b1 (by omega) (by omega) _ r1, keep 16 _ b2 (by omega) (by omega) _ r2,
        keep 24 _ b3 (by omega) (by omega) _ r3, by simp [stepT, e, hT0], hkf.step h⟩

end InitECandidate.Solver.GuestBound
