import InitECandidate.Solver.GuestBound.RaiseCheck
import InitECandidate.Solver.GuestBound.PolyCalls

/-!
# From whole-state frame facts to owned ranges

`Assn.holds_range_change`: if a step changes memory only inside `[a, b)` and
changes no global, then `Range a b ⋆ R` still holds. This is how results proved
earlier in the "memory is unchanged outside …" style (`memcpy`, `memzero`, the
RLP and trie frame lemmas) are used with the framed logic.

Also: owned ranges are disjoint intervals, the four-word store, and `memcpy`
into an owned range.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Keys outside an owned set did not change: the owned set and the frame survive. -/
theorem Assn.owns_change {S : Key → Prop} {R : Assn} {V V' : View}
    (h : (Assn.Owns S ⋆ R).holdsV V) (hV : ∀ k, ¬ S k → V' k = V k) :
    (Assn.Owns S ⋆ R).holdsV V' := by
  classical
  obtain ⟨h0, hs, h1, h2, hd, rfl, hp, hr⟩ := h
  obtain ⟨-, hs2⟩ := (Heap.sub_union hd).mp hs
  have h2S : ∀ k c, h2 k = some c → ¬ S k := by
    intro k c hc e
    rcases hd k with e1 | e1
    · exact absurd e1 ((hp k).mpr e)
    · rw [e1] at hc; cases hc
  let h1' : Heap := fun k => if S k then some (V' k) else none
  have hd' : Heap.Disj h1' h2 := by
    intro k
    by_cases e : S k
    · right
      cases hc : h2 k with
      | none => rfl
      | some c => exact absurd e (h2S k c hc)
    · left
      simp [h1', e]
  refine ⟨_, (Heap.sub_union hd').mpr ⟨?_, ?_⟩, h1', h2, hd', rfl, ?_, hr⟩
  · intro k c hc
    by_cases e : S k
    · simp [h1', e] at hc
      exact hc
    · simp [h1', e] at hc
  · intro k c hc
    rw [hV k (h2S k c hc)]
    exact hs2 k c hc
  · intro k
    by_cases e : S k <;> simp [h1', e]

/-- Memory changed only inside an owned range, and no global changed. -/
theorem Assn.holds_range_change {a b : Word} {R : Assn} {s s' : St σ}
    (h : (Assn.Range a b ⋆ R).holds s) (hg : s'.globals = s.globals)
    (hm : ∀ x : Word, (x.toNat < a.toNat ∨ b.toNat ≤ x.toNat) → s'.memory x = s.memory x) :
    (Assn.Range a b ⋆ R).holds s' := by
  refine Assn.owns_change h (fun k hk => ?_)
  cases k with
  | glob x => simp [St.view, hg]
  | mem x =>
    refine hm x ?_
    by_cases h1 : x.toNat < a.toNat
    · exact Or.inl h1
    · right
      by_contra h2
      exact hk ⟨x, rfl, by omega, by omega⟩

/-- Two owned non-empty ranges do not overlap. -/
theorem Assn.range_disjoint {a b c d : Word} {R : Assn} {V : View}
    (h : (Assn.Range a b ⋆ Assn.Range c d ⋆ R).holdsV V) (hab : a.toNat < b.toNat)
    (hcd : c.toNat < d.toNat) : b.toNat ≤ c.toNat ∨ d.toNat ≤ a.toNat := by
  obtain ⟨h0, -, h1, h23, hd, rfl, hp1, h2, h3, hd23, rfl, hp2, -⟩ := h
  by_contra hne
  have key : ∃ x : Word, a.toNat ≤ x.toNat ∧ x.toNat < b.toNat ∧ c.toNat ≤ x.toNat ∧
      x.toNat < d.toNat := by
    by_cases hac : a.toNat ≤ c.toNat
    · exact ⟨c, hac, by omega, Nat.le_refl _, hcd⟩
    · exact ⟨a, Nat.le_refl _, hab, by omega, by omega⟩
  obtain ⟨x, hx1, hx2, hx3, hx4⟩ := key
  have e1 : h1 (.mem x) ≠ none := (hp1 _).mpr ⟨x, rfl, hx1, hx2⟩
  have e2 : h2 (.mem x) ≠ none := (hp2 _).mpr ⟨x, rfl, hx3, hx4⟩
  rcases hd (.mem x) with e | e
  · exact e1 e
  · exact e2 (Heap.union_none.mp e).1

/-- `st a, <w0, w1, w2, w3>; rest` into owned cells. -/
theorem WPr.seq_store4_at (hE : GuestEnv E) {a val : Exp Word} {q : Prog Word}
    {addr w0 w1 w2 w3 : Word} {A A1 A2 A3 A' R : Assn} (h : (A ⋆ R).holds s)
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : ∀ y, E.eval s val = some y → y = .rStruct [.word w0, .word w1, .word w2, .word w3])
    (h0 : Step (.mem addr) (.word w0) A A1)
    (h1 : Step (.mem (addr + 8#64)) (.word w1) A1 A2)
    (h2 : Step (.mem (addr + 8#64 + 8#64)) (.word w2) A2 A3)
    (h3 : Step (.mem (addr + 8#64 + 8#64 + 8#64)) (.word w3) A3 A')
    (hq : ∀ m, (A' ⋆ R).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.store a val) q) Q := by
  refine WPr.seq (fun s' => ∃ m, s' = ⟨s.locals, s.globals, m, s.ffi⟩ ∧ (A' ⋆ R).holds s') ?_ ?_
  · intro r hr
    obtain ⟨fuel, n, hrun⟩ := hr
    rcases store_four_inv hE hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
    · exact Or.inl herr
    have := ha _ ha'
    simp only [PanValue.word.injEq] at this
    subst this
    have := hv y hy
    subst this
    have hm' := hm w0 w1 w2 w3 rfl
    subst hm'
    refine Or.inr ⟨_, rfl, ?_⟩
    have e0 := h0 _ _ _ (upd_setCell s addr' w0 s.locals s.ffi) h
    have e1 := h1 _ _ _ (upd_setCell _ (addr' + 8#64) w1 s.locals s.ffi) e0
    have e2 := h2 _ _ _ (upd_setCell _ (addr' + 8#64 + 8#64) w2 s.locals s.ffi) e1
    exact h3 _ _ _ (upd_setCell _ (addr' + 8#64 + 8#64 + 8#64) w3 s.locals s.ffi) e2
  · rintro _ ⟨m, rfl, hm⟩
    exact hq m hm

/-- The values of a three-element argument list. -/
theorem evalArgs3_inv {e1 e2 e3 : Exp Word} {values : List (PanValue Word)}
    (h : E.evalArgs s [e1, e2, e3] = some values) :
    ∃ v1 v2 v3, E.eval s e1 = some v1 ∧ E.eval s e2 = some v2 ∧ E.eval s e3 = some v3 ∧
      values = [v1, v2, v3] := by
  simp only [evalArgs_cons, evalArgs_nil] at h
  cases h1 : E.eval s e1 with
  | none => rw [h1] at h; simp at h
  | some v1 =>
    cases h2 : E.eval s e2 with
    | none => rw [h1, h2] at h; simp at h
    | some v2 =>
      cases h3 : E.eval s e3 with
      | none => rw [h1, h2, h3] at h; simp at h
      | some v3 =>
        rw [h1, h2, h3] at h
        simp at h
        exact ⟨v1, v2, v3, rfl, rfl, rfl, h.symm⟩

/-- `memcpy(dst, src, n); rest` where the destination is an owned range. -/
theorem WPr.seq_memcpy_range (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {q : Prog Word}
    {dst src nW hi : Word} {F : Assn} (h1 : ∀ y, E.eval s e1 = some y → y = .word dst)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word src)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word nW)
    (P : CpPre dst src nW) (hal : dst.toNat % 8 = 0) (hhi : dst.toNat + nW.toNat ≤ hi.toNat)
    (hpre : (Assn.Range dst hi ⋆ F).holds s) (htrap : ∀ r, Trap r → Q r)
    (hq : ∀ m, (Assn.Range dst hi ⋆ F).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "memcpy" [e1, e2, e3]) q) Q := by
  refine WPr.seq (fun s' => ∃ m, s' = ⟨s.locals, s.globals, m, s.ffi⟩ ∧
      (Assn.Range dst hi ⋆ F).holds s')
    (WPr.call_spec (fun rb => RaiseIn (fun _ => false) rb ∧ (Stopped rb ∨ ∃ l m',
      rb = .returned l s.globals m' s.ffi [.word 0#64] ∧
        CopyInv s.memory dst src nW.toNat m')) ?_ ?_ ?_ ?_) ?_
  · intro parameters cbody values cl hlk hvalues hbind r hr
    rcases memcpy_raises hE parameters cbody hlk _ r hr with he | hra
    · exact Or.inl he
    have hparams := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
      hlk).2
    obtain ⟨v1, v2, v3, g1, g2, g3, rfl⟩ := evalArgs3_inv hvalues
    have := h1 _ g1
    subst this
    have := h2 _ g2
    subst this
    have := h3 _ g3
    subst this
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact Or.inr ⟨hra, memcpy_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ r
      dst src nW
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) P hr⟩
  · rintro l g m ffi vs ⟨-, hst | ⟨l', m', heq, hinv⟩⟩
    · exact hst.elim
    injection heq with _ hg hm hf _
    subst hg hm hf
    refine ⟨_, rfl, Assn.holds_range_change hpre rfl (fun x hx => hinv.cells x ?_)⟩
    by_cases hx8 : x.toNat % 8 = 0
    · rcases hx with hx | hx
      · left; omega
      · right; left; omega
    · exact Or.inr (Or.inr hx8)
  · rintro l g m ffi exc v ⟨hra, -⟩
    cases hra
  · intro l g m ffi ev _
    exact htrap _ trivial
  · rintro _ ⟨m, rfl, hm⟩
    exact hq m hm

end InitECandidate.Solver.GuestBound
