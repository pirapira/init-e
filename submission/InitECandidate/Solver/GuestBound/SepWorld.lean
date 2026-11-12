import InitECandidate.Solver.GuestBound.SepBridge

/-!
# Whole-memory invariants as owned assertions

The invariants of the heap data structures (`HeapOk`, `HtabOK`, the trie
predicates) are stated on the whole memory and globals. `Assn.Region S P`
owns exactly the keys in `S` and says that `P` holds of every view extending
the owned part. With `Local S P` (`P` only looks at keys in `S`) this lets an
old-style specification

  "`P` before; afterwards `P'`, and nothing outside `S` changed"

be used next to other owned assertions (`Assn.region_change`), and the
invariant be read back (`Assn.region_elim`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type}

/-- Owns exactly `S`; `P` holds of every view that extends the owned part. -/
def Assn.Region (S : Key → Prop) (P : View → Prop) : Assn :=
  fun h => (∀ k, h k ≠ none ↔ S k) ∧ ∀ V, Heap.Sub h V → P V

/-- `P` only depends on the keys in `S`. -/
def Local (S : Key → Prop) (P : View → Prop) : Prop :=
  ∀ V V' : View, (∀ k, S k → V' k = V k) → P V → P V'

theorem Local.and {S : Key → Prop} {P Q : View → Prop} (hp : Local S P) (hq : Local S Q) :
    Local S (fun V => P V ∧ Q V) :=
  fun V V' hV h => ⟨hp V V' hV h.1, hq V V' hV h.2⟩

theorem Local.mono {S S' : Key → Prop} {P : View → Prop} (h : Local S P)
    (hS : ∀ k, S k → S' k) : Local S' P :=
  fun V V' hV hP => h V V' (fun k hk => hV k (hS k hk)) hP

theorem Local.const (S : Key → Prop) (φ : Prop) : Local S (fun _ => φ) := fun _ _ _ h => h

/-- The invariant of an owned region holds of the state. -/
theorem Assn.region_elimV {S : Key → Prop} {P : View → Prop} {R : Assn} {V : View}
    (h : (Assn.Region S P ⋆ R).holdsV V) : P V := by
  obtain ⟨h0, hs, h1, h2, hd, rfl, hp, -⟩ := h
  exact hp.2 V ((Heap.sub_union hd).mp hs).1

/-- Forget the invariant, keep the ownership. -/
theorem Assn.region_owns {S : Key → Prop} {P : View → Prop} :
    ∀ h, Assn.Region S P h → Assn.Owns S h := fun _ h => h.1

/-- A step that changes only keys of the region and establishes `P'`. -/
theorem Assn.region_changeV {S : Key → Prop} {P P' : View → Prop} {R : Assn} {V V' : View}
    (h : (Assn.Region S P ⋆ R).holdsV V) (hl : Local S P') (hV : ∀ k, ¬ S k → V' k = V k)
    (hP : P' V') : (Assn.Region S P' ⋆ R).holdsV V' := by
  classical
  obtain ⟨h0, hs, h1, h2, hd, rfl, hp, hr⟩ := h
  obtain ⟨-, hs2⟩ := (Heap.sub_union hd).mp hs
  have h2S : ∀ k c, h2 k = some c → ¬ S k := by
    intro k c hc e
    rcases hd k with e1 | e1
    · exact absurd e1 ((hp.1 k).mpr e)
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
  have hsub1 : Heap.Sub h1' V' := by
    intro k c hc
    by_cases e : S k
    · simp only [h1', e, if_true, Option.some.injEq] at hc
      exact hc
    · simp [h1', e] at hc
  refine ⟨_, (Heap.sub_union hd').mpr ⟨hsub1, ?_⟩, h1', h2, hd', rfl, ⟨?_, ?_⟩, hr⟩
  · intro k c hc
    rw [hV k (h2S k c hc)]
    exact hs2 k c hc
  · intro k
    by_cases e : S k <;> simp [h1', e]
  · intro V2 hV2
    refine hl V' V2 (fun k hk => ?_) hP
    exact hV2 k (V' k) (by simp [h1', hk])

/-- An owned set whose view satisfies a local predicate is a region. -/
theorem Assn.region_introV {S : Key → Prop} {P : View → Prop} {R : Assn} {V : View}
    (h : (Assn.Owns S ⋆ R).holdsV V) (hl : Local S P) (hP : P V) :
    (Assn.Region S P ⋆ R).holdsV V := by
  obtain ⟨h0, hs, h1, h2, hd, rfl, hp, hr⟩ := h
  refine ⟨_, hs, h1, h2, hd, rfl, ⟨hp, fun V2 hV2 => ?_⟩, hr⟩
  have hs1 := ((Heap.sub_union hd).mp hs).1
  refine hl V V2 (fun k hk => ?_) hP
  cases hc : h1 k with
  | none => exact absurd hc ((hp k).mpr hk)
  | some c => rw [hV2 k c hc, hs1 k c hc]

theorem Assn.region_elim {S : Key → Prop} {P : View → Prop} {R : Assn} {s : St σ}
    (h : (Assn.Region S P ⋆ R).holds s) : P s.view := Assn.region_elimV h

theorem Assn.region_change {S : Key → Prop} {P P' : View → Prop} {R : Assn} {s s' : St σ}
    (h : (Assn.Region S P ⋆ R).holds s) (hl : Local S P')
    (hV : ∀ k, ¬ S k → s'.view k = s.view k) (hP : P' s'.view) :
    (Assn.Region S P' ⋆ R).holds s' := Assn.region_changeV h hl hV hP

end InitECandidate.Solver.GuestBound
