import InitECandidate.Solver.GuestBound.SepDom

/-!
# Carving a fresh range into a frame

A new frame is built in a range `[pv, M)` of the scratch arena that is owned
with unknown contents. `range_carve` splits that range into

* the listed cells `L` (the frame's tracked cells), each owned with unknown
  content (`CellsU L`), ready to be written (`Step.exCell`);
* the stack buffer;
* the rest, as `JunkW M (· ∈ L) pv base cap`.

It is the converse of `Fr.region`, which gives a finished frame's region back.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- `⌜True⌝` is a unit of `⋆`. -/
theorem Assn.true_sep (A : Assn) : (⌜True⌝ ⋆ A) = A := by
  funext h
  apply propext
  constructor
  · rintro ⟨h1, h2, -, rfl, ⟨-, rfl⟩, ha⟩
    rw [Heap.empty_union]
    exact ha
  · intro ha
    exact ⟨Heap.empty, h, Heap.disj_empty h, (Heap.empty_union h).symm, ⟨trivial, rfl⟩, ha⟩

/-- The cells of `L`, owned with unknown content. -/
def CellsU : List Word → Assn
  | [] => ⌜True⌝
  | a :: L => (Assn.ex fun c => Assn.cell (.mem a) c) ⋆ CellsU L

/-- A store into a cell owned with unknown content. -/
theorem Step.exCell {k : Key} {w : PanValue Word} :
    Step k w (Assn.ex fun c => Assn.cell k c) (k ↦ w) := by
  intro V V' R hu h
  obtain ⟨c, hc⟩ := Assn.holdsV_ex.mp h
  exact Step.cell V V' R hu hc

theorem ownsW_single (a : Word) :
    Assn.OwnsW (fun x => x = a) = Assn.ex (fun c => Assn.cell (.mem a) c) := by
  rw [← Assn.owns_single]
  unfold Assn.OwnsW
  congr 1
  funext k
  apply propext
  constructor
  · rintro ⟨x, rfl, rfl⟩
    rfl
  · rintro rfl
    exact ⟨a, rfl, rfl⟩

/-- Split listed cells off an owned set. -/
theorem ownsW_carve (P : Word → Prop) :
    ∀ (L : List Word), L.Nodup → (∀ a, a ∈ L → P a) →
      Assn.OwnsW P = (CellsU L ⋆ Assn.OwnsW (fun x => P x ∧ x ∉ L))
  | [], _, _ => by
      rw [CellsU, Assn.true_sep]
      congr 1
      funext x
      simp
  | a :: L, hn, hL => by
      have hn' := List.nodup_cons.mp hn
      have h1 : Assn.OwnsW P =
          (Assn.OwnsW (fun x => x = a) ⋆ Assn.OwnsW (fun x => P x ∧ x ≠ a)) := by
        refine Assn.ownsW_split (fun x => ?_) (fun x h1 h2 => h2.2 h1)
        constructor
        · intro hx
          by_cases e : x = a
          · exact Or.inl e
          · exact Or.inr ⟨hx, e⟩
        · rintro (rfl | ⟨hx, -⟩)
          · exact hL _ (List.mem_cons_self ..)
          · exact hx
      have h2 := ownsW_carve (fun x => P x ∧ x ≠ a) L hn'.2 (fun b hb =>
        ⟨hL b (List.mem_cons_of_mem _ hb), fun e => hn'.1 (e ▸ hb)⟩)
      have h3 : (fun x => (P x ∧ x ≠ a) ∧ x ∉ L) = (fun x => P x ∧ x ∉ a :: L) := by
        funext x
        apply propext
        simp only [List.mem_cons, not_or]
        tauto
      rw [h1, h2, h3, ownsW_single, CellsU, Assn.sep_assoc]

/-- A fresh range as a frame's tracked cells, stack buffer and junk. -/
theorem range_carve {pv M base cap : Word} (L : List Word) (hn : L.Nodup)
    (hT : (base + 32#64 * cap).toNat = base.toNat + 32 * cap.toNat)
    (hpb : pv.toNat ≤ base.toNat) (hbM : base.toNat + 32 * cap.toNat ≤ M.toNat)
    (hL : ∀ a, a ∈ L → pv.toNat ≤ a.toNat ∧ a.toNat < M.toNat ∧
      ¬ (base.toNat ≤ a.toNat ∧ a.toNat < base.toNat + 32 * cap.toNat)) :
    Assn.Range pv M = (CellsU L ⋆ Assn.Range base (base + 32#64 * cap) ⋆
      JunkW M (fun x => x ∈ L) pv base cap) := by
  rw [Assn.range_eq_ownsW, ownsW_carve _ L hn (fun a ha => ⟨(hL a ha).1, (hL a ha).2.1⟩)]
  congr 1
  rw [Assn.range_eq_ownsW]
  unfold JunkW
  refine Assn.ownsW_split (fun x => ?_) (fun x h1 h2 => h2.2.2.1 ⟨h1.1, by omega⟩)
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    by_cases hs : base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + 32 * cap.toNat
    · exact Or.inl ⟨hs.1, by omega⟩
    · exact Or.inr ⟨h1, h2, hs, h3⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
    · refine ⟨⟨by omega, by omega⟩, fun hx => ?_⟩
      exact (hL x hx).2.2 ⟨h1, by omega⟩
    · exact ⟨⟨h1, h2⟩, h4⟩

end InitECandidate.Solver.GuestBound
