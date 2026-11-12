import InitECandidate.Solver.GuestBound.SepChain

/-!
# Giving a frame's region back

`Dom A P`: every heap satisfying `A` owns exactly the memory addresses in
`P`. Points-to cells, ranges and junk have such a domain, and so do their
separating conjunctions. `Fr.region`: the free gap of a frame together with
everything it keeps while suspended is exactly the interval from its memory
buffer to the end of its scratch interval. When a child frame ends, this is
the parent's free gap again.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type}

/-- Every heap satisfying `A` owns exactly the memory addresses in `P`. -/
structure Dom (A : Assn) (P : Word → Prop) : Prop where
  out : ∀ h, A h → Assn.OwnsW P h

theorem Dom.pts {a : Word} {v : PanValue Word} : Dom (.mem a ↦ v) (fun x => x = a) := by
  refine ⟨?_⟩
  rintro h rfl k
  by_cases e : k = .mem a
  · subst e
    simp [Heap.single_self]
  · rw [Heap.single_ne _ e]
    simp only [ne_eq, not_true_eq_false, false_iff]
    rintro ⟨x, rfl, rfl⟩
    exact e rfl

theorem Dom.owns {P : Word → Prop} : Dom (Assn.OwnsW P) P := ⟨fun _ h => h⟩

theorem Dom.range {a b : Word} :
    Dom (Assn.Range a b) (fun x => a.toNat ≤ x.toNat ∧ x.toNat < b.toNat) := ⟨fun _ h => h⟩

theorem Dom.junk {M : Word} {K : Word → Prop} {pv base cap : Word} :
    Dom (JunkW M K pv base cap) (fun x => pv.toNat ≤ x.toNat ∧ x.toNat < M.toNat ∧
      ¬ (base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + 32 * cap.toNat) ∧ ¬ K x) := ⟨fun _ h => h⟩

theorem Dom.sep {A B : Assn} {P Q : Word → Prop} (ha : Dom A P) (hb : Dom B Q) :
    Dom (A ⋆ B) (fun x => P x ∨ Q x) := by
  refine ⟨?_⟩
  rintro h ⟨h1, h2, -, rfl, h1a, h2b⟩ k
  have e1 := ha.out h1 h1a k
  have e2 := hb.out h2 h2b k
  have hu : Heap.union h1 h2 k ≠ none ↔ h1 k ≠ none ∨ h2 k ≠ none := by
    rw [ne_eq, Heap.union_none]
    by_cases c : h1 k = none <;> simp [c]
  rw [hu, e1, e2]
  constructor
  · rintro (⟨x, rfl, hx⟩ | ⟨x, rfl, hx⟩)
    · exact ⟨x, rfl, Or.inl hx⟩
    · exact ⟨x, rfl, Or.inr hx⟩
  · rintro ⟨x, rfl, hx | hx⟩
    · exact Or.inl ⟨x, rfl, hx⟩
    · exact Or.inr ⟨x, rfl, hx⟩

theorem Dom.congr {A : Assn} {P P' : Word → Prop} (h : Dom A P) (hp : ∀ x, P x ↔ P' x) :
    Dom A P' := by
  have : P = P' := funext (fun x => propext (hp x))
  rw [← this]
  exact h

theorem Dom.single {a : Word} {v : PanValue Word} : Dom (.mem a ↦ v) (fun x => x ∈ [a]) :=
  Dom.pts.congr (fun x => by simp)

theorem Dom.cons {a : Word} {v : PanValue Word} {B : Assn} {l : List Word}
    (h : Dom B (fun x => x ∈ l)) : Dom (.mem a ↦ v ⋆ B) (fun x => x ∈ a :: l) :=
  (Dom.sep Dom.pts h).congr (fun x => by simp)

/-- The tracked cells of a frame own exactly `Fr.addrs`. -/
theorem Fr.cells_dom (F : Fr) : Dom F.cells (Fr.addrs F.e F.Z.cc F.Z.msg) := by
  unfold Fr.cells RecCells AccCells
  simp only [Assn.sep_assoc]
  show Dom _ (fun x => x ∈ _)
  repeat (refine Dom.cons ?_)
  exact Dom.single

/-- The free gap and everything a frame keeps while suspended: exactly the
interval from its memory buffer to the end of its scratch interval. -/
theorem Fr.region {D : Word → Prop} (c : Fr) (hok : c.Ok D) (hK : ∀ x, c.K x ↔ Fr.addrs c.e c.Z.cc c.Z.msg x)
    (hKM : ∀ x, c.K x → x.toNat < c.M.toNat) :
    Dom (Assn.Range c.fv c.X.pv ⋆ c.susp)
      (fun x => c.Y.mem.toNat ≤ x.toNat ∧ x.toNat < c.M.toNat) := by
  unfold Fr.susp
  refine Dom.congr (Dom.sep Dom.range (Dom.sep Dom.range (Dom.sep Dom.junk (Dom.sep Dom.range
    ((Fr.cells_dom c).congr (fun x => (hK x).symm)))))) (fun x => ?_)
  have htop := hok.buf.top
  have hfp := hok.ok.ok.fp
  have hpb := hok.ok.pb
  have hbM := hok.ok.bM
  have hcap := hok.ok.ok.cap_le
  have hbh := hok.ok.ok.base_hi
  have e1 : (c.Y.mem + c.Y.cap).toNat = c.fv.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    exact htop
  have e2 : (c.X.base + 32#64 * c.X.cap).toNat = c.X.base.toNat + 32 * c.X.cap.toNat := by
    bv_omega
  rw [e1, e2]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, -, -⟩ | ⟨h1, h2⟩ | hk)
    · omega
    · omega
    · omega
    · omega
    · have := hok.ok.Kpv x hk
      have := hKM x hk
      omega
  · rintro ⟨h1, h2⟩
    by_cases hx1 : x.toNat < c.fv.toNat
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, hx1⟩)))
    by_cases hx2 : x.toNat < c.X.pv.toNat
    · exact Or.inl ⟨by omega, hx2⟩
    by_cases hs : c.X.base.toNat ≤ x.toNat ∧ x.toNat < c.X.base.toNat + 32 * c.X.cap.toNat
    · exact Or.inr (Or.inl hs)
    by_cases hk : c.K x
    · exact Or.inr (Or.inr (Or.inr (Or.inr hk)))
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, h2, hs, hk⟩))

/-- An assertion with a known domain can be forgotten down to ownership. -/
theorem Assn.holds_forget {A R : Assn} {P : Word → Prop} {s : St σ} (hd : Dom A P)
    (h : (A ⋆ R).holds s) : (Assn.OwnsW P ⋆ R).holds s :=
  Assn.holdsV_mono (Assn.sep_mono hd.out (fun _ h => h)) h

/-- When a child frame ends, its gap and everything it kept become one range,
which by `Link` is the parent's free gap. -/
theorem Fr.reclaim {D : Word → Prop} {c p : Fr} {R : Assn} {s : St σ} (hok : c.Ok D) (hl : Link c p)
    (h : (Assn.Range c.fv c.X.pv ⋆ c.susp ⋆ R).holds s) :
    (Assn.Range p.fv p.X.pv ⋆ R).holds s := by
  have h1 : ((Assn.Range c.fv c.X.pv ⋆ c.susp) ⋆ R).holds s := Assn.holds_assoc_l h
  have h2 := Assn.holds_forget (Fr.region c hok hl.Kdom hl.KM) h1
  rw [hl.mem, hl.top] at h2
  exact h2

end InitECandidate.Solver.GuestBound
