import InitECandidate.Solver.GuestBound.ParseG2

/-!
# Building and moving buffer invariants

`BufsK.ofChain` builds the invariant from a list of buffers in decreasing
address order; `rebase` forgets the reference memory; `carry` moves the
invariant to a memory that agrees on the canonical buffers; `Bufs` (field
size 12) and `BufsK 12` are interchangeable. Used where one function holds
buffers of several field sizes (`bn254_pairing_check`, issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m m' m0 : Word → Option (PanValue Word)} {Wr : List Word} {K : Nat}

/-- Aligned buffers of `32 * K` bytes in decreasing address order, all below `top`. -/
def Chain (K : Nat) : List Word → Nat → Prop
  | [], _ => True
  | B :: rest, top => B.toNat % 8 = 0 ∧ B.toNat + 32 * K ≤ top ∧ Chain K rest B.toNat

theorem Chain.geo {l : List Word} {top : Nat} (h : Chain K l top) :
    ∀ B ∈ l, B.toNat % 8 = 0 ∧ B.toNat + 32 * K ≤ top := by
  induction l generalizing top with
  | nil => intro B hB; cases hB
  | cons A rest ih =>
    obtain ⟨h1, h2, h3⟩ := h
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · exact ⟨h1, h2⟩
    · have := ih h3 B hB
      exact ⟨this.1, by omega⟩

theorem Chain.sep {l : List Word} {top : Nat} (h : Chain K l top) :
    ∀ B ∈ l, ∀ C ∈ l, B = C ∨ B.toNat + 32 * K ≤ C.toNat ∨ C.toNat + 32 * K ≤ B.toNat := by
  induction l generalizing top with
  | nil => intro B hB; cases hB
  | cons A rest ih =>
    obtain ⟨h1, h2, h3⟩ := h
    intro B hB C hC
    rcases List.mem_cons.mp hB with hB0 | hB1
    · rcases List.mem_cons.mp hC with hC0 | hC1
      · exact Or.inl (hB0.trans hC0.symm)
      · rw [hB0]
        exact Or.inr (Or.inr (h3.geo C hC1).2)
    · rcases List.mem_cons.mp hC with hC0 | hC1
      · rw [hC0]
        exact Or.inr (Or.inl (h3.geo B hB1).2)
      · exact ih h3 B hB1 C hC1

/-- The invariant on a chain of buffers below `hp`, none known canonical yet;
all of them writable, the reference memory is the current one. -/
theorem BufsK.ofChain {hp : Word} {All : List Word} (h : Chain K All hp.toNat)
    (hpb : hp.toNat ≤ 2952790016) (hpa : hp.toNat % 8 = 0)
    (m : Word → Option (PanValue Word)) : BufsK K hp m All hp All [] m :=
  ⟨hpb, hpa, Nat.le_refl _, h.geo, h.sep, fun _ hB => (by cases hB), fun _ hB => (by cases hB),
    fun _ _ _ => rfl⟩

/-- Forget the reference memory. -/
theorem BufsK.rebase {pv0 hp : Word} {All Cn : List Word} (h : BufsK K pv0 m0 Wr hp All Cn m) :
    BufsK K pv0 m Wr hp All Cn m :=
  ⟨h.hpb, h.hpa, h.ple, h.geo, h.sep, h.sub, h.can, fun _ _ _ => rfl⟩

/-- Move to a memory that agrees on every canonical buffer. -/
theorem BufsK.carry {pv0 hp : Word} {All Cn : List Word} (h : BufsK K pv0 m0 Wr hp All Cn m)
    (hfr : ∀ B ∈ Cn, ∀ x : Word, B.toNat ≤ x.toNat → x.toNat < B.toNat + 32 * K → m' x = m x) :
    BufsK K pv0 m' Wr hp All Cn m' :=
  ⟨h.hpb, h.hpa, h.ple, h.geo, h.sep, h.sub,
    fun B hB => (h.can B hB).frame (by have := (h.geo B (h.sub B hB)).2; have := h.hpb; omega)
      (hfr B hB), fun _ _ _ => rfl⟩

/-- Keep only some of the canonical buffers and take the current memory as reference. -/
theorem BufsK.carrySub {pv0 hp : Word} {All Cn Cn' : List Word}
    (h : BufsK K pv0 m0 Wr hp All Cn m) (hsub : ∀ B ∈ Cn', B ∈ Cn)
    (hfr : ∀ B ∈ Cn', ∀ x : Word, B.toNat ≤ x.toNat → x.toNat < B.toNat + 32 * K → m' x = m x) :
    BufsK K pv0 m' Wr hp All Cn' m' :=
  (h.mono hsub).carry hfr

theorem Bufs.toK {pv0 hp : Word} {All Cn : List Word} (h : Bufs pv0 m0 Wr hp All Cn m) :
    BufsK 12 pv0 m0 Wr hp All Cn m :=
  ⟨h.hpb, h.hpa, h.ple, fun B hB => by have := h.geo B hB; exact ⟨this.1, by omega⟩,
    fun B hB C hC => by
      rcases h.sep B hB C hC with e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega)),
    h.sub, h.can, fun x hx hW => h.low x hx (fun B hB => by have := hW B hB; omega)⟩

theorem BufsK.to12 {pv0 hp : Word} {All Cn : List Word} (h : BufsK 12 pv0 m0 Wr hp All Cn m) :
    Bufs pv0 m0 Wr hp All Cn m :=
  ⟨h.hpb, h.hpa, h.ple, fun B hB => by have := h.geo B hB; exact ⟨this.1, by omega⟩,
    fun B hB C hC => by
      rcases h.sep B hB C hC with e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega)),
    h.sub, h.can, fun x hx hW => h.low x hx (fun B hB => by have := hW B hB; omega)⟩

end InitECandidate.Solver.GuestBound
