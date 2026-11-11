import InitECandidate.Solver.GuestBound.HtabFind

/-!
# Hash tables: the crit-bit order

`HtabKeys` adds the key order to the structural invariant `HtabWF`: every
internal node tests a bit on which its two subtrees differ and on whose
earlier bits they agree, and bit indices grow towards the leaves. From it,
the root is an ancestor of every live node, and the descent for a stored key
stays on the ancestors of its leaf.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- Ghost key bits: `rep i j` is bit `j` of some key below node `i`. -/
abbrev KeyRep := Nat → Word → Bool

/-- The crit-bit order of a table. -/
structure HtabKeys (m : Word → Option (PanValue Word)) (v : HtabV) (kind : Nat → NodeKind)
    (rep : KeyRep) : Prop where
  internal_bits : ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .internal →
    ∀ b l r : Word, Rd m (nodeField v i 24) b → Rd m (nodeField v i 8) l →
      Rd m (nodeField v i 16) r →
      b.toNat < (v.kl * 8#64).toNat ∧ rep l.toNat b = false ∧ rep r.toNat b = true ∧
      (∀ j : Word, j.toNat < b.toNat → rep l.toNat j = rep i j ∧ rep r.toNat j = rep i j) ∧
      (∀ bl, Rd m (nodeField v l.toNat 24) bl → b.toNat < bl.toNat) ∧
      (∀ br, Rd m (nodeField v r.toNat 24) br → b.toNat < br.toNat)

/-- A node index handed out and not on the free list. -/
def LiveN (v : HtabV) (kind : Nat → NodeKind) (i : Nat) : Prop :=
  1 ≤ i ∧ i < v.next.toNat ∧ kind i ≠ .free

/-- `Anc a c`: following parent fields from `c` reaches `a`. -/
inductive Anc (m : Word → Option (PanValue Word)) (v : HtabV) : Nat → Nat → Prop
  | refl (c : Nat) : Anc m v c c
  | up {a c : Nat} (p : Word) : Rd m (nodeField v c 0) p → p ≠ 0 → Anc m v a p.toNat →
      Anc m v a c

variable {m : Word → Option (PanValue Word)} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
  {rep : KeyRep}

theorem live_bit (hwf : HtabWF m t v kind) {i : Nat} (h : LiveN v kind i) :
    ∃ b, Rd m (nodeField v i 24) b := by
  obtain ⟨h1, h2, h3⟩ := h
  cases hk : kind i with
  | free => exact absurd hk h3
  | leaf =>
    obtain ⟨_, _, _, -, -, -, hb, -⟩ := hwf.leaf_ok i h1 h2 hk
    exact ⟨_, hb⟩
  | internal =>
    obtain ⟨_, _, _, b, -, -, -, hb, -⟩ := hwf.internal_ok i h1 h2 hk
    exact ⟨b, hb⟩

theorem live_parent (hwf : HtabWF m t v kind) {i : Nat} (h : LiveN v kind i) :
    ∃ p, Rd m (nodeField v i 0) p ∧ ParentOk m v kind i p := by
  obtain ⟨h1, h2, h3⟩ := h
  cases hk : kind i with
  | free => exact absurd hk h3
  | leaf =>
    obtain ⟨p, _, _, hp, -, -, -, hpar, -⟩ := hwf.leaf_ok i h1 h2 hk
    exact ⟨p, hp, hpar⟩
  | internal =>
    obtain ⟨p, _, _, _, hp, -, -, -, -, hpar, -⟩ := hwf.internal_ok i h1 h2 hk
    exact ⟨p, hp, hpar⟩

/-- The parent of a live node below the root: a live internal node testing an
earlier bit, with the node as one of its children. -/
theorem parent_internal (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) {i : Nat}
    (hi : i < v.next.toNat) {p : Word} (hpar : ParentOk m v kind i p) (hp0 : p ≠ 0) :
    LiveN v kind p.toNat ∧ kind p.toNat = .internal ∧
      ∃ b l r : Word, Rd m (nodeField v p.toNat 24) b ∧ Rd m (nodeField v p.toNat 8) l ∧
        Rd m (nodeField v p.toNat 16) r ∧ (l.toNat = i ∨ r.toNat = i) ∧
        rep l.toNat b = false ∧ rep r.toNat b = true ∧
        (∀ j : Word, j.toNat < b.toNat → rep i j = rep p.toNat j) ∧
        (∀ bi, Rd m (nodeField v i 24) bi → b.toNat < bi.toNat) := by
  rcases hpar with ⟨h0, -⟩ | ⟨h1, h2, hkind, hchild⟩
  · exact absurd h0 hp0
  obtain ⟨_, l, r, b, -, hl, hr, hb, -⟩ := hwf.internal_ok _ h1 h2 hkind
  obtain ⟨-, hrl, hrr, hagree, hbl, hbr⟩ := hk.internal_bits _ h1 h2 hkind b l r hb hl hr
  have hi64 : i < 2 ^ 64 := by have := v.next.isLt; omega
  have hside : l.toNat = i ∨ r.toNat = i := by
    rcases hchild with hc | hc
    · left
      rw [Rd.inj hl hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
    · right
      rw [Rd.inj hr hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
  refine ⟨⟨h1, h2, by rw [hkind]; exact NodeKind.noConfusion⟩, hkind, b, l, r, hb, hl, hr,
    hside, hrl, hrr, ?_, ?_⟩
  · intro j hj
    rcases hside with rfl | rfl
    · exact (hagree j hj).1
    · exact (hagree j hj).2
  · intro bi hbi
    rcases hside with rfl | rfl
    · exact hbl bi hbi
    · exact hbr bi hbi

/-- The root is an ancestor of every live node. -/
theorem root_anc (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) :
    ∀ (n c : Nat) (b : Word), LiveN v kind c → Rd m (nodeField v c 24) b → b.toNat < n →
      Anc m v v.root.toNat c := by
  intro n
  induction n with
  | zero => intro c b _ _ h; omega
  | succ n ih =>
    intro c b hc hb hlt
    obtain ⟨p, hp, hpar⟩ := live_parent hwf hc
    by_cases hp0 : p = 0
    · rcases hpar with ⟨-, hroot⟩ | ⟨h1, -⟩
      · rw [hroot]
        exact .refl c
      · rw [hp0] at h1
        exact absurd h1 (by decide)
    · obtain ⟨hlive, -, bp, _, _, hbp, -, -, -, -, -, -, hup⟩ :=
        parent_internal hwf hk hc.2.1 hpar hp0
      have := hup b hb
      exact .up p hp hp0 (ih p.toNat bp hlive hbp (by omega))

/-- A strict ancestor of a live node is a live internal node. -/
theorem anc_internal (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) {a c : Nat}
    (h : Anc m v a c) : LiveN v kind c → a ≠ c → LiveN v kind a ∧ kind a = .internal := by
  induction h with
  | refl => intro _ hne; exact absurd rfl hne
  | @up c p hp hp0 _ ih =>
    intro hc _
    obtain ⟨p', hp', hpar⟩ := live_parent hwf hc
    have := Rd.inj hp' hp
    subst this
    obtain ⟨hlive, hkind, -⟩ := parent_internal hwf hk hc.2.1 hpar hp0
    by_cases hap : a = p'.toNat
    · subst hap
      exact ⟨hlive, hkind⟩
    · exact ih hlive hap

/-- Below a strict ancestor `a` of `c`, the child on the side of `c`'s bit at
`a` is again an ancestor of `c`. -/
theorem anc_child (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) {a c : Nat}
    (h : Anc m v a c) : LiveN v kind c → a ≠ c →
      ∀ ba l r bc : Word, Rd m (nodeField v a 24) ba → Rd m (nodeField v a 8) l →
        Rd m (nodeField v a 16) r → Rd m (nodeField v c 24) bc →
        ba.toNat < bc.toNat ∧ (rep c ba = false → Anc m v l.toNat c) ∧
          (rep c ba = true → Anc m v r.toNat c) := by
  induction h with
  | refl => intro _ hne; exact absurd rfl hne
  | @up c p hp hp0 hanc ih =>
    intro hc _ ba l r bc hba hl hr hbc
    obtain ⟨p', hp', hpar⟩ := live_parent hwf hc
    have := Rd.inj hp' hp
    subst this
    obtain ⟨hlive, -, bp, l', r', hbp, hl', hr', hside, hrl, hrr, hagree, hup⟩ :=
      parent_internal hwf hk hc.2.1 hpar hp0
    have hlt := hup bc hbc
    by_cases hap : a = p'.toNat
    · subst hap
      have e1 := Rd.inj hba hbp
      have e2 := Rd.inj hl hl'
      have e3 := Rd.inj hr hr'
      subst e1 e2 e3
      refine ⟨hlt, ?_, ?_⟩
      · intro hf
        rcases hside with rfl | rfl
        · exact .refl _
        · rw [hrr] at hf
          cases hf
      · intro hf
        rcases hside with rfl | rfl
        · rw [hrl] at hf
          cases hf
        · exact .refl _
    · obtain ⟨hlt', hleft, hright⟩ := ih hlive hap ba l r bp hba hl hr hbp
      have hrep : rep c ba = rep p'.toNat ba := hagree ba hlt'
      refine ⟨by omega, ?_, ?_⟩
      · intro hf
        exact .up p' hp hp0 (hleft (hrep ▸ hf))
      · intro hf
        exact .up p' hp hp0 (hright (hrep ▸ hf))

end InitECandidate.Solver.GuestBound
