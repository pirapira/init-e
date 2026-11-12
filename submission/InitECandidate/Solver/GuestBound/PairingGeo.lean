import InitECandidate.Solver.GuestBound.PairingCost

/-!
# `bn254_pairing_check`: the layout of its buffers

Eleven allocations above the constant table, of field sizes 1 (`g1`, `t1`),
2 (`g2`, `t2`) and 12 (`Q`, `P`, `fnum`, `fden`, `anum`, `aden`, `res`). One
buffer invariant per field size, and the lemmas that carry one of them across
writes of another (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m m' m0 : Word → Option (PanValue Word)}

/-- Addresses of the buffers of `bn254_pairing_check`, in allocation order. -/
structure PCGeo (Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word) : Prop where
  aGt : Gt.toNat % 8 = 0
  a1 : g1.toNat % 8 = 0
  a2 : g2.toNat % 8 = 0
  a3 : t1.toNat % 8 = 0
  a4 : t2.toNat % 8 = 0
  a5 : Qb.toNat % 8 = 0
  a6 : Pb.toNat % 8 = 0
  a7 : fnum.toNat % 8 = 0
  a8 : fden.toNat % 8 = 0
  a9 : anum.toNat % 8 = 0
  a10 : aden.toNat % 8 = 0
  a11 : res.toNat % 8 = 0
  ahp : hp.toNat % 8 = 0
  o1 : Gt.toNat + 384 ≤ g1.toNat
  o2 : g1.toNat + 96 ≤ g2.toNat
  o3 : g2.toNat + 192 ≤ t1.toNat
  o4 : t1.toNat + 96 ≤ t2.toNat
  o5 : t2.toNat + 192 ≤ Qb.toNat
  o6 : Qb.toNat + 1152 ≤ Pb.toNat
  o7 : Pb.toNat + 1152 ≤ fnum.toNat
  o8 : fnum.toNat + 384 ≤ fden.toNat
  o9 : fden.toNat + 384 ≤ anum.toNat
  o10 : anum.toNat + 384 ≤ aden.toNat
  o11 : aden.toNat + 384 ≤ res.toNat
  o12 : res.toNat + 384 ≤ hp.toNat
  hb : hp.toNat ≤ 2952790016

/-- Offsets of the coordinates of the points in `bn254_pairing_check`. -/
structure PCOff (g1 g2 t1 t2 Qb Pb : Word) : Prop where
  g1b : (g1 + 1#64 * 32#64).toNat = g1.toNat + 32
  g1c : (g1 + 2#64 * (1#64 * 32#64)).toNat = g1.toNat + 64
  t1b : (t1 + 1#64 * 32#64).toNat = t1.toNat + 32
  t1c : (t1 + 2#64 * (1#64 * 32#64)).toNat = t1.toNat + 64
  g2b : (g2 + 2#64 * 32#64).toNat = g2.toNat + 64
  g2c : (g2 + 2#64 * (2#64 * 32#64)).toNat = g2.toNat + 128
  t2b : (t2 + 2#64 * 32#64).toNat = t2.toNat + 64
  t2c : (t2 + 2#64 * (2#64 * 32#64)).toNat = t2.toNat + 128
  q1 : (Qb + 384#64).toNat = Qb.toNat + 384
  q2 : (Qb + 768#64).toNat = Qb.toNat + 768
  p1 : (Pb + 384#64).toNat = Pb.toNat + 384
  p2 : (Pb + 768#64).toNat = Pb.toNat + 768

theorem PCGeo.off {Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word}
    (h : PCGeo Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp) : PCOff g1 g2 t1 t2 Qb Pb := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11,
    o12, hb⟩ := h
  have e32 : (1#64 * 32#64 : Word).toNat = 32 := by decide
  have e64 : (2#64 * (1#64 * 32#64) : Word).toNat = 64 := by decide
  have f64 : (2#64 * 32#64 : Word).toNat = 64 := by decide
  have f128 : (2#64 * (2#64 * 32#64) : Word).toNat = 128 := by decide
  have k384 : (384#64 : Word).toNat = 384 := by decide
  have k768 : (768#64 : Word).toNat = 768 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [add_toNat_small (by omega)] <;> omega

theorem PCGeo.chain1 {Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word}
    (h : PCGeo Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp) :
    Chain 1 [t1 + 2#64 * (1#64 * 32#64), t1 + 1#64 * 32#64, t1, g1 + 2#64 * (1#64 * 32#64), g1 + 1#64 * 32#64, g1] hp.toNat := by
  have ho := h.off
  obtain ⟨-, a1, a2, a3, a4, -, -, -, -, -, -, -, -, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10,
    o11, o12, hb⟩ := h
  obtain ⟨g1b, g1c, t1b, t1c, -, -, -, -, -, -, -, -⟩ := ho
  rw [Chain, Chain, Chain, Chain, Chain, Chain, Chain]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

theorem PCGeo.chain2 {Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word}
    (h : PCGeo Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp) :
    Chain 2 [t2 + 2#64 * (2#64 * 32#64), t2 + 2#64 * 32#64, t2, g2 + 2#64 * (2#64 * 32#64), g2 + 2#64 * 32#64, g2] hp.toNat := by
  have ho := h.off
  obtain ⟨-, a1, a2, a3, a4, -, -, -, -, -, -, -, -, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10,
    o11, o12, hb⟩ := h
  obtain ⟨-, -, -, -, g2b, g2c, t2b, t2c, -, -, -, -⟩ := ho
  rw [Chain, Chain, Chain, Chain, Chain, Chain, Chain]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

theorem PCGeo.chain12 {Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word}
    (h : PCGeo Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp) :
    Chain 12 [res, aden, anum, fden, fnum, Pb + 768#64, Pb + 384#64, Pb, Qb + 768#64, Qb + 384#64, Qb, Gt] hp.toNat := by
  have ho := h.off
  obtain ⟨aGt, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, -, o1, o2, o3, o4, o5, o6, o7, o8,
    o9, o10, o11, o12, hb⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, q1, q2, p1, p2⟩ := ho
  rw [Chain, Chain, Chain, Chain, Chain, Chain, Chain, Chain, Chain, Chain, Chain, Chain, Chain]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> omega

/-- A cell outside `g1` and `t1` is outside every buffer of field size 1. -/
theorem PCGeo.out1 {Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word}
    (h : PCGeo Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp) (x : Word)
    (h1 : x.toNat < g1.toNat ∨ g1.toNat + 96 ≤ x.toNat)
    (h2 : x.toNat < t1.toNat ∨ t1.toNat + 96 ≤ x.toNat) :
    ∀ B ∈ [t1 + 2#64 * (1#64 * 32#64), t1 + 1#64 * 32#64, t1, g1 + 2#64 * (1#64 * 32#64), g1 + 1#64 * 32#64, g1], x.toNat < B.toNat ∨ B.toNat + 32 * 1 ≤ x.toNat := by
  obtain ⟨g1b, g1c, t1b, t1c, -, -, -, -, -, -, -, -⟩ := h.off
  intro B hB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- A cell outside `g2` and `t2` is outside every buffer of field size 2. -/
theorem PCGeo.out2 {Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word}
    (h : PCGeo Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp) (x : Word)
    (h1 : x.toNat < g2.toNat ∨ g2.toNat + 192 ≤ x.toNat)
    (h2 : x.toNat < t2.toNat ∨ t2.toNat + 192 ≤ x.toNat) :
    ∀ B ∈ [t2 + 2#64 * (2#64 * 32#64), t2 + 2#64 * 32#64, t2, g2 + 2#64 * (2#64 * 32#64), g2 + 2#64 * 32#64, g2], x.toNat < B.toNat ∨ B.toNat + 32 * 2 ≤ x.toNat := by
  obtain ⟨-, -, -, -, g2b, g2c, t2b, t2c, -, -, -, -⟩ := h.off
  intro B hB
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- The `Fq12` invariant survives a write that touches only `g1`, `t1` below the heap pointer. -/
theorem PCGeo.carry12_1 {Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word}
    (h : PCGeo Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp)
    (hB : Bufs hp m0 [res, aden, anum, fden, fnum, Pb + 768#64, Pb + 384#64, Pb, Qb + 768#64, Qb + 384#64, Qb, Gt] hp [res, aden, anum, fden, fnum, Pb + 768#64, Pb + 384#64, Pb, Qb + 768#64, Qb + 384#64, Qb, Gt] [aden, anum, Gt] m)
    (hlow : ∀ x : Word, x.toNat < hp.toNat →
      (∀ B ∈ [t1 + 2#64 * (1#64 * 32#64), t1 + 1#64 * 32#64, t1, g1 + 2#64 * (1#64 * 32#64), g1 + 1#64 * 32#64, g1], x.toNat < B.toNat ∨ B.toNat + 32 * 1 ≤ x.toNat) → m' x = m x) :
    Bufs hp m' [res, aden, anum, fden, fnum, Pb + 768#64, Pb + 384#64, Pb, Qb + 768#64, Qb + 384#64, Qb, Gt] hp [res, aden, anum, fden, fnum, Pb + 768#64, Pb + 384#64, Pb, Qb + 768#64, Qb + 384#64, Qb, Gt] [aden, anum, Gt] m' := by
  refine (hB.toK.carry (fun B hBm x h1 h2 => ?_)).to12
  have hg := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11,
    o12, hb⟩ := hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hBm
  rcases hBm with rfl | rfl | rfl <;>
    exact hlow x (by omega) (h.out1 x (by omega) (by omega))

/-- The `Fq12` invariant survives a write that touches only `g2`, `t2` below the heap pointer. -/
theorem PCGeo.carry12_2 {Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word}
    (h : PCGeo Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp)
    (hB : Bufs hp m0 [res, aden, anum, fden, fnum, Pb + 768#64, Pb + 384#64, Pb, Qb + 768#64, Qb + 384#64, Qb, Gt] hp [res, aden, anum, fden, fnum, Pb + 768#64, Pb + 384#64, Pb, Qb + 768#64, Qb + 384#64, Qb, Gt] [aden, anum, Gt] m)
    (hlow : ∀ x : Word, x.toNat < hp.toNat →
      (∀ B ∈ [t2 + 2#64 * (2#64 * 32#64), t2 + 2#64 * 32#64, t2, g2 + 2#64 * (2#64 * 32#64), g2 + 2#64 * 32#64, g2], x.toNat < B.toNat ∨ B.toNat + 32 * 2 ≤ x.toNat) → m' x = m x) :
    Bufs hp m' [res, aden, anum, fden, fnum, Pb + 768#64, Pb + 384#64, Pb, Qb + 768#64, Qb + 384#64, Qb, Gt] hp [res, aden, anum, fden, fnum, Pb + 768#64, Pb + 384#64, Pb, Qb + 768#64, Qb + 384#64, Qb, Gt] [aden, anum, Gt] m' := by
  refine (hB.toK.carry (fun B hBm x h1 h2 => ?_)).to12
  have hg := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11,
    o12, hb⟩ := hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hBm
  rcases hBm with rfl | rfl | rfl <;>
    exact hlow x (by omega) (h.out2 x (by omega) (by omega))

/-- The parsed G1 point survives a write that leaves `[g1, g1 + 96)` alone. -/
theorem PCGeo.carry1 {Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word}
    (h : PCGeo Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp) {Cn : List Word}
    (hB : BufsK 1 hp m0 [t1 + 2#64 * (1#64 * 32#64), t1 + 1#64 * 32#64, t1, g1 + 2#64 * (1#64 * 32#64), g1 + 1#64 * 32#64, g1] hp [t1 + 2#64 * (1#64 * 32#64), t1 + 1#64 * 32#64, t1, g1 + 2#64 * (1#64 * 32#64), g1 + 1#64 * 32#64, g1] Cn m) (hsub : ∀ B ∈ [g1 + 2#64 * (1#64 * 32#64), g1 + 1#64 * 32#64, g1], B ∈ Cn)
    (hfr : ∀ x : Word, g1.toNat ≤ x.toNat → x.toNat < g1.toNat + 96 → m' x = m x) :
    BufsK 1 hp m' [t1 + 2#64 * (1#64 * 32#64), t1 + 1#64 * 32#64, t1, g1 + 2#64 * (1#64 * 32#64), g1 + 1#64 * 32#64, g1] hp [t1 + 2#64 * (1#64 * 32#64), t1 + 1#64 * 32#64, t1, g1 + 2#64 * (1#64 * 32#64), g1 + 1#64 * 32#64, g1] [g1 + 2#64 * (1#64 * 32#64), g1 + 1#64 * 32#64, g1] m' := by
  obtain ⟨g1b, g1c, -, -, -, -, -, -, -, -, -, -⟩ := h.off
  refine hB.carrySub hsub (fun B hBm x h1 h2 => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hBm
  rcases hBm with rfl | rfl | rfl <;> exact hfr x (by omega) (by omega)

/-- The parsed G2 point survives a write that leaves `[g2, g2 + 192)` alone. -/
theorem PCGeo.carry2 {Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp : Word}
    (h : PCGeo Gt g1 g2 t1 t2 Qb Pb fnum fden anum aden res hp) {Cn : List Word}
    (hB : BufsK 2 hp m0 [t2 + 2#64 * (2#64 * 32#64), t2 + 2#64 * 32#64, t2, g2 + 2#64 * (2#64 * 32#64), g2 + 2#64 * 32#64, g2] hp [t2 + 2#64 * (2#64 * 32#64), t2 + 2#64 * 32#64, t2, g2 + 2#64 * (2#64 * 32#64), g2 + 2#64 * 32#64, g2] Cn m) (hsub : ∀ B ∈ [g2 + 2#64 * (2#64 * 32#64), g2 + 2#64 * 32#64, g2], B ∈ Cn)
    (hfr : ∀ x : Word, g2.toNat ≤ x.toNat → x.toNat < g2.toNat + 192 → m' x = m x) :
    BufsK 2 hp m' [t2 + 2#64 * (2#64 * 32#64), t2 + 2#64 * 32#64, t2, g2 + 2#64 * (2#64 * 32#64), g2 + 2#64 * 32#64, g2] hp [t2 + 2#64 * (2#64 * 32#64), t2 + 2#64 * 32#64, t2, g2 + 2#64 * (2#64 * 32#64), g2 + 2#64 * 32#64, g2] [g2 + 2#64 * (2#64 * 32#64), g2 + 2#64 * 32#64, g2] m' := by
  obtain ⟨-, -, -, -, g2b, g2c, -, -, -, -, -, -⟩ := h.off
  refine hB.carrySub hsub (fun B hBm x h1 h2 => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hBm
  rcases hBm with rfl | rfl | rfl <;> exact hfr x (by omega) (by omega)

end InitECandidate.Solver.GuestBound
