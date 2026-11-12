import InitECandidate.Solver.GuestBound.IsZeroBytes
import InitECandidate.Solver.GuestBound.FqInv

/-!
# Polynomials over the bn254 base field in memory

A coefficient is four words; a polynomial buffer is consecutive coefficients.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The four words at `a` hold the number `n`. -/
def Fe (m : Word → Option (PanValue Word)) (a : Word) (n : Nat) : Prop :=
  ∃ w0 w1 w2 w3 : Word, m a = some (.word w0) ∧ m (a + 8#64) = some (.word w1) ∧
    m (a + 8#64 + 8#64) = some (.word w2) ∧ m (a + 8#64 + 8#64 + 8#64) = some (.word w3) ∧
    limbsVal [w0, w1, w2, w3] = n

theorem gb_zero (a : Word) : gb a 0#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [gb_toNat]
  simp

theorem off8 (a : Word) : a + 8#64 = off a 8 := rfl

theorem off16 (a : Word) : a + 8#64 + 8#64 = off a 16 := by
  unfold off
  rw [BitVec.add_assoc]
  rfl

theorem off24 (a : Word) : a + 8#64 + 8#64 + 8#64 = off a 24 := by
  unfold off
  rw [BitVec.add_assoc, BitVec.add_assoc]
  rfl

theorem off0 (a : Word) : off a 0 = a := by
  unfold off
  simp

/-- An aligned word cell is zero exactly when its eight bytes are. -/
theorem cell_zero_iff {m : Word → Option (PanValue Word)} {A : Word} {j : Nat} {w : Word}
    (h8 : (A.toNat + j) % 8 = 0) (h64 : A.toNat + j + 8 ≤ 2 ^ 64)
    (hw : m (off A j) = some (.word w)) :
    (∀ k, k < 8 → byteAt m (off A (j + k)) = some 0#64) ↔ w = 0#64 := by
  have hX : (off A j).toNat = A.toNat + j := off_toNat (by omega)
  constructor
  · intro h
    refine word_ext (A := off A j) (B := off A j) (by rw [hX]; exact h8) (by rw [hX]; exact h8)
      (by rw [hX]; exact h64) (by rw [hX]; exact h64) (fun k hk => ?_)
    have := h k hk
    rw [byteAt_cell h64 h8 hk hw] at this
    rw [Option.some.inj this, gb_zero]
  · rintro rfl k hk
    rw [byteAt_cell h64 h8 hk hw, gb_zero]

/-- A coefficient at an aligned address is zero exactly when its 32 bytes are. -/
theorem fe_zero_iff {m : Word → Option (PanValue Word)} {A : Word} {n : Nat}
    (hal : A.toNat % 8 = 0) (h64 : A.toNat + 32 ≤ 2 ^ 64) (hfe : Fe m A n) :
    (∀ k, k < 32 → byteAt m (off A k) = some 0#64) ↔ n = 0 := by
  obtain ⟨w0, w1, w2, w3, h0, h1, h2, h3, hn⟩ := hfe
  rw [← off0 A] at h0
  rw [off8] at h1
  rw [off16] at h2
  rw [off24] at h3
  have c0 := cell_zero_iff (j := 0) (by omega) (by omega) h0
  have c1 := cell_zero_iff (j := 8) (by omega) (by omega) h1
  have c2 := cell_zero_iff (j := 16) (by omega) (by omega) h2
  have c3 := cell_zero_iff (j := 24) (by omega) (by omega) h3
  have t0 := w0.isLt
  have t1 := w1.isLt
  have t2 := w2.isLt
  have t3 := w3.isLt
  simp only [limbsVal] at hn
  constructor
  · intro h
    have e0 := c0.mp (fun k hk => by have := h (0 + k) (by omega); exact this)
    have e1 := c1.mp (fun k hk => h (8 + k) (by omega))
    have e2 := c2.mp (fun k hk => h (16 + k) (by omega))
    have e3 := c3.mp (fun k hk => h (24 + k) (by omega))
    subst e0 e1 e2 e3
    rw [← hn]
    rfl
  · intro hz
    have z0 : w0 = 0#64 := BitVec.eq_of_toNat_eq (by show w0.toNat = 0; omega)
    have z1 : w1 = 0#64 := BitVec.eq_of_toNat_eq (by show w1.toNat = 0; omega)
    have z2 : w2 = 0#64 := BitVec.eq_of_toNat_eq (by show w2.toNat = 0; omega)
    have z3 : w3 = 0#64 := BitVec.eq_of_toNat_eq (by show w3.toNat = 0; omega)
    intro k hk
    obtain ⟨j, k', rfl, hk'⟩ : ∃ j k', k = 8 * j + k' ∧ k' < 8 := ⟨k / 8, k % 8, by omega, by omega⟩
    have hj : j < 4 := by omega
    interval_cases j
    · exact (c0.mpr z0) k' hk'
    · exact (c1.mpr z1) k' hk'
    · exact (c2.mpr z2) k' hk'
    · exact (c3.mpr z3) k' hk'

/-- `var x = is_zero_bytes(e1, e2)`. -/
theorem WPs.decCall_izb (hE : GuestEnv E) {x : VarName} {body : Prog Word} {e1 e2 : Exp Word}
    {p nW : Word} (h1 : E.eval s e1 = some (.word p)) (h2 : E.eval s e2 = some (.word nW))
    (h : ∀ z, ((z = 1#64 ∧ ∀ k, k < nW.toNat → byteAt s.memory (off p k) = some 0#64) ∨
        (z = 0#64 ∧ ∃ k x, k < nW.toNat ∧ byteAt s.memory (off p k) = some x ∧ x ≠ 0#64)) →
      WPs E ⟨updatePanValueMap s.locals x (.word z), s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "is_zero_bytes" [e1, e2] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 19 hE.functions (by guest_decl_at 19) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := is_zero_bytes_spec hE parameters cbody hlookup
    ⟨cl, s.globals, s.memory, s.ffi⟩ rb p nW
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hcallee
  rcases hpost with hst | ⟨l, z, rfl, hz⟩
  · cases rb with
    | raised lr g m f ex v =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f => exact hout.elim
    | _ => exact absurd hst (fun h => h)
  · obtain ⟨r', -, hrun', rfl⟩ := hout
    rcases h z hz r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

end InitECandidate.Solver.GuestBound
