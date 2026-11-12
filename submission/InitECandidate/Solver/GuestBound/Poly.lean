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

/-- Address of coefficient `i` of the polynomial at `a`. -/
def coefAddr (a : Word) (i : Nat) : Word := a + BitVec.ofNat 64 i * 32#64

theorem coefAddr_toNat {a : Word} {i : Nat} (h : a.toNat + 32 * i + 32 ≤ 2 ^ 64) :
    (coefAddr a i).toNat = a.toNat + 32 * i := by
  unfold coefAddr
  have h32 : (32#64 : Word).toNat = 32 := by decide
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h32]
  have e1 : i % 2 ^ 64 = i := Nat.mod_eq_of_lt (by omega)
  rw [e1]
  have e2 : i * 32 % 2 ^ 64 = i * 32 := Nat.mod_eq_of_lt (by omega)
  rw [e2]
  exact (Nat.mod_eq_of_lt (by omega)).trans (by omega)

/-- The first `n` coefficients at `a` are `c 0, …, c (n-1)`. -/
def PolyAt (m : Word → Option (PanValue Word)) (a : Word) (c : Nat → Nat) (n : Nat) : Prop :=
  ∀ i, i < n → Fe m (coefAddr a i) (c i)

/-- What `fq_poly_deg` returns: the index of the highest nonzero coefficient, or -1. -/
def DegQ (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (c : Nat → Nat) (n : Nat) (r : Result σ) : Prop :=
  ∃ l d, r = .returned l g m f [.word d] ∧
    ((d = 0#64 - 1#64 ∧ ∀ i, i < n → c i = 0) ∨
      (d.toNat < n ∧ c d.toNat ≠ 0 ∧ ∀ i, d.toNat < i → i < n → c i = 0))

def DegI (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (A : Word) (c : Nat → Nat) (n j : Nat) (a : St σ) : Prop :=
  a.globals = g ∧ a.memory = m ∧ a.ffi = f ∧ a.locals "a" = some (.word A) ∧
    a.locals "i" = some (.word (BitVec.ofNat 64 j)) ∧ j ≤ n ∧
    ∀ k, j ≤ k → k < n → c k = 0

theorem ofNat_pred {j : Nat} (h1 : 1 ≤ j) (hj : j < 2 ^ 64) :
    (BitVec.ofNat 64 j : Word) - 1#64 = BitVec.ofNat 64 (j - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

set_option maxHeartbeats 8000000 in
theorem fq_poly_deg_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq_poly_deg" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A nW : Word) (c : Nat → Nat)
    (ha : s.locals "a" = some (.word A)) (hn : s.locals "n" = some (.word nW))
    (hal : A.toNat % 8 = 0) (h64 : A.toNat + 32 * nW.toNat ≤ 2 ^ 64)
    (hpoly : PolyAt s.memory A c nW.toNat) (h : Runs E s body r) :
    Stopped r ∨ DegQ s.globals s.memory s.ffi c nW.toNat r := by
  have hbody := (fun_of_index 680 hE.functions (by guest_decl_at 680) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (DegQ s.globals s.memory s.ffi c nW.toNat)) r h
  refine WPs.dec (w := nW) (of_eval (by lk [hn])) ?_
  refine WPs.conseq (Q' := DegQ s.globals s.memory s.ffi c nW.toNat) ?_
    (by rintro r ⟨l, d, rfl, hd⟩; exact ⟨_, d, rfl, hd⟩)
  have hjt : ∀ j : Nat, j ≤ nW.toNat → (BitVec.ofNat 64 j : Word).toNat = j := by
    intro j hj
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := nW.isLt; omega)
  have hnn : BitVec.ofNat 64 nW.toNat = nW := by simp
  refine WPs.seqG (fun a => DegI s.globals s.memory s.ffi A c nW.toNat 0 a)
    (WPs.loopG (I := fun a => ∃ j, DegI s.globals s.memory s.ffi A c nW.toNat j a)
      ⟨nW.toNat, rfl, rfl, rfl, by lk [ha], by rw [hnn]; lk [], Nat.le_refl _,
        fun k h1 h2 => absurd h2 (by omega)⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨j, hg, hm, hf, hA, hI, hjn, hz⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hm hf hA hI
    subst hg hm hf
    have hc := eval_cmp_inv hE (op := .lower) (of_eval (eval_const _ (0#64 : Word)))
      (of_eval (w := BitVec.ofNat 64 j) (by lk [hI])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hpos : 0 < j := by
      by_contra hge
      have hnl : ¬ (0#64 : Word) < BitVec.ofNat 64 j := by
        rw [BitVec.lt_def, hjt j hjn]
        show ¬ (0 < j)
        exact hge
      rw [hc] at hw
      simp [evalPanCmp, hnl] at hw
    have hj64 : j < 2 ^ 64 := by have := nW.isLt; omega
    refine WPs.seq (fun a' => a' = ⟨updatePanValueMap la "i" (.word (BitVec.ofNat 64 (j - 1))),
        s.globals, s.memory, s.ffi⟩)
      (WPs.assign (old := BitVec.ofNat 64 j) hI
        (of_eval (w := BitVec.ofNat 64 (j - 1)) (by ev [hI, ofNat_pred (show 1 ≤ j by omega) hj64]))
        ⟨_, _, _, _, rfl, rfl⟩) ?_
    rintro _ rfl
    have hca := coefAddr_toNat (a := A) (i := j - 1) (by omega)
    have hfe := hpoly (j - 1) (by omega)
    have hzi := fe_zero_iff (by rw [hca]; omega) (by rw [hca]; omega) hfe
    have h32 : (32#64 : Word).toNat = 32 := by decide
    refine WPs.decCall_izb hE (p := coefAddr A (j - 1)) (nW := 32#64)
      (by unfold coefAddr; ev [evalPanOp, hA]) (eval_const _ _) (fun z hzq => ?_)
    rw [h32] at hzq
    rcases hzq with ⟨rfl, hall⟩ | ⟨rfl, k, x, hk, hbx, hx0⟩
    · -- zero coefficient: keep going
      refine WPs.ite (w := 0#64) (fun y hy => by
        rw [eval_cmp_inv hE (of_eval (w := 1#64) (by lk [])) (of_eval (eval_const _ _)) y hy]
        rfl) ?_
      rw [if_pos (show (0#64 : Word) = 0 from rfl)]
      refine WPs.skip ?_
      simp only [restorePanValueFfiLocal]
      refine ⟨j - 1, rfl, rfl, rfl, ?_, ?_, by omega, ?_⟩
      · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hA]
      · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      · intro k hk1 hk2
        by_cases hkj : k = j - 1
        · rw [hkj]
          exact hzi.mp hall
        · exact hz k (by omega) hk2
    · -- nonzero coefficient: return its index
      refine WPs.ite (w := 1#64) (fun y hy => by
        rw [eval_cmp_inv hE (of_eval (w := 0#64) (by lk [])) (of_eval (eval_const _ _)) y hy]
        rfl) ?_
      rw [if_neg (by decide)]
      refine WPs.ret (of_eval (w := BitVec.ofNat 64 (j - 1)) (by lk [])) ?_
      refine ⟨_, BitVec.ofNat 64 (j - 1), rfl, Or.inr ?_⟩
      rw [hjt (j - 1) (by omega)]
      refine ⟨by omega, fun h0 => ?_, fun i hi1 hi2 => hz i (by omega) hi2⟩
      have := hzi.mpr h0 k hk
      rw [hbx] at this
      exact hx0 (Option.some.inj this)
  · rintro a k ⟨j, hg, hm, hf, hA, hI, hjn, hz⟩ hcond
    have hc := eval_cmp_inv hE (op := .lower) (of_eval (eval_const _ (0#64 : Word)))
      (of_eval (w := BitVec.ofNat 64 j) (by lk [hI])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hj0 : j = 0 := by
      by_contra hne
      have hl : (0#64 : Word) < BitVec.ofNat 64 j := by
        rw [BitVec.lt_def, hjt j hjn]
        show 0 < j
        omega
      simp [evalPanCmp, hl] at hc
    subst hj0
    exact ⟨hg, hm, hf, hA, hI, hjn, hz⟩
  · rintro a ⟨hg, hm, hf, hA, hI, hjn, hz⟩
    refine WPs.ret (of_eval (w := 0#64 - 1#64) (by ev [])) ?_
    exact ⟨_, 0#64 - 1#64, by rw [hg, hm, hf], Or.inl ⟨rfl, fun i hi => hz i (Nat.zero_le _) hi⟩⟩

end InitECandidate.Solver.GuestBound
