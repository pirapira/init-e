import InitECandidate.Solver.GuestBound.PolyRules

/-!
# `fq_poly_submul`

`a[s + i] -= q * b[i]` for `i ≤ db`, on canonical coefficients in disjoint
buffers.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Memory after storing four words at `a`. -/
abbrev set4 (m : Word → Option (PanValue Word)) (a w0 w1 w2 w3 : Word) :
    Word → Option (PanValue Word) :=
  setCell (setCell (setCell (setCell m a w0) (a + 8#64) w1) (a + 8#64 + 8#64) w2)
    (a + 8#64 + 8#64 + 8#64) w3

theorem a8_toNat {a : Word} (h : a.toNat + 32 ≤ 2 ^ 64) : (a + 8#64).toNat = a.toNat + 8 := by
  rw [off8]; exact off_toNat (by omega)

theorem a16_toNat {a : Word} (h : a.toNat + 32 ≤ 2 ^ 64) :
    (a + 8#64 + 8#64).toNat = a.toNat + 16 := by
  rw [off16]; exact off_toNat (by omega)

theorem a24_toNat {a : Word} (h : a.toNat + 32 ≤ 2 ^ 64) :
    (a + 8#64 + 8#64 + 8#64).toNat = a.toNat + 24 := by
  rw [off24]; exact off_toNat (by omega)

theorem set4_other {m : Word → Option (PanValue Word)} {a w0 w1 w2 w3 x : Word}
    (h64 : a.toNat + 32 ≤ 2 ^ 64) (hx : x.toNat < a.toNat ∨ a.toNat + 32 ≤ x.toNat) :
    set4 m a w0 w1 w2 w3 x = m x := by
  have NE : ∀ {p q : Word}, p.toNat ≠ q.toNat → p ≠ q := fun h e => h (congrArg _ e)
  unfold set4
  rw [setCell_ne' _ (NE (by rw [a24_toNat h64]; omega)),
    setCell_ne' _ (NE (by rw [a16_toNat h64]; omega)),
    setCell_ne' _ (NE (by rw [a8_toNat h64]; omega)), setCell_ne' _ (NE (by omega))]

theorem fe_set4 {m : Word → Option (PanValue Word)} {a w0 w1 w2 w3 : Word}
    (h64 : a.toNat + 32 ≤ 2 ^ 64) : Fe (set4 m a w0 w1 w2 w3) a (limbsVal [w0, w1, w2, w3]) := by
  have NE : ∀ {p q : Word}, p.toNat ≠ q.toNat → p ≠ q := fun h e => h (congrArg _ e)
  have h8 := a8_toNat h64
  have h16 := a16_toNat h64
  have h24 := a24_toNat h64
  unfold set4
  refine ⟨w0, w1, w2, w3, ?_, ?_, ?_, ?_, rfl⟩
  · exact (((Rd.here m a w0).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))
  · exact ((Rd.here _ _ w1).frame _ (NE (by omega))).frame _ (NE (by omega))
  · exact (Rd.here _ _ w2).frame _ (NE (by omega))
  · exact Rd.here _ _ w3

theorem fe_congr {m m' : Word → Option (PanValue Word)} {a : Word} {n : Nat}
    (h64 : a.toNat + 32 ≤ 2 ^ 64)
    (h : ∀ x : Word, a.toNat ≤ x.toNat → x.toNat < a.toNat + 32 → m' x = m x)
    (hfe : Fe m a n) : Fe m' a n := by
  obtain ⟨w0, w1, w2, w3, c0, c1, c2, c3, hn⟩ := hfe
  refine ⟨w0, w1, w2, w3, ?_, ?_, ?_, ?_, hn⟩
  · rw [h a (Nat.le_refl _) (by omega)]; exact c0
  · rw [h _ (by rw [a8_toNat h64]; omega) (by rw [a8_toNat h64]; omega)]; exact c1
  · rw [h _ (by rw [a16_toNat h64]; omega) (by rw [a16_toNat h64]; omega)]; exact c2
  · rw [h _ (by rw [a24_toNat h64]; omega) (by rw [a24_toNat h64]; omega)]; exact c3

/-- What `fq_poly_submul` does to memory. -/
def SubMulRel (m m' : Word → Option (PanValue Word)) (A : Word) (S D Qv : Nat)
    (ca cb : Nat → Nat) : Prop :=
  (∀ x : Word, (x.toNat < A.toNat + 32 * S ∨ A.toNat + 32 * (S + D + 1) ≤ x.toNat) →
    m' x = m x) ∧
  ∀ i, i ≤ D → ∃ v P, Fe m' (coefAddr A (S + i)) v ∧ P < bnP ∧
    P * 2 ^ 256 % bnP = Qv * cb i % bnP ∧ v = (ca i + bnP - P) % bnP

def SubI (g : VarName → Option (PanValue Word)) (m0 : Word → Option (PanValue Word))
    (f : FfiState σ) (A B sW dbW q0 q1 q2 q3 : Word) (ca cb : Nat → Nat) (j : Nat)
    (a : St σ) : Prop :=
  a.globals = g ∧ a.ffi = f ∧ a.locals "a" = some (.word A) ∧ a.locals "b" = some (.word B) ∧
    a.locals "q" = some (.rStruct [.word q0, .word q1, .word q2, .word q3]) ∧
    a.locals "s" = some (.word sW) ∧ a.locals "db" = some (.word dbW) ∧
    a.locals "i" = some (.word (BitVec.ofNat 64 j)) ∧ j ≤ dbW.toNat + 1 ∧
    (∀ x : Word, (x.toNat < A.toNat + 32 * sW.toNat ∨ A.toNat + 32 * (sW.toNat + j) ≤ x.toNat) →
      a.memory x = m0 x) ∧
    ∀ i, i < j → ∃ v P, Fe a.memory (coefAddr A (sW.toNat + i)) v ∧ P < bnP ∧
      P * 2 ^ 256 % bnP = limbsVal [q0, q1, q2, q3] * cb i % bnP ∧ v = (ca i + bnP - P) % bnP

set_option maxHeartbeats 16000000 in
theorem fq_poly_submul_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq_poly_submul" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A B sW dbW q0 q1 q2 q3 : Word) (ca cb : Nat → Nat)
    (ha : s.locals "a" = some (.word A)) (hb : s.locals "b" = some (.word B))
    (hq : s.locals "q" = some (.rStruct [.word q0, .word q1, .word q2, .word q3]))
    (hs : s.locals "s" = some (.word sW)) (hdb : s.locals "db" = some (.word dbW))
    (hQv : limbsVal [q0, q1, q2, q3] < bnP)
    (hA64 : A.toNat + 32 * (sW.toNat + dbW.toNat + 1) ≤ 2 ^ 64)
    (hB64 : B.toNat + 32 * (dbW.toNat + 1) ≤ 2 ^ 64)
    (hdisj : B.toNat + 32 * (dbW.toNat + 1) ≤ A.toNat + 32 * sW.toNat ∨
      A.toNat + 32 * (sW.toNat + dbW.toNat + 1) ≤ B.toNat)
    (hpb : ∀ i, i ≤ dbW.toNat → Fe s.memory (coefAddr B i) (cb i) ∧ cb i < bnP)
    (hpa : ∀ i, i ≤ dbW.toNat → Fe s.memory (coefAddr A (sW.toNat + i)) (ca i) ∧ ca i < bnP)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      SubMulRel s.memory m' A sW.toNat dbW.toNat (limbsVal [q0, q1, q2, q3]) ca cb := by
  have hbody := (fun_of_index 681 hE.functions (by guest_decl_at 681) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    SubMulRel s.memory m' A sW.toNat dbW.toNat (limbsVal [q0, q1, q2, q3]) ca cb)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    SubMulRel s.memory m' A sW.toNat dbW.toNat (limbsVal [q0, q1, q2, q3]) ca cb) ?_
    (by rintro r ⟨l, m', rfl, hrel⟩; exact ⟨_, m', rfl, hrel⟩)
  have hD64 := dbW.isLt
  have hjt : ∀ j : Nat, j ≤ dbW.toNat + 1 → (BitVec.ofNat 64 j : Word).toNat = j := by
    intro j hj
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine WPs.seqG (fun a => SubI s.globals s.memory s.ffi A B sW dbW q0 q1 q2 q3 ca cb
      (dbW.toNat + 1) a)
    (WPs.loopG (I := fun a => ∃ j, SubI s.globals s.memory s.ffi A B sW dbW q0 q1 q2 q3 ca cb j a)
      ⟨0, rfl, rfl, by lk [ha], by lk [hb], by lk [hq], by lk [hs], by lk [hdb], by lk [],
        Nat.zero_le _, fun _ _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨j, hg, hf, hA, hB, hQ, hS, hDB, hI, hjn, hfr, hent⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hA hB hQ hS hDB hI hfr hent
    subst hg hf
    have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := dbW) (by lk [hDB]))
      (of_eval (w := BitVec.ofNat 64 j) (by lk [hI])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hjD : j ≤ dbW.toNat := by
      by_contra hgt
      have hl : dbW < (BitVec.ofNat 64 j : Word) := by
        rw [BitVec.lt_def, hjt j hjn]
        omega
      rw [hc] at hw
      simp [evalPanCmp, hl] at hw
    have hcB := coefAddr_toNat (a := B) (i := j) (by omega)
    have hcA := coefAddr_toNat (a := A) (i := sW.toNat + j) (by omega)
    have hfeB : Fe ma (coefAddr B j) (cb j) :=
      fe_congr (by rw [hcB]; omega) (fun x h1 h2 => hfr x (by rw [hcB] at h1 h2; omega))
        (hpb j hjD).1
    have hfeA : Fe ma (coefAddr A (sW.toNat + j)) (ca j) :=
      fe_congr (by rw [hcA]; omega) (fun x h1 h2 => hfr x (by rw [hcA] at h1 h2; omega))
        (hpa j hjD).1
    have hsj : sW + BitVec.ofNat 64 j = BitVec.ofNat 64 (sW.toNat + j) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    have hAaddr : ∀ st : St σ, st.locals "a" = some (.word A) → st.locals "s" = some (.word sW) →
        st.locals "i" = some (.word (BitVec.ofNat 64 j)) →
        E.eval st (.op .add [.var .local "a", .panOp .mul [.op .add [.var .local "s",
          .var .local "i"], .const 32#64]]) = some (.word (coefAddr A (sW.toNat + j))) := by
      intro st h1 h2 h3
      unfold coefAddr
      rw [← hsj]
      ev [evalPanOp, h1, h2, h3]
    refine WPs.dec_load4 hE (of_eval (by unfold coefAddr; ev [evalPanOp, hB, hI])) hfeB
      (fun b0 b1 b2 b3 hbv => ?_)
    refine WPs.decCall_fqmul hE (a0 := q0) (a1 := q1) (a2 := q2) (a3 := q3) (b0 := b0) (b1 := b1)
      (b2 := b2) (b3 := b3) (by lk [hQ]) (by lk []) hQv (by rw [hbv]; exact (hpb j hjD).2)
      (fun p0 p1 p2 p3 hPlt hPeq => ?_)
    refine WPs.dec_load4 hE (of_eval (hAaddr _ (by lk [hA]) (by lk [hS]) (by lk [hI]))) hfeA
      (fun a0 a1 a2 a3 hav => ?_)
    refine WPs.seq (fun st => ∃ d0 d1 d2 d3 : Word,
        limbsVal [d0, d1, d2, d3] = (ca j + bnP - limbsVal [p0, p1, p2, p3]) % bnP ∧
        st = ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap la "bi"
          (.rStruct [.word b0, .word b1, .word b2, .word b3])) "p"
          (.rStruct [.word p0, .word p1, .word p2, .word p3])) "ai"
          (.rStruct [.word a0, .word a1, .word a2, .word a3])) "ai"
          (.rStruct [.word d0, .word d1, .word d2, .word d3]), s.globals, ma, s.ffi⟩)
      (WPs.call_fqsub hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b0 := p0) (b1 := p1)
        (b2 := p2) (b3 := p3) (by lk []) (by lk []) (by rw [hav]; exact (hpa j hjD).2) hPlt
        (fun d0 d1 d2 d3 hd => ⟨_, _, _, _, rfl, d0, d1, d2, d3, by rw [hd, hav], rfl⟩)) ?_
    rintro _ ⟨d0, d1, d2, d3, hd, rfl⟩
    refine WPs.seq_store4 hE (w0 := d0) (w1 := d1) (w2 := d2) (w3 := d3)
      (of_eval (hAaddr _ (by lk [hA]) (by lk [hS]) (by lk [hI]))) (by lk []) ?_
    refine WPs.assign (old := BitVec.ofNat 64 j) (by lk [hI])
      (of_eval (w := BitVec.ofNat 64 (j + 1)) (by ev [hI, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    have h64 : (coefAddr A (sW.toNat + j)).toNat + 32 ≤ 2 ^ 64 := by rw [hcA]; omega
    refine ⟨j + 1, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_⟩
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hA]
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hB]
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hQ]
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hS]
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hDB]
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
    · intro x hx
      show set4 ma (coefAddr A (sW.toNat + j)) d0 d1 d2 d3 x = s.memory x
      rw [set4_other h64 (by rw [hcA]; omega)]
      exact hfr x (by omega)
    · intro i hi
      by_cases hij : i = j
      · subst hij
        refine ⟨limbsVal [d0, d1, d2, d3], limbsVal [p0, p1, p2, p3], fe_set4 h64, hPlt, ?_, hd⟩
        rw [hPeq, hbv]
      · obtain ⟨v, P, hfe, hP1, hP2, hv⟩ := hent i (by omega)
        have hci := coefAddr_toNat (a := A) (i := sW.toNat + i) (by omega)
        refine ⟨v, P, fe_congr (by rw [hci]; omega) (fun x h1 h2 => ?_) hfe, hP1, hP2, hv⟩
        show set4 ma (coefAddr A (sW.toNat + j)) d0 d1 d2 d3 x = ma x
        exact set4_other h64 (by rw [hcA]; rw [hci] at h1 h2; omega)
  · rintro a k ⟨j, hg, hf, hA, hB, hQ, hS, hDB, hI, hjn, hfr, hent⟩ hcond
    have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := dbW) (by lk [hDB]))
      (of_eval (w := BitVec.ofNat 64 j) (by lk [hI])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hgt : dbW.toNat < j := by
      by_contra hle
      have hl : ¬ dbW < (BitVec.ofNat 64 j : Word) := by
        rw [BitVec.lt_def, hjt j hjn]
        omega
      simp [evalPanCmp, hl] at hc
    have : j = dbW.toNat + 1 := by omega
    subst this
    exact ⟨hg, hf, hA, hB, hQ, hS, hDB, hI, hjn, hfr, hent⟩
  · rintro a ⟨hg, hf, hA, hB, hQ, hS, hDB, hI, hjn, hfr, hent⟩
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    exact ⟨_, a.memory, by rw [hg, hf], fun x hx => hfr x (by omega),
      fun i hi => hent i (by omega)⟩

end InitECandidate.Solver.GuestBound
