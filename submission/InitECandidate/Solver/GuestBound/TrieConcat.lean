import InitECandidate.Solver.GuestBound.TrieFresh

/-!
# `nibbles_concat` against the world invariant

The concatenation of two nibble arrays lying in immutable blocks is a fresh
immutable block.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

set_option maxHeartbeats 8000000 in
theorem nibbles_concat_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "nibbles_concat" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (a al b bl : Word)
    (ha : s.locals "a" = some (.word a)) (hal : s.locals "al" = some (.word al))
    (hb : s.locals "b" = some (.word b)) (hbl : s.locals "bl" = some (.word bl))
    (hW : WorldTJ Rg s.globals s.memory)
    (haI : al ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ a.toNat ∧
      a.toNat + al.toNat ≤ hi.toNat)
    (hbI : bl ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ b.toNat ∧
      b.toNat + bl.toNat ≤ hi.toNat)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' out, r = .returned l g' m' s.ffi [.word out] ∧
      WorldTJ (Rg.addIm out (out + (al + bl))) g' m' ∧
      (out + (al + bl)).toNat = out.toNat + al.toNat + bl.toNat ∧
      s.globals "heap_ptr" = some (.word out) ∧
      (∀ A : Word, A.toNat % 8 = 0 → A.toNat + 8 ≤ out.toNat → m' A = s.memory A) ∧
      (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 252 hE.functions (by guest_decl_at 252) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' out, r = .returned l g' m' s.ffi [.word out] ∧
    WorldTJ (Rg.addIm out (out + (al + bl))) g' m' ∧
    (out + (al + bl)).toNat = out.toNat + al.toNat + bl.toNat ∧
    s.globals "heap_ptr" = some (.word out) ∧
    (∀ A : Word, A.toNat % 8 = 0 → A.toNat + 8 ≤ out.toNat → m' A = s.memory A) ∧
    (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  -- where the sources are: below the heap pointer, and nibbles
  obtain ⟨pv, hp, hpH, hsa, hsb⟩ : ∃ pv, s.globals "heap_ptr" = some (.word pv) ∧ InHeap pv ∧
      (Nibs s.memory a al.toNat ∧ (al.toNat = 0 ∨ a.toNat + al.toNat ≤ pv.toNat)) ∧
      (Nibs s.memory b bl.toNat ∧ (bl.toNat = 0 ∨ b.toNat + bl.toNat ≤ pv.toNat)) := by
    have hW0 := hW
    obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hD, hB, hCn, hNd, hIm⟩ := hW
    refine ⟨pv, hp, hpH, ?_, ?_⟩
    · by_cases h0 : al = 0#64
      · subst h0
        exact ⟨fun j hj => absurd hj (by simp), Or.inl rfl⟩
      · obtain ⟨lo, hi, hI, h1, h2⟩ := haI h0
        have := (hIm.free lo hi hI).2.hi_
        exact ⟨hW0.im_nibs hI h1 h2, Or.inr (by omega)⟩
    · by_cases h0 : bl = 0#64
      · subst h0
        exact ⟨fun j hj => absurd hj (by simp), Or.inl rfl⟩
      · obtain ⟨lo, hi, hI, h1, h2⟩ := hbI h0
        have := (hIm.free lo hi hI).2.hi_
        exact ⟨hW0.im_nibs hI h1 h2, Or.inr (by omega)⟩
  obtain ⟨hna, hpa⟩ := hsa
  obtain ⟨hnb, hpb⟩ := hsb
  have hpE := hpH.1
  have hp8 := hpH.2
  have hpB : HBASE ≤ pv.toNat := by
    obtain ⟨pv', T, N, J, C, n, hp', hpH', hJg, hCg, hng, hHW, -⟩ := hW
    have e : pv' = pv := by
      rw [hp] at hp'
      simpa using hp'.symm
    subst e
    have := hHW.jrn.lo
    have := hHW.jrn.hi
    omega
  have eab : (al + bl).toNat = al.toNat + bl.toNat := by
    rw [BitVec.toNat_add]
    omega
  refine WPs.decCall_alloc hE (pv := pv) (nv := al + bl) (by ev [hal, hbl]) hp hpH
    (fun qv hq hqH => ?_)
  have hqE := hqH.1
  have e1 : (pv + al).toNat = pv.toNat + al.toNat := by
    rw [BitVec.toNat_add]
    omega
  have e2 : (pv + (al + bl)).toNat = pv.toNat + al.toNat + bl.toNat := by
    rw [BitVec.toNat_add, eab]
    omega
  refine WPs.seqG (fun x => ∃ m1, x = ⟨updatePanValueMap s.locals "out" (.word pv),
      updatePanValueMap s.globals "heap_ptr" (.word qv), m1, s.ffi⟩ ∧
      CopyInv s.memory pv a al.toNat m1)
    (WPs.call_memcpy hE (dst := pv) (src := a) (nW := al) (of_eval (by lk [])) (of_eval (by lk [ha]))
      (of_eval (by lk [hal])) ⟨by omega, by omega, by omega, by omega⟩
      (fun m1 hm1 => ⟨m1, rfl, hm1⟩)) ?_
  rintro _ ⟨m1, rfl, hc1⟩
  refine WPs.seqG (fun x => ∃ m2, x = ⟨updatePanValueMap s.locals "out" (.word pv),
      updatePanValueMap s.globals "heap_ptr" (.word qv), m2, s.ffi⟩ ∧
      CopyInv m1 (pv + al) b bl.toNat m2)
    (WPs.call_memcpy hE (dst := pv + al) (src := b) (nW := bl) (of_eval (by ev [hal]))
      (of_eval (by lk [hb])) (of_eval (by lk [hbl])) ⟨by omega, by omega, by omega, by omega⟩
      (fun m2 hm2 => ⟨m2, rfl, hm2⟩)) ?_
  rintro _ ⟨m2, rfl, hc2⟩
  refine WPs.ret (w := pv) (of_eval (by lk [])) ?_
  simp only [restorePanValueFfiLocal]
  have keep : ∀ A : Word, A.toNat % 8 = 0 →
      (A.toNat + 8 ≤ pv.toNat ∨ pv.toNat + al.toNat + bl.toNat ≤ A.toNat) → m2 A = s.memory A := by
    intro A h8 hA
    rw [hc2.cells A (by rcases hA with h1 | h1 <;> omega),
      hc1.cells A (by rcases hA with h1 | h1 <;> omega)]
  refine ⟨_, _, m2, pv, rfl, WorldTJ.fresh_nibs hW hp (by simp [updatePanValueMap]) hqH
    (by omega) (fun x hx => by simp [update_lookup, hx])
    (fun A h8 hlt => keep A h8 (Or.inl (by omega)))
    (fun A hA => ?_) (by omega) ?_, e2, hp, fun A h8 hlt => keep A h8 (Or.inl hlt),
    fun x hx => by simp [update_lookup, hx], fun A hA => ?_⟩
  · rw [hc2.cells A (by unfold HBASE at hA hpB; omega),
      hc1.cells A (by unfold HBASE at hA hpB; omega)]
  · intro j hj
    rw [e2] at hj
    have hoj : (off pv j).toNat = pv.toNat + j := off_toNat (by omega)
    by_cases hja : j < al.toNat
    · obtain ⟨x, hx, h16⟩ := hna j hja
      refine ⟨x, ?_, h16⟩
      rw [hc2.rest _ (Or.inl (by omega)), hc1.copied j hja]
      exact hx
    · obtain ⟨x, hx, h16⟩ := hnb (j - al.toNat) (by omega)
      refine ⟨x, ?_, h16⟩
      have eo : off pv j = off (pv + al) (j - al.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [hoj, off_toNat (by omega), e1]
        omega
      have hob : (off b (j - al.toNat)).toNat = b.toNat + (j - al.toNat) :=
        off_toNat (by omega)
      rw [eo, hc2.copied (j - al.toNat) (by omega), hc1.rest _ (Or.inl (by omega))]
      exact hx
  · rw [hc2.cells A (by unfold HBASE at hA hpB; omega),
      hc1.cells A (by unfold HBASE at hA hpB; omega)]

end InitECandidate.Solver.GuestBound
