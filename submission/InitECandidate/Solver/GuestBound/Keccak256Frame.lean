import InitECandidate.Solver.GuestBound.KeccakAbsorb
import InitECandidate.Solver.GuestBound.MemFrame
import InitECandidate.Solver.GuestBound.KeyNibbles
import InitECandidate.Solver.GuestBound.TrieLeafIns
import InitECandidate.Solver.GuestBound.Fq12InvInner

/-!
# `keccak256` writes only its state, its pad block and its output

`keccak256(p, n, out)` zeroes the 200-byte state `keccak_st`, absorbs the full
blocks of the input, builds the last block in the 136-byte buffer `keccak_pad`,
absorbs it, and copies 32 bytes of the state to `out`.  Every other memory cell
is left as it was.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A cell outside the three blocks `keccak256` writes. -/
def KOut (stp pad out : Word) (x : Word) : Prop :=
  (x.toNat < stp.toNat / 8 * 8 ∨ stp.toNat + 200 ≤ x.toNat) ∧
  (x.toNat < pad.toNat / 8 * 8 ∨ pad.toNat + 136 ≤ x.toNat) ∧
  (x.toNat < out.toNat / 8 * 8 ∨ out.toNat + 32 ≤ x.toNat)

/-- Memory agrees outside the three blocks. -/
def KFr (stp pad out : Word) (m0 m : Word → Option (PanValue Word)) : Prop :=
  ∀ x : Word, KOut stp pad out x → m x = m0 x

theorem toNat_add_lit (a : Word) (k : Nat) (h : a.toNat + k < 2 ^ 64) :
    (a + BitVec.ofNat 64 k).toNat = a.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- A word load gives a word, if it gives anything. -/
theorem load_word (hE : GuestEnv E) {a : Exp Word} {addr : Word}
    (ha : ∀ y, E.eval s a = some y → y = .word addr) :
    ∀ y, E.eval s (.load .one a) = some y → ∃ w : Word, y = .word w := by
  intro y hy
  obtain ⟨w, hw⟩ := eval_load_any hE ha
  exact ⟨w, hw y hy⟩

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

/-- What a returning `memzero` leaves. -/
theorem memzero_hull_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {dst nW : Word}
    (h : CalleeRet E s "memzero" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word dst)) (h2 : E.eval s e2 = some (.word nW))
    (h64 : dst.toNat + nW.toNat + 32 < 2 ^ 64) :
    g = s.globals ∧ ffi = s.ffi ∧ Hull s.memory dst nW m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 17 hE.functions (by guest_decl_at 17) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases memzero_frame hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ dst nW
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) h64 hrun
    with hst | ⟨l', m', heq, hfr⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr⟩

/-- What a returning `memcpy` leaves. -/
theorem memcpy_hull_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {dst nW : Word}
    {v2 : PanValue Word}
    (h : CalleeRet E s "memcpy" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word dst)) (h2 : E.eval s e2 = some v2)
    (h3 : E.eval s e3 = some (.word nW))
    (h64 : dst.toNat + nW.toNat + 32 < 2 ^ 64) :
    g = s.globals ∧ ffi = s.ffi ∧ Hull s.memory dst nW m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases memcpy_frame hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ dst nW
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) h64 hrun
    with hst | ⟨l', m', heq, hfr⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr⟩

/-- What a returning `keccak_absorb_block` leaves. -/
theorem absorb_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {stp : Word} {v2 : PanValue Word}
    (h : CalleeRet E s "keccak_absorb_block" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word stp)) (h2 : E.eval s e2 = some v2)
    (h64 : stp.toNat + 200 < 2 ^ 64) :
    g = s.globals ∧ ffi = s.ffi ∧
      ∀ x : Word, (x.toNat < stp.toNat ∨ stp.toNat + 200 ≤ x.toNat) → m x = s.memory x := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 102 hE.functions (by guest_decl_at 102) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases keccak_absorb_frame hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ stp
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) h64 hrun
    with hst | ⟨l', m', heq, hfr⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr⟩

end rets

/-- Invariant of the block loop of `keccak256`. -/
def K2I (s : St σ) (stp pad pv nv ov : Word) (a : St σ) : Prop :=
  a.globals = s.globals ∧ a.ffi = s.ffi ∧ a.locals "stp" = some (.word stp) ∧
    a.locals "p" = some (.word pv) ∧ a.locals "n" = some (.word nv) ∧
    a.locals "out" = some (.word ov) ∧ KFr stp pad ov s.memory a.memory ∧
    ∃ iv : Word, a.locals "i" = some (.word iv) ∧ iv.toNat ≤ nv.toNat

set_option maxHeartbeats 8000000 in
theorem keccak256_frame (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "keccak256" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv nv ov stp pad : Word)
    (hp : s.locals "p" = some (.word pv)) (hn : s.locals "n" = some (.word nv))
    (ho : s.locals "out" = some (.word ov))
    (hst : s.globals "keccak_st" = some (.word stp))
    (hpd : s.globals "keccak_pad" = some (.word pad))
    (hs64 : stp.toNat + 232 < 2 ^ 64) (hp64 : pad.toNat + 168 < 2 ^ 64)
    (ho64 : ov.toNat + 64 < 2 ^ 64) (hn64 : nv.toNat + 136 < 2 ^ 64) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      KFr stp pad ov s.memory m' := by
  have hbody := (fun_of_index 103 hE.functions (by guest_decl_at 103) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    KFr stp pad ov s.memory m')) r h
  have h200 : (200#64 : Word).toNat = 200 := by decide
  have h136 : (136#64 : Word).toNat = 136 := by decide
  have h32 : (32#64 : Word).toNat = 32 := by decide
  refine WPs.dec (w := stp) (of_eval (by rw [eval_global]; exact hst)) ?_
  refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
  obtain ⟨rfl, rfl, hz1⟩ := memzero_hull_ret hE hret (dst := stp) (nW := 200#64) (by lk [])
    (eval_const _ _) (by rw [h200]; omega)
  dsimp only
  have hfr1 : KFr stp pad ov s.memory m1 := fun x hx =>
    hz1 x (by have hx' := hx; unfold KOut at hx'; rw [h200]; omega)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.seqG (fun a => K2I s stp pad pv nv ov a ∧ ∃ k, E.cond a
      (.cmp .notLower (.var .local "n") (.op .add [.var .local "i", .const 136#64])) = some (0, k))
    (WPs.loopG (I := K2I s stp pad pv nv ov)
      ⟨rfl, rfl, by lk [], by lk [hp], by lk [hn], by lk [ho], hfr1, 0#64, by lk [],
        Nat.zero_le _⟩ ?_ (fun a k hI hk => ⟨hI, k, hk⟩)) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hstp, hp', hn', ho', hfr, iv, hi, hin⟩ ⟨w, cc, hcond, hw⟩
    dsimp only at hg hf hstp hp' hn' ho' hfr hi
    subst hg hf
    have e136 : (iv + 136#64).toNat = iv.toNat + 136 := toNat_add_lit iv 136 (by omega)
    have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := nv) (by lk [hn']))
      (of_eval (w := iv + 136#64) (by ev [hi])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hle : iv.toNat + 136 ≤ nv.toNat := by
      by_contra hgt
      have hl : nv < iv + 136#64 := by
        rw [BitVec.lt_def, e136]
        omega
      rw [hc] at hw
      simp [evalPanCmp, hl] at hw
    refine WPs.seq_call_ret (fun vs g m ffi hret => ?_)
    obtain ⟨rfl, rfl, hab⟩ := absorb_ret hE hret (stp := stp) (v2 := .word (pv + iv))
      (by lk [hstp]) (by ev [hp', hi]) (by omega)
    refine WPs.assign (old := iv) (w := iv + 136#64) hi (of_eval (by ev [hi])) ?_
    exact ⟨rfl, rfl, by lk [hstp], by lk [hp'], by lk [hn'], by lk [ho'],
      fun x hx => (hab x (by have hx' := hx; unfold KOut at hx'; omega)).trans (hfr x hx),
      iv + 136#64, by lk [], by omega⟩
  rintro ⟨la, ga, ma, fa⟩ ⟨⟨hg, hf, hstp, hp', hn', ho', hfr, iv, hi, hin⟩, k, hk⟩
  dsimp only at hg hf hstp hp' hn' ho' hfr hi
  subst hg hf
  have e136 : (iv + 136#64).toNat = iv.toNat + 136 := toNat_add_lit iv 136 (by omega)
  have hc := eval_cmp_inv hE (op := .notLower) (of_eval (w := nv) (by lk [hn']))
    (of_eval (w := iv + 136#64) (by ev [hi])) _ (cond_of_eval hk)
  simp only [PanValue.word.injEq] at hc
  have hlt : nv.toNat < iv.toNat + 136 := by
    by_contra hge
    have hl : ¬ nv < iv + 136#64 := by
      rw [BitVec.lt_def, e136]
      omega
    simp [evalPanCmp, hl] at hc
  have erem : (nv - iv).toNat = nv.toNat - iv.toNat := by
    rw [BitVec.toNat_sub]
    omega
  have eaddr : (pad + (nv - iv)).toNat = pad.toNat + (nv.toNat - iv.toNat) := by
    rw [BitVec.toNat_add, erem]
    omega
  have e135 : (pad + 135#64).toNat = pad.toNat + 135 := toNat_add_lit pad 135 (by omega)
  refine WPs.dec (w := nv - iv) (of_eval (by ev [hn', hi])) ?_
  refine WPs.seq_call_ret (fun vs g m2 ffi hret => ?_)
  obtain ⟨rfl, rfl, hz2⟩ := memzero_hull_ret hE hret (dst := pad) (nW := 136#64)
    (by rw [eval_global]; exact hpd) (eval_const _ _) (by rw [h136]; omega)
  dsimp only
  refine WPs.seq_call_ret (fun vs g m3 ffi hret => ?_)
  obtain ⟨rfl, rfl, hz3⟩ := memcpy_hull_ret hE hret (dst := pad) (nW := nv - iv)
    (v2 := .word (pv + iv)) (by rw [eval_global]; exact hpd) (by ev [hp', hi]) (by lk [])
    (by rw [erem]; omega)
  dsimp only
  refine WPs.seq_storeByte_fr hE (addr := pad + (nv - iv)) (of_eval (by ev [hpd]))
    (fun m4 _ hm4 => ?_)
  refine WPs.seq_storeByte_fr hE (addr := pad + 135#64) (of_eval (by ev [hpd]))
    (fun m5 _ hm5 => ?_)
  refine WPs.seq_call_ret (fun vs g m6 ffi hret => ?_)
  obtain ⟨rfl, rfl, hab⟩ := absorb_ret hE hret (stp := stp) (v2 := .word pad)
    (by lk [hstp]) (by rw [eval_global]; exact hpd) (by omega)
  dsimp only at hm4 hm5 hab ⊢
  have hfr6 : KFr stp pad ov s.memory m6 := fun x hx => by
    have hx' := hx
    unfold KOut at hx'
    exact (hab x (by omega)).trans ((hm5 x (by rw [e135]; omega)).trans
      ((hm4 x (by rw [eaddr]; omega)).trans ((hz3 x (by rw [erem]; omega)).trans
        ((hz2 x (by rw [h136]; omega)).trans (hfr x hx)))))
  refine WPs.seqG (fun a => ∃ m7, a = ⟨updatePanValueMap la "rem" (.word (nv - iv)), s.globals,
      m7, s.ffi⟩ ∧ KFr stp pad ov s.memory m7) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · refine WPs.call_ret (fun vs g m7 ffi hret => ?_)
      obtain ⟨rfl, rfl, hz7⟩ := memcpy_hull_ret hE hret (dst := ov) (nW := 32#64)
        (v2 := .word stp) (by lk [ho']) (by lk [hstp]) (eval_const _ _) (by rw [h32]; omega)
      exact ⟨m7, rfl, fun x hx =>
        (hz7 x (by have hx' := hx; unfold KOut at hx'; rw [h32]; omega)).trans (hfr6 x hx)⟩
    · have hl : ∀ (a : Exp Word) (addr : Word) (m : Word → Option (PanValue Word)),
          (E.eval ⟨updatePanValueMap la "rem" (.word (nv - iv)), s.globals, m, s.ffi⟩ a =
            some (.word addr)) →
          ∀ y, E.eval ⟨updatePanValueMap la "rem" (.word (nv - iv)), s.globals, m, s.ffi⟩
            (.load .one a) = some y → ∃ w : Word, y = .word w :=
        fun a addr m ha => load_word hE (of_eval ha)
      have ho6 : ∀ m : Word → Option (PanValue Word),
          E.eval ⟨updatePanValueMap la "rem" (.word (nv - iv)), s.globals, m, s.ffi⟩
            (.var .local "out") = some (.word ov) := fun m => by lk [ho']
      have hs6 : ∀ m : Word → Option (PanValue Word),
          E.eval ⟨updatePanValueMap la "rem" (.word (nv - iv)), s.globals, m, s.ffi⟩
            (.var .local "stp") = some (.word stp) := fun m => by lk [hstp]
      refine WPs.seq_store_rng hE
        (s := ⟨updatePanValueMap la "rem" (.word (nv - iv)), s.globals, m6, s.ffi⟩)
        (addr := ov) (lo := ov.toNat) (hi := ov.toNat + 32) (m0 := m6)
        (of_eval (ho6 m6)) (hl _ stp m6 (hs6 m6)) (by omega) (by omega)
        (fun _ _ => rfl) (fun m7 hm7 => ?_)
      refine WPs.seq_store_rng hE (addr := ov + 8#64) (lo := ov.toNat) (hi := ov.toNat + 32)
        (m0 := m6) (of_eval (by ev [ho'])) (hl _ (stp + 8#64) _ (by ev [hstp]))
        (by rw [toNat_add_lit ov 8 (by omega)]; omega)
        (by rw [toNat_add_lit ov 8 (by omega)]; omega) hm7 (fun m8 hm8 => ?_)
      refine WPs.seq_store_rng hE (addr := ov + 16#64) (lo := ov.toNat) (hi := ov.toNat + 32)
        (m0 := m6) (of_eval (by ev [ho'])) (hl _ (stp + 16#64) _ (by ev [hstp]))
        (by rw [toNat_add_lit ov 16 (by omega)]; omega)
        (by rw [toNat_add_lit ov 16 (by omega)]; omega) hm8 (fun m9 hm9 => ?_)
      refine WPs.last (WPs.seq_store_rng hE (addr := ov + 24#64) (lo := ov.toNat) (hi := ov.toNat + 32)
        (m0 := m6) (of_eval (by ev [ho'])) (hl _ (stp + 24#64) _ (by ev [hstp]))
        (by rw [toNat_add_lit ov 24 (by omega)]; omega)
        (by rw [toNat_add_lit ov 24 (by omega)]; omega) hm9 (fun m10 hm10 => WPs.skip ?_))
      exact ⟨m10, rfl, fun x hx =>
        (hm10 x (by have hx' := hx; unfold KOut at hx'; omega)).trans (hfr6 x hx)⟩
  rintro _ ⟨m7, rfl, hfr7⟩
  refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  exact ⟨_, m7, rfl, hfr7⟩

end InitECandidate.Solver.GuestBound
