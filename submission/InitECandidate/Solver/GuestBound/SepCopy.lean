import InitECandidate.Solver.GuestBound.MemFrame
import InitECandidate.Solver.GuestBound.SepReturn
import InitECandidate.Solver.GuestBound.SepSwap

/-!
# Copies into an owned range

`memzero`, `memcpy` and `buffer_read` with the destination inside an owned
range, for any alignment and any source. Used by the copy opcodes
(`calldatacopy`, `codecopy`, `returndatacopy`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `memzero(dst, n); rest` inside an owned range, any alignment. -/
theorem WPr.seq_memzero_any (hE : GuestEnv E) {e1 e2 : Exp Word} {q : Prog Word}
    {dst nW lo hi : Word} {F : Assn} (h1 : ∀ y, E.eval s e1 = some y → y = .word dst)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word nW)
    (h64 : dst.toNat + nW.toNat + 32 < 2 ^ 64) (hlo : lo.toNat ≤ dst.toNat / 8 * 8)
    (hhi : dst.toNat + nW.toNat ≤ hi.toNat)
    (hpre : (Assn.Range lo hi ⋆ F).holds s) (htrap : ∀ r, Trap r → Q r)
    (hq : ∀ m, (Assn.Range lo hi ⋆ F).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "memzero" [e1, e2]) q) Q := by
  refine WPr.seq (fun s' => ∃ m, s' = ⟨s.locals, s.globals, m, s.ffi⟩ ∧
      (Assn.Range lo hi ⋆ F).holds s')
    (WPr.call_spec (fun rb => RaiseIn (fun _ => false) rb ∧ (Stopped rb ∨ ∃ l m',
      rb = .returned l s.globals m' s.ffi [.word 0#64] ∧ Hull s.memory dst nW m')) ?_ ?_ ?_ ?_) ?_
  · intro parameters cbody values cl hlk hvalues hbind r hr
    rcases memzero_raises hE parameters cbody hlk _ r hr with he | hra
    · exact Or.inl he
    have hparams := (fun_of_index 17 hE.functions (by guest_decl_at 17) (by decide +kernel)
      hlk).2
    obtain ⟨v1, v2, g1, g2, rfl⟩ := evalArgs2_inv hvalues
    have := h1 _ g1
    subst this
    have := h2 _ g2
    subst this
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact Or.inr ⟨hra, memzero_frame hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ r
      dst nW
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) h64 hr⟩
  · rintro l g m ffi vs ⟨-, hst | ⟨l', m', heq, hinv⟩⟩
    · exact hst.elim
    injection heq with _ hg hm hf _
    subst hg hm hf
    exact ⟨_, rfl, Assn.holds_range_change hpre rfl (fun x hx => hinv x (by omega))⟩
  · rintro l g m ffi exc v ⟨hra, -⟩
    cases hra
  · intro l g m ffi ev _
    exact htrap _ trivial
  · rintro _ ⟨m, rfl, hm⟩
    exact hq m hm

/-- `memcpy(dst, src, n); rest` with the destination inside an owned range;
any alignment, any source. -/
theorem WPr.seq_memcpy_any (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {q : Prog Word}
    {dst nW lo hi : Word} {F : Assn} (h1 : ∀ y, E.eval s e1 = some y → y = .word dst)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word nW)
    (h64 : dst.toNat + nW.toNat + 32 < 2 ^ 64) (hlo : lo.toNat ≤ dst.toNat / 8 * 8)
    (hhi : dst.toNat + nW.toNat ≤ hi.toNat)
    (hpre : (Assn.Range lo hi ⋆ F).holds s) (htrap : ∀ r, Trap r → Q r)
    (hq : ∀ m, (Assn.Range lo hi ⋆ F).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "memcpy" [e1, e2, e3]) q) Q := by
  refine WPr.seq (fun s' => ∃ m, s' = ⟨s.locals, s.globals, m, s.ffi⟩ ∧
      (Assn.Range lo hi ⋆ F).holds s')
    (WPr.call_spec (fun rb => RaiseIn (fun _ => false) rb ∧ (Stopped rb ∨ ∃ l m',
      rb = .returned l s.globals m' s.ffi [.word 0#64] ∧ Hull s.memory dst nW m')) ?_ ?_ ?_ ?_) ?_
  · intro parameters cbody values cl hlk hvalues hbind r hr
    rcases memcpy_raises hE parameters cbody hlk _ r hr with he | hra
    · exact Or.inl he
    have hparams := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
      hlk).2
    obtain ⟨v1, v2, v3, g1, g2, g3, rfl⟩ := evalArgs3_inv hvalues
    have := h1 _ g1
    subst this
    have := h3 _ g3
    subst this
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact Or.inr ⟨hra, memcpy_frame hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ r
      dst nW
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) h64 hr⟩
  · rintro l g m ffi vs ⟨-, hst | ⟨l', m', heq, hinv⟩⟩
    · exact hst.elim
    injection heq with _ hg hm hf _
    subst hg hm hf
    exact ⟨_, rfl, Assn.holds_range_change hpre rfl (fun x hx => hinv x (by omega))⟩
  · rintro l g m ffi exc v ⟨hra, -⟩
    cases hra
  · intro l g m ffi ev _
    exact htrap _ trivial
  · rintro _ ⟨m, rfl, hm⟩
    exact hq m hm

/-- `memcpy(dst, src, n)` as the last statement of a block. -/
theorem WPr.call_memcpy_any (hE : GuestEnv E) {e1 e2 e3 : Exp Word}
    {dst nW lo hi : Word} {F : Assn} (h1 : ∀ y, E.eval s e1 = some y → y = .word dst)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word nW)
    (h64 : dst.toNat + nW.toNat + 32 < 2 ^ 64) (hlo : lo.toNat ≤ dst.toNat / 8 * 8)
    (hhi : dst.toNat + nW.toNat ≤ hi.toNat)
    (hpre : (Assn.Range lo hi ⋆ F).holds s) (htrap : ∀ r, Trap r → Q r)
    (hq : ∀ m, (Assn.Range lo hi ⋆ F).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      Q (.normal s.locals s.globals m s.ffi)) :
    WPr E s (.call (some (none, none)) "memcpy" [e1, e2, e3]) Q := by
  refine WPr.call_spec (fun rb => RaiseIn (fun _ => false) rb ∧ (Stopped rb ∨ ∃ l m',
      rb = .returned l s.globals m' s.ffi [.word 0#64] ∧ Hull s.memory dst nW m')) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind r hr
    rcases memcpy_raises hE parameters cbody hlk _ r hr with he | hra
    · exact Or.inl he
    have hparams := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
      hlk).2
    obtain ⟨v1, v2, v3, g1, g2, g3, rfl⟩ := evalArgs3_inv hvalues
    have := h1 _ g1
    subst this
    have := h3 _ g3
    subst this
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact Or.inr ⟨hra, memcpy_frame hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ r
      dst nW
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) h64 hr⟩
  · rintro l g m ffi vs ⟨-, hst | ⟨l', m', heq, hinv⟩⟩
    · exact hst.elim
    injection heq with _ hg hm hf _
    subst hg hm hf
    exact hq _ (Assn.holds_range_change hpre rfl (fun x hx => hinv x (by omega)))
  · rintro l g m ffi exc v ⟨hra, -⟩
    cases hra
  · intro l g m ffi ev _
    exact htrap _ trivial

/-- A local assignment whose value is known to be some word. -/
theorem WPr.assign_local_ev {x : VarName} {e : Exp Word}
    (h : ∀ v, E.eval s e = some v →
      Q (.normal (updatePanValueMap s.locals x v) s.globals s.memory s.ffi)) :
    WPr E s (.assign .local x e) Q := by
  intro r hr
  rw [runs_assign_local] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl rfl
  | some y =>
    rw [hv] at hr
    simp only at hr
    split at hr
    · subst hr; exact Or.inr (h _ hv)
    · subst hr; exact Or.inl rfl

set_option maxHeartbeats 2000000 in
/-- `buffer_read(buf, buf_len, start, size, out)` with `[out, out + size)`
inside an owned range: only the range changes. The source may be anything. -/
theorem buffer_read_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "buffer_read" E.functions = some (parameters, body))
    (c : St σ) (size out lo hi : Word) {F : Assn}
    (hsz : c.locals "size" = some (.word size)) (hout : c.locals "out" = some (.word out))
    (h64 : out.toNat + size.toNat + 32 < 2 ^ 64) (hlo : lo.toNat ≤ out.toNat / 8 * 8)
    (hhi : out.toNat + size.toNat ≤ hi.toNat) (hpre : (Assn.Range lo hi ⋆ F).holds c) :
    WPr E c body (fun r => Trap r ∨ ∃ l m, r = .returned l c.globals m c.ffi [.word 0#64] ∧
      (Assn.Range lo hi ⋆ F).holds (⟨l, c.globals, m, c.ffi⟩ : St σ)) := by
  have hbody := (fun_of_index 462 hE.functions (by guest_decl_at 462) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  refine WPr.dec_ev (fun v hv => ?_)
  rw [eval_const] at hv
  cases hv
  refine WPr.seq (fun s' => ∃ av : Word, s'.locals "avail" = some (.word av) ∧
      s'.locals "out" = some (.word out) ∧ s'.locals "size" = some (.word size) ∧
      s'.globals = c.globals ∧ s'.ffi = c.ffi ∧ av.toNat ≤ size.toNat ∧
      (Assn.Range lo hi ⋆ F).holds s') (WPr.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPr.skip ⟨0#64, by simp (config := { decide := true }) [update_lookup],
        by simp (config := { decide := true }) [update_lookup, hout],
        by simp (config := { decide := true }) [update_lookup, hsz], rfl, rfl, by simp,
        Assn.holds_congr rfl rfl hpre⟩
    · refine WPr.seq (fun s' => ∃ w1 : Word, s' = ⟨updatePanValueMap (updatePanValueMap c.locals
          "avail" (.word 0#64)) "avail" (.word w1), c.globals, c.memory, c.ffi⟩)
        (WPr.assign_local_ev (fun v hv => ?_)) ?_
      · obtain ⟨w1, rfl⟩ := eval_op_word hE hv
        exact ⟨w1, rfl⟩
      rintro _ ⟨w1, rfl⟩
      refine WPr.seq (fun s' => ∃ av : Word, s'.locals "avail" = some (.word av) ∧
          s'.locals "out" = some (.word out) ∧ s'.locals "size" = some (.word size) ∧
          s'.globals = c.globals ∧ s'.memory = c.memory ∧ s'.ffi = c.ffi ∧
          av.toNat ≤ size.toNat) (WPr.ite_both (fun w2 hw2 => ?_)) ?_
      · split
        · rename_i h0
          rw [h0] at hw2
          obtain ⟨x, y, hx, hy, hc⟩ := cmp_zero_inv hE hw2
          have hx' : x = size := by
            have := of_eval (w := size) (by lk [hsz]) _ hx
            simpa using this
          have hy' : y = w1 := by
            have := of_eval (w := w1) (by lk []) _ hy
            simpa using this
          subst hx' hy'
          have hge : ¬ x < y := lower_zero hc
          refine WPr.skip ⟨y, by simp (config := { decide := true }) [update_lookup],
            by simp (config := { decide := true }) [update_lookup, hout],
            by simp (config := { decide := true }) [update_lookup, hsz], rfl, rfl, rfl, ?_⟩
          by_contra hgt
          exact hge (BitVec.lt_def.mpr (by omega))
        · refine WPr.assign_local (old := w1) (w := size)
            (by simp (config := { decide := true }) [update_lookup]) (of_eval (by lk [hsz])) ?_
          exact ⟨size, by simp (config := { decide := true }) [update_lookup],
            by simp (config := { decide := true }) [update_lookup, hout],
            by simp (config := { decide := true }) [update_lookup, hsz], rfl, rfl, rfl,
            Nat.le_refl _⟩
      rintro ⟨L, g, m, f⟩ ⟨av, hav, hout', hsz', hg, hm, hf, hle⟩
      dsimp only at hav hout' hsz' hg hm hf
      subst g m f
      refine WPr.call_memcpy_any hE (dst := out) (nW := av) (lo := lo) (hi := hi) (F := F)
        (of_eval (by lk [hout'])) (of_eval (by lk [hav])) (by omega) hlo (by omega)
        (Assn.holds_congr rfl rfl hpre)
        (fun r ht => by cases r <;> first | exact ht.elim | exact Or.inl (Trap.restore ht))
        (fun m' hm' => ?_)
      exact ⟨av, hav, hout', hsz', rfl, rfl, hle, Assn.holds_congr rfl rfl hm'⟩
  rintro ⟨L, g, m, f⟩ ⟨av, hav, hout', hsz', hg, hf, hle, hh⟩
  dsimp only at hav hout' hsz' hg hf
  subst g f
  have e1 : (out + av).toNat = out.toNat + av.toNat := by bv_omega
  have e2 : (size - av).toNat = size.toNat - av.toNat := by bv_omega
  refine WPr.seq_memzero_any hE (dst := out + av) (nW := size - av) (lo := lo) (hi := hi)
    (F := F) (of_eval (by ev [hout', hav])) (of_eval (by ev [hsz', hav])) (by omega) (by omega)
    (by omega) hh (fun r ht => Or.inl ht.restore) (fun m' hm' => ?_)
  refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  exact Or.inr ⟨_, _, rfl, Assn.holds_congr rfl rfl hm'⟩

end InitECandidate.Solver.GuestBound
