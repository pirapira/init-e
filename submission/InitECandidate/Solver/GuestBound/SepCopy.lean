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

theorem evalArgs5_inv {e1 e2 e3 e4 e5 : Exp Word} {values : List (PanValue Word)}
    (h : E.evalArgs s [e1, e2, e3, e4, e5] = some values) :
    ∃ v1 v2 v3 v4 v5, E.eval s e1 = some v1 ∧ E.eval s e2 = some v2 ∧ E.eval s e3 = some v3 ∧
      E.eval s e4 = some v4 ∧ E.eval s e5 = some v5 ∧ values = [v1, v2, v3, v4, v5] := by
  simp only [evalArgs_cons, evalArgs_nil] at h
  cases h1 : E.eval s e1 with
  | none => rw [h1] at h; simp at h
  | some v1 =>
    cases h2 : E.eval s e2 with
    | none => rw [h1, h2] at h; simp at h
    | some v2 =>
      cases h3 : E.eval s e3 with
      | none => rw [h1, h2, h3] at h; simp at h
      | some v3 =>
        cases h4 : E.eval s e4 with
        | none => rw [h1, h2, h3, h4] at h; simp at h
        | some v4 =>
          cases h5 : E.eval s e5 with
          | none => rw [h1, h2, h3, h4, h5] at h; simp at h
          | some v5 =>
            rw [h1, h2, h3, h4, h5] at h
            simp at h
            exact ⟨v1, v2, v3, v4, v5, rfl, rfl, rfl, rfl, rfl, h.symm⟩

/-- `var x = words_of(n); rest`: some word below `2^59`. -/
theorem op_words_of (hE : GuestEnv E) {x : VarName} {args : List (Exp Word)} {body : Prog Word}
    {n : Word} (hargs : E.evalArgs s args = some [.word n])
    (hk : ∀ w : Word, w.toNat < 2 ^ 59 →
      WPr E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x .one "words_of" args body) Q := by
  refine WPr.decCall_spec (fun rb => ∃ l w, rb = .returned l s.globals s.memory s.ffi
      [.word w] ∧ w.toNat < 2 ^ 59) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 443 hE.functions (by guest_decl_at 443) (by decide +kernel)
      hlk).2
    rw [hargs] at hvalues
    cases hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    refine WPr.conseq (words_of_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ n
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])) ?_
    rintro r ⟨l, w, cv, rfl, -, hw⟩
    have := cv.isLt
    exact ⟨l, w, rfl, by omega⟩
  · rintro l g m ffi v ⟨l', w, hC, hw⟩
    injection hC with _ hg hm hf hv'
    subst hg hm hf
    simp only [List.cons.injEq, and_true] at hv'
    subst hv'
    exact hk w hw
  · rintro l g m ffi exc v ⟨_, _, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨_, _, hC, -⟩
    cases hC

/-- `var x = add_sat(a, b); rest`: the sum, or `2^64 - 1` when it does not fit. -/
theorem op_add_sat (hE : GuestEnv E) {x : VarName} {args : List (Exp Word)} {body : Prog Word}
    {a b : Word} (hargs : E.evalArgs s args = some [.word a, .word b])
    (hk : ∀ t : Word, ((a.toNat + b.toNat < 2 ^ 64 ∧ t.toNat = a.toNat + b.toNat) ∨
        (2 ^ 64 ≤ a.toNat + b.toNat ∧ t = 18446744073709551615#64)) →
      WPr E ⟨updatePanValueMap s.locals x (.word t), s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x .one "add_sat" args body) Q := by
  refine WPr.decCall_spec (fun rb => ∃ l t, rb = .returned l s.globals s.memory s.ffi
      [.word t] ∧ ((a.toNat + b.toNat < 2 ^ 64 ∧ t.toNat = a.toNat + b.toNat) ∨
        (2 ^ 64 ≤ a.toNat + b.toNat ∧ t = 18446744073709551615#64))) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 441 hE.functions (by guest_decl_at 441) (by decide +kernel)
      hlk).2
    rw [hargs] at hvalues
    cases hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact add_sat_exact hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ a b
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  · rintro l g m ffi v ⟨l', t, hC, ht⟩
    injection hC with _ hg hm hf hv'
    subst hg hm hf
    simp only [List.cons.injEq, and_true] at hv'
    subst hv'
    exact hk t ht
  · rintro l g m ffi exc v ⟨_, _, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨_, _, hC, -⟩
    cases hC

/-- A handler outcome is never `.normal`, so it passes through a sequence. -/
theorem AcceptsM.mid {M : Word} {K : Word → Prop} {e mem0 : Word} {R : Assn}
    {ffi : FfiState σ} {X0 : OpSt} {Rm : St σ → Prop} (h : AcceptsM M K e mem0 R ffi X0 Q) :
    AcceptsM M K e mem0 R ffi X0 (fun r => match r with
      | .normal l g m f => Rm ⟨l, g, m, f⟩
      | r => Q r) := by
  intro r hr
  cases r with
  | normal l g m f =>
    rcases hr with (ht | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩
    · exact ht.elim
    · cases hC
    · cases hC
  | _ => exact h _ hr

set_option maxHeartbeats 1000000 in
/-- `buffer_read(.., n, out)` as the last statement of a block, writing inside
the frame's memory buffer. -/
theorem op_buffer_read (hE : GuestEnv E) {e1 e2 e3 e4 e5 : Exp Word} {nW out : Word}
    {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt} {Y : MemSt}
    (h4 : ∀ y, E.eval s e4 = some y → y = .word nW)
    (h5 : ∀ y, E.eval s e5 = some y → y = .word out)
    (hlo : Y.mem.toNat ≤ out.toNat) (hhi : out.toNat + nW.toNat ≤ Y.mem.toNat + Y.cap.toNat)
    (hok : FrameOk M K fv X) (hY : MBufOk Y fv)
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s) (htrap : ∀ r, Trap r → Q r)
    (hq : ∀ g m, (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds (⟨s.locals, g, m, s.ffi⟩ : St σ) →
      Q (.normal s.locals g m s.ffi)) :
    WPr E s (.call (some (none, none)) "buffer_read" [e1, e2, e3, e4, e5]) Q := by
  have htop := hY.top
  have hfp := hok.ok.fp
  have hpv := hok.ok.pv_hi
  have hmal := hY.mal
  have hmc : (Y.mem + Y.cap).toNat = Y.mem.toNat + Y.cap.toNat := by bv_omega
  have hF : (Assn.Range Y.mem (Y.mem + Y.cap) ⋆ (MemTail e Y ⋆ FrameOp M K e fv X) ⋆
      R).holds s :=
    Assn.holds_perm h (by unfold MemExtra; ac_rfl)
  refine WPr.call_spec (fun r => Trap r ∨ ∃ l m, r = .returned l s.globals m s.ffi [.word 0#64] ∧
      (Assn.Range Y.mem (Y.mem + Y.cap) ⋆ (MemTail e Y ⋆ FrameOp M K e fv X) ⋆ R).holds
        (⟨l, s.globals, m, s.ffi⟩ : St σ)) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 462 hE.functions (by guest_decl_at 462) (by decide +kernel)
      hlk).2
    obtain ⟨v1, v2, v3, v4, v5, -, -, -, g4, g5, rfl⟩ := evalArgs5_inv hvalues
    have := h4 _ g4
    subst this
    have := h5 _ g5
    subst this
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact buffer_read_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ nW out
      Y.mem (Y.mem + Y.cap)
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by omega) (by omega) (by omega) (Assn.holds_congr rfl rfl hF)
  · rintro l g m ffi vs (ht | ⟨l', m', hC, hh⟩)
    · exact ht.elim
    · injection hC with _ hg hm hf _
      subst hg hm hf
      exact hq _ _ (Assn.holds_perm (Assn.holds_congr rfl rfl hh) (by unfold MemExtra; ac_rfl))
  · rintro l g m ffi exc v (ht | ⟨_, _, hC, -⟩)
    · exact htrap _ ht
    · cases hC
  · rintro l g m ffi ev _
    exact htrap _ trivial

end InitECandidate.Solver.GuestBound
