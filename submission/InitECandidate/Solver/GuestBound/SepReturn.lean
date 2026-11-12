import InitECandidate.Solver.GuestBound.SepStop

/-!
# `op_return` and `op_revert`

Both pay for and perform the memory growth covering the returned data, record
the return-data pointer and length, and end the frame: `op_return` clears the
running flag, `op_revert` raises `EvmErr 1`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The memory length, from the frame's assertion. -/
theorem holds_len {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt} {Y : MemSt}
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s) :
    s.memory (e + 32#64) = some (.word Y.len) := by
  have h2 : (MemTail e Y ⋆ (Assn.Range Y.mem (Y.mem + Y.cap) ⋆ FrameOp M K e fv X) ⋆ R).holds s :=
    Assn.holds_perm h (by unfold MemExtra; ac_rfl)
  unfold MemTail at h2
  exact (by look : Look (.mem (e + 32#64)) (.word Y.len) _) _ _ h2

/-- `var x = extend_memory_cost1(start, size); rest`, with the value. -/
theorem op_cost1 (hE : GuestEnv E) {x : VarName} {args : List (Exp Word)} {body : Prog Word}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word} {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {X : OpSt} {Y : MemSt}
    (hargs : E.evalArgs s args = some [.rStruct [.word a0, .word a1, .word a2, .word a3],
      .rStruct [.word b0, .word b1, .word b2, .word b3]])
    (hok : FrameOk M K fv X) (hY : MBufOk Y fv)
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s)
    (hk : ∀ cost xp : Word, CostOk (satW a0 a1 a2 a3) (satW b0 b1 b2 b3) Y.len cost xp →
      WPr E ⟨updatePanValueMap s.locals x (.rStruct [.word cost, .word xp]), s.globals, s.memory,
        s.ffi⟩ body (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x (.comb [.one, .one]) "extend_memory_cost1" args body) Q := by
  have hev := holds_ev h
  have hlen := holds_len h
  have hlb : Y.len.toNat ≤ 2 ^ 62 := by
    have := hY.lc; have := hY.top; have := hok.ok.fp; have := hok.ok.pv_hi; omega
  refine WPr.decCall_spec (fun rb => ∃ l cost xp, rb = .returned l s.globals s.memory s.ffi
      [.rStruct [.word cost, .word xp]] ∧
      CostOk (satW a0 a1 a2 a3) (satW b0 b1 b2 b3) Y.len cost xp) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 458 hE.functions (by guest_decl_at 458) (by decide +kernel)
      hlk).2
    rw [hargs] at hvalues
    cases hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact extend_memory_cost1_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩
      a0 a1 a2 a3 b0 b1 b2 b3 e Y.len
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hev hlen hY.l32
      hlb
  · rintro l g m ffi v ⟨l', cost, xp, hC, hcost⟩
    injection hC with _ hg hm hf hv'
    subst hg hm hf
    simp only [List.cons.injEq, and_true] at hv'
    subst hv'
    exact hk cost xp hcost
  · rintro l g m ffi exc v ⟨l', cost, xp, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', cost, xp, hC, -⟩
    cases hC

/-- `charge_gas(e); rest` for a computed amount, under the stack-level invariant. -/
theorem op_charge_val (hE : GuestEnv E) {args : List (Exp Word)} {q : Prog Word} {a : Word}
    (hargs : E.evalArgs s args = some [.word a]) {M : Word} {K : Word → Prop} {e fv : Word}
    {R : Assn} {X0 X : OpSt} {n : Nat} (hok : FrameOk M K fv X) (hp : Adv X X0 n)
    (h : (FrameOp M K e fv X ⋆ R).holds s) (hab : AcceptsAbort M K e fv R s.ffi X0 Q)
    (hq : ¬ X.gl < a → ∀ g m, FrameOk M K fv { X with gl := X.gl - a, used := X.used + a } →
      Adv { X with gl := X.gl - a, used := X.used + a } X0 (n + a.toNat) →
      (FrameOp M K e fv { X with gl := X.gl - a, used := X.used + a } ⋆ R).holds
        (⟨s.locals, g, m, s.ffi⟩ : St σ) → WPr E ⟨s.locals, g, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "charge_gas" args) q) Q := by
  refine WPr.seq_call_framedT (Assn.holds_focus (OpW_gas ..) (Assn.holds_assoc_r h))
    (fun p b v cl a1 a2 a3 => (charge_gas_hc hE hargs e X.gl X.used p b v cl a1 a2 a3).toT)
    (fun r ht => hab r (Or.inl ht)) ?_ ?_
  · intro l g m ffi vs hh
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC
    obtain ⟨⟨hge, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
    injection hC with _ _ _ hf _
    subst hf
    refine hq hge g m ⟨hok.ok, hok.pb, hok.bM, hok.Kpv, hok.Kst⟩ ⟨?_, hp.2⟩
      (Assn.holds_assoc_l (P := OpW e X.sp X.cap X.base X.pv fv (X.gl - a) (X.used + a) X.pc)
        (Assn.holds_unfocus (OpW_gas ..) hk))
    have h1 := hp.1
    have : (X.gl - a).toNat + a.toNat = X.gl.toNat := by
      have : ¬ X.gl.toNat < a.toNat := fun h => hge (BitVec.lt_def.mpr h)
      bv_omega
    show (X.gl - a).toNat + (n + a.toNat) ≤ X0.gl.toNat
    omega
  · intro l g m ffi exc v _ hh
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      exact hab _ (Or.inr ⟨X, n, hok, hp, Assn.holds_assoc_l
        (Assn.holds_unfocus (OpW_gas ..) (Assn.holds_congr rfl rfl hk)), _, _, _, _, rfl⟩)
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC

/-- `extend_memory(e); rest` under the frame invariant with its memory buffer. -/
theorem op_extend (hE : GuestEnv E) {args : List (Exp Word)} {q : Prog Word} {x : Word}
    (hargs : E.evalArgs s args = some [.word x]) (hx8 : x.toNat % 32 = 0)
    (hxb : x.toNat < 2 ^ 37) {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {X0 X : OpSt} {Y : MemSt} (hok : FrameOk M K fv X) (hY : MBufOk Y fv)
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s) (hQ : AcceptsM M K e R s.ffi X0 Q)
    (hq : ∀ (fv' cap' : Word) g m, FrameOk M K fv' X →
      MBufOk { Y with len := Y.len + x, cap := cap' } fv' →
      (Y.len + x).toNat = Y.len.toNat + x.toNat →
      (FrameOp M K e fv' X ⋆ MemExtra e { Y with len := Y.len + x, cap := cap' } ⋆ R).holds
        (⟨s.locals, g, m, s.ffi⟩ : St σ) → WPr E ⟨s.locals, g, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "extend_memory" args) q) Q := by
  have hmok : MemOk Y.len Y.cap Y.mem X.pv fv :=
    ⟨hY.mal, hY.cal, by have := hY.l32; omega, hY.lc, hY.top, hok.ok.fp, hok.ok.pv_hi⟩
  have hF : (MemW e Y.len Y.cap Y.mem X.pv fv ⋆ ((.mem (e + 64#64) ↦ .word X.gl ⋆
      .mem (e + 184#64) ↦ .word X.used) ⋆ RestCM M K e X Y.run Y.rd Y.rl) ⋆ R).holds s := by
    have h0 := Assn.holds_focus (FrameM_cmw M K e fv X Y)
      (Assn.holds_assoc_l (P := FrameOp M K e fv X) h)
    rw [CMW_mem] at h0
    exact Assn.holds_perm h0 (by ac_rfl)
  refine WPr.seq_call_framedT hF (extend_memory_hc hE hargs e Y.len Y.cap Y.mem X.pv fv
    (by omega) (by omega) hmok) (fun r ht => hQ r (Or.inl (Or.inl ht))) ?_ ?_
  · intro l g m ffi vs hh
    obtain ⟨cap', hh⟩ := Assn.holdsV_ex.mp hh
    obtain ⟨fv', hh⟩ := Assn.holdsV_ex.mp hh
    obtain ⟨⟨⟨ok', hlx, hfv⟩, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
    injection hC with _ _ _ hf _
    subst hf
    refine hq fv' cap' g m
      ⟨⟨hok.ok.cap_pos, hok.ok.cap_le, hok.ok.sp_le, hok.ok.base_al, hok.ok.base_hi, ok'.fp,
        hok.ok.pv_hi⟩, hok.pb, hok.bM, hok.Kpv, hok.Kst⟩
      ⟨ok'.mal, ok'.cal, by show (Y.len + x).toNat % 32 = 0; have := hY.l32; omega, ok'.lc,
        ok'.top⟩ hlx ?_
    have hk' : (CMW e (Y.len + x) cap' Y.mem X.pv fv' X.gl X.used ⋆
        RestCM M K e X Y.run Y.rd Y.rl ⋆ R).holds (⟨s.locals, g, m, s.ffi⟩ : St σ) := by
      rw [CMW_mem]
      exact Assn.holds_perm hk (by ac_rfl)
    exact Assn.holds_assoc_r (Assn.holds_unfocus (FrameM_cmw M K e fv' X
      { Y with len := Y.len + x, cap := cap' }) hk')
  · intro l g m ffi exc v _ hh
    obtain ⟨cap', hh⟩ := Assn.holdsV_ex.mp hh
    obtain ⟨fv', hh⟩ := Assn.holdsV_ex.mp hh
    obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
    cases hC

/-- `st ev + 120, v; st ev + 128, w; rest`: record the return data. -/
theorem op_set_retdata (hE : GuestEnv E) {v1 v2 : Exp Word} {q : Prog Word} {M : Word}
    {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt} {Y : MemSt} {p n : Word}
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s)
    (h1 : ∀ y, E.eval s v1 = some y → y = .word p)
    (h2 : ∀ (m : Word → Option (PanValue Word)) y,
      E.eval ⟨s.locals, s.globals, m, s.ffi⟩ v2 = some y → y = .word n)
    (hq : ∀ m, (FrameOp M K e fv X ⋆ MemExtra e { Y with rd := p, rl := n } ⋆ R).holds
        (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) → WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.store (.op .add [.var .global "ev", .const 120#64]) v1)
      (.seq (.store (.op .add [.var .global "ev", .const 128#64]) v2) q)) Q := by
  have hev := holds_ev h
  have h0 : (MemTail e Y ⋆ (Assn.Range Y.mem (Y.mem + Y.cap) ⋆ FrameOp M K e fv X) ⋆ R).holds s :=
    Assn.holds_perm h (by unfold MemExtra; ac_rfl)
  unfold MemTail at h0
  refine WPr.seq_store_at hE h0 (addr := e + 120#64) (w := p)
    (of_eval (by ev [eval_global, hev])) h1 (by step) (fun m1 hm1 => ?_)
  refine WPr.seq_store_at hE hm1 (addr := e + 128#64) (w := n)
    (of_eval (by ev [eval_global, hev])) (h2 m1) (by step) (fun m2 hm2 => ?_)
  have hm' : (MemTail e { Y with rd := p, rl := n } ⋆ (Assn.Range Y.mem (Y.mem + Y.cap) ⋆
      FrameOp M K e fv X) ⋆ R).holds (⟨s.locals, s.globals, m2, s.ffi⟩ : St σ) := hm2
  exact hq m2 (Assn.holds_perm hm' (by unfold MemExtra; ac_rfl))

/-- `raise EvmErr k; rest` under the frame invariant with its memory buffer. -/
theorem op_raiseM {k : Word} {q : Prog Word} {M : Word} {K : Word → Prop} {e fv : Word}
    {R : Assn} {X0 X : OpSt} {Y : MemSt} {n : Nat} (hok : FrameOk M K fv X) (hY : MBufOk Y fv)
    (hp : Adv X X0 n) (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s)
    (hQ : AcceptsM M K e R s.ffi X0 Q) :
    WPr E s (.seq (.raise "EvmErr" (.const k)) q) Q := by
  refine WPr.seq (fun _ => False) (WPr.raise (fun v hv => ?_)) (fun _ h => h.elim)
  rw [eval_const] at hv
  cases hv
  exact hQ _ (Or.inl (Or.inr ⟨fv, X, Y, n, hok, hY, hp, Assn.holds_congr rfl rfl h,
    _, _, _, _, rfl⟩))

set_option maxHeartbeats 4000000 in
theorem op_return_frameM (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_return" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt) (Y0 : MemSt)
    (hok : FrameOk M K fv X0) (hY : MBufOk Y0 fv) (hgl : X0.gl.toNat < 2 ^ 64 - 1)
    (h : (FrameOp M K e fv X0 ⋆ MemExtra e Y0 ⋆ R).holds s) :
    WPr E s body (HandlerQM M K e R s.ffi X0) := by
  have hbody := (fun_of_index 568 hE.functions (by guest_decl_at 568) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine op_pop_sh hE hok hp h (AcceptsM.refl.toH hY).abort
    (fun v g m hsh_start hok hp h => ?_)
  obtain ⟨a0, a1, a2, a3, rfl⟩ := struct4_of_shape hsh_start
  refine op_pop_sh hE hok hp h (AcceptsM.refl.restore.toH hY).abort
    (fun v g m hsh_size hok hp h => ?_)
  obtain ⟨b0, b1, b2, b3, rfl⟩ := struct4_of_shape hsh_size
  refine op_cost1 hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b0 := b0) (b1 := b1)
    (b2 := b2) (b3 := b3)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      update_lookup]) hok hY h (fun cost xp hcost => ?_)
  have h1 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
    s.locals "start" (.rStruct [.word a0, .word a1, .word a2, .word a3])) "size"
    (.rStruct [.word b0, .word b1, .word b2, .word b3])) "x" (.rStruct [.word cost, .word xp]),
    g, m, s.ffi⟩ : St σ)) rfl rfl h
  refine op_charge_val hE (a := cost)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      evalF_rField, update_lookup]) hok hp h1
    (AcceptsM.refl.restore.restore.restore.toH hY).abort (fun hge g2 m2 hok hp h2 => ?_)
  have hcm : cost ≠ 18446744073709551615#64 := by
    intro hmax
    rw [hmax] at hge
    have : ¬ X0.gl.toNat < (18446744073709551615#64 : Word).toNat :=
      fun h => hge (BitVec.lt_def.mpr h)
    simp at this
    omega
  obtain ⟨hx32, hxs, -⟩ := hcost.resolve_left hcm
  refine op_extend hE (x := xp)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      evalF_rField, update_lookup]) hx32 hxs hok hY h2 AcceptsM.refl.restore.restore.restore
    (fun fv' cap' g3 m3 hok hY _ h3 => ?_)
  refine op_sat_word hE (a0 := b0) (a1 := b1) (a2 := b2) (a3 := b3)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      update_lookup]) ?_
  refine op_sat_word hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      update_lookup]) ?_
  have h4 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
    (updatePanValueMap (updatePanValueMap s.locals "start"
      (.rStruct [.word a0, .word a1, .word a2, .word a3])) "size"
      (.rStruct [.word b0, .word b1, .word b2, .word b3])) "x"
      (.rStruct [.word cost, .word xp])) "n" (.word (satW b0 b1 b2 b3))) "s"
      (.word (satW a0 a1 a2 a3)), g3, m3, s.ffi⟩ : St σ)) rfl rfl h3
  refine op_set_retdata hE (p := Y0.mem + satW a0 a1 a2 a3) (n := satW b0 b1 b2 b3) h4
    (mem_addr_eval hE (Y := { Y0 with len := Y0.len + xp, cap := cap' }) h4 (by lk []))
    (fun _ => of_eval (by lk [])) (fun m5 h5 => ?_)
  refine op_clear_run hE h5 (fun m6 h6 => ?_)
  refine op_return_stopped hok ?_ hp ?_ h6
    AcceptsM.refl.restore.restore.restore.restore.restore
  · exact ⟨hY.mal, hY.cal, hY.l32, hY.lc, hY.top⟩
  · rfl

set_option maxHeartbeats 4000000 in
theorem op_revert_frameM (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_revert" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt) (Y0 : MemSt)
    (hok : FrameOk M K fv X0) (hY : MBufOk Y0 fv) (hgl : X0.gl.toNat < 2 ^ 64 - 1)
    (h : (FrameOp M K e fv X0 ⋆ MemExtra e Y0 ⋆ R).holds s) :
    WPr E s body (HandlerQM M K e R s.ffi X0) := by
  have hbody := (fun_of_index 569 hE.functions (by guest_decl_at 569) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine op_pop_sh hE hok hp h (AcceptsM.refl.toH hY).abort
    (fun v g m hsh_start hok hp h => ?_)
  obtain ⟨a0, a1, a2, a3, rfl⟩ := struct4_of_shape hsh_start
  refine op_pop_sh hE hok hp h (AcceptsM.refl.restore.toH hY).abort
    (fun v g m hsh_size hok hp h => ?_)
  obtain ⟨b0, b1, b2, b3, rfl⟩ := struct4_of_shape hsh_size
  refine op_cost1 hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b0 := b0) (b1 := b1)
    (b2 := b2) (b3 := b3)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      update_lookup]) hok hY h (fun cost xp hcost => ?_)
  have h1 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
    s.locals "start" (.rStruct [.word a0, .word a1, .word a2, .word a3])) "size"
    (.rStruct [.word b0, .word b1, .word b2, .word b3])) "x" (.rStruct [.word cost, .word xp]),
    g, m, s.ffi⟩ : St σ)) rfl rfl h
  refine op_charge_val hE (a := cost)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      evalF_rField, update_lookup]) hok hp h1
    (AcceptsM.refl.restore.restore.restore.toH hY).abort (fun hge g2 m2 hok hp h2 => ?_)
  have hcm : cost ≠ 18446744073709551615#64 := by
    intro hmax
    rw [hmax] at hge
    have : ¬ X0.gl.toNat < (18446744073709551615#64 : Word).toNat :=
      fun h => hge (BitVec.lt_def.mpr h)
    simp at this
    omega
  obtain ⟨hx32, hxs, -⟩ := hcost.resolve_left hcm
  refine op_extend hE (x := xp)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      evalF_rField, update_lookup]) hx32 hxs hok hY h2 AcceptsM.refl.restore.restore.restore
    (fun fv' cap' g3 m3 hok hY _ h3 => ?_)
  refine op_sat_word hE (a0 := b0) (a1 := b1) (a2 := b2) (a3 := b3)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      update_lookup]) ?_
  refine op_sat_word hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      update_lookup]) ?_
  have h4 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
    (updatePanValueMap (updatePanValueMap s.locals "start"
      (.rStruct [.word a0, .word a1, .word a2, .word a3])) "size"
      (.rStruct [.word b0, .word b1, .word b2, .word b3])) "x"
      (.rStruct [.word cost, .word xp])) "n" (.word (satW b0 b1 b2 b3))) "s"
      (.word (satW a0 a1 a2 a3)), g3, m3, s.ffi⟩ : St σ)) rfl rfl h3
  refine op_set_retdata hE (p := Y0.mem + satW a0 a1 a2 a3) (n := satW b0 b1 b2 b3) h4
    (mem_addr_eval hE (Y := { Y0 with len := Y0.len + xp, cap := cap' }) h4 (by lk []))
    (fun _ => of_eval (by lk [])) (fun m5 h5 => ?_)
  refine op_raiseM hok ?_ hp h5
    AcceptsM.refl.restore.restore.restore.restore.restore
  exact ⟨hY.mal, hY.cal, hY.l32, hY.lc, hY.top⟩

end InitECandidate.Solver.GuestBound
