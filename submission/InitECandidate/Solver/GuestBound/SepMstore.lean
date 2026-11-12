import InitECandidate.Solver.GuestBound.SepBe

/-!
# `op_mstore` under the frame invariant with the memory buffer

After `charge_with_memory` the 32 bytes at `start` lie inside the memory in
use, hence inside the buffer, so `u256_to_be32` writes owned memory.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `var x = sat_word(e); rest`, with the value. -/
theorem op_sat_word (hE : GuestEnv E) {x : VarName} {args : List (Exp Word)} {body : Prog Word}
    {a0 a1 a2 a3 : Word}
    (hargs : E.evalArgs s args = some [.rStruct [.word a0, .word a1, .word a2, .word a3]])
    (hk : WPr E ⟨updatePanValueMap s.locals x (.word (satW a0 a1 a2 a3)), s.globals, s.memory,
        s.ffi⟩ body (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x .one "sat_word" args body) Q := by
  refine WPr.decCall_spec (fun rb => ∃ l, rb = .returned l s.globals s.memory s.ffi
      [.word (satW a0 a1 a2 a3)]) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 440 hE.functions (by guest_decl_at 440) (by decide +kernel)
      hlk).2
    rw [hargs] at hvalues
    cases hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact sat_word_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ a0 a1 a2 a3
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  · rintro l g m ffi v ⟨l', hC⟩
    injection hC with _ hg hm hf hv'
    subst hg hm hf
    simp only [List.cons.injEq, and_true] at hv'
    subst hv'
    exact hk
  · rintro l g m ffi exc v ⟨l', hC⟩
    cases hC
  · rintro l g m ffi ev ⟨l', hC⟩
    cases hC

/-- The address `mem + x` as the handlers compute it. -/
theorem mem_addr_eval (hE : GuestEnv E) {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {X : OpSt} {Y : MemSt} {x : VarName} {sv : Word}
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s)
    (hx : s.locals x = some (.word sv)) :
    ∀ y, E.eval s (.op .add [.load .one (.op .add [.var .global "ev", .const 24#64]),
      .var .local x]) = some y → y = .word (Y.mem + sv) := by
  have h' := Assn.holds_assoc_r (Assn.holds_focus (FrameM_cmw M K e fv X Y)
    (Assn.holds_assoc_l (P := FrameOp M K e fv X) h))
  unfold MemW at h'
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at h' (by look)
  exact eval_add2_inv hE
    (eval_load_at hE (addr := e + 24#64) (of_eval (by ev [eval_global, hev])) h' (by look))
    (of_eval (by lk [hx]))

set_option maxHeartbeats 1000000 in
/-- `u256_to_be32(v, mem + off); rest` when the 32 bytes lie inside the buffer. -/
theorem op_store32 (hE : GuestEnv E) {e1 e2 : Exp Word} {q : Prog Word}
    {w0 w1 w2 w3 out : Word} {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {X0 X : OpSt} {Y : MemSt}
    (h1 : ∀ y, E.eval s e1 = some y → y = .rStruct [.word w0, .word w1, .word w2, .word w3])
    (h2 : ∀ y, E.eval s e2 = some y → y = .word out)
    (hlo : Y.mem.toNat ≤ out.toNat) (hhi : out.toNat + 32 ≤ Y.mem.toNat + Y.cap.toNat)
    (hok : FrameOk M K fv X) (hY : MBufOk Y fv)
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s) (hQ : AcceptsM M K e R s.ffi X0 Q)
    (hq : ∀ g m, (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds (⟨s.locals, g, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, g, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "u256_to_be32" [e1, e2]) q) Q := by
  have htop := hY.top
  have hfp := hok.ok.fp
  have hpv := hok.ok.pv_hi
  have hmc : (Y.mem + Y.cap).toNat = Y.mem.toNat + Y.cap.toNat := by bv_omega
  have hF : (Assn.Range Y.mem (Y.mem + Y.cap) ⋆ (MemTail e Y ⋆ FrameOp M K e fv X) ⋆
      R).holds s :=
    Assn.holds_perm h (by unfold MemExtra; ac_rfl)
  refine WPr.seq_call_framedT hF (Qc := fun r =>
      ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆ Assn.Range Y.mem (Y.mem + Y.cap)) ?_
    (fun r ht => hQ r (Or.inl (Or.inl ht))) ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 87 hE.functions (by guest_decl_at 87) (by decide +kernel)
      hlk).2
    obtain ⟨v1, v2, g1, g2, rfl⟩ := evalArgs2_inv hvalues
    have := h1 _ g1
    subst this
    have := h2 _ g2
    subst this
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact u256_to_be32_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ out w0 w1
      w2 w3 Y.mem (Y.mem + Y.cap)
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hY.mal hlo (by omega) (by omega)
  · intro l g m ffi vs hh
    obtain ⟨⟨_, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
    injection hC with _ _ _ hf _
    subst hf
    exact hq g m (Assn.holds_perm hk (by unfold MemExtra; ac_rfl))
  · intro l g m ffi exc v _ hh
    obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
    cases hC

set_option maxHeartbeats 2000000 in
theorem op_mstore_frameM (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_mstore" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt) (Y0 : MemSt)
    (hok : FrameOk M K fv X0) (hY : MBufOk Y0 fv) (hgl : X0.gl.toNat < 2 ^ 64 - 1)
    (h : (FrameOp M K e fv X0 ⋆ MemExtra e Y0 ⋆ R).holds s) :
    WPr E s body (HandlerQM M K e R s.ffi X0) := by
  have hbody := (fun_of_index 508 hE.functions (by guest_decl_at 508) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine op_pop_sh hE hok hp h (AcceptsM.refl.toH hY).abort
    (fun v g m hsh_start hok hp h => ?_)
  obtain ⟨a0, a1, a2, a3, rfl⟩ := struct4_of_shape hsh_start
  refine op_pop_sh hE hok hp h (AcceptsM.refl.restore.toH hY).abort
    (fun v g m hsh_value hok hp h => ?_)
  obtain ⟨c0, c1, c2, c3, rfl⟩ := struct4_of_shape hsh_value
  refine op_charge_mem hE (base := 3#64) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := 32#64) (b1 := 0#64) (b2 := 0#64) (b3 := 0#64)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_const, eval_local,
      evalF_rStruct, update_lookup]) hok hY hp hgl h AcceptsM.refl.restore.restore
    (fun fv' x total cap' g m hok hY hp hacc h => ?_)
  have hacc' : (satW a0 a1 a2 a3).toNat + 32 ≤ (Y0.len + x).toNat := by
    have e32 : satW (32#64) (0#64) (0#64) (0#64) = 32#64 := by simp [satW]
    rw [e32] at hacc
    rcases hacc with h0 | h1
    · exact absurd h0 (by decide)
    · simpa using h1
  refine op_sat_word hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      update_lookup]) ?_
  have hh := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
    s.locals "start" (.rStruct [.word a0, .word a1, .word a2, .word a3])) "value"
    (.rStruct [.word c0, .word c1, .word c2, .word c3])) "s" (.word (satW a0 a1 a2 a3)), g, m,
    s.ffi⟩ : St σ)) rfl rfl h
  have hlc := hY.lc
  have htop := hY.top
  have hfp := hok.ok.fp
  have hpv := hok.ok.pv_hi
  have hadd : (Y0.mem + satW a0 a1 a2 a3).toNat = Y0.mem.toNat + (satW a0 a1 a2 a3).toNat := by
    have h1 : (satW a0 a1 a2 a3).toNat ≤ cap'.toNat := by
      have : (Y0.len + x).toNat ≤ cap'.toNat := hlc
      omega
    have h2 : Y0.mem.toNat + cap'.toNat = fv'.toNat := htop
    bv_omega
  refine op_store32 hE (out := Y0.mem + satW a0 a1 a2 a3) (w0 := c0) (w1 := c1) (w2 := c2)
    (w3 := c3) (Y := { Y0 with len := Y0.len + x, cap := cap' })
    (fun y hy => by
      rw [eval_local] at hy
      simp (config := { decide := true }) [update_lookup] at hy
      exact hy.symm)
    (mem_addr_eval hE (Y := { Y0 with len := Y0.len + x, cap := cap' }) hh (by lk []))
    (by show Y0.mem.toNat ≤ _; omega)
    (by
      show (Y0.mem + satW a0 a1 a2 a3).toNat + 32 ≤ Y0.mem.toNat + cap'.toNat
      have : (Y0.len + x).toNat ≤ cap'.toNat := hlc
      omega)
    hok hY hh AcceptsM.refl.restore.restore.restore (fun g2 m2 h2 => ?_)
  refine op_pc_add hE (d := 1#64)
    (by simp [evalArgs_cons, evalArgs_nil, eval_const]) hok hp h2
    (AcceptsM.refl.restore.restore.restore.toH hY).abort (fun g3 m3 hok hp h3 => ?_)
  exact op_return hok hp (by decide) h3 (AcceptsM.refl.restore.restore.restore.toH hY)

/-- `stb mem + off, v; rest` when the byte lies inside the buffer. -/
theorem op_storeByte_mem (hE : GuestEnv E) {a v : Exp Word} {q : Prog Word} {addr : Word}
    {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt} {Y : MemSt}
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hlo : Y.mem.toNat ≤ addr.toNat) (hhi : addr.toNat < Y.mem.toNat + Y.cap.toNat)
    (hok : FrameOk M K fv X) (hY : MBufOk Y fv)
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s)
    (hq : ∀ m, (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds
        (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) → WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.storeByte a v) q) Q := by
  have htop := hY.top
  have hmal := hY.mal
  have hfp := hok.ok.fp
  have hpv := hok.ok.pv_hi
  have hmc : (Y.mem + Y.cap).toNat = Y.mem.toNat + Y.cap.toNat := by bv_omega
  have hF : (Assn.Range Y.mem (Y.mem + Y.cap) ⋆ (MemTail e Y ⋆ FrameOp M K e fv X) ⋆
      R).holds s :=
    Assn.holds_perm h (by unfold MemExtra; ac_rfl)
  refine WPr.seq_storeByte_range hE hF ha (by omega) (by omega) (fun m hm => ?_)
  exact hq m (Assn.holds_perm hm (by unfold MemExtra; ac_rfl))

set_option maxHeartbeats 2000000 in
theorem op_mstore8_frameM (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_mstore8" E.functions = some (parameters, body))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt) (Y0 : MemSt)
    (hok : FrameOk M K fv X0) (hY : MBufOk Y0 fv) (hgl : X0.gl.toNat < 2 ^ 64 - 1)
    (h : (FrameOp M K e fv X0 ⋆ MemExtra e Y0 ⋆ R).holds s) :
    WPr E s body (HandlerQM M K e R s.ffi X0) := by
  have hbody := (fun_of_index 509 hE.functions (by guest_decl_at 509) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only
  have hp : Adv X0 X0 0 := ⟨Nat.le_refl _, Nat.le_refl _⟩
  refine op_pop_sh hE hok hp h (AcceptsM.refl.toH hY).abort
    (fun v g m hsh_start hok hp h => ?_)
  obtain ⟨a0, a1, a2, a3, rfl⟩ := struct4_of_shape hsh_start
  refine op_pop_sh hE hok hp h (AcceptsM.refl.restore.toH hY).abort
    (fun v g m hsh_value hok hp h => ?_)
  obtain ⟨c0, c1, c2, c3, rfl⟩ := struct4_of_shape hsh_value
  refine op_charge_mem hE (base := 3#64) (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := 1#64) (b1 := 0#64) (b2 := 0#64) (b3 := 0#64)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_const, eval_local,
      evalF_rStruct, update_lookup]) hok hY hp hgl h AcceptsM.refl.restore.restore
    (fun fv' x total cap' g m hok hY hp hacc h => ?_)
  have hacc' : (satW a0 a1 a2 a3).toNat + 1 ≤ (Y0.len + x).toNat := by
    have e1 : satW (1#64) (0#64) (0#64) (0#64) = 1#64 := by simp [satW]
    rw [e1] at hacc
    rcases hacc with h0 | h1
    · exact absurd h0 (by decide)
    · simpa using h1
  refine op_sat_word hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
      update_lookup]) ?_
  have hh := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
    s.locals "start" (.rStruct [.word a0, .word a1, .word a2, .word a3])) "value"
    (.rStruct [.word c0, .word c1, .word c2, .word c3])) "s" (.word (satW a0 a1 a2 a3)), g, m,
    s.ffi⟩ : St σ)) rfl rfl h
  have hlc := hY.lc
  have htop := hY.top
  have hfp := hok.ok.fp
  have hpv := hok.ok.pv_hi
  have hadd : (Y0.mem + satW a0 a1 a2 a3).toNat = Y0.mem.toNat + (satW a0 a1 a2 a3).toNat := by
    have h1 : (satW a0 a1 a2 a3).toNat ≤ cap'.toNat := by
      have : (Y0.len + x).toNat ≤ cap'.toNat := hlc
      omega
    have h2 : Y0.mem.toNat + cap'.toNat = fv'.toNat := htop
    bv_omega
  refine op_storeByte_mem hE (addr := Y0.mem + satW a0 a1 a2 a3)
    (Y := { Y0 with len := Y0.len + x, cap := cap' })
    (mem_addr_eval hE (Y := { Y0 with len := Y0.len + x, cap := cap' }) hh (by lk []))
    (by show Y0.mem.toNat ≤ _; omega)
    (by
      show (Y0.mem + satW a0 a1 a2 a3).toNat < Y0.mem.toNat + cap'.toNat
      have : (Y0.len + x).toNat ≤ cap'.toNat := hlc
      omega)
    hok hY hh (fun m2 h2 => ?_)
  refine op_pc_add hE (d := 1#64)
    (by simp [evalArgs_cons, evalArgs_nil, eval_const]) hok hp h2
    (AcceptsM.refl.restore.restore.restore.toH hY).abort (fun g3 m3 hok hp h3 => ?_)
  exact op_return hok hp (by decide) h3 (AcceptsM.refl.restore.restore.restore.toH hY)

end InitECandidate.Solver.GuestBound
