import InitECandidate.Solver.GuestBound.MemCost

/-!
# `charge_with_memory` as a framed specification

`charge_with_memory(base, start, size)` computes the cost of extending memory
to cover the access, charges `base` plus that cost, and extends memory. It
raises out-of-gas with nothing changed, or returns with the access inside the
memory in use and at least `base` gas charged.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ}

/-- `extend_memory(e)` at a call site where the argument evaluates to `x`. -/
theorem extend_memory_hc (hE : GuestEnv E) {args : List (Exp Word)} {x : Word}
    (hargs : E.evalArgs s args = some [.word x]) (e len cap mem pv fv : Word)
    (hx8 : x.toNat % 8 = 0) (hxb : x.toNat ≤ 2 ^ 50) (ok : MemOk len cap mem pv fv) :
    ∀ parameters cbody values cl,
      lookupPanFunction "extend_memory" E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (MemW e len cap mem pv fv)
        (fun r => Assn.ex fun cap' : Word => Assn.ex fun fv' : Word =>
          ⌜(MemOk (len + x) cap' mem pv fv' ∧ (len + x).toNat = len.toNat + x.toNat ∧
              fv.toNat ≤ fv'.toNat) ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
            MemW e (len + x) cap' mem pv fv') := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 460 hE.functions (by guest_decl_at 460) (by decide +kernel)
    hlk).2
  rw [hargs] at hvalues
  cases hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact extend_memory_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e len cap
    mem pv fv x (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hx8 hxb ok

/-- The memory buffer with the gas counters. -/
def CMW (e len cap mem pv fv gl used : Word) : Assn :=
  MemW e len cap mem pv fv ⋆ .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 184#64) ↦ .word used

/-- `MemW` without `ev`. -/
def MemNoEv (e len cap mem pv fv : Word) : Assn :=
  Assn.Range mem (mem + cap) ⋆ .mem (e + 32#64) ↦ .word len ⋆ .mem (e + 40#64) ↦ .word cap ⋆
    .mem (e + 24#64) ↦ .word mem ⋆ .glob "scratch_ptr" ↦ .word pv ⋆
    .glob "frame_mem_ptr" ↦ .word fv ⋆ Assn.Range fv pv

theorem CMW_gas (e len cap mem pv fv gl used : Word) :
    CMW e len cap mem pv fv gl used = (GasCells e gl used ⋆ MemNoEv e len cap mem pv fv) := by
  unfold CMW MemW GasCells MemNoEv; ac_rfl

theorem CMW_mem (e len cap mem pv fv gl used : Word) :
    CMW e len cap mem pv fv gl used =
      (MemW e len cap mem pv fv ⋆ (.mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 184#64) ↦ .word used)) :=
  rfl

set_option maxHeartbeats 2000000 in
theorem charge_with_memory_framed (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "charge_with_memory" E.functions = some (parameters, body))
    (s : St σ) (e len cap mem pv fv gl used base a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb : s.locals "base" = some (.word base))
    (hst : s.locals "start" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hsz : s.locals "size" = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (ok : MemOk len cap mem pv fv) (hl32 : len.toNat % 32 = 0)
    (hgl : gl.toNat < 2 ^ 64 - 1) :
    WPFt E s body (CMW e len cap mem pv fv gl used) (fun r => Assn.or
      (⌜∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 4#64)⌝ ⋆
        CMW e len cap mem pv fv gl used)
      (Assn.ex fun cap' : Word => Assn.ex fun fv' : Word => Assn.ex fun x : Word =>
        Assn.ex fun total : Word =>
          ⌜(MemOk (len + x) cap' mem pv fv' ∧ (len + x).toNat = len.toNat + x.toNat ∧
              x.toNat % 32 = 0 ∧
              (satW b0 b1 b2 b3 = 0#64 ∨ (satW a0 a1 a2 a3).toNat + (satW b0 b1 b2 b3).toNat ≤
                len.toNat + x.toNat) ∧
              base.toNat ≤ total.toNat ∧ total.toNat ≤ gl.toNat ∧ fv.toNat ≤ fv'.toNat) ∧
            ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
          CMW e (len + x) cap' mem pv fv' (gl - total) (used + total))) := by
  have hbody := (fun_of_index 461 hE.functions (by guest_decl_at 461) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  dsimp only
  have hM := Assn.holds_focus (CMW_mem ..) hR
  unfold MemW at hM
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hM (by look)
  have hlen : s.memory (e + 32#64) = some (.word len) :=
    (by look : Look (.mem (e + 32#64)) (.word len) _) _ _ hM
  have hlb : len.toNat ≤ 2 ^ 62 := by
    have := ok.lc; have := ok.top; have := ok.fp; have := ok.pvh; omega
  -- x = extend_memory_cost1(start, size)
  refine WPr.decCall_spec (fun rb => ∃ l cost x, rb = .returned l s.globals s.memory s.ffi
      [.rStruct [.word cost, .word x]] ∧
      CostOk (satW a0 a1 a2 a3) (satW b0 b1 b2 b3) len cost x) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 458 hE.functions (by guest_decl_at 458) (by decide +kernel)
      hlk).2
    have hvals : values = [.rStruct [.word a0, .word a1, .word a2, .word a3],
        .rStruct [.word b0, .word b1, .word b2, .word b3]] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local, hst, hsz]
        at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact extend_memory_cost1_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩
      a0 a1 a2 a3 b0 b1 b2 b3 e len
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hev hlen hl32 hlb
  rotate_left
  · rintro l g m ffi exc v ⟨l', cost, x, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', cost, x, hC, -⟩
    cases hC
  rintro l g m ffi v ⟨l', cost, x, hC, hcost⟩
  injection hC with _ hg hm hf hv'
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  -- total = add_sat(base, cost)
  refine WPr.decCall_spec (fun rb => ∃ l t, rb = .returned l s.globals s.memory s.ffi [.word t] ∧
      ((base.toNat + cost.toNat < 2 ^ 64 ∧ t.toNat = base.toNat + cost.toNat) ∨
        (2 ^ 64 ≤ base.toNat + cost.toNat ∧ t = 18446744073709551615#64))) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 441 hE.functions (by guest_decl_at 441) (by decide +kernel)
      hlk).2
    have hvals : values = [.word base, .word cost] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local, evalF_rField,
        update_lookup, hb] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact add_sat_exact hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ base cost
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  rotate_left
  · rintro l g m ffi exc v ⟨l', t, hC, -⟩
    cases hC
  · rintro l g m ffi ev ⟨l', t, hC, -⟩
    cases hC
  rintro l1 g m ffi v ⟨l', total, hC, htot⟩
  injection hC with _ hg hm hf hv'
  subst hg hm hf
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  have hbt : base.toNat ≤ total.toNat := by
    rcases htot with ⟨-, h⟩ | ⟨-, h⟩
    · omega
    · rw [h]; have := base.isLt; simp; omega
  have hR2 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap s.locals "x"
    (.rStruct [.word cost, .word x])) "total" (.word total), s.globals, s.memory, s.ffi⟩ : St σ))
    rfl rfl hR
  -- charge_gas(total)
  refine WPr.seq_call_framedT (Assn.holds_focus (CMW_gas ..) hR2)
    (fun p b v cl a1' a2' a3' => (charge_gas_hc hE (a := total)
      (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        update_lookup]) e gl used p b v cl a1' a2' a3').toT) (by trap_tac) ?_ ?_
  rotate_left
  · intro l2 g2 m2 ffi2 exc v _ h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      simp only [restorePanValueFfiLocal]
      exact Or.inr (Assn.holds_or_left (Assn.holds_pure_intro ⟨_, _, _, rfl⟩
        (Assn.holds_unfocus (CMW_gas ..) (Assn.holds_congr rfl rfl hk))))
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
  intro l2 g2 m2 ffi2 vs2 h
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  obtain ⟨⟨hge, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
  injection hC with _ _ _ hf _
  subst hf
  have htg : total.toNat ≤ gl.toNat := Nat.le_of_not_lt (fun h => hge (BitVec.lt_def.mpr h))
  have hcm : cost ≠ 18446744073709551615#64 := by
    intro hmax
    rw [hmax] at htot
    rcases htot with ⟨h1, h2⟩ | ⟨-, h2⟩
    · simp at h1 h2
      omega
    · rw [h2] at htg
      simp at htg
      omega
  obtain ⟨hx32, hxs, hacc⟩ := hcost.resolve_left hcm
  have hO := Assn.holds_unfocus (CMW_gas e len cap mem pv fv (gl - total) (used + total)) hk
  -- extend_memory(x)
  refine WPr.seq_call_framedT (Assn.holds_focus (CMW_mem ..) hO)
    (extend_memory_hc hE (x := x) (by simp (config := { decide := true }) [evalArgs_cons,
      evalArgs_nil, eval_local, evalF_rField, update_lookup]) e len cap mem pv fv (by omega)
      (by omega) ok) (by trap_tac) ?_ ?_
  rotate_left
  · intro l3 g3 m3 ffi3 exc v _ h
    obtain ⟨cap', h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨fv', h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  intro l3 g3 m3 ffi3 vs3 h
  obtain ⟨cap', h⟩ := Assn.holdsV_ex.mp h
  obtain ⟨fv', h⟩ := Assn.holdsV_ex.mp h
  obtain ⟨⟨⟨ok', hlx, hfv⟩, _, _, _, hC⟩, hk3⟩ := Assn.holds_pure_elim h
  injection hC with _ _ _ hf _
  subst hf
  have hO3 := Assn.holds_unfocus
    (CMW_mem e (len + x) cap' mem pv fv' (gl - total) (used + total)) hk3
  refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  refine Or.inr (Assn.holds_or_right (Assn.holdsV_ex.mpr ⟨cap', Assn.holdsV_ex.mpr ⟨fv',
    Assn.holdsV_ex.mpr ⟨x, Assn.holdsV_ex.mpr ⟨total, ?_⟩⟩⟩⟩))
  exact Assn.holds_pure_intro ⟨⟨ok', hlx, hx32, hacc, hbt, htg, hfv⟩, _, _, _, rfl⟩
    (Assn.holds_congr rfl rfl hO3)

end InitECandidate.Solver.GuestBound
