import InitECandidate.Solver.GuestBound.SepFrameMem

/-!
# `extend_memory` as a framed specification

The EVM memory of a frame is a buffer `[mem, mem + cap)` at the top of the
frame-memory arena (`mem + cap = frame_mem_ptr`), of which the first `len`
bytes are in use. `extend_memory(expand_by)` grows `len`; when that passes
`cap` it extends the buffer in place by allocating from the arena, and zeroes
the new bytes.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The bounds of a frame's EVM memory buffer. -/
structure MemOk (len cap mem pv fv : Word) : Prop where
  mal : mem.toNat % 8 = 0
  cal : cap.toNat % 8 = 0
  lal : len.toNat % 8 = 0
  lc : len.toNat ≤ cap.toNat
  top : mem.toNat + cap.toNat = fv.toNat
  fp : fv.toNat ≤ pv.toNat
  pvh : pv.toNat ≤ 2 ^ 62

/-- What `extend_memory` owns. -/
def MemW (e len cap mem pv fv : Word) : Assn :=
  Assn.Range mem (mem + cap) ⋆ .glob "ev" ↦ .word e ⋆ .mem (e + 32#64) ↦ .word len ⋆
    .mem (e + 40#64) ↦ .word cap ⋆ .mem (e + 24#64) ↦ .word mem ⋆
    .glob "scratch_ptr" ↦ .word pv ⋆ .glob "frame_mem_ptr" ↦ .word fv ⋆ Assn.Range fv pv

set_option maxHeartbeats 2000000 in
/-- `extend_memory(x)` for `x` a multiple of 8: traps, or returns with `len + x`
bytes in use and the buffer still at the top of the arena. -/
theorem extend_memory_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "extend_memory" E.functions = some (parameters, body))
    (s : St σ) (e len cap mem pv fv x : Word) (hx : s.locals "expand_by" = some (.word x))
    (hx8 : x.toNat % 8 = 0) (hxb : x.toNat ≤ 2 ^ 50) (ok : MemOk len cap mem pv fv) :
    WPFt E s body (MemW e len cap mem pv fv) (fun r => Assn.ex fun cap' : Word =>
      Assn.ex fun fv' : Word =>
        ⌜(MemOk (len + x) cap' mem pv fv' ∧ (len + x).toNat = len.toNat + x.toNat ∧
            fv.toNat ≤ fv'.toNat) ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
          MemW e (len + x) cap' mem pv fv') := by
  have hbody := (fun_of_index 460 hE.functions (by guest_decl_at 460) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  have hR0 := hR
  unfold MemW at hR
  dsimp only
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hR (by look)
  have hmal := ok.mal
  have hcal := ok.cal
  have hlal := ok.lal
  have hlc := ok.lc
  have htop := ok.top
  have hfp := ok.fp
  have hpvh := ok.pvh
  have etop : mem + cap = fv := by bv_omega
  have hlx : (len + x).toNat = len.toNat + x.toNat := by bv_omega
  -- nothing to do when `expand_by = 0`
  refine WPr.seq (IsState s) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .equal) (of_eval (w := x) (by lk [hx]))
      (of_eval (w := 0#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · exact WPr.skip rfl
    · rename_i hnz
      have hz : x = 0#64 := by
        by_contra hne
        exact hnz (by rw [hcv]; simp [evalPanCmp, hne])
      refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
      refine Or.inr (Assn.holdsV_ex.mpr ⟨cap, Assn.holdsV_ex.mpr ⟨fv, ?_⟩⟩)
      have e0 : len + x = len := by rw [hz]; simp
      rw [e0]
      exact Assn.holds_pure_intro ⟨⟨ok, by rw [hz]; simp, Nat.le_refl _⟩, _, _, _, rfl⟩
        (Assn.holds_congr rfl rfl hR0)
  intro a ha
  have ha' : a = s := ha
  rw [ha']
  clear ha ha' a
  refine WPr.dec_ev (fun v hv => ?_)
  have hm := eval_load_at hE (addr := e + 32#64) (v := .word len)
    (of_eval (by ev [eval_global, hev])) hR (by look) v hv
  subst hm
  refine WPr.dec_ev (fun v hv => ?_)
  have hm := eval_load_at hE (addr := e + 40#64) (v := .word cap)
    (of_eval (by ev [eval_global, hev]))
    (Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "len" (.word len), s.globals,
      s.memory, s.ffi⟩ : St σ)) rfl rfl hR) (by look) v hv
  subst hm
  refine WPr.dec_ev (fun v hv => ?_)
  have hm := (of_eval (w := len + x) (by ev [hx])) v hv
  subst hm
  refine WPr.seq (fun s' => ∃ l g m cap' fv', s' = ⟨l, g, m, s.ffi⟩ ∧
      l "len" = some (.word len) ∧ l "expand_by" = some (.word x) ∧
      l "nlen" = some (.word (len + x)) ∧ MemOk len cap' mem pv fv' ∧
      (len + x).toNat ≤ cap'.toNat ∧ fv.toNat ≤ fv'.toNat ∧
      (MemW e len cap' mem pv fv' ⋆ R).holds s') (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := cap) (by lk []))
      (of_eval (w := len + x) (by lk [])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      have hnl := lower_zero hcv.symm
      exact WPr.skip ⟨_, _, _, cap, fv, rfl, by lk [], by lk [hx], by lk [], ok,
        Nat.le_of_not_lt (fun h => hnl (BitVec.lt_def.mpr h)), Nat.le_refl _,
        Assn.holds_congr rfl rfl hR0⟩
    rename_i h0
    have hlt : cap.toNat < (len + x).toNat := BitVec.lt_def.mp (cmp_lower_ne (by rw [← hcv]; exact h0))
    refine WPr.dec_ev (fun v hv => ?_)
    have hm := (of_eval (w := cap * 2#64) (by pan [])) v hv
    subst hm
    have hc2 : (cap * 2#64).toNat = 2 * cap.toNat := by bv_omega
    refine WPr.seq (fun s' => ∃ l nc, s' = ⟨l, s.globals, s.memory, s.ffi⟩ ∧
        l "ncap" = some (.word nc) ∧ l "cap" = some (.word cap) ∧
        l "len" = some (.word len) ∧ l "expand_by" = some (.word x) ∧
        l "nlen" = some (.word (len + x)) ∧ (len + x).toNat ≤ nc.toNat ∧ nc.toNat % 8 = 0 ∧
        nc.toNat ≤ 2 ^ 63) (WPr.ite_both (fun w2 hw2 => ?_)) ?_
    · have hcv2 := eval_cmp_inv hE (op := .lower) (of_eval (w := cap * 2#64) (by lk []))
        (of_eval (w := len + x) (by lk [])) _ hw2
      simp only [PanValue.word.injEq] at hcv2
      split
      · rename_i h02
        rw [h02] at hcv2
        have hnl := lower_zero hcv2.symm
        have : ¬ (cap * 2#64).toNat < (len + x).toNat := fun h => hnl (BitVec.lt_def.mpr h)
        exact WPr.skip ⟨_, cap * 2#64, rfl, by lk [], by lk [], by lk [], by lk [hx], by lk [],
          by omega, by omega, by omega⟩
      · have hn : (len + x + 1024#64).toNat = len.toNat + x.toNat + 1024 := by bv_omega
        exact WPr.assign_local (old := cap * 2#64) (w := len + x + 1024#64) (by lk [])
          (of_eval (by ev [])) ⟨_, len + x + 1024#64, rfl, by lk [], by lk [], by lk [],
            by lk [hx], by lk [], by omega, by omega, by omega⟩
    rintro _ ⟨l, nc, rfl, hlnc, hlcap, hllen, hlx', hlnl, hnc1, hnc8, hncb⟩
    have hW := Assn.holds_congr (s' := (⟨l, s.globals, s.memory, s.ffi⟩ : St σ)) rfl rfl hR
    have hsub : (nc - cap).toNat = nc.toNat - cap.toNat := by bv_omega
    have hA : (ArenaPtrs pv fv ⋆ (Assn.Range mem (mem + cap) ⋆ .glob "ev" ↦ .word e ⋆
        .mem (e + 32#64) ↦ .word len ⋆ .mem (e + 40#64) ↦ .word cap ⋆
        .mem (e + 24#64) ↦ .word mem ⋆ Assn.Range fv pv) ⋆ R).holds
        (⟨l, s.globals, s.memory, s.ffi⟩ : St σ) :=
      Assn.holds_perm hW (by unfold ArenaPtrs; ac_rfl)
    refine WPr.seq_call_framedT hA (frame_mem_alloc_hc hE (nv := nc - cap)
      (by ev [hlnc, hlcap]) pv fv ok.fp ok.pvh) (by trap_tac) ?_ ?_
    rotate_left
    · intro l1 g1 m1 ffi1 exc v _ h
      obtain ⟨qv, h⟩ := Assn.holdsV_ex.mp h
      obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    intro l1 g1 m1 ffi1 vs1 h
    obtain ⟨qv, h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨⟨⟨hq1, hq2, hq3, hq4⟩, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    have hqv : qv.toNat = mem.toNat + nc.toNat := by omega
    have eq1 : mem + nc = qv := by bv_omega
    have e1 := Assn.range_split (a := fv) (q := qv) (b := pv) (by omega) hq2
    have e2 := Assn.range_split (a := mem) (q := fv) (b := qv) (by omega) (by omega)
    have hk2 : ((Assn.Range mem (mem + nc) ⋆ .glob "ev" ↦ .word e ⋆
        .mem (e + 32#64) ↦ .word len ⋆ .mem (e + 40#64) ↦ .word cap ⋆
        .mem (e + 24#64) ↦ .word mem ⋆ .glob "scratch_ptr" ↦ .word pv ⋆
        .glob "frame_mem_ptr" ↦ .word qv ⋆ Assn.Range qv pv) ⋆ R).holds
        (⟨l, g1, m1, s.ffi⟩ : St σ) :=
      Assn.holds_perm hk (by unfold ArenaPtrs; rw [etop, eq1, e1, e2]; ac_rfl)
    have hevg : g1 "ev" = some (.word e) := Assn.glob_at hk2 (by look)
    have hdst : (mem + cap).toNat = fv.toNat := by rw [etop]
    refine WPr.seq_memzero_range hE (dst := mem + cap) (nW := nc - cap) (lo := mem)
      (hi := mem + nc)
      (eval_add2_inv hE
        (eval_load_at hE (addr := e + 24#64) (of_eval (by ev [eval_global, hevg])) hk2 (by look))
        (of_eval (by lk [hlcap])))
      (of_eval (by ev [hlnc, hlcap])) (by omega) (by omega) (by omega) (by omega)
      (by rw [eq1]; omega) (Assn.holds_assoc_r hk2) (by trap_tac) (fun m2 hm2 => ?_)
    have hm2' := Assn.holds_assoc_l hm2
    refine WPr.store_at hE hm2' (addr := e + 40#64) (w := nc)
      (of_eval (by ev [eval_global, hevg])) (of_eval (by lk [hlnc])) (by step)
      (fun m3 hm3 => ?_)
    simp only [restorePanValueFfiLocal]
    refine ⟨_, _, _, nc, qv, rfl, ?_, ?_, ?_, ⟨ok.mal, hnc8, ok.lal, by omega, by omega, hq2,
      ok.pvh⟩, hnc1, by omega, Assn.holds_congr rfl rfl hm3⟩
    · simp (config := { decide := true }) [restorePanValueLocal, hllen]
    · simp (config := { decide := true }) [restorePanValueLocal, hlx']
    · simp (config := { decide := true }) [restorePanValueLocal, hlnl]
  -- zero the new bytes and record the new length
  rintro _ ⟨l, g, m, cap', fv', rfl, hllen, hlx', hlnl, ok', hle, hfv, hT⟩
  unfold MemW at hT
  have hevg : g "ev" = some (.word e) := Assn.glob_at hT (by look)
  have htop' := ok'.top
  have hfp' := ok'.fp
  have hml : (mem + len).toNat = mem.toNat + len.toNat := by bv_omega
  have hmc : (mem + cap').toNat = mem.toNat + cap'.toNat := by bv_omega
  refine WPr.seq_memzero_range hE (dst := mem + len) (nW := x) (lo := mem) (hi := mem + cap')
    (eval_add2_inv hE
      (eval_load_at hE (addr := e + 24#64) (of_eval (by ev [eval_global, hevg])) hT (by look))
      (of_eval (by lk [hllen])))
    (of_eval (by lk [hlx'])) (by omega) hx8 (by omega) (by omega) (by omega)
    (Assn.holds_assoc_r hT) (by trap_tac) (fun m2 hm2 => ?_)
  have hm2' := Assn.holds_assoc_l hm2
  refine WPr.seq_store_at hE hm2' (addr := e + 32#64) (w := len + x)
    (of_eval (by ev [eval_global, hevg])) (of_eval (by lk [hlnl])) (by step) (fun m3 hm3 => ?_)
  refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  refine Or.inr (Assn.holdsV_ex.mpr ⟨cap', Assn.holdsV_ex.mpr ⟨fv', ?_⟩⟩)
  exact Assn.holds_pure_intro ⟨⟨⟨ok'.mal, ok'.cal, by omega, hle, ok'.top, ok'.fp, ok'.pvh⟩,
    hlx, hfv⟩, _, _, _, rfl⟩ (Assn.holds_congr rfl rfl hm3)

end InitECandidate.Solver.GuestBound
