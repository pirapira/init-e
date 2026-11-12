import InitECandidate.Solver.GuestBound.SepBridge

/-!
# `stack_push` as a framed specification

The EVM stack of a frame is a buffer of `cap` 32-byte slots in the scratch
arena. `stack_push` stores at slot `sp`; when `sp = cap` it first allocates a
buffer of twice the size (at most 1024 slots) with `scratch_alloc`, copies the
old one, and switches to it. The old buffer and the unused tail of the
allocation stay owned: they are returned when the frame's scratch mark is
released.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem Step.left {k : Key} {w : PanValue Word} {X X' Y : Assn} (h : Step k w X X') :
    Step k w (X ⋆ Y) (X' ⋆ Y) := by
  intro V V' R hu hV
  rw [Assn.sep_assoc] at hV ⊢
  exact h V V' _ hu hV

theorem Assn.holds_assoc_r {P A R : Assn} {s : St σ} (h : ((P ⋆ A) ⋆ R).holds s) :
    (P ⋆ A ⋆ R).holds s := by
  unfold Assn.holds at h ⊢
  rw [Assn.sep_assoc] at h
  exact h

theorem Assn.holds_assoc_l {P A R : Assn} {s : St σ} (h : (P ⋆ A ⋆ R).holds s) :
    ((P ⋆ A) ⋆ R).holds s := by
  unfold Assn.holds at h ⊢
  rw [Assn.sep_assoc]
  exact h

/-- `st a, v` as a last statement, into an owned cell. -/
theorem WPr.store_at (hE : GuestEnv E) {a val : Exp Word} {addr w : Word}
    {A A' R : Assn} (h : (A ⋆ R).holds s)
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : ∀ y, E.eval s val = some y → y = .word w)
    (hstep : Step (.mem addr) (.word w) A A')
    (hq : ∀ m, (A' ⋆ R).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      Q (.normal s.locals s.globals m s.ffi)) :
    WPr E s (.store a val) Q := by
  intro r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  rcases store_word_inv hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · exact Or.inl herr
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  have := hv y hy
  subst this
  have hm' := hm w rfl
  subst hm'
  exact Or.inr (hq _ (hstep _ _ _ (upd_setCell s addr' w s.locals s.ffi) h))

/-- `x = e` as a last statement, for a word-valued local `x`. -/
theorem WPr.assign_local {x : VarName} {e : Exp Word} {old w : Word}
    (hx : s.locals x = some (.word old)) (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : Q (.normal (updatePanValueMap s.locals x (.word w)) s.globals s.memory s.ffi)) :
    WPr E s (.assign .local x e) Q := by
  intro r hr
  rw [runs_assign_local] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl rfl
  | some y =>
    have := he y hv
    subst this
    rw [hv] at hr
    simp only [panValueAssignmentValid, hx, shape_word, shape_matches_self, if_true] at hr
    subst hr
    exact Or.inr h

/-- Evaluate an expression of locals, constants and `*`. -/
macro "pan" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := { decide := true }) [evalF_panOp, evalArgs_cons, evalArgs_nil, evalF_local,
    update_lookup, evalPanOp, $hs,*])

/-- The bounds the stack of a frame and the scratch arena satisfy. -/
structure StackOk (sp cap base pv fv : Word) : Prop where
  cap_pos : 0 < cap.toNat
  cap_le : cap.toNat ≤ 1024
  sp_le : sp.toNat ≤ cap.toNat
  base_al : base.toNat % 8 = 0
  base_hi : base.toNat + 32 * cap.toNat ≤ 2 ^ 62
  fp : fv.toNat ≤ pv.toNat
  pv_hi : pv.toNat ≤ 2 ^ 62

/-- The tail of `stack_push`: store the value at slot `sp` and bump `sp`. -/
theorem stack_push_tail (hE : GuestEnv E) {a : St σ} {e sp cap b hiw w0 w1 w2 w3 : Word}
    {Rest R : Assn} (hsp : a.locals "sp" = some (.word sp))
    (hv : a.locals "v" = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (h : ((Assn.Range b hiw ⋆ .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word sp ⋆
      .mem (e + 232#64) ↦ .word cap ⋆ .mem (e + 8#64) ↦ .word b ⋆ Rest) ⋆ R).holds a)
    (hlt : sp.toNat < cap.toNat) (hcap : cap.toNat ≤ 1024)
    (hhi : hiw.toNat = b.toNat + 32 * cap.toNat) (hb : b.toNat + 32 * cap.toNat ≤ 2 ^ 62) :
    WPr E a
      (.seq (.ite (.cmp .equal (.var .local "sp") (.const 1024#64))
          (.raise "EvmErr" (.const 3#64)) .skip)
        (.seq (.store (.op .add [.load .one (.op .add [.var .global "ev", .const 8#64]),
            .panOp .mul [.var .local "sp", .const 32#64]]) (.var .local "v"))
          (.seq (.store (.op .add [.var .global "ev", .const 16#64])
              (.op .add [.var .local "sp", .const 1#64]))
            (.return (.const 0#64)))))
      (fun r => ∃ l g m, r = .returned l g m a.ffi [.word 0#64] ∧
        ((Assn.Range b hiw ⋆ .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word (sp + 1#64) ⋆
          .mem (e + 232#64) ↦ .word cap ⋆ .mem (e + 8#64) ↦ .word b ⋆ Rest) ⋆ R).holds r.st) := by
  have hev : a.globals "ev" = some (.word e) := Assn.glob_at h (by look)
  refine WPr.seq (fun s' => s' = a) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .equal) (of_eval (w := sp) (by lk [hsp]))
      (of_eval (w := 1024#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · exact WPr.skip rfl
    · rename_i h0
      have hz : sp = 1024#64 := by
        by_contra hne
        exact h0 (by rw [hcv]; simp [evalPanCmp, hne])
      subst hz
      exact absurd hlt (by simp; omega)
  rintro _ rfl
  have a0 : (b + sp * 32#64).toNat = b.toNat + 32 * sp.toNat := by bv_omega
  have a1 : (b + sp * 32#64 + 8#64).toNat = b.toNat + 32 * sp.toNat + 8 := by bv_omega
  have a2 : (b + sp * 32#64 + 8#64 + 8#64).toNat = b.toNat + 32 * sp.toNat + 16 := by bv_omega
  have a3 : (b + sp * 32#64 + 8#64 + 8#64 + 8#64).toNat = b.toNat + 32 * sp.toNat + 24 := by
    bv_omega
  refine WPr.seq_store4_at hE h (addr := b + sp * 32#64)
    (eval_add2_inv hE
      (eval_load_at hE (addr := e + 8#64) (of_eval (by ev [eval_global, hev])) h (by look))
      (of_eval (w := sp * 32#64) (by pan [hsp])))
    (fun y hy => by rw [evalF_local, hv] at hy; exact (Option.some.inj hy).symm)
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega)))
    (Step.left (Step.range (by omega) (by omega))) (fun m1 h1 => ?_)
  refine WPr.seq_store_at hE h1 (addr := e + 16#64) (w := sp + 1#64)
    (of_eval (by ev [eval_global, hev])) (of_eval (by ev [hsp])) (by step) (fun m2 h2 => ?_)
  exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
    ⟨_, _, _, rfl, Assn.holds_congr rfl rfl h2⟩

/-- What `stack_push` owns: the stack buffer, the stack fields of the frame
record, the arena pointers and the free part of the scratch arena. -/
def StackW (e sp cap base pv fv : Word) : Assn :=
  Assn.Range base (base + 32#64 * cap) ⋆ .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word sp ⋆
    .mem (e + 232#64) ↦ .word cap ⋆ .mem (e + 8#64) ↦ .word base ⋆
    .glob "scratch_ptr" ↦ .word pv ⋆ .glob "frame_mem_ptr" ↦ .word fv ⋆ Assn.Range fv pv

set_option maxHeartbeats 1000000 in
/-- `stack_push(v)`: stack overflow with nothing changed; or the value stored
in place; or the buffer reallocated at `qv` with `nc` slots and the value
stored there. Traps (arena exhausted) are exempt. -/
theorem stack_push_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "stack_push" E.functions = some (parameters, body))
    (s : St σ) (e sp cap base pv fv w0 w1 w2 w3 : Word)
    (hv : s.locals "v" = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (ok : StackOk sp cap base pv fv) :
    WPFt E s body (StackW e sp cap base pv fv) (fun r => Assn.or
      (⌜sp.toNat = cap.toNat ∧ ∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 3#64)⌝ ⋆
        StackW e sp cap base pv fv)
      (Assn.or
        (⌜sp.toNat < cap.toNat ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
          StackW e (sp + 1#64) cap base pv fv)
        (Assn.ex fun qv : Word => Assn.ex fun nc : Word =>
          ⌜(StackOk (sp + 1#64) nc qv qv fv ∧ qv.toNat + 32 * nc.toNat ≤ pv.toNat ∧
              sp.toNat = cap.toNat) ∧
            ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
          (StackW e (sp + 1#64) nc qv qv fv ⋆ Assn.Range (qv + 32#64 * nc) pv ⋆
            Assn.Range base (base + 32#64 * cap))))) := by
  have hbody := (fun_of_index 454 hE.functions (by guest_decl_at 454) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  have hR0 := hR
  unfold StackW at hR
  dsimp only
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hR (by look)
  have hhi : (base + 32#64 * cap).toNat = base.toNat + 32 * cap.toNat := by
    have := ok.cap_le
    have := ok.base_hi
    bv_omega
  refine WPr.dec_ev (fun v hv' => ?_)
  have hm := eval_load_at hE (addr := e + 16#64) (v := .word sp)
    (of_eval (by ev [eval_global, hev])) hR (by look) v hv'
  subst hm
  refine WPr.dec_ev (fun v hv' => ?_)
  have hm := eval_load_at hE (addr := e + 232#64) (v := .word cap)
    (of_eval (by ev [eval_global, hev]))
    (Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "sp" (.word sp), s.globals,
      s.memory, s.ffi⟩ : St σ)) rfl rfl hR) (by look) v hv'
  subst hm
  have h2 := Assn.holds_congr (s' := (⟨updatePanValueMap
    (updatePanValueMap s.locals "sp" (.word sp)) "cap" (.word cap), s.globals, s.memory,
    s.ffi⟩ : St σ)) rfl rfl hR
  refine WPr.seq (fun s' => ∃ l g m, s' = ⟨l, g, m, s.ffi⟩ ∧ l "sp" = some (.word sp) ∧
      l "v" = some (.rStruct [.word w0, .word w1, .word w2, .word w3]) ∧
      ((sp.toNat < cap.toNat ∧ ((Assn.Range base (base + 32#64 * cap) ⋆
          .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word sp ⋆ .mem (e + 232#64) ↦ .word cap ⋆
          .mem (e + 8#64) ↦ .word base ⋆ .glob "scratch_ptr" ↦ .word pv ⋆
          .glob "frame_mem_ptr" ↦ .word fv ⋆ Assn.Range fv pv) ⋆ R).holds s') ∨
        ∃ qv nc : Word, StackOk (sp + 1#64) nc qv qv fv ∧ sp.toNat < nc.toNat ∧
          qv.toNat + 32 * nc.toNat ≤ pv.toNat ∧ sp.toNat = cap.toNat ∧
          ((Assn.Range qv (qv + 32#64 * nc) ⋆ .glob "ev" ↦ .word e ⋆
            .mem (e + 16#64) ↦ .word sp ⋆ .mem (e + 232#64) ↦ .word nc ⋆
            .mem (e + 8#64) ↦ .word qv ⋆ .glob "scratch_ptr" ↦ .word qv ⋆
            .glob "frame_mem_ptr" ↦ .word fv ⋆ Assn.Range fv qv ⋆
            Assn.Range (qv + 32#64 * nc) pv ⋆ Assn.Range base (base + 32#64 * cap)) ⋆
            R).holds s')) ?_ ?_
  · -- the growth block
    refine WPr.ite_both (fun w hw => ?_)
    have hcv := eval_cmp_inv hE (op := .notLower) (of_eval (w := sp) (by lk []))
      (of_eval (w := cap) (by lk [])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      have hlt : sp < cap := cmp_notLower_zero hcv.symm
      exact WPr.skip ⟨_, _, _, rfl, by lk [], by lk [hv],
        Or.inl ⟨BitVec.lt_def.mp hlt, h2⟩⟩
    rename_i h0
    have hge : ¬ sp < cap := cmp_notLower_ne (by rw [← hcv]; exact h0)
    have hspcap : sp.toNat = cap.toNat := by
      have := ok.sp_le
      have : ¬ sp.toNat < cap.toNat := fun h => hge (BitVec.lt_def.mpr h)
      omega
    refine WPr.seq (fun s' => s' = ⟨updatePanValueMap
        (updatePanValueMap s.locals "sp" (.word sp)) "cap" (.word cap), s.globals, s.memory,
        s.ffi⟩ ∧ cap.toNat < 1024) (WPr.ite_both (fun w2 hw2 => ?_)) ?_
    · have hcv2 := eval_cmp_inv hE (op := .notLower) (of_eval (w := cap) (by lk []))
        (of_eval (w := 1024#64) (eval_const _ _)) _ hw2
      simp only [PanValue.word.injEq] at hcv2
      split
      · rename_i h02
        rw [h02] at hcv2
        have := cmp_notLower_zero hcv2.symm
        exact WPr.skip ⟨rfl, by simpa using BitVec.lt_def.mp this⟩
      · refine WPr.raise (fun v hv' => ?_)
        rw [eval_const] at hv'
        cases hv'
        simp only [restorePanValueFfiLocal]
        exact Or.inr (Assn.holds_or_left (Assn.holds_pure_intro ⟨hspcap, _, _, _, rfl⟩
          (Assn.holds_congr rfl rfl hR0)))
    rintro _ ⟨rfl, hcaplt⟩
    refine WPr.dec_ev (fun v hv' => ?_)
    have hnc := (of_eval (w := cap * 2#64) (by pan [])) v hv'
    subst hnc
    refine WPr.seq (fun s' => ∃ l nc, s' = ⟨l, s.globals, s.memory, s.ffi⟩ ∧
        l "ncap" = some (.word nc) ∧ l "sp" = some (.word sp) ∧
        l "v" = some (.rStruct [.word w0, .word w1, .word w2, .word w3]) ∧
        cap.toNat < nc.toNat ∧ nc.toNat ≤ 1024) (WPr.ite_both (fun w3' hw3 => ?_)) ?_
    · have hcv3 := eval_cmp_inv hE (op := .lower) (of_eval (w := 1024#64) (eval_const _ _))
        (of_eval (w := cap * 2#64) (by lk [])) _ hw3
      simp only [PanValue.word.injEq] at hcv3
      have hcp := ok.cap_pos
      split
      · rename_i h03
        rw [h03] at hcv3
        have hnl := lower_zero hcv3.symm
        refine WPr.skip ⟨_, cap * 2#64, rfl, by lk [], by lk [], by lk [hv], ?_, ?_⟩
        · bv_omega
        · have : ¬ (1024#64).toNat < (cap * 2#64).toNat := fun h => hnl (BitVec.lt_def.mpr h)
          simpa using this
      · refine WPr.assign_local (old := cap * 2#64) (w := 1024#64) (by lk [])
          (of_eval (eval_const _ _)) ⟨_, 1024#64, rfl, by lk [], by lk [], by lk [hv], ?_, ?_⟩
        · simpa using hcaplt
        · simp
    rintro _ ⟨l, nc, rfl, hlnc, hlsp, hlv, hc1, hc2⟩
    have hW := Assn.holds_congr (s' := (⟨l, s.globals, s.memory, s.ffi⟩ : St σ)) rfl rfl hR
    have hA : (ArenaPtrs pv fv ⋆ (Assn.Range base (base + 32#64 * cap) ⋆
        .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word sp ⋆ .mem (e + 232#64) ↦ .word cap ⋆
        .mem (e + 8#64) ↦ .word base ⋆ Assn.Range fv pv) ⋆ R).holds
        (⟨l, s.globals, s.memory, s.ffi⟩ : St σ) :=
      Assn.holds_perm hW (by unfold ArenaPtrs; ac_rfl)
    refine WPr.decCall_framedT hA (scratch_alloc_hc hE (nv := nc * 32#64) (by pan [hlnc]) pv fv
      ok.fp) ?_ ?_ ?_
    · intro r hr
      cases r <;> first
        | exact hr.elim
        | (simp only [restorePanValueFfiLocal]; exact Or.inl hr)
    · intro l' g m ffi v h
      obtain ⟨qv, h⟩ := Assn.holdsV_ex.mp h
      obtain ⟨⟨⟨hq1, hq2, hq3⟩, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
      injection hC with _ _ _ hf hvv
      subst hf
      simp only [List.cons.injEq, and_true] at hvv
      subst hvv
      have hpv := ok.pv_hi
      have hn32 : (nc * 32#64).toNat = 32 * nc.toNat := by bv_omega
      have hhi2 : (qv + 32#64 * nc).toNat = qv.toNat + 32 * nc.toNat := by bv_omega
      have e1 := Assn.range_split (a := fv) (q := qv) (b := pv) hq1 (by omega)
      have e2 := Assn.range_split (a := qv) (q := qv + 32#64 * nc) (b := pv) (by omega)
        (by omega)
      have hk2 : ((Assn.Range qv (qv + 32#64 * nc) ⋆ .glob "ev" ↦ .word e ⋆
          .mem (e + 16#64) ↦ .word sp ⋆ .mem (e + 232#64) ↦ .word cap ⋆
          .mem (e + 8#64) ↦ .word base ⋆ .glob "scratch_ptr" ↦ .word qv ⋆
          .glob "frame_mem_ptr" ↦ .word fv ⋆ Assn.Range fv qv ⋆
          Assn.Range (qv + 32#64 * nc) pv ⋆ Assn.Range base (base + 32#64 * cap)) ⋆ R).holds
          (⟨updatePanValueMap l "ns" (.word qv), g, m, s.ffi⟩ : St σ) :=
        Assn.holds_perm hk (by unfold ArenaPtrs; rw [e1, e2]; ac_rfl)
      have hevX : g "ev" = some (.word e) := Assn.glob_at hk2 (by look)
      have hdj : (qv + 32#64 * nc).toNat ≤ base.toNat ∨
          (base + 32#64 * cap).toNat ≤ qv.toNat :=
        Assn.range_disjoint (R := (.glob "ev" ↦ .word e ⋆
          .mem (e + 16#64) ↦ .word sp ⋆ .mem (e + 232#64) ↦ .word cap ⋆
          .mem (e + 8#64) ↦ .word base ⋆ .glob "scratch_ptr" ↦ .word qv ⋆
          .glob "frame_mem_ptr" ↦ .word fv ⋆ Assn.Range fv qv ⋆
          Assn.Range (qv + 32#64 * nc) pv) ⋆ R) (Assn.holds_perm hk2 (by ac_rfl))
          (by have := ok.cap_pos; omega) (by have := ok.cap_pos; omega)
      have hbh := ok.base_hi
      have hsp32 : (sp * 32#64).toNat = 32 * sp.toNat := by bv_omega
      refine WPr.seq_memcpy_range hE (dst := qv) (src := base) (nW := sp * 32#64)
        (hi := qv + 32#64 * nc) (of_eval (by lk []))
        (eval_load_at hE (addr := e + 8#64) (of_eval (by ev [eval_global, hevX])) hk2 (by look))
        (of_eval (by pan [hlsp])) ⟨by omega, by omega, by omega, by omega⟩ hq3 (by omega)
        (Assn.holds_assoc_r hk2) ?_ (fun m1 hm1 => ?_)
      · intro r hr
        cases r <;> first
          | exact hr.elim
          | (simp only [restorePanValueFfiLocal]; exact Or.inl hr)
      have hm1' := Assn.holds_assoc_l hm1
      refine WPr.seq_store_at hE hm1' (addr := e + 8#64) (w := qv)
        (of_eval (by ev [eval_global, hevX])) (of_eval (by lk [])) (by step) (fun m2 hm2 => ?_)
      refine WPr.store_at hE hm2 (addr := e + 232#64) (w := nc)
        (of_eval (by ev [eval_global, hevX])) (of_eval (by lk [hlnc])) (by step)
        (fun m3 hm3 => ?_)
      simp only [restorePanValueFfiLocal]
      refine ⟨_, _, _, rfl, ?_, ?_, Or.inr ⟨qv, nc, ⟨by omega, hc2, ?_, hq3, by omega, hq1,
        by omega⟩, by omega, by omega, hspcap, Assn.holds_congr rfl rfl hm3⟩⟩
      · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hlsp]
      · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hlv]
      · have : (sp + 1#64).toNat = sp.toNat + 1 := by bv_omega
        omega
    · intro l' g m ffi exc v hne h
      obtain ⟨qv, h⟩ := Assn.holdsV_ex.mp h
      obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
  · -- the store
    rintro _ ⟨l, g, m, rfl, hlsp, hlv, ⟨hlt, hW⟩ | ⟨qv, nc, okn, hlt, hle, hsc, hG⟩⟩
    · refine WPr.conseq (stack_push_tail hE hlsp hlv hW hlt ok.cap_le hhi ok.base_hi) ?_
      rintro r ⟨l', g', m', rfl, hh⟩
      simp only [restorePanValueFfiLocal]
      exact Or.inr (Assn.holds_or_right (Assn.holds_or_left
        (Assn.holds_pure_intro ⟨hlt, _, _, _, rfl⟩
          (Assn.holds_perm (Assn.holds_congr rfl rfl hh) (by unfold StackW; rfl)))))
    · have hhi2 : (qv + 32#64 * nc).toNat = qv.toNat + 32 * nc.toNat := by
        have := okn.cap_le
        have := okn.base_hi
        bv_omega
      refine WPr.conseq (stack_push_tail hE hlsp hlv hG hlt okn.cap_le hhi2 okn.base_hi) ?_
      rintro r ⟨l', g', m', rfl, hh⟩
      simp only [restorePanValueFfiLocal]
      refine Or.inr (Assn.holds_or_right (Assn.holds_or_right
        (Assn.holdsV_ex.mpr ⟨qv, Assn.holdsV_ex.mpr ⟨nc, ?_⟩⟩)))
      exact Assn.holds_pure_intro ⟨⟨okn, hle, hsc⟩, _, _, _, rfl⟩
        (Assn.holds_perm (Assn.holds_congr rfl rfl hh) (by unfold StackW; ac_rfl))

end InitECandidate.Solver.GuestBound
