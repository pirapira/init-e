import InitECandidate.Solver.GuestBound.SepStack
import InitECandidate.Solver.GuestBound.ParseSteps

/-!
# Binary stack handlers as one framed specification

`binop_framed` covers every handler of the shape
`x = pop; y = pop; charge_gas(G); r = f(x, y); push(r); pc_add(1); return 0`
for a callee `f` that changes nothing and never raises. Either it raises
`EvmErr` with the gas fields untouched and the stack pointer not above where it
was, or it returns with `G` gas charged, one slot fewer, and the program
counter advanced.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `WPr.decCall_spec`, with the shape check on the bound value. -/
theorem WPr.decCall_specS {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} (C : Result σ → Prop)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody C)
    (hret : ∀ l g m ffi v, C (.returned l g m ffi [v]) →
      panShapeMatches (panValueShape E.structs v) sh = true →
      WPr E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r')))
    (hraise : ∀ l g m ffi exc v, C (.raised l g m ffi exc v) →
      Q (.raised (fun _ => none) g m ffi exc v))
    (hffi : ∀ l g m ffi ev, C (.finalFfi l g m ffi ev) → Q (.finalFfi (fun _ => none) g m ffi ev)) :
    WPr E s (.decCall x sh f args body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl herr
  have hcal := hc parameters cbody values cl hlookup hvalues hbind rb hcallee
  cases rb with
  | returned lr g m ffi vs =>
    cases vs with
    | nil => exact hout.elim
    | cons v rest =>
      cases rest with
      | cons v' rest' => exact hout.elim
      | nil =>
        obtain ⟨r', hsh, hrun', rfl⟩ := hout
        rcases hcal with he | hC
        · cases he
        rcases hret lr g m ffi v hC hsh r' hrun' with he | hq
        · exact Or.inl (isError_restore he)
        · exact Or.inr hq
  | raised lr g m ffi ex v =>
    simp only at hout
    subst hout
    rcases hcal with he | hC
    · cases he
    · exact Or.inr (hraise lr g m ffi ex v hC)
  | finalFfi lr g m ffi ev =>
    simp only at hout
    subst hout
    rcases hcal with he | hC
    · cases he
    · exact Or.inr (hffi lr g m ffi ev hC)
  | _ => exact hout.elim

/-- `var x = f(args); rest` for a callee that changes nothing and never raises. -/
theorem WPr.decCall_quiet {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} (hq : FunKeeps (quietKeeper E) f)
    (hr : FunRaises E (fun _ => false) f) (htrap : ∀ r, Trap r → Q r)
    (hret : ∀ v, panShapeMatches (panValueShape E.structs v) sh = true →
      WPr E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x sh f args body) Q := by
  refine WPr.decCall_specS (fun rb => RaiseIn (fun _ => false) rb ∧
    rb.st.globals = s.globals ∧ rb.st.memory = s.memory ∧ rb.st.ffi = s.ffi) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk _ _ r hr'
    rcases hr parameters cbody hlk _ r hr' with he | h
    · exact Or.inl he
    · obtain ⟨fuel, n, hrun⟩ := hr'
      exact Or.inr ⟨h, hq parameters cbody hlk fuel ⟨cl, s.globals, s.memory, s.ffi⟩ r n hrun⟩
  · rintro l g m ffi v ⟨-, hg, hm, hf⟩ hsh
    dsimp only [PanValueFfiControlResult.st] at hg hm hf
    subst hg hm hf
    exact hret v hsh
  · rintro l g m ffi exc v ⟨h, -⟩
    cases h
  · intro l g m ffi ev _
    exact htrap _ trivial

/-- The postcondition of `stack_push`. -/
def StackPushPost (ffi : FfiState σ) (e sp cap base pv fv : Word) (r : Result σ) : Assn :=
  Assn.or
    (⌜sp.toNat = cap.toNat ∧ ∃ l g m, r = .raised l g m ffi "EvmErr" (.word 3#64)⌝ ⋆
      StackW e sp cap base pv fv)
    (Assn.or
      (⌜sp.toNat < cap.toNat ∧ ∃ l g m, r = .returned l g m ffi [.word 0#64]⌝ ⋆
        StackW e (sp + 1#64) cap base pv fv)
      (Assn.ex fun qv : Word => Assn.ex fun nc : Word =>
        ⌜(StackOk (sp + 1#64) nc qv qv fv ∧ qv.toNat + 32 * nc.toNat ≤ pv.toNat ∧
            sp.toNat = cap.toNat) ∧
          ∃ l g m, r = .returned l g m ffi [.word 0#64]⌝ ⋆
        (StackW e (sp + 1#64) nc qv qv fv ⋆ Assn.Range (qv + 32#64 * nc) pv ⋆
          Assn.Range base (base + 32#64 * cap))))

/-- `stack_push(e)` at a call site where the argument is a four-word value. -/
theorem stack_push_hc (hE : GuestEnv E) {args : List (Exp Word)} {w0 w1 w2 w3 : Word}
    (hargs : E.evalArgs s args = some [.rStruct [.word w0, .word w1, .word w2, .word w3]])
    (e sp cap base pv fv : Word) (ok : StackOk sp cap base pv fv) :
    ∀ parameters cbody values cl,
      lookupPanFunction "stack_push" E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (StackW e sp cap base pv fv)
        (StackPushPost s.ffi e sp cap base pv fv) := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 454 hE.functions (by guest_decl_at 454) (by decide +kernel)
    hlk).2
  rw [hargs] at hvalues
  cases hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact stack_push_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e sp cap
    base pv fv w0 w1 w2 w3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) ok

/-- What a stack handler owns: the stack, the gas counters and the program counter. -/
def OpW (e sp cap base pv fv gl used pc : Word) : Assn :=
  StackW e sp cap base pv fv ⋆ .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 184#64) ↦ .word used ⋆
    .mem e ↦ .word pc

/-- `OpW` without the stack pointer. -/
def OpNoSp (e cap base pv fv gl used pc : Word) : Assn :=
  Assn.Range base (base + 32#64 * cap) ⋆ .mem (e + 232#64) ↦ .word cap ⋆
    .mem (e + 8#64) ↦ .word base ⋆ .glob "scratch_ptr" ↦ .word pv ⋆
    .glob "frame_mem_ptr" ↦ .word fv ⋆ Assn.Range fv pv ⋆ .mem (e + 64#64) ↦ .word gl ⋆
    .mem (e + 184#64) ↦ .word used ⋆ .mem e ↦ .word pc

/-- `OpW` without the gas counters. -/
def OpNoGas (e sp cap base pv fv pc : Word) : Assn :=
  Assn.Range base (base + 32#64 * cap) ⋆ .mem (e + 16#64) ↦ .word sp ⋆
    .mem (e + 232#64) ↦ .word cap ⋆ .mem (e + 8#64) ↦ .word base ⋆
    .glob "scratch_ptr" ↦ .word pv ⋆ .glob "frame_mem_ptr" ↦ .word fv ⋆ Assn.Range fv pv ⋆
    .mem e ↦ .word pc

/-- `OpW` without the program counter. -/
def OpNoPc (e sp cap base pv fv gl used : Word) : Assn :=
  Assn.Range base (base + 32#64 * cap) ⋆ .mem (e + 16#64) ↦ .word sp ⋆
    .mem (e + 232#64) ↦ .word cap ⋆ .mem (e + 8#64) ↦ .word base ⋆
    .glob "scratch_ptr" ↦ .word pv ⋆ .glob "frame_mem_ptr" ↦ .word fv ⋆ Assn.Range fv pv ⋆
    .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 184#64) ↦ .word used

/-- `OpW` without the stack. -/
def OpNoStack (e gl used pc : Word) : Assn :=
  .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 184#64) ↦ .word used ⋆ .mem e ↦ .word pc

theorem OpW_sp (e sp cap base pv fv gl used pc : Word) :
    OpW e sp cap base pv fv gl used pc = (SpCell e sp ⋆ OpNoSp e cap base pv fv gl used pc) := by
  unfold OpW StackW SpCell OpNoSp; ac_rfl

theorem OpW_gas (e sp cap base pv fv gl used pc : Word) :
    OpW e sp cap base pv fv gl used pc = (GasCells e gl used ⋆ OpNoGas e sp cap base pv fv pc) := by
  unfold OpW StackW GasCells OpNoGas; ac_rfl

theorem OpW_pc (e sp cap base pv fv gl used pc : Word) :
    OpW e sp cap base pv fv gl used pc = (PcCell e pc ⋆ OpNoPc e sp cap base pv fv gl used) := by
  unfold OpW StackW PcCell OpNoPc; ac_rfl

theorem OpW_stack (e sp cap base pv fv gl used pc : Word) :
    OpW e sp cap base pv fv gl used pc =
      (StackW e sp cap base pv fv ⋆ OpNoStack e gl used pc) := rfl

/-- Put a part of what is owned first, as a callee's precondition. -/
theorem Assn.holds_focus {A P F R : Assn} {s : St σ} (e : A = (P ⋆ F)) (h : (A ⋆ R).holds s) :
    (P ⋆ F ⋆ R).holds s := by
  subst e
  exact Assn.holds_assoc_r h

/-- Back from a callee's postcondition to the whole. -/
theorem Assn.holds_unfocus {A P F R : Assn} {s : St σ} (e : A = (P ⋆ F))
    (h : (P ⋆ F ⋆ R).holds s) : (A ⋆ R).holds s := by
  subst e
  exact Assn.holds_assoc_l h

/-- Close the trap obligation of a call rule. -/
macro "trap_tac" : tactic => `(tactic| (
  intro r hr
  cases r <;> first
    | exact hr.elim
    | exact Or.inl hr
    | (simp only [restorePanValueFfiLocal]; exact Or.inl hr)))

/-- The body shared by the binary stack handlers. -/
def binopBody (f : FunName) (G : Word) : Prog Word :=
  .decCall "x" (.comb [.one, .one, .one, .one]) "stack_pop" []
    (.decCall "y" (.comb [.one, .one, .one, .one]) "stack_pop" []
      (.seq (.call (some (none, none)) "charge_gas" [.const G])
        (.decCall "r" (.comb [.one, .one, .one, .one]) f [.var .local "x", .var .local "y"]
          (.seq (.call (some (none, none)) "stack_push" [.var .local "r"])
            (.seq (.call (some (none, none)) "pc_add" [.const 1#64])
              (.return (.const 0#64)))))))

/-- What a binary stack handler leaves. -/
def BinopPost (ffi : FfiState σ) (e sp cap base pv fv gl used pc G : Word) (r : Result σ) :
    Assn :=
  Assn.or
    (Assn.ex fun sp' : Word =>
      ⌜sp'.toNat ≤ sp.toNat ∧ ∃ l g m code, r = .raised l g m ffi "EvmErr" (.word code)⌝ ⋆
        OpW e sp' cap base pv fv gl used pc)
    (⌜(2 ≤ sp.toNat ∧ ¬ gl < G) ∧ ∃ l g m, r = .returned l g m ffi [.word 0#64]⌝ ⋆
      OpW e (sp - 1#64) cap base pv fv (gl - G) (used + G) (pc + 1#64))

set_option maxHeartbeats 1000000 in
/-- A binary stack handler with a callee that changes nothing and never raises. -/
theorem binop_framed (hE : GuestEnv E) {f : FunName} (G : Word)
    (hq : FunKeeps (quietKeeper E) f) (hr : FunRaises E (fun _ => false) f)
    (s : St σ) (e sp cap base pv fv gl used pc : Word) (ok : StackOk sp cap base pv fv) :
    WPFt E s (binopBody f G) (OpW e sp cap base pv fv gl used pc)
      (BinopPost s.ffi e sp cap base pv fv gl used pc G) := by
  intro R hR
  unfold binopBody
  -- first pop
  refine WPr.decCall_framedT (Assn.holds_focus (OpW_sp ..) hR)
    (fun p b v cl a1 a2 a3 => (stack_pop_hc hE e sp p b v cl a1 a2 a3).toT) (by trap_tac) ?_ ?_
  rotate_left
  · intro l g m ffi exc v _ h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      exact Or.inr (Assn.holds_or_left (Assn.holdsV_ex.mpr ⟨sp,
        Assn.holds_pure_intro ⟨Nat.le_refl _, _, _, _, _, rfl⟩
          (Assn.holds_unfocus (OpW_sp ..) (Assn.holds_congr rfl rfl hk))⟩))
    · obtain ⟨⟨-, _, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
  intro l g m ffi vx h
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  obtain ⟨⟨hne1, _, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
  injection hC with _ _ _ hf _
  subst hf
  have hO1 := Assn.holds_unfocus (OpW_sp e (sp - 1#64) cap base pv fv gl used pc) hk
  have hs1 : (sp - 1#64).toNat = sp.toNat - 1 ∧ 1 ≤ sp.toNat := by
    have : sp.toNat ≠ 0 := fun h0 => hne1 (by bv_omega)
    constructor <;> bv_omega
  -- second pop
  refine WPr.decCall_framedT (Assn.holds_focus (OpW_sp ..) hO1)
    (fun p b v cl a1 a2 a3 => (stack_pop_hc hE e (sp - 1#64) p b v cl a1 a2 a3).toT)
    (by trap_tac) ?_ ?_
  rotate_left
  · intro l2 g2 m2 ffi2 exc v _ h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      simp only [restorePanValueFfiLocal]
      exact Or.inr (Assn.holds_or_left (Assn.holdsV_ex.mpr ⟨sp - 1#64,
        Assn.holds_pure_intro ⟨by omega, _, _, _, _, rfl⟩
          (Assn.holds_unfocus (OpW_sp ..) (Assn.holds_congr rfl rfl hk))⟩))
    · obtain ⟨⟨-, _, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
  intro l2 g2 m2 ffi2 vy h
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  obtain ⟨⟨hne2, _, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
  injection hC with _ _ _ hf _
  subst hf
  have hO2 := Assn.holds_unfocus (OpW_sp e (sp - 1#64 - 1#64) cap base pv fv gl used pc) hk
  have hs2 : (sp - 1#64 - 1#64).toNat = sp.toNat - 2 ∧ 2 ≤ sp.toNat := by
    have : (sp - 1#64).toNat ≠ 0 := fun h0 => hne2 (by bv_omega)
    constructor <;> bv_omega
  -- charge gas
  refine WPr.seq_call_framedT (Assn.holds_focus (OpW_gas ..) hO2)
    (fun p b v cl a1 a2 a3 => (charge_gas_hc hE (a := G)
      (by simp [evalArgs_cons, evalArgs_nil, eval_const]) e gl used p b v cl a1 a2 a3).toT)
    (by trap_tac) ?_ ?_
  rotate_left
  · intro l3 g3 m3 ffi3 exc v _ h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      simp only [restorePanValueFfiLocal]
      exact Or.inr (Assn.holds_or_left (Assn.holdsV_ex.mpr ⟨sp - 1#64 - 1#64,
        Assn.holds_pure_intro ⟨by omega, _, _, _, _, rfl⟩
          (Assn.holds_unfocus (OpW_gas ..) (Assn.holds_congr rfl rfl hk))⟩))
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
  intro l3 g3 m3 ffi3 vs3 h
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  obtain ⟨⟨hge, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
  injection hC with _ _ _ hf _
  subst hf
  have hO3 := Assn.holds_unfocus
    (OpW_gas e (sp - 1#64 - 1#64) cap base pv fv (gl - G) (used + G) pc) hk
  -- the pure callee
  refine WPr.decCall_quiet hq hr (by trap_tac) (fun vr hsh => ?_)
  obtain ⟨w0, w1, w2, w3, rfl⟩ := struct4_of_shape hsh
  have hO4 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap
    (updatePanValueMap s.locals "x" vx) "y" vy) "r"
    (.rStruct [.word w0, .word w1, .word w2, .word w3]), g3, m3, s.ffi⟩ : St σ)) rfl rfl hO3
  have ok2 : StackOk (sp - 1#64 - 1#64) cap base pv fv :=
    ⟨ok.cap_pos, ok.cap_le, by have := ok.sp_le; omega, ok.base_al, ok.base_hi, ok.fp, ok.pv_hi⟩
  have hsplt : (sp - 1#64 - 1#64).toNat < cap.toNat := by have := ok.sp_le; omega
  -- push
  refine WPr.seq_call_framedT (Assn.holds_focus (OpW_stack ..) hO4)
    (stack_push_hc hE (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3)
      (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil,
      evalF_local, update_lookup]) e (sp - 1#64 - 1#64) cap base pv fv ok2) (by trap_tac) ?_ ?_
  rotate_left
  · intro l5 g5 m5 ffi5 exc v _ h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨hcontra, -⟩, -⟩ := Assn.holds_pure_elim h
      omega
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    · obtain ⟨qv, h⟩ := Assn.holdsV_ex.mp h
      obtain ⟨nc, h⟩ := Assn.holdsV_ex.mp h
      obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
  intro l5 g5 m5 ffi5 vs5 h
  rcases Assn.holds_or_elim h with h | h
  · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  rcases Assn.holds_or_elim h with h | h
  rotate_left
  · obtain ⟨qv, h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨nc, h⟩ := Assn.holdsV_ex.mp h
    obtain ⟨⟨⟨-, -, hcontra⟩, -⟩, -⟩ := Assn.holds_pure_elim h
    omega
  obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
  injection hC with _ _ _ hf _
  subst hf
  have hsp1 : sp - 1#64 - 1#64 + 1#64 = sp - 1#64 := by bv_omega
  rw [hsp1] at hk
  have hO5 := Assn.holds_unfocus
    (OpW_stack e (sp - 1#64) cap base pv fv (gl - G) (used + G) pc) hk
  -- advance the program counter
  refine WPr.seq_call_framedT (Assn.holds_focus (OpW_pc ..) hO5)
    (fun p b v cl a1 a2 a3 => (pc_add_hc hE (n := 1#64)
      (by simp [evalArgs_cons, evalArgs_nil, eval_const]) e pc p b v cl a1 a2 a3).toT)
    (by trap_tac) ?_ ?_
  rotate_left
  · intro l6 g6 m6 ffi6 exc v _ h
    obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
    cases hC
  intro l6 g6 m6 ffi6 vs6 h
  obtain ⟨⟨_, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
  injection hC with _ _ _ hf _
  subst hf
  refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  exact Or.inr (Assn.holds_or_right (Assn.holds_pure_intro ⟨⟨hs2.2, hge⟩, _, _, _, rfl⟩
    (Assn.holds_unfocus (OpW_pc ..) (Assn.holds_congr rfl rfl hk))))

end InitECandidate.Solver.GuestBound
