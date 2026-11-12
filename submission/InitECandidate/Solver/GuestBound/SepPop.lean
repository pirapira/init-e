import InitECandidate.Solver.GuestBound.SepCall

/-!
# `stack_pop` and `op_pop` as framed specifications

Also the call-site forms `charge_gas_hc`, `pc_add_hc`, `stack_pop_hc`: the
callee hypothesis that `WPr.seq_call_framed` / `WPr.decCall_framed` ask for,
from the evaluated arguments, so that handlers do not repeat the binding of
parameters.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `return e` for whatever `e` evaluates to. -/
theorem WPr.ret_any {e : Exp Word}
    (h : ∀ v, E.eval s e = some v → Q (.returned (fun _ => none) s.globals s.memory s.ffi [v])) :
    WPr E s (.return e) Q := by
  intro r hr
  rw [runs_return] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl rfl
  | some y =>
    rw [hv] at hr
    simp only at hr
    split at hr
    · subst hr; exact Or.inr (h y hv)
    · subst hr; exact Or.inl rfl

/-- `x = e; rest` for a word-valued local `x`. -/
theorem WPr.seq_assign_local {x : VarName} {e : Exp Word} {q : Prog Word} {old w : Word}
    (hx : s.locals x = some (.word old)) (he : ∀ y, E.eval s e = some y → y = .word w)
    (h : WPr E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩ q Q) :
    WPr E s (.seq (.assign .local x e) q) Q := by
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory,
    s.ffi⟩) ?_ (by rintro _ rfl; exact h)
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
    exact Or.inr rfl

/-- `var x = f(args); rest` for a callee with a framed specification. -/
theorem WPr.decCall_framed {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} {P F : Assn} {Qc : Result σ → Assn} (hpre : (P ⋆ F).holds s)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody P Qc)
    (hret : ∀ l g m ffi v, (Qc (.returned l g m ffi [v]) ⋆ F).holds
        (⟨updatePanValueMap s.locals x v, g, m, ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r')))
    (hraise : ∀ l g m ffi exc v, (Qc (.raised l g m ffi exc v) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.raised (fun _ => none) g m ffi exc v))
    (hffi : ∀ l g m ffi ev, (Qc (.finalFfi l g m ffi ev) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.finalFfi (fun _ => none) g m ffi ev)) :
    WPr E s (.decCall x sh f args body) Q := by
  refine WPr.decCall_spec (fun rb => (Qc rb ⋆ F).holds rb.st)
    (fun parameters cbody values cl hlk hvalues hbind =>
      hc parameters cbody values cl hlk hvalues hbind F (Assn.holds_congr rfl rfl hpre))
    (fun l g m ffi v hC => hret l g m ffi v (Assn.holds_congr rfl rfl hC))
    (fun l g m ffi exc v hC => hraise l g m ffi exc v (Assn.holds_congr rfl rfl hC))
    (fun l g m ffi ev hC => hffi l g m ffi ev (Assn.holds_congr rfl rfl hC))

/-- `charge_gas(e)` at a call site where the argument evaluates to `a`. -/
theorem charge_gas_hc (hE : GuestEnv E) {args : List (Exp Word)} {a : Word}
    (hargs : E.evalArgs s args = some [.word a]) (e gl used : Word) :
    ∀ parameters cbody values cl,
      lookupPanFunction "charge_gas" E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (GasCells e gl used) (fun r => Assn.or
        (⌜gl < a ∧ ∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 4#64)⌝ ⋆ GasCells e gl used)
        (⌜¬ gl < a ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
          GasCells e (gl - a) (used + a))) := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 448 hE.functions (by guest_decl_at 448) (by decide +kernel)
    hlk).2
  rw [hargs] at hvalues
  cases hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact charge_gas_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e a gl
    used (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])

/-- `pc_add(e)` at a call site where the argument evaluates to `n`. -/
theorem pc_add_hc (hE : GuestEnv E) {args : List (Exp Word)} {n : Word}
    (hargs : E.evalArgs s args = some [.word n]) (e pc : Word) :
    ∀ parameters cbody values cl,
      lookupPanFunction "pc_add" E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (PcCell e pc)
        (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆ PcCell e (pc + n)) := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 468 hE.functions (by guest_decl_at 468) (by decide +kernel)
    hlk).2
  rw [hargs] at hvalues
  cases hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact pc_add_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e pc n
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])

/-- The stack pointer (a count of 32-byte slots) of the current frame. -/
def SpCell (e sp : Word) : Assn :=
  .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word sp

/-- `stack_pop()`: raises on an empty stack with nothing changed; otherwise the
stack pointer drops by one and some value is returned. -/
theorem stack_pop_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "stack_pop" E.functions = some (parameters, body))
    (s : St σ) (e sp : Word) :
    WPFr E s body (SpCell e sp) (fun r => Assn.or
      (⌜sp = 0#64 ∧ ∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 2#64)⌝ ⋆ SpCell e sp)
      (⌜sp ≠ 0#64 ∧ ∃ l g m v, r = .returned l g m s.ffi [v]⌝ ⋆ SpCell e (sp - 1#64))) := by
  have hbody := (fun_of_index 453 hE.functions (by guest_decl_at 453) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  unfold SpCell at hR
  dsimp only
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hR (by look)
  refine WPr.dec_ev (fun v hv => ?_)
  have hm := eval_load_at hE (addr := e + 16#64) (v := .word sp)
    (of_eval (by ev [eval_global, hev])) hR (by look) v hv
  subst hm
  have h1 := Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "sp" (.word sp), s.globals,
    s.memory, s.ffi⟩ : St σ)) rfl rfl hR
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap s.locals "sp" (.word sp), s.globals,
      s.memory, s.ffi⟩ ∧ sp ≠ 0#64) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .equal) (of_eval (w := sp) (by lk []))
      (of_eval (w := 0#64) (eval_const _ _)) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      refine WPr.skip ⟨rfl, fun hz => ?_⟩
      rw [hz] at hcv
      simp [evalPanCmp] at hcv
    · rename_i h0
      have hz : sp = 0#64 := by
        by_contra hne
        exact h0 (by rw [hcv]; simp [evalPanCmp, hne])
      refine WPr.raise (fun v hv => ?_)
      rw [eval_const] at hv
      cases hv
      simp only [restorePanValueFfiLocal]
      refine Assn.holds_or_left (Assn.holds_pure_intro ⟨hz, _, _, _, rfl⟩ ?_)
      exact Assn.holds_congr rfl rfl hR
  rintro _ ⟨rfl, hne⟩
  refine WPr.seq_assign_local (old := sp) (w := sp - 1#64) (by lk []) (of_eval (by ev [])) ?_
  have h2 := Assn.holds_congr (s' := (⟨updatePanValueMap
    (updatePanValueMap s.locals "sp" (.word sp)) "sp" (.word (sp - 1#64)), s.globals,
    s.memory, s.ffi⟩ : St σ)) rfl rfl hR
  refine WPr.seq_store_at hE h2 (addr := e + 16#64) (w := sp - 1#64)
    (of_eval (by ev [eval_global, hev])) (of_eval (by lk []))
    (by step) (fun m1 h3 => ?_)
  refine WPr.ret_any (fun v _ => ?_)
  simp only [restorePanValueFfiLocal]
  refine Assn.holds_or_right (Assn.holds_pure_intro ⟨hne, _, _, _, _, rfl⟩ ?_)
  exact Assn.holds_congr rfl rfl h3

/-- `stack_pop()` at a call site. -/
theorem stack_pop_hc (hE : GuestEnv E) (e sp : Word) :
    ∀ parameters cbody values cl,
      lookupPanFunction "stack_pop" E.functions = some (parameters, cbody) →
      E.evalArgs s [] = some values →
      bindPanValueParameters parameters values = some cl →
      WPFr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (SpCell e sp) (fun r => Assn.or
        (⌜sp = 0#64 ∧ ∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 2#64)⌝ ⋆ SpCell e sp)
        (⌜sp ≠ 0#64 ∧ ∃ l g m v, r = .returned l g m s.ffi [v]⌝ ⋆ SpCell e (sp - 1#64))) :=
  fun parameters cbody _ cl hlk _ _ =>
    stack_pop_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e sp

/-- What a simple handler owns: stack pointer, gas left, gas used, program counter. -/
def OpCells (e sp gl used pc : Word) : Assn :=
  .glob "ev" ↦ .word e ⋆ .mem (e + 16#64) ↦ .word sp ⋆ .mem (e + 64#64) ↦ .word gl ⋆
    .mem (e + 184#64) ↦ .word used ⋆ .mem e ↦ .word pc

/-- `op_pop`: stack underflow with nothing changed; or out of gas after the
pop; or one slot popped, two units of gas charged, program counter advanced. -/
theorem op_pop_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_pop" E.functions = some (parameters, body))
    (s : St σ) (e sp gl used pc : Word) :
    WPFr E s body (OpCells e sp gl used pc) (fun r => Assn.or
      (⌜sp = 0#64 ∧ ∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 2#64)⌝ ⋆
        OpCells e sp gl used pc)
      (Assn.or
        (⌜(sp ≠ 0#64 ∧ gl < 2#64) ∧ ∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 4#64)⌝ ⋆
          OpCells e (sp - 1#64) gl used pc)
        (⌜(sp ≠ 0#64 ∧ ¬ gl < 2#64) ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
          OpCells e (sp - 1#64) (gl - 2#64) (used + 2#64) (pc + 1#64)))) := by
  have hbody := (fun_of_index 513 hE.functions (by guest_decl_at 513) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  dsimp only
  have hR1 : (SpCell e sp ⋆ (.mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 184#64) ↦ .word used ⋆
      .mem e ↦ .word pc) ⋆ R).holds s :=
    Assn.holds_perm hR (by unfold OpCells SpCell; ac_rfl)
  refine WPr.decCall_framed hR1 (stack_pop_hc hE e sp) ?_ ?_ ?_
  · intro l g m ffi v h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    obtain ⟨⟨hne, _, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    have hk1 : (GasCells e gl used ⋆ (.mem (e + 16#64) ↦ .word (sp - 1#64) ⋆
        .mem e ↦ .word pc) ⋆ R).holds
        (⟨updatePanValueMap s.locals "x" v, g, m, s.ffi⟩ : St σ) :=
      Assn.holds_perm hk (by unfold GasCells SpCell; ac_rfl)
    refine WPr.seq_call_framed hk1 (charge_gas_hc hE (a := 2#64)
      (by simp [evalArgs_cons, evalArgs_nil, eval_const]) e gl used) ?_ ?_ ?_
    · intro l1 g1 m1 ffi1 vs1 h1
      rcases Assn.holds_or_elim h1 with h1 | h1
      · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h1
        cases hC
      obtain ⟨⟨hge, _, _, _, hC⟩, hk2⟩ := Assn.holds_pure_elim h1
      injection hC with _ _ _ hf _
      subst hf
      have hk3 : (PcCell e pc ⋆ (.mem (e + 16#64) ↦ .word (sp - 1#64) ⋆
          .mem (e + 64#64) ↦ .word (gl - 2#64) ⋆ .mem (e + 184#64) ↦ .word (used + 2#64)) ⋆
          R).holds (⟨updatePanValueMap s.locals "x" v, g1, m1, s.ffi⟩ : St σ) :=
        Assn.holds_perm hk2 (by unfold GasCells PcCell; ac_rfl)
      refine WPr.seq_call_framed hk3 (pc_add_hc hE (n := 1#64)
        (by simp [evalArgs_cons, evalArgs_nil, eval_const]) e pc) ?_ ?_ ?_
      · intro l2 g2 m2 ffi2 vs2 h2
        obtain ⟨⟨_, _, _, hC⟩, hk4⟩ := Assn.holds_pure_elim h2
        injection hC with _ _ _ hf _
        subst hf
        refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
        simp only [restorePanValueFfiLocal]
        refine Assn.holds_or_right (Assn.holds_or_right
          (Assn.holds_pure_intro ⟨⟨hne, hge⟩, _, _, _, rfl⟩ ?_))
        exact Assn.holds_perm (Assn.holds_congr rfl rfl hk4)
          (by unfold OpCells PcCell; ac_rfl)
      · intro l2 g2 m2 ffi2 exc v2 h2
        obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h2
        cases hC
      · intro l2 g2 m2 ffi2 ev h2
        obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h2
        cases hC
    · intro l1 g1 m1 ffi1 exc v1 h1
      rcases Assn.holds_or_elim h1 with h1 | h1
      · obtain ⟨⟨hlt, _, _, _, hC⟩, hk2⟩ := Assn.holds_pure_elim h1
        injection hC with _ _ _ hf hx hv
        subst hf hx hv
        simp only [restorePanValueFfiLocal]
        refine Assn.holds_or_right (Assn.holds_or_left
          (Assn.holds_pure_intro ⟨⟨hne, hlt⟩, _, _, _, rfl⟩ ?_))
        exact Assn.holds_perm (Assn.holds_congr rfl rfl hk2)
          (by unfold OpCells GasCells; ac_rfl)
      · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h1
        cases hC
    · intro l1 g1 m1 ffi1 ev h1
      rcases Assn.holds_or_elim h1 with h1 | h1
      · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h1
        cases hC
      · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h1
        cases hC
  · intro l g m ffi exc v h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨hz, _, _, _, hC⟩, hkeep⟩ := Assn.holds_pure_elim h
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      refine Assn.holds_or_left (Assn.holds_pure_intro ⟨hz, _, _, _, rfl⟩ ?_)
      exact Assn.holds_perm (Assn.holds_congr rfl rfl hkeep)
        (by unfold OpCells SpCell; ac_rfl)
    · obtain ⟨⟨-, _, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
  · intro l g m ffi ev h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    · obtain ⟨⟨-, _, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC

end InitECandidate.Solver.GuestBound
