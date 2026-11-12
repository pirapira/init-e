import InitECandidate.Solver.GuestBound.SepFrameGas

/-!
# Calling a function with a framed specification; `op_jumpdest`

`WPr.seq_call_framed` runs `f(args); rest` where `f` has a `WPFr` specification:
the caller splits what it owns into the callee's precondition and a frame `F`,
and continues with the callee's postcondition next to the same `F`.

`op_jumpdest_framed` is the first opcode handler done this way: it either
raises out-of-gas with nothing changed, or charges one unit of gas and advances
the program counter.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem Assn.holds_or_elim {P P' R : Assn} {s : St σ} (h : (Assn.or P P' ⋆ R).holds s) :
    (P ⋆ R).holds s ∨ (P' ⋆ R).holds s := by
  obtain ⟨h0, hs, h1, h2, hd, rfl, hp | hp, hr⟩ := h
  · exact Or.inl ⟨_, hs, h1, h2, hd, rfl, hp, hr⟩
  · exact Or.inr ⟨_, hs, h1, h2, hd, rfl, hp, hr⟩

theorem Assn.holds_pure_elim {φ : Prop} {P R : Assn} {s : St σ}
    (h : ((⌜φ⌝ ⋆ P) ⋆ R).holds s) : φ ∧ (P ⋆ R).holds s := by
  unfold Assn.holds at h
  rw [Assn.sep_assoc] at h
  exact Assn.holdsV_pure.mp h

theorem Assn.holds_pure_intro {φ : Prop} {P R : Assn} {s : St σ} (hφ : φ)
    (h : (P ⋆ R).holds s) : ((⌜φ⌝ ⋆ P) ⋆ R).holds s := by
  unfold Assn.holds
  rw [Assn.sep_assoc]
  exact Assn.holdsV_pure.mpr ⟨hφ, h⟩

/-- `f(args)` with no destination, for a callee with a framed specification. -/
theorem WPr.call_framed {f : FunName} {args : List (Exp Word)} {P F : Assn}
    {Qc : Result σ → Assn} (hpre : (P ⋆ F).holds s)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody P Qc)
    (hret : ∀ l g m ffi vs, (Qc (.returned l g m ffi vs) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.normal s.locals g m ffi))
    (hraise : ∀ l g m ffi exc v, (Qc (.raised l g m ffi exc v) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.raised (fun _ => none) g m ffi exc v))
    (hffi : ∀ l g m ffi ev, (Qc (.finalFfi l g m ffi ev) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.finalFfi (fun _ => none) g m ffi ev)) :
    WPr E s (.call (some (none, none)) f args) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl herr
  have hcal := hc parameters body values cl hlookup hvalues hbind F
    (Assn.holds_congr rfl rfl hpre) rb hcallee
  cases rb with
  | returned lr g m ffi vs =>
    simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl herr
    · obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
      have : l' = s.locals := funext (fun x => hl x (by simp))
      subst this
      rcases hcal with he | hq
      · cases he
      · exact Or.inr (hret lr _ m ffi vs (Assn.holds_congr rfl rfl hq))
  | raised lr g m ffi ex v =>
    simp only [CallOutcome] at hout
    subst hout
    rcases hcal with he | hq
    · cases he
    · exact Or.inr (hraise lr g m ffi ex v (Assn.holds_congr rfl rfl hq))
  | finalFfi lr g m ffi ev =>
    simp only [CallOutcome] at hout
    subst hout
    rcases hcal with he | hq
    · cases he
    · exact Or.inr (hffi lr g m ffi ev (Assn.holds_congr rfl rfl hq))
  | _ =>
    simp only [CallOutcome] at hout
    exact Or.inl hout

/-- `f(args); rest` for a callee with a framed specification. -/
theorem WPr.seq_call_framed {f : FunName} {args : List (Exp Word)} {q : Prog Word}
    {P F : Assn} {Qc : Result σ → Assn} (hpre : (P ⋆ F).holds s)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFr E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody P Qc)
    (hret : ∀ l g m ffi vs, (Qc (.returned l g m ffi vs) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → WPr E ⟨s.locals, g, m, ffi⟩ q Q)
    (hraise : ∀ l g m ffi exc v, (Qc (.raised l g m ffi exc v) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.raised (fun _ => none) g m ffi exc v))
    (hffi : ∀ l g m ffi ev, (Qc (.finalFfi l g m ffi ev) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.finalFfi (fun _ => none) g m ffi ev)) :
    WPr E s (.seq (.call (some (none, none)) f args) q) Q := by
  refine WPr.seq (fun s' => ∃ l g m ffi vs, s' = ⟨s.locals, g, m, ffi⟩ ∧
      (Qc (.returned l g m ffi vs) ⋆ F).holds s')
    (WPr.call_framed hpre hc (fun l g m ffi vs h => ⟨l, g, m, ffi, vs, rfl, h⟩) hraise hffi) ?_
  rintro _ ⟨l, g, m, ffi, vs, rfl, h⟩
  exact hret l g m ffi vs h

/-- The program counter of the current frame. -/
def PcCell (e pc : Word) : Assn :=
  .glob "ev" ↦ .word e ⋆ .mem e ↦ .word pc

/-- `pc_add(n)` advances the program counter. -/
theorem pc_add_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "pc_add" E.functions = some (parameters, body))
    (s : St σ) (e pc n : Word) (hn : s.locals "n" = some (.word n)) :
    WPFr E s body (PcCell e pc)
      (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆ PcCell e (pc + n)) := by
  have hbody := (fun_of_index 468 hE.functions (by guest_decl_at 468) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  unfold PcCell at hR
  dsimp only
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hR (by look)
  refine WPr.seq_store_at hE hR (addr := e) (w := pc + n)
    (of_eval (by ev [eval_global, hev]))
    (eval_add2_inv hE
      (eval_load_at hE (addr := e) (of_eval (by ev [eval_global, hev])) hR (by look))
      (of_eval (by lk [hn])))
    (by step) (fun m1 h1 => ?_)
  refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  exact Assn.holds_pure_intro ⟨_, _, _, rfl⟩ (Assn.holds_congr rfl rfl h1)

/-- What `op_jumpdest` owns: gas left, gas used, program counter. -/
def JumpdestCells (e gl used pc : Word) : Assn :=
  .glob "ev" ↦ .word e ⋆ .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 184#64) ↦ .word used ⋆
    .mem e ↦ .word pc

/-- `op_jumpdest`: out of gas with nothing changed, or one unit of gas charged
and the program counter advanced by one. -/
theorem op_jumpdest_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_jumpdest" E.functions = some (parameters, body))
    (s : St σ) (e gl used pc : Word) :
    WPFr E s body (JumpdestCells e gl used pc) (fun r => Assn.or
      (⌜gl < 1#64 ∧ ∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 4#64)⌝ ⋆
        JumpdestCells e gl used pc)
      (⌜¬ gl < 1#64 ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        JumpdestCells e (gl - 1#64) (used + 1#64) (pc + 1#64))) := by
  have hbody := (fun_of_index 507 hE.functions (by guest_decl_at 507) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  dsimp only
  have hR1 : (GasCells e gl used ⋆ .mem e ↦ .word pc ⋆ R).holds s :=
    Assn.holds_perm hR (by unfold JumpdestCells GasCells; ac_rfl)
  refine WPr.seq_call_framed hR1 (Qc := fun r => Assn.or
      (⌜gl < 1#64 ∧ ∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 4#64)⌝ ⋆ GasCells e gl used)
      (⌜¬ gl < 1#64 ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        GasCells e (gl - 1#64) (used + 1#64))) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind
    have hparams := (fun_of_index 448 hE.functions (by guest_decl_at 448) (by decide +kernel)
      hlk).2
    have hvals : values = [.word 1#64] := by
      simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_const] at hvalues
      exact hvalues.symm
    subst hvals
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact charge_gas_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e 1#64 gl
      used (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  · intro l g m ffi vs h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    obtain ⟨⟨hge, _, _, _, hC⟩, h⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    have h2 : (PcCell e pc ⋆ (.mem (e + 64#64) ↦ .word (gl - 1#64) ⋆
        .mem (e + 184#64) ↦ .word (used + 1#64)) ⋆ R).holds
        (⟨s.locals, g, m, s.ffi⟩ : St σ) :=
      Assn.holds_perm h (by unfold GasCells PcCell; ac_rfl)
    refine WPr.seq_call_framed h2 (Qc := fun r =>
      ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆ PcCell e (pc + 1#64)) ?_ ?_ ?_ ?_
    · intro parameters cbody values cl hlk hvalues hbind
      have hparams := (fun_of_index 468 hE.functions (by guest_decl_at 468) (by decide +kernel)
        hlk).2
      have hvals : values = [.word 1#64] := by
        simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_const] at hvalues
        exact hvalues.symm
      subst hvals
      rw [hparams] at hbind
      simp [bindPanValueParameters] at hbind
      exact pc_add_framed hE parameters cbody hlk ⟨cl, g, m, s.ffi⟩ e pc 1#64
        (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    · intro l' g' m' ffi' vs' h3
      obtain ⟨⟨_, _, _, hC⟩, h3⟩ := Assn.holds_pure_elim h3
      injection hC with _ _ _ hf _
      subst hf
      refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
      refine Assn.holds_or_right (Assn.holds_pure_intro ⟨hge, _, _, _, rfl⟩ ?_)
      exact Assn.holds_perm (Assn.holds_congr rfl rfl h3)
        (by unfold JumpdestCells PcCell; ac_rfl)
    · intro l' g' m' ffi' exc v h3
      obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h3
      cases hC
    · intro l' g' m' ffi' ev h3
      obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h3
      cases hC
  · intro l g m ffi exc v h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨hlt, _, _, _, hC⟩, hkeep⟩ := Assn.holds_pure_elim h
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      refine Assn.holds_or_left (Assn.holds_pure_intro ⟨hlt, _, _, _, rfl⟩ ?_)
      exact Assn.holds_perm (Assn.holds_congr rfl rfl hkeep)
        (by unfold JumpdestCells GasCells; ac_rfl)
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
  · intro l g m ffi ev h
    rcases Assn.holds_or_elim h with h | h
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC

end InitECandidate.Solver.GuestBound
