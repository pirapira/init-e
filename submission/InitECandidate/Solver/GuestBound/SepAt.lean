import InitECandidate.Solver.GuestBound.SepGas

/-!
# Reading and writing an owned cell anywhere in a `⋆` chain

`Look k v X`: any state satisfying `X ⋆ R` has `v` at `k`.
`Step k w X X'`: writing `w` at `k` turns `X ⋆ R` into `X' ⋆ R`.
Both are found by the tactics `look` and `step` for a right-nested chain of
points-to assertions, so proofs do not reorder the chain by hand.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- `V'` is `V` with `w` at `k`. -/
def Upd (V V' : Heap) (k : Key) (w : PanValue Word) : Prop :=
  V' k = some w ∧ ∀ k', k' ≠ k → V' k' = V k'

def Look (k : Key) (v : PanValue Word) (X : Assn) : Prop :=
  ∀ (V : Heap) (R : Assn), (X ⋆ R).holdsV V → V k = some v

def Step (k : Key) (w : PanValue Word) (X X' : Assn) : Prop :=
  ∀ (V V' : Heap) (R : Assn), Upd V V' k w → (X ⋆ R).holdsV V → (X' ⋆ R).holdsV V'

theorem Look.here {k : Key} {v : PanValue Word} : Look k v (k ↦ v) :=
  fun _ _ h => Assn.holdsV_pts h

theorem Look.head {k : Key} {v : PanValue Word} {Y : Assn} : Look k v (k ↦ v ⋆ Y) := by
  intro V R h
  rw [Assn.sep_assoc] at h
  exact Assn.holdsV_pts h

theorem Look.skip {k : Key} {v : PanValue Word} {P X : Assn} (h : Look k v X) :
    Look k v (P ⋆ X) := by
  intro V R hV
  have e : ((P ⋆ X) ⋆ R) = (X ⋆ P ⋆ R) := by ac_rfl
  rw [e] at hV
  exact h V _ hV

theorem Step.here {k : Key} {v w : PanValue Word} : Step k w (k ↦ v) (k ↦ w) :=
  fun _ _ _ hu h => Assn.holdsV_update h hu.1 hu.2

theorem Step.head {k : Key} {v w : PanValue Word} {Y : Assn} :
    Step k w (k ↦ v ⋆ Y) (k ↦ w ⋆ Y) := by
  intro V V' R hu h
  rw [Assn.sep_assoc] at h ⊢
  exact Assn.holdsV_update h hu.1 hu.2

theorem Step.skip {k : Key} {w : PanValue Word} {P X X' : Assn} (h : Step k w X X') :
    Step k w (P ⋆ X) (P ⋆ X') := by
  intro V V' R hu hV
  have e : ((P ⋆ X) ⋆ R) = (X ⋆ P ⋆ R) := by ac_rfl
  have e' : ((P ⋆ X') ⋆ R) = (X' ⋆ P ⋆ R) := by ac_rfl
  rw [e] at hV
  rw [e']
  exact h V V' _ hu hV

/-- Find an owned key in a chain. -/
macro "look" : tactic => `(tactic|
  repeat (first | exact Look.here | exact Look.head | apply Look.skip))

/-- Update an owned key in a chain. -/
macro "step" : tactic => `(tactic|
  repeat (first | exact Step.here | exact Step.head | apply Step.skip))

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem upd_setCell (s : St σ) (a w : Word) (l : VarName → Option (PanValue Word))
    (f : FfiState σ) :
    Upd s.view (St.view (⟨l, s.globals, setCell s.memory a w, f⟩ : St σ)) (.mem a) (.word w) := by
  refine ⟨by simp [St.view, setCell], ?_⟩
  intro k' hk'
  cases k' with
  | glob x => rfl
  | mem b =>
    have : b ≠ a := fun e => hk' (by rw [e])
    simp [St.view, setCell, this]

/-- The value of an owned global. -/
theorem Assn.glob_at {A R : Assn} {x : VarName} {v : PanValue Word} (h : (A ⋆ R).holds s)
    (hl : Look (.glob x) v A) : s.globals x = some v :=
  hl _ _ h

/-- A word load from an owned cell. -/
theorem eval_load_at (hE : GuestEnv E) {a : Exp Word} {addr : Word} {v : PanValue Word}
    {A R : Assn} (ha : ∀ y, E.eval s a = some y → y = .word addr) (h : (A ⋆ R).holds s)
    (hl : Look (.mem addr) v A) : ∀ y, E.eval s (.load .one a) = some y → y = v := by
  intro y hy
  obtain ⟨addr', w', ha', rfl, hm⟩ := eval_load_one hE.mem hy
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  have hv : s.memory addr' = some v := hl _ _ h
  rw [hm] at hv
  exact Option.some.inj hv

/-- `st a, v; rest` into an owned cell: the rest runs from a state whose
memory is known only through the updated assertion. -/
theorem WPr.seq_store_at (hE : GuestEnv E) {a val : Exp Word} {q : Prog Word} {addr w : Word}
    {A A' R : Assn} (h : (A ⋆ R).holds s)
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : ∀ y, E.eval s val = some y → y = .word w)
    (hstep : Step (.mem addr) (.word w) A A')
    (hq : ∀ m, (A' ⋆ R).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.store a val) q) Q := by
  refine WPr.seq (fun s' => ∃ m, s' = ⟨s.locals, s.globals, m, s.ffi⟩ ∧ (A' ⋆ R).holds s') ?_ ?_
  · intro r hr
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
    exact Or.inr ⟨_, rfl, hstep _ _ _ (upd_setCell s addr' w s.locals s.ffi) h⟩
  · rintro _ ⟨m, rfl, hm⟩
    exact hq m hm

/-- The gas fields that state-gas accounting touches, with the message record. -/
def StateGas (e gl sgl sp msg r0 : Word) : Assn :=
  .glob "ev" ↦ .word e ⋆ .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 72#64) ↦ .word sgl ⋆
    .mem (e + 192#64) ↦ .word sp ⋆ .mem (e + 112#64) ↦ .word msg ⋆
    .mem (msg + 48#64) ↦ .word r0

/-- `refill_frame_state_gas`: the spilled gas returns to gas left, so their sum
is unchanged; the reservoir is reset from the message. -/
theorem refill_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "refill_frame_state_gas" E.functions = some (parameters, body))
    (s : St σ) (e gl sgl sp msg r0 : Word) :
    WPFr E s body (StateGas e gl sgl sp msg r0)
      (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        StateGas e (gl + sp) r0 0#64 msg r0) := by
  have hbody := (fun_of_index 452 hE.functions (by guest_decl_at 452) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  unfold StateGas at hR
  dsimp only
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at hR (by look)
  refine WPr.dec_ev (fun v hv => ?_)
  have hm := eval_load_at hE (addr := e + 112#64) (v := .word msg)
    (of_eval (by ev [eval_global, hev])) hR (by look) v hv
  subst hm
  have h1 := Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "msg" (.word msg), s.globals,
    s.memory, s.ffi⟩ : St σ)) rfl rfl hR
  refine WPr.seq_store_at hE h1 (addr := e + 64#64) (w := gl + sp)
    (of_eval (by ev [eval_global, hev]))
    (eval_add2_inv hE
      (eval_load_at hE (addr := e + 64#64) (of_eval (by ev [eval_global, hev])) h1 (by look))
      (eval_load_at hE (addr := e + 192#64) (of_eval (by ev [eval_global, hev])) h1 (by look)))
    (by step) (fun m1 h2 => ?_)
  refine WPr.seq_store_at hE h2 (addr := e + 72#64) (w := r0)
    (of_eval (by ev [eval_global, hev]))
    (eval_load_at hE (addr := msg + 48#64) (of_eval (by ev [])) h2 (by look))
    (by step) (fun m2 h3 => ?_)
  refine WPr.seq_store_at hE h3 (addr := e + 192#64) (w := 0#64)
    (of_eval (by ev [eval_global, hev])) (of_eval (eval_const _ _))
    (by step) (fun m3 h4 => ?_)
  refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  show ((⌜_⌝ ⋆ StateGas _ _ _ _ _ _) ⋆ R).holds _
  rw [Assn.sep_assoc]
  exact Assn.holdsV_pure.mpr ⟨⟨_, _, _, rfl⟩, Assn.holds_congr rfl rfl h4⟩

end InitECandidate.Solver.GuestBound
