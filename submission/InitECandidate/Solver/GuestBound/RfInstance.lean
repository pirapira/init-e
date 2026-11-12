import InitECandidate.Solver.GuestBound.DispatchBlock

/-!
# An instance of the loop interface for the current frame

`rfSpec` builds an `RfSpec` whose invariant is the current frame's assertion
and whose measure is `2·(gas left + spilled) + (1 if the exception flag is
clear)`, read from memory. Its `dispatch` field is proved from
`rfDispatch_step`. Still supplied by the caller: the handlers in `restOps`, the
two cost bounds, and the `finish` field (the end-of-frame block).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The word at an address, as a number (0 if there is none). -/
def rdNat (m : Word → Option (PanValue Word)) (a : Word) : Nat :=
  match m a with
  | some (.word w) => w.toNat
  | _ => 0

/-- The measure of the current frame. -/
def rfMu (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word)) : Nat :=
  match g "ev", g "cur_cont" with
  | some (.word e), some (.word cc) =>
      2 * (rdNat m (e + 64#64) + rdNat m (e + 192#64)) +
        (if rdNat m (cc + 32#64) = 0 then 1 else 0)
  | _, _ => 0

/-- The invariant of the current frame. -/
def rfInv (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) : Prop :=
  ∃ (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X : OpSt) (Y : ExSt),
    FrameOk M K fv X ∧ X.gl.toNat + Y.sp.toNat < 2 ^ 64 ∧
      (FrameOp M K e fv X ⋆ ExcExtra e Y ⋆ R).holds (⟨fun _ => none, g, m, f⟩ : St σ)

theorem Assn.mem_at {A R : Assn} {s : St σ} {a : Word} {v : PanValue Word}
    (h : (A ⋆ R).holds s) (hl : Look (.mem a) v A) : s.memory a = some v :=
  hl _ _ h

/-- The measure, from the frame's assertion. -/
theorem rfMu_eq {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt} {Y : ExSt}
    {s : St σ} (h : (FrameOp M K e fv X ⋆ ExcExtra e Y ⋆ R).holds s) :
    rfMu s.globals s.memory =
      2 * (X.gl.toNat + Y.sp.toNat) + (if Y.fl.toNat = 0 then 1 else 0) := by
  have h' := Assn.holds_focus (FrameX_exc M K e fv X Y)
    (Assn.holds_assoc_l (P := FrameOp M K e fv X) h)
  unfold ExcW at h'
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at h' (by look)
  have hcc : s.globals "cur_cont" = some (.word Y.cc) := Assn.glob_at h' (by look)
  have h64 : s.memory (e + 64#64) = some (.word X.gl) := Assn.mem_at h' (by look)
  have h192 : s.memory (e + 192#64) = some (.word Y.sp) := Assn.mem_at h' (by look)
  have hfl : s.memory (Y.cc + 32#64) = some (.word Y.fl) := Assn.mem_at h' (by look)
  simp [rfMu, rdNat, hev, hcc, h64, h192, hfl]

/-- The exception flag read by the loop's first test. -/
theorem rfC1_flag (hE : GuestEnv E) {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {X : OpSt} {Y : ExSt} {s : St σ} (h : (FrameOp M K e fv X ⋆ ExcExtra e Y ⋆ R).holds s)
    (hc : E.eval s rfC1 = some (.word 0#64)) : Y.fl = 0#64 := by
  have h' := Assn.holds_focus (FrameX_exc M K e fv X Y)
    (Assn.holds_assoc_l (P := FrameOp M K e fv X) h)
  unfold ExcW at h'
  have hcc : s.globals "cur_cont" = some (.word Y.cc) := Assn.glob_at h' (by look)
  have hcv := eval_cmp_inv hE (op := .notEqual)
    (eval_load_at hE (addr := Y.cc + 32#64) (v := .word Y.fl)
      (of_eval (by ev [eval_global, hcc])) h' (by look))
    (of_eval (w := 0#64) (eval_const _ _)) _ hc
  simp only [PanValue.word.injEq] at hcv
  by_contra hne
  simp [evalPanCmp, hne] at hcv

theorem Trap.stopped {r : Result σ} (h : Trap r) : Stopped r := by
  cases r <;> trivial

/-- The loop interface for the current frame. -/
def rfSpec (hE : GuestEnv E) (hrest : ∀ f, f ∈ restOps → HandlerSpec E f) (BD BF : Nat)
    (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (finish : ∀ a : St σ, rfInv a.globals a.memory a.ffi →
      WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
        (l "go" = some (.word 0#64) ∨
          (l "go" = a.locals "go" ∧ rfInv g m f ∧ rfMu g m < rfMu a.globals a.memory)))) :
    RfSpec E where
  Inv := rfInv
  μ := rfMu
  DispatchPre := fun a => ∃ l, E.eval ⟨l, a.globals, a.memory, a.ffi⟩ rfC1 = some (.word 0#64)
  BD := BD
  BF := BF
  costD := costD
  costF := costF
  pre := fun a _ h1 _ _ _ => ⟨_, h1⟩
  finish := finish
  dispatch := by
    rintro a ⟨M, K, e, fv, R, X, Y, hok, hno, hh⟩ ⟨l0, hpre⟩
    have hha := Assn.holds_congr (s' := a) rfl rfl hh
    have hfl : Y.fl = 0#64 := rfC1_flag hE
      (Assn.holds_congr (s' := (⟨l0, a.globals, a.memory, a.ffi⟩ : St σ)) rfl rfl hh) hpre
    refine WPr.wps (rfDispatch_step hE hrest a M K e fv R X Y hok hno hha) (fun r hr => ?_)
    rcases hr with ht | ⟨l, g, m, X', Y', rfl, hok', hh', hl, hcase⟩
    · exact Or.inl ht.stopped
    · refine Or.inr ⟨l, g, m, a.ffi, rfl, ⟨M, K, e, fv, R, X', Y', hok', ?_,
        Assn.holds_congr rfl rfl hh'⟩, ?_, hl "go" (by decide), hl "done" (by decide)⟩
      · rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
      · have e1 := rfMu_eq hh'
        have e2 := rfMu_eq hha
        dsimp only at e1
        rw [e1, e2]
        rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h2]
          omega
        · rw [h2, hfl]
          simp
          omega

/-- `run_frames` from a state satisfying the current-frame invariant. -/
theorem run_frames_bound_frame (hE : GuestEnv E) (hrest : ∀ f, f ∈ restOps → HandlerSpec E f)
    (BD BF : Nat) (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (finish : ∀ a : St σ, rfInv a.globals a.memory a.ffi →
      WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
        (l "go" = some (.word 0#64) ∨
          (l "go" = a.locals "go" ∧ rfInv g m f ∧ rfMu g m < rfMu a.globals a.memory))))
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "run_frames" E.functions = some (parameters, body))
    (s : St σ) (hI : rfInv s.globals s.memory s.ffi) (fuel : Nat) (r : Result σ) (n : Nat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ (rfMu s.globals s.memory + 1 + 1) * (expCost rfCond + (BD + BF + 200) + 1) + 10 :=
  run_frames_bound hE (rfSpec hE hrest BD BF costD costF finish) parameters body hlookup s hI
    fuel r n hrun hne

end InitECandidate.Solver.GuestBound
