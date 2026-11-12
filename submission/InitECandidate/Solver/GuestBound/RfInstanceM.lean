import InitECandidate.Solver.GuestBound.DispatchM
import InitECandidate.Solver.GuestBound.RfInstance

/-!
# The loop interface at the memory level

The current frame's assertion is `FrameOp ⋆ MemExtra ⋆ ExcExtraM`: stack, gas,
program counter and scratch junk; the memory buffer, the running flag and the
return data; and the cells only `frame_exception` touches. The measure is
`2·(gas left + spilled) + (1 if running) + (1 if the exception flag is clear)`.

One dispatch lowers it: the opcode returned having used gas or cleared the
running flag, or it raised `EvmErr` and `frame_exception` set the exception
flag.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The frame fields that only `frame_exception` touches. -/
structure ExStM where
  sgl : Word
  sp : Word
  msg : Word
  r0 : Word
  code : Word
  cc : Word
  fl : Word
  ee : Word

/-- The cells of `ExStM`. -/
def ExcExtraM (e : Word) (Z : ExStM) : Assn :=
  .mem (e + 72#64) ↦ .word Z.sgl ⋆ .mem (e + 192#64) ↦ .word Z.sp ⋆
    .mem (e + 112#64) ↦ .word Z.msg ⋆ .mem (Z.msg + 48#64) ↦ .word Z.r0 ⋆
    .mem (e + 160#64) ↦ .word Z.code ⋆ .glob "cur_cont" ↦ .word Z.cc ⋆
    .mem (Z.cc + 32#64) ↦ .word Z.fl ⋆ .glob "evm_empty" ↦ .word Z.ee

/-- The frame without what `frame_exception` owns. -/
def RestExcM (M : Word) (K : Word → Prop) (e fv : Word) (X : OpSt) (Y : MemSt) : Assn :=
  OpNoGas e X.sp X.cap X.base X.pv fv X.pc ⋆ JunkW M K X.pv X.base X.cap ⋆
    Assn.Range Y.mem (Y.mem + Y.cap) ⋆ .mem (e + 32#64) ↦ .word Y.len ⋆
    .mem (e + 40#64) ↦ .word Y.cap ⋆ .mem (e + 24#64) ↦ .word Y.mem ⋆
    .mem (e + 104#64) ↦ .word Y.run

theorem FrameX_excM (M : Word) (K : Word → Prop) (e fv : Word) (X : OpSt) (Y : MemSt)
    (Z : ExStM) :
    (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtraM e Z) =
      (ExcW e X.gl Z.sgl Z.sp Z.msg Z.r0 X.used Z.code Y.rd Y.rl Z.cc Z.fl Z.ee ⋆
        RestExcM M K e fv X Y) := by
  unfold FrameOp ExcW ExcExtraM MemExtra MemTail RestExcM
  rw [OpW_gas]
  unfold GasCells
  ac_rfl

/-- The frame seen as what `frame_exception` owns and the rest. -/
theorem holds_excM {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt} {Y : MemSt}
    {Z : ExStM} {s : St σ}
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtraM e Z ⋆ R).holds s) :
    (ExcW e X.gl Z.sgl Z.sp Z.msg Z.r0 X.used Z.code Y.rd Y.rl Z.cc Z.fl Z.ee ⋆
      RestExcM M K e fv X Y ⋆ R).holds s :=
  Assn.holds_focus (FrameX_excM M K e fv X Y Z)
    (Assn.holds_perm (P' := (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtraM e Z) ⋆ R) h
      (by ac_rfl))

theorem holds_of_excM {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt}
    {Y : MemSt} {Z : ExStM} {s : St σ}
    (h : (ExcW e X.gl Z.sgl Z.sp Z.msg Z.r0 X.used Z.code Y.rd Y.rl Z.cc Z.fl Z.ee ⋆
      RestExcM M K e fv X Y ⋆ R).holds s) :
    (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtraM e Z ⋆ R).holds s :=
  Assn.holds_perm (Assn.holds_unfocus (FrameX_excM M K e fv X Y Z) h) (by ac_rfl)

/-- The stack-side fields after `frame_exception(err)`. -/
def excX (X1 : OpSt) (Z : ExStM) (err : Word) : OpSt :=
  { X1 with gl := if err = 1#64 then X1.gl + Z.sp else 0#64,
            used := if err = 1#64 then X1.used else X1.used + (X1.gl + Z.sp) }

/-- The return-data fields after `frame_exception(err)`. -/
def excY (Y1 : MemSt) (Z : ExStM) (err : Word) : MemSt :=
  { Y1 with rd := if err = 1#64 then Y1.rd else Z.ee, rl := if err = 1#64 then Y1.rl else 0#64 }

/-- The exception-side fields after `frame_exception(err)`. -/
def excZ (Z : ExStM) (err : Word) : ExStM :=
  { Z with sgl := Z.r0, sp := 0#64, code := err, fl := 1#64 }

set_option maxHeartbeats 2000000 in
/-- One dispatch from the current frame's assertion. -/
theorem rfDispatch_stepM (hE : GuestEnv E) (hrest : ∀ f, f ∈ restOpsM → HandlerSpecM E f)
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X : OpSt) (Y : MemSt)
    (Z : ExStM) (hok : FrameOk M K fv X) (hY : MBufOk Y fv)
    (hno : X.gl.toNat + Z.sp.toNat < 2 ^ 64 - 1)
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtraM e Z ⋆ R).holds s) :
    WPr E s rfDispatch (fun r => Trap r ∨ ∃ l g m fv' X' Y' Z', r = .normal l g m s.ffi ∧
      FrameOk M K fv' X' ∧ MBufOk Y' fv' ∧
      (FrameOp M K e fv' X' ⋆ MemExtra e Y' ⋆ ExcExtraM e Z' ⋆ R).holds ⟨l, g, m, s.ffi⟩ ∧
      (∀ x, x ≠ "err" → l x = s.locals x) ∧
      X'.gl.toNat + Z'.sp.toNat ≤ X.gl.toNat + Z.sp.toNat ∧
      ((Z'.fl = Z.fl ∧ (X'.gl.toNat + Z'.sp.toNat < X.gl.toNat + Z.sp.toNat ∨
          Y'.run = 0#64)) ∨ Z'.fl = 1#64)) := by
  unfold rfDispatch
  refine WPr.callH (fun rb hrb => ?_)
  obtain ⟨parameters, body, values, cl, hlk, -, -, hrun⟩ := hrb
  have hd := op_dispatch_frameM hE hrest parameters body hlk ⟨cl, s.globals, s.memory, s.ffi⟩
    M K e fv (ExcExtraM e Z ⋆ R) X Y hok hY (by omega) (Assn.holds_congr rfl rfl h) rb hrun
  cases rb with
  | returned l g m ffi vs =>
    rcases hd with he | hq
    · cases he
    rcases hq with (ht | ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩) |
      ⟨fv1, X1, Y1, n, hok1, hY1, hp1, hn, hh, _, _, _, hC⟩
    · exact ht.elim
    · cases hC
    injection hC with _ _ _ hf _
    subst hf
    intro l' g' hassign
    obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
    have : l' = s.locals := funext (fun x => hl x (by simp))
    subst this
    have hle := hp1.1
    refine Or.inr ⟨_, _, _, fv1, X1, Y1, Z, rfl, hok1, hY1, Assn.holds_congr rfl rfl hh,
      fun _ _ => rfl, by omega, Or.inl ⟨rfl, ?_⟩⟩
    rcases hn with hn | hn
    · exact Or.inl (by omega)
    · exact Or.inr hn
  | raised l g m ffi e' v =>
    rcases hd with he | hq
    · cases he
    rcases hq with (ht | ⟨fv1, X1, Y1, n, hok1, hY1, hp1, hh, _, _, _, _, hC⟩) |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC⟩
    · have ht' : e' = "TrapErr" := ht
      subst ht'
      exact ⟨fun _ => Or.inl rfl, fun h0 => absurd h0 (by decide)⟩
    rotate_left
    · cases hC
    injection hC with _ _ _ hf hx hv
    subst hf hx hv
    refine ⟨fun h0 => absurd rfl h0, fun _ => ?_⟩
    have hE1 := holds_excM (Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "err" v, g, m,
      s.ffi⟩ : St σ)) rfl rfl hh)
    refine WPr.call_framed hE1 (Qc := fun r => Assn.ex fun err : Word =>
        ⌜v = .word err ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        ExcW e (if err = 1#64 then X1.gl + Z.sp else 0#64) Z.r0 0#64 Z.msg Z.r0
          (if err = 1#64 then X1.used else X1.used + (X1.gl + Z.sp)) err
          (if err = 1#64 then Y1.rd else Z.ee) (if err = 1#64 then Y1.rl else 0#64) Z.cc 1#64
          Z.ee) ?_ ?_ ?_ ?_
    · intro parameters2 cbody values2 cl2 hlk2 hvalues2 hbind2
      have hparams := (fun_of_index 579 hE.functions (by guest_decl_at 579) (by decide +kernel)
        hlk2).2
      have hvals : values2 = [v] := by
        simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
          update_lookup] at hvalues2
        exact hvalues2.symm
      subst hvals
      rw [hparams] at hbind2
      simp [bindPanValueParameters] at hbind2
      exact frame_exception_framed hE parameters2 cbody hlk2 ⟨cl2, g, m, s.ffi⟩ e X1.gl Z.sgl
        Z.sp Z.msg Z.r0 X1.used Z.code Y1.rd Y1.rl Z.cc Z.fl Z.ee v
        (by rw [← hbind2]; simp (config := { decide := true }) [updatePanValueMap])
    · intro l2 g2 m2 ffi2 vs2 hpost
      obtain ⟨err, hpost⟩ := Assn.holdsV_ex.mp hpost
      obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hpost
      injection hC with _ _ _ hf _
      subst hf
      have hle := hp1.1
      refine Or.inr ⟨_, _, _, fv1, excX X1 Z err, excY Y1 Z err, excZ Z err,
        rfl, ⟨hok1.ok, hok1.pb, hok1.bM, hok1.Kpv, hok1.Kst⟩,
        ⟨hY1.mal, hY1.cal, hY1.l32, hY1.lc, hY1.top⟩, ?_, ?_, ?_, Or.inr rfl⟩
      · exact holds_of_excM (X := excX X1 Z err) (Y := excY Y1 Z err) (Z := excZ Z err) hk
      · intro x hx
        simp [update_lookup, hx]
      · show (if err = 1#64 then X1.gl + Z.sp else 0#64).toNat + (0#64 : Word).toNat ≤
          X.gl.toNat + Z.sp.toNat
        split
        · have : (X1.gl + Z.sp).toNat = X1.gl.toNat + Z.sp.toNat := by bv_omega
          simp
          omega
        · simp
    · intro l2 g2 m2 ffi2 exc v2 hpost
      obtain ⟨err, hpost⟩ := Assn.holdsV_ex.mp hpost
      obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hpost
      cases hC
    · intro l2 g2 m2 ffi2 ev hpost
      obtain ⟨err, hpost⟩ := Assn.holdsV_ex.mp hpost
      obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hpost
      cases hC
  | finalFfi l g m ffi ev => exact Or.inl trivial
  | _ => trivial

/-- The measure of the current frame, with the running flag. -/
def rfMuM (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word)) : Nat :=
  match g "ev", g "cur_cont" with
  | some (.word e), some (.word cc) =>
      2 * (rdNat m (e + 64#64) + rdNat m (e + 192#64)) +
        (if rdNat m (e + 104#64) = 0 then 0 else 1) +
        (if rdNat m (cc + 32#64) = 0 then 1 else 0)
  | _, _ => 0

/-- The invariant of the current frame. -/
def rfInvM (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) : Prop :=
  ∃ (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X : OpSt) (Y : MemSt) (Z : ExStM),
    FrameOk M K fv X ∧ MBufOk Y fv ∧ X.gl.toNat + Z.sp.toNat < 2 ^ 64 - 1 ∧
      (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtraM e Z ⋆ R).holds (⟨fun _ => none, g, m, f⟩ : St σ)

/-- The running flag, from the frame's assertion. -/
theorem holds_run {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt} {Y : MemSt}
    {Z : ExStM} {s : St σ}
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtraM e Z ⋆ R).holds s) :
    s.memory (e + 104#64) = some (.word Y.run) := by
  have h2 : (MemTail e Y ⋆ (Assn.Range Y.mem (Y.mem + Y.cap) ⋆ FrameOp M K e fv X ⋆
      ExcExtraM e Z) ⋆ R).holds s := Assn.holds_perm h (by unfold MemExtra; ac_rfl)
  unfold MemTail at h2
  exact Assn.mem_at h2 (by look)

theorem rfMuM_eq {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt} {Y : MemSt}
    {Z : ExStM} {s : St σ}
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtraM e Z ⋆ R).holds s) :
    rfMuM s.globals s.memory = 2 * (X.gl.toNat + Z.sp.toNat) +
      (if Y.run.toNat = 0 then 0 else 1) + (if Z.fl.toNat = 0 then 1 else 0) := by
  have hrun := holds_run h
  have h' := holds_excM h
  unfold ExcW at h'
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at h' (by look)
  have hcc : s.globals "cur_cont" = some (.word Z.cc) := Assn.glob_at h' (by look)
  have h64 : s.memory (e + 64#64) = some (.word X.gl) := Assn.mem_at h' (by look)
  have h192 : s.memory (e + 192#64) = some (.word Z.sp) := Assn.mem_at h' (by look)
  have hfl : s.memory (Z.cc + 32#64) = some (.word Z.fl) := Assn.mem_at h' (by look)
  simp [rfMuM, rdNat, hev, hcc, h64, h192, hfl, hrun]

/-- The exception flag read by the loop's first test. -/
theorem rfC1_flagM (hE : GuestEnv E) {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {X : OpSt} {Y : MemSt} {Z : ExStM} {s : St σ}
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtraM e Z ⋆ R).holds s)
    (hc : E.eval s rfC1 = some (.word 0#64)) : Z.fl = 0#64 := by
  have h' := holds_excM h
  unfold ExcW at h'
  have hcc : s.globals "cur_cont" = some (.word Z.cc) := Assn.glob_at h' (by look)
  have hcv := eval_cmp_inv hE (op := .notEqual)
    (eval_load_at hE (addr := Z.cc + 32#64) (v := .word Z.fl)
      (of_eval (by ev [eval_global, hcc])) h' (by look))
    (of_eval (w := 0#64) (eval_const _ _)) _ hc
  simp only [PanValue.word.injEq] at hcv
  by_contra hne
  simp [evalPanCmp, hne] at hcv

/-- The running flag read by the loop's second test. -/
theorem rfC2_run (hE : GuestEnv E) {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {X : OpSt} {Y : MemSt} {Z : ExStM} {s : St σ}
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ ExcExtraM e Z ⋆ R).holds s)
    (hc : E.eval s rfC2 = some (.word 0#64)) : Y.run ≠ 0#64 := by
  have h' := holds_excM h
  unfold ExcW at h'
  have hev : s.globals "ev" = some (.word e) := Assn.glob_at h' (by look)
  have hcv := eval_cmp_inv hE (op := .equal)
    (eval_load_inv2 hE (addr := e + 104#64) (w := Y.run) (of_eval (by ev [eval_global, hev]))
      (holds_run h))
    (of_eval (w := 0#64) (eval_const _ _)) _ hc
  simp only [PanValue.word.injEq] at hcv
  intro hz
  rw [hz] at hcv
  simp [evalPanCmp] at hcv

/-- The loop interface for the current frame. -/
def rfSpecM (hE : GuestEnv E) (hrest : ∀ f, f ∈ restOpsM → HandlerSpecM E f) (BD BF : Nat)
    (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (finish : ∀ a : St σ, rfInvM a.globals a.memory a.ffi →
      WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
        (l "go" = some (.word 0#64) ∨
          (l "go" = a.locals "go" ∧ rfInvM g m f ∧ rfMuM g m < rfMuM a.globals a.memory)))) :
    RfSpec E where
  Inv := rfInvM
  μ := rfMuM
  DispatchPre := fun a =>
    (∃ l, E.eval ⟨l, a.globals, a.memory, a.ffi⟩ rfC1 = some (.word 0#64)) ∧
      ∃ l, E.eval ⟨l, a.globals, a.memory, a.ffi⟩ rfC2 = some (.word 0#64)
  BD := BD
  BF := BF
  costD := costD
  costF := costF
  pre := fun a _ h1 h2 _ _ => ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  finish := finish
  dispatch := by
    rintro a ⟨M, K, e, fv, R, X, Y, Z, hok, hY, hno, hh⟩ ⟨⟨l1, hpre1⟩, ⟨l2, hpre2⟩⟩
    have hha := Assn.holds_congr (s' := a) rfl rfl hh
    have hfl : Z.fl = 0#64 := rfC1_flagM hE
      (Assn.holds_congr (s' := (⟨l1, a.globals, a.memory, a.ffi⟩ : St σ)) rfl rfl hh) hpre1
    have hrun : Y.run ≠ 0#64 := rfC2_run hE
      (Assn.holds_congr (s' := (⟨l2, a.globals, a.memory, a.ffi⟩ : St σ)) rfl rfl hh) hpre2
    have hrun' : Y.run.toNat ≠ 0 := fun h0 => hrun (by bv_omega)
    refine WPr.wps (rfDispatch_stepM hE hrest a M K e fv R X Y Z hok hY hno hha) (fun r hr => ?_)
    rcases hr with ht | ⟨l, g, m, fv', X', Y', Z', rfl, hok', hY', hh', hl, hle, hcase⟩
    · exact Or.inl ht.stopped
    · refine Or.inr ⟨l, g, m, a.ffi, rfl, ⟨M, K, e, fv', R, X', Y', Z', hok', hY', by omega,
        Assn.holds_congr rfl rfl hh'⟩, ?_, hl "go" (by decide), hl "done" (by decide)⟩
      have e1 := rfMuM_eq hh'
      have e2 := rfMuM_eq hha
      dsimp only at e1
      have ha : (if Y'.run.toNat = 0 then 0 else 1 : Nat) ≤ 1 := by split <;> omega
      have hb : (if Z'.fl.toNat = 0 then 1 else 0 : Nat) ≤ 1 := by split <;> omega
      have ho1 : (if Y.run.toNat = 0 then 0 else 1 : Nat) = 1 := if_neg hrun'
      have ho2 : (if Z.fl.toNat = 0 then 1 else 0 : Nat) = 1 := by rw [hfl]; rfl
      rw [e1, e2, ho1, ho2]
      rcases hcase with ⟨_, h2 | h2⟩ | h1
      · omega
      · have : (if Y'.run.toNat = 0 then 0 else 1 : Nat) = 0 := by rw [h2]; rfl
        omega
      · have : (if Z'.fl.toNat = 0 then 1 else 0 : Nat) = 0 := by rw [h1]; rfl
        omega

/-- `run_frames` from a state satisfying the current-frame invariant. -/
theorem run_frames_bound_frameM (hE : GuestEnv E)
    (hrest : ∀ f, f ∈ restOpsM → HandlerSpecM E f) (BD BF : Nat)
    (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (finish : ∀ a : St σ, rfInvM a.globals a.memory a.ffi →
      WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
        (l "go" = some (.word 0#64) ∨
          (l "go" = a.locals "go" ∧ rfInvM g m f ∧ rfMuM g m < rfMuM a.globals a.memory))))
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "run_frames" E.functions = some (parameters, body))
    (s : St σ) (hI : rfInvM s.globals s.memory s.ffi) (fuel : Nat) (r : Result σ) (n : Nat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ (rfMuM s.globals s.memory + 1 + 1) * (expCost rfCond + (BD + BF + 200) + 1) + 10 :=
  run_frames_bound hE (rfSpecM hE hrest BD BF costD costF finish) parameters body hlookup s hI
    fuel r n hrun hne

end InitECandidate.Solver.GuestBound
