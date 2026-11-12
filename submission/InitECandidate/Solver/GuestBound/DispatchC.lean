import InitECandidate.Solver.GuestBound.SepChain

/-!
# Dispatch on a chain: handlers that may push a frame

Most handlers stay in their frame (`HandlerSpecM`). The six call/create
opcodes may start a child frame. `PushD` is that outcome: the running frame
`F` became a suspended frame `F'` of the same identity, with a child `c`
linked on top of it, the world index may have changed (tables in `D` stay
live), and child plus parent hold at least one unit of gas less than `F` did.

`HandlerSpecPush` is the statement to prove for those six handlers;
`op_dispatch_chain` is the dispatcher with both kinds of leaves.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {ι : Type}

/-- The opcodes that may start a child frame. -/
def callOps : List FunName :=
  ["op_create", "op_create2", "op_call", "op_callcode", "op_delegatecall", "op_staticcall"]

/-- A child frame was pushed on `F`. -/
def PushD (W : ι → Assn) (D : ι → Word → Prop) (i : ι) (F : Fr) (R : Assn) (st : St σ) : Prop :=
  ∃ (i' : ι) (F' c : Fr), F'.M = F.M ∧ F'.K = F.K ∧ F'.e = F.e ∧ F'.C = F.C ∧ F'.A = F.A ∧
    F'.Y.mem = F.Y.mem ∧ F'.Z.cc = F.Z.cc ∧ F'.Z.msg = F.Z.msg ∧ F'.Z.ee = F.Z.ee ∧
    F'.Ok (D i') ∧ c.Ok (D i') ∧ Link c F' ∧ (∀ t, D i t → D i' t) ∧
    c.gas + F'.gas + 1 ≤ F.gas ∧ (c.full ⋆ F'.susp ⋆ W i' ⋆ R).holds st

theorem PushD.congr {W : ι → Assn} {D : ι → Word → Prop} {i : ι} {F : Fr} {R : Assn}
    {st st' : St σ} (h : PushD W D i F R st) (hg : st'.globals = st.globals)
    (hm : st'.memory = st.memory) : PushD W D i F R st' := by
  obtain ⟨i', F', c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hh⟩ := h
  exact ⟨i', F', c, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    Assn.holds_congr hg hm hh⟩

/-- What the rest of the running frame's assertion is, seen from a handler. -/
def frameRest (W : ι → Assn) (i : ι) (F : Fr) (R : Assn) : Assn :=
  ExcExtraM F.e F.Z ⋆ RecCells F.Z.cc F.C ⋆ AccCells F.e F.A ⋆ W i ⋆ R

/-- The outcome of a handler on a chain: it stayed in its frame, or it pushed a child. -/
def HandlerQC (W : ι → Assn) (D : ι → Word → Prop) (i : ι) (F : Fr) (R : Assn)
    (ffi : FfiState σ) (r : Result σ) : Prop :=
  HandlerQM F.M F.K F.e F.Y.mem (frameRest W i F R) ffi F.X r ∨
    ∃ l g m, r = .returned l g m ffi [.word 0#64] ∧ PushD W D i F R ⟨l, g, m, ffi⟩

/-- A handler that may push a child frame. -/
def HandlerSpecPush (E : Env σ) (W : ι → Assn) (D : ι → Word → Prop) (f : FunName) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    ∀ (s : St σ) (i : ι) (F : Fr) (R : Assn), F.Ok (D i) → F.X.gl.toNat < 2 ^ 64 - 1 →
      (F.full ⋆ W i ⋆ R).holds s → WPr E s body (HandlerQC W D i F R s.ffi)

/-- The frame's assertion, split the way single-frame handlers see it. -/
theorem holds_frameRest {W : ι → Assn} {i : ι} {F : Fr} {R : Assn} {s : St σ}
    (h : (F.full ⋆ W i ⋆ R).holds s) :
    (FrameOp F.M F.K F.e F.fv F.X ⋆ MemExtra F.e F.Y ⋆ frameRest W i F R).holds s :=
  Assn.holds_perm h (by unfold Fr.full frameRest; ac_rfl)

/-- A leaf of the dispatcher for a handler that may push a frame. -/
theorem handler_leafC {W : ι → Assn} {D : ι → Word → Prop} {f : FunName}
    (hf : HandlerSpecPush E W D f) (args : List (Exp Word)) (s : St σ) (i : ι) (F : Fr)
    (R : Assn) (hok : F.Ok (D i)) (hgl : F.X.gl.toNat < 2 ^ 64 - 1)
    (h : (F.full ⋆ W i ⋆ R).holds s) :
    WPr E s (.seq (.call (some (none, none)) f args) (.return (.const 0#64)))
      (HandlerQC W D i F R s.ffi) := by
  refine WPr.seq (fun s' => ∃ g m, s' = ⟨s.locals, g, m, s.ffi⟩ ∧
      ((∃ fv' X Y n, FrameOk F.M F.K fv' X ∧ MBufOk Y fv' ∧ Y.mem = F.Y.mem ∧ Adv X F.X n ∧
        (0 < n ∨ Y.run = 0#64) ∧
        (FrameOp F.M F.K F.e fv' X ⋆ MemExtra F.e Y ⋆ frameRest W i F R).holds s') ∨
        PushD W D i F R s'))
    (WPr.call_spec (HandlerQC W D i F R s.ffi)
      (fun parameters body _ cl hlk _ _ =>
        hf parameters body hlk ⟨cl, s.globals, s.memory, s.ffi⟩ i F R hok hgl
          (Assn.holds_congr rfl rfl h)) ?_ ?_ ?_) ?_
  · rintro l g m ffi vs (((ht | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) |
      ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hn, hh, _, _, _, hC⟩) | ⟨l', g', m', hC, hpd⟩)
    · exact ht.elim
    · cases hC
    · injection hC with _ _ _ hf' _
      subst hf'
      exact ⟨g, m, rfl, Or.inl ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hn,
        Assn.holds_congr rfl rfl hh⟩⟩
    · injection hC with _ hg hm hf' _
      subst hg hm hf'
      exact ⟨g, m, rfl, Or.inr (hpd.congr rfl rfl)⟩
  · rintro l g m ffi exc v (((ht | ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hh, _, _, _, _, hC⟩) |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) | ⟨_, _, _, hC, _⟩)
    · exact Or.inl (Or.inl (Or.inl ht))
    · injection hC with _ _ _ hf' hx hv
      subst hf' hx hv
      exact Or.inl (Or.inl (Or.inr ⟨fv', X, Y, n, hokX, hYX, hmX, hp,
        Assn.holds_congr rfl rfl hh, _, _, _, _, rfl⟩))
    · cases hC
    · cases hC
  · intro l g m ffi ev _
    exact Or.inl (Or.inl (Or.inl trivial))
  · rintro _ ⟨g, m, rfl, hcase⟩
    refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
    rcases hcase with ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hn, hh⟩ | hpd
    · exact Or.inl (Or.inr ⟨fv', X, Y, n, hokX, hYX, hmX, hp, hn, Assn.holds_congr rfl rfl hh,
        _, _, _, rfl⟩)
    · exact Or.inr ⟨_, _, _, rfl, hpd.congr rfl rfl⟩

/-- The dispatcher on a chain. -/
theorem op_dispatch_chain (hE : GuestEnv E) {W : ι → Assn} {D : ι → Word → Prop}
    (hrest : ∀ f, f ∈ restOpsM → f ∉ callOps → HandlerSpecM E f)
    (hcall : ∀ f, f ∈ callOps → HandlerSpecPush E W D f)
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "op_dispatch" E.functions = some (parameters, body))
    (s : St σ) (i : ι) (F : Fr) (R : Assn) (hok : F.Ok (D i))
    (hgl : F.X.gl.toNat < 2 ^ 64 - 1) (h : (F.full ⋆ W i ⋆ R).holds s) :
    WPr E s body (fun r => match r with
      | .normal l g m f => (⟨l, g, m, f⟩ : St σ) = s
      | r => HandlerQC W D i F R s.ffi r) := by
  have hbody := (fun_of_index 577 hE.functions (by guest_decl_at 577) (by decide +kernel)
    hlookup).1
  subst hbody
  have hfr := holds_frameRest h
  have hall : ∀ f, (provedOps ++ restOps).contains f = true → f ∉ callOps →
      HandlerSpecM E f := by
    intro f hf hnc
    rcases List.mem_append.mp (List.contains_iff_mem.mp hf) with h1 | h2
    · exact handlers_provedM hE f (List.mem_append_left _ h1)
    · by_cases hm : memOps.contains f = true
      · exact handlers_provedM hE f (List.mem_append_right _ (List.contains_iff_mem.mp hm))
      · exact hrest f (List.mem_filter.mpr ⟨h2, by simpa using hm⟩) hnc
  refine tree_sound (ok := fun f => (provedOps ++ restOps).contains f) (P := fun a => a = s)
    (Q := HandlerQC W D i F R s.ffi) ?_ ?_ ?_ _ (by decide +kernel) s rfl
  · rintro f args hf _ rfl
    by_cases hc : f ∈ callOps
    · exact handler_leafC (hcall f hc) args _ i F R hok hgl h
    · exact WPr.conseq (handler_leafM (hall f hf hc) args _ F.M F.K F.e F.fv
        (frameRest W i F R) F.X F.Y hok.ok hok.buf hgl hfr) (fun r hr => Or.inl hr)
  · rintro _ k rfl
    exact Or.inl (Or.inl (Or.inr ⟨F.fv, F.X, F.Y, 0, hok.ok, hok.buf, rfl,
      ⟨Nat.le_refl _, Nat.le_refl _⟩, Assn.holds_congr rfl rfl hfr, _, _, _, _, rfl⟩))
  · rintro l g m f (((ht | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) | ⟨_, _, _, hC, _⟩)
    · exact ht.elim
    · cases hC
    · cases hC
    · cases hC

/-- What is left of the frame's assertion once `frame_exception`'s cells are taken out. -/
def chainRest (W : ι → Assn) (i : ι) (F : Fr) (R : Assn) : Assn :=
  RecCells F.Z.cc F.C ⋆ AccCells F.e F.A ⋆ W i ⋆ R

set_option maxHeartbeats 2000000 in
/-- One dispatch on a chain: a trap; or the running frame continues (possibly
after `frame_exception`); or a child frame was pushed. -/
theorem rfDispatch_stepC (hE : GuestEnv E) {W : ι → Assn} {D : ι → Word → Prop}
    (hrest : ∀ f, f ∈ restOpsM → f ∉ callOps → HandlerSpecM E f)
    (hcall : ∀ f, f ∈ callOps → HandlerSpecPush E W D f)
    (s : St σ) (i : ι) (F : Fr) (R : Assn) (hok : F.Ok (D i))
    (hno : F.X.gl.toNat + F.Z.sp.toNat < 2 ^ 64 - 1) (h : (F.full ⋆ W i ⋆ R).holds s) :
    WPr E s rfDispatch (fun r => Trap r ∨
      (∃ l g m fv' X' Y' Z', r = .normal l g m s.ffi ∧
        FrameOk F.M F.K fv' X' ∧ MBufOk Y' fv' ∧
        (FrameOp F.M F.K F.e fv' X' ⋆ MemExtra F.e Y' ⋆ ExcExtraM F.e Z' ⋆
          chainRest W i F R).holds ⟨l, g, m, s.ffi⟩ ∧
        (∀ x, x ≠ "err" → l x = s.locals x) ∧
        X'.gl.toNat + Z'.sp.toNat ≤ F.X.gl.toNat + F.Z.sp.toNat ∧
        ((Z'.fl = F.Z.fl ∧ (X'.gl.toNat + Z'.sp.toNat < F.X.gl.toNat + F.Z.sp.toNat ∨
            Y'.run = 0#64)) ∨ Z'.fl = 1#64) ∧
        (Y'.mem = F.Y.mem ∧ Z'.cc = F.Z.cc ∧ Z'.msg = F.Z.msg ∧ Z'.ee = F.Z.ee)) ∨
      ∃ l g m, r = .normal l g m s.ffi ∧ (∀ x, x ≠ "err" → l x = s.locals x) ∧
        PushD W D i F R ⟨l, g, m, s.ffi⟩) := by
  unfold rfDispatch
  refine WPr.callH (fun rb hrb => ?_)
  obtain ⟨parameters, body, values, cl, hlk, -, -, hrun⟩ := hrb
  have hd := op_dispatch_chain hE hrest hcall parameters body hlk ⟨cl, s.globals, s.memory, s.ffi⟩
    i F R hok (by omega) (Assn.holds_congr rfl rfl h) rb hrun
  cases rb with
  | returned l g m ffi vs =>
    rcases hd with he | hq
    · cases he
    rcases hq with ((ht | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) |
      ⟨fv1, X1, Y1, n, hok1, hY1, hm1, hp1, hn, hh, _, _, _, hC⟩) | ⟨l0, g0, m0, hC, hpd⟩
    · exact ht.elim
    · cases hC
    · injection hC with _ _ _ hf _
      subst hf
      intro l' g' hassign
      obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
      have : l' = s.locals := funext (fun x => hl x (by simp))
      subst this
      have hle := hp1.1
      refine Or.inr (Or.inl ⟨_, _, _, fv1, X1, Y1, F.Z, rfl, hok1, hY1,
        Assn.holds_congr rfl rfl hh, fun _ _ => rfl, by omega, Or.inl ⟨rfl, ?_⟩, hm1, rfl, rfl,
        rfl⟩)
      rcases hn with hn | hn
      · exact Or.inl (by omega)
      · exact Or.inr hn
    · injection hC with _ hg0 hm0 hf _
      subst hg0 hm0 hf
      intro l' g' hassign
      obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
      have : l' = s.locals := funext (fun x => hl x (by simp))
      subst this
      exact Or.inr (Or.inr ⟨_, _, _, rfl, fun _ _ => rfl, hpd.congr rfl rfl⟩)
  | raised l g m ffi e' v =>
    rcases hd with he | hq
    · cases he
    rcases hq with ((ht | ⟨fv1, X1, Y1, n, hok1, hY1, hm1, hp1, hh, _, _, _, _, hC⟩) |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hC⟩) | ⟨_, _, _, hC, _⟩
    · have ht' : e' = "TrapErr" := ht
      subst ht'
      exact ⟨fun _ => Or.inl rfl, fun h0 => absurd h0 (by decide)⟩
    rotate_left
    · cases hC
    · cases hC
    injection hC with _ _ _ hf hx hv
    subst hf hx hv
    refine ⟨fun h0 => absurd rfl h0, fun _ => ?_⟩
    have hh' : (FrameOp F.M F.K F.e fv1 X1 ⋆ MemExtra F.e Y1 ⋆ ExcExtraM F.e F.Z ⋆
        chainRest W i F R).holds (⟨updatePanValueMap s.locals "err" v, g, m, s.ffi⟩ : St σ) :=
      Assn.holds_congr rfl rfl hh
    have hE1 := holds_excM hh'
    refine WPr.call_framed hE1 (Qc := fun r => Assn.ex fun err : Word =>
        ⌜v = .word err ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        ExcW F.e (if err = 1#64 then X1.gl + F.Z.sp else 0#64) F.Z.r0 0#64 F.Z.msg F.Z.r0
          (if err = 1#64 then X1.used else X1.used + (X1.gl + F.Z.sp)) err
          (if err = 1#64 then Y1.rd else F.Z.ee) (if err = 1#64 then Y1.rl else 0#64) F.Z.cc
          1#64 F.Z.ee) ?_ ?_ ?_ ?_
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
      exact frame_exception_framed hE parameters2 cbody hlk2 ⟨cl2, g, m, s.ffi⟩ F.e X1.gl F.Z.sgl
        F.Z.sp F.Z.msg F.Z.r0 X1.used F.Z.code Y1.rd Y1.rl F.Z.cc F.Z.fl F.Z.ee v
        (by rw [← hbind2]; simp (config := { decide := true }) [updatePanValueMap])
    · intro l2 g2 m2 ffi2 vs2 hpost
      obtain ⟨err, hpost⟩ := Assn.holdsV_ex.mp hpost
      obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hpost
      injection hC with _ _ _ hf _
      subst hf
      have hle := hp1.1
      refine Or.inr (Or.inl ⟨_, _, _, fv1, excX X1 F.Z err, excY Y1 F.Z err, excZ F.Z err,
        rfl, ⟨hok1.ok, hok1.pb, hok1.bM, hok1.Kpv, hok1.Kst⟩,
        ⟨hY1.mal, hY1.cal, hY1.l32, hY1.lc, hY1.top⟩, ?_, ?_, ?_, Or.inr rfl, hm1, rfl, rfl,
        rfl⟩)
      · exact holds_of_excM (X := excX X1 F.Z err) (Y := excY Y1 F.Z err) (Z := excZ F.Z err) hk
      · intro x hx
        simp [update_lookup, hx]
      · show (if err = 1#64 then X1.gl + F.Z.sp else 0#64).toNat + (0#64 : Word).toNat ≤
          F.X.gl.toNat + F.Z.sp.toNat
        split
        · have : (X1.gl + F.Z.sp).toNat = X1.gl.toNat + F.Z.sp.toNat := by bv_omega
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

theorem Fr.Ok.mono {D D' : Word → Prop} {F : Fr} (h : F.Ok D) (hD : ∀ t, D t → D' t) :
    F.Ok D' :=
  ⟨h.ok, h.buf, hD _ h.acc.1, hD _ h.acc.2⟩

theorem ChainOk.mono {D D' : Word → Prop} (hD : ∀ t, D t → D' t) :
    ∀ {F : Fr} {ps : List Fr}, ChainOk D F ps → ChainOk D' F ps
  | _, [], h => ⟨h.1.mono hD, h.2⟩
  | _, _ :: _, h => ⟨h.1.mono hD, h.2.1, ChainOk.mono hD h.2.2⟩

theorem Fr.mu_le (F : Fr) : F.mu ≤ 4 * F.gas + 3 := by
  unfold Fr.mu
  have ha : (if F.Y.run.toNat = 0 then 0 else 1 : Nat) ≤ 1 := by split <;> omega
  have hb : (if F.Z.fl.toNat = 0 then 1 else 0 : Nat) ≤ 1 := by split <;> omega
  omega

/-- The loop interface on a chain, with handlers that may push frames; the
end-of-frame block is assumed. -/
noncomputable def rfChainC (W : ι → Assn) (D : ι → Word → Prop) (hE : GuestEnv E)
    (hrest : ∀ f, f ∈ restOpsM → f ∉ callOps → HandlerSpecM E f)
    (hcall : ∀ f, f ∈ callOps → HandlerSpecPush E W D f)
    (BD BF : Nat) (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (finish : ∀ (a : St σ) (n : Nat), chainInv W D n a.globals a.memory →
      WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
        (l "go" = some (.word 0#64) ∨
          (l "go" = a.locals "go" ∧ ∃ n', n' < n ∧ chainInv W D n' g m)))) :
    RfGhost E where
  InvN := chainInv W D
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
    rintro a n ⟨i, F, ps, R, hch, hgas, hmu, hh⟩ ⟨⟨l1, hpre1⟩, ⟨l2, hpre2⟩⟩
    have h0 : (F.full ⋆ suspA ps ⋆ W i ⋆ R).holds a := by
      unfold Assn.holds
      rw [view_eq]
      exact hh
    have hF : ∀ s' : St σ, s'.globals = a.globals → s'.memory = a.memory →
        (FrameOp F.M F.K F.e F.fv F.X ⋆ MemExtra F.e F.Y ⋆ ExcExtraM F.e F.Z ⋆
          (RecCells F.Z.cc F.C ⋆ AccCells F.e F.A ⋆ suspA ps ⋆ W i ⋆ R)).holds s' := by
      intro s' hg hm
      exact Assn.holds_congr hg hm (Assn.holds_perm h0 (by unfold Fr.full; ac_rfl))
    have hfl : F.Z.fl = 0#64 := rfC1_flagM hE (hF ⟨l1, a.globals, a.memory, a.ffi⟩ rfl rfl) hpre1
    have hrun : F.Y.run ≠ 0#64 :=
      rfC2_run hE (hF ⟨l2, a.globals, a.memory, a.ffi⟩ rfl rfl) hpre2
    have hrun' : F.Y.run.toNat ≠ 0 := fun h0 => hrun (by bv_omega)
    have hok := hch.head
    have ho1 : (if F.Y.run.toNat = 0 then 0 else 1 : Nat) = 1 := if_neg hrun'
    have ho2 : (if F.Z.fl.toNat = 0 then 1 else 0 : Nat) = 1 := by rw [hfl]; rfl
    have hFmu : F.mu = 4 * F.gas + 3 := by
      unfold Fr.mu
      rw [ho1, ho2]
    refine WPr.wps (rfDispatch_stepC hE hrest hcall a i F (suspA ps ⋆ R) hok
      (by unfold Fr.gas at hgas; omega) (Assn.holds_perm h0 (by ac_rfl))) (fun r hr => ?_)
    rcases hr with ht | ⟨l, g, m, fv', X', Y', Z', rfl, hok', hY', hh', hl, hle, hcase,
      hmem, hcc, hmsg, hee⟩ | ⟨l, g, m, rfl, hl, hpd⟩
    · exact Or.inl ht.stopped
    · obtain ⟨F', hF'⟩ : ∃ F' : Fr, F' = ⟨F.M, F.K, F.e, fv', X', Y', Z', F.C, F.A⟩ := ⟨_, rfl⟩
      have hmuF : F'.mu < F.mu ∧ F'.gas ≤ F.gas := by
        subst hF'
        unfold Fr.mu Fr.gas
        dsimp only
        have ha : (if Y'.run.toNat = 0 then 0 else 1 : Nat) ≤ 1 := by split <;> omega
        have hb : (if Z'.fl.toNat = 0 then 1 else 0 : Nat) ≤ 1 := by split <;> omega
        rw [ho1, ho2]
        refine ⟨?_, hle⟩
        rcases hcase with ⟨_, h2 | h2⟩ | h1
        · omega
        · have : (if Y'.run.toNat = 0 then 0 else 1 : Nat) = 0 := by rw [h2]; rfl
          omega
        · have : (if Z'.fl.toNat = 0 then 1 else 0 : Nat) = 0 := by rw [h1]; rfl
          omega
      refine Or.inr ⟨l, g, m, a.ffi, rfl, ⟨F'.mu + muSum ps, by omega, i, F', ps, R, ?_,
        by omega, Nat.le_refl _, ?_⟩, hl "go" (by decide), hl "done" (by decide)⟩
      · subst hF'
        exact hch.replace ⟨hok', hY', hok.acc⟩ rfl rfl rfl rfl hmem hcc hmsg hee
      · subst hF'
        have h1 : (Fr.full ⟨F.M, F.K, F.e, fv', X', Y', Z', F.C, F.A⟩ ⋆ suspA ps ⋆ W i ⋆
            R).holds (⟨l, g, m, a.ffi⟩ : St σ) := by
          refine Assn.holds_perm hh' ?_
          unfold Fr.full chainRest
          dsimp only
          rw [hcc]
          ac_rfl
        unfold Assn.holds at h1
        rw [view_eq] at h1
        exact h1
    · obtain ⟨i', F', c, e1, e2, e3, e4, e5, e6, e7, e8, e9, hokF', hokc, hlink, hD, hgasP,
        hhP⟩ := hpd
      have hchF' : ChainOk (D i') F' ps :=
        (ChainOk.mono hD hch).replace hokF' e4 e1 e2 e3 e6 e7 e8 e9
      have hmuc := c.mu_le
      have hmuF' := F'.mu_le
      refine Or.inr ⟨l, g, m, a.ffi, rfl, ⟨c.mu + (F'.mu + muSum ps), by
          simp only [muSum] at hmu ⊢
          omega, i', c, F' :: ps, R, ⟨hokc, hlink, hchF'⟩, ?_, ?_, ?_⟩,
        hl "go" (by decide), hl "done" (by decide)⟩
      · simp only [gasSum, List.map_cons, List.sum_cons] at hgas ⊢
        omega
      · simp only [muSum, List.map_cons, List.sum_cons]
        exact Nat.le_refl _
      · have h1 : (c.full ⋆ suspA (F' :: ps) ⋆ W i' ⋆ R).holds (⟨l, g, m, a.ffi⟩ : St σ) :=
          Assn.holds_perm hhP (by simp only [suspA]; ac_rfl)
        unfold Assn.holds at h1
        rw [view_eq] at h1
        exact h1

/-- `run_frames` from a chain of frames of measure at most `k`, with handlers
that may push frames. -/
theorem run_frames_bound_chainC (W : ι → Assn) (D : ι → Word → Prop) (hE : GuestEnv E)
    (hrest : ∀ f, f ∈ restOpsM → f ∉ callOps → HandlerSpecM E f)
    (hcall : ∀ f, f ∈ callOps → HandlerSpecPush E W D f)
    (BD BF : Nat) (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (finish : ∀ (a : St σ) (n : Nat), chainInv W D n a.globals a.memory →
      WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
        (l "go" = some (.word 0#64) ∨
          (l "go" = a.locals "go" ∧ ∃ n', n' < n ∧ chainInv W D n' g m))))
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "run_frames" E.functions = some (parameters, body))
    (s : St σ) (k : Nat) (hI : chainInv W D k s.globals s.memory) (fuel : Nat) (r : Result σ)
    (n : Nat) (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ (k + 1 + 1) * (expCost rfCond + (BD + BF + 200) + 1) + 10 :=
  run_frames_bound_ghost hE (rfChainC W D hE hrest hcall BD BF costD costF finish) parameters
    body hlookup s k hI fuel r n hrun hne

end InitECandidate.Solver.GuestBound
