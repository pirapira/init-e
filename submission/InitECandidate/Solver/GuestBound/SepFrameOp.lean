import InitECandidate.Solver.GuestBound.SepPushWord

/-!
# The scratch region of a frame, in a form every stack step preserves

A frame owns every address of its scratch interval `[pv, M)`: the tracked
cells (a fixed set `K`, owned elsewhere), the stack buffer, and the rest,
`JunkW M K pv base cap`. Allocations lower `pv`, so the junk grows; when the
stack moves, the old buffer joins the junk and the new one leaves it
(`junk_realloc`). When the frame ends, the whole interval can be given back.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- The addresses satisfying `P` are owned, with unknown content. -/
def Assn.OwnsW (P : Word → Prop) : Assn := Assn.Owns (fun k => ∃ x, k = .mem x ∧ P x)

theorem Assn.ownsW_split {P P1 P2 : Word → Prop} (hS : ∀ x, P x ↔ P1 x ∨ P2 x)
    (hd : ∀ x, P1 x → P2 x → False) : Assn.OwnsW P = (Assn.OwnsW P1 ⋆ Assn.OwnsW P2) := by
  refine Assn.owns_split (fun k => ?_) (fun k => ?_)
  · constructor
    · rintro ⟨x, rfl, hx⟩
      rcases (hS x).mp hx with h | h
      · exact Or.inl ⟨x, rfl, h⟩
      · exact Or.inr ⟨x, rfl, h⟩
    · rintro (⟨x, rfl, hx⟩ | ⟨x, rfl, hx⟩)
      · exact ⟨x, rfl, (hS x).mpr (Or.inl hx)⟩
      · exact ⟨x, rfl, (hS x).mpr (Or.inr hx)⟩
  · rintro ⟨x, rfl, hx⟩ ⟨y, hy, hy'⟩
    cases hy
    exact hd x hx hy'

theorem Assn.range_eq_ownsW (a b : Word) :
    Assn.Range a b = Assn.OwnsW (fun x => a.toNat ≤ x.toNat ∧ x.toNat < b.toNat) := rfl

/-- The part of a frame's scratch interval `[pv, M)` that is neither the stack
buffer nor a tracked cell. -/
def JunkW (M : Word) (K : Word → Prop) (pv base cap : Word) : Assn :=
  Assn.OwnsW (fun x => pv.toNat ≤ x.toNat ∧ x.toNat < M.toNat ∧
    ¬ (base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + 32 * cap.toNat) ∧ ¬ K x)

/-- The stack moved to a fresh block `[qv, qv + 32·nc)` below the old scratch
pointer: the unused tail of the allocation and the old buffer join the junk. -/
theorem junk_realloc {M : Word} {K : Word → Prop} {pv base cap qv nc : Word}
    (hT : (qv + 32#64 * nc).toNat = qv.toNat + 32 * nc.toNat)
    (hhi : (base + 32#64 * cap).toNat = base.toNat + 32 * cap.toNat)
    (hq : qv.toNat + 32 * nc.toNat ≤ pv.toNat) (hpb : pv.toNat ≤ base.toNat)
    (hbM : base.toNat + 32 * cap.toNat ≤ M.toNat)
    (hKpv : ∀ x, K x → pv.toNat ≤ x.toNat)
    (hKst : ∀ x, K x → ¬ (base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + 32 * cap.toNat)) :
    (Assn.Range (qv + 32#64 * nc) pv ⋆ Assn.Range base (base + 32#64 * cap) ⋆
      JunkW M K pv base cap) = JunkW M K qv qv nc := by
  classical
  rw [Assn.range_eq_ownsW, Assn.range_eq_ownsW]
  unfold JunkW
  rw [← Assn.ownsW_split (P := fun x => (base.toNat ≤ x.toNat ∧
      x.toNat < (base + 32#64 * cap).toNat) ∨ (pv.toNat ≤ x.toNat ∧ x.toNat < M.toNat ∧
      ¬ (base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + 32 * cap.toNat) ∧ ¬ K x))
    (fun x => Iff.rfl) (fun x h1 h2 => h2.2.2.1 ⟨h1.1, by omega⟩)]
  refine (Assn.ownsW_split (fun x => ?_) (fun x h1 h2 => ?_)).symm
  · constructor
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hx : x.toNat < pv.toNat
      · exact Or.inl ⟨by omega, hx⟩
      · right
        by_cases hb : base.toNat ≤ x.toNat ∧ x.toNat < base.toNat + 32 * cap.toNat
        · exact Or.inl ⟨hb.1, by omega⟩
        · exact Or.inr ⟨by omega, h2, hb, h4⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨by omega, by omega, by omega, fun hk => by have := hKpv x hk; omega⟩
      · exact ⟨by omega, by omega, by omega, fun hk => hKst x hk ⟨h1, by omega⟩⟩
      · exact ⟨by omega, h2, by omega, h4⟩
  · rcases h2 with ⟨h2, h3⟩ | ⟨h2, -⟩
    · omega
    · omega

/-- An allocation that is not used for the stack: the block joins the junk. -/
theorem junk_alloc {M : Word} {K : Word → Prop} {pv base cap qv : Word}
    (hq : qv.toNat ≤ pv.toNat) (hpb : pv.toNat ≤ base.toNat) (hpM : pv.toNat ≤ M.toNat)
    (hKpv : ∀ x, K x → pv.toNat ≤ x.toNat) :
    (Assn.Range qv pv ⋆ JunkW M K pv base cap) = JunkW M K qv base cap := by
  rw [Assn.range_eq_ownsW]
  unfold JunkW
  refine (Assn.ownsW_split (fun x => ?_) (fun x h1 h2 => ?_)).symm
  · constructor
    · rintro ⟨h1, h2, h3, h4⟩
      by_cases hx : x.toNat < pv.toNat
      · exact Or.inl ⟨h1, hx⟩
      · exact Or.inr ⟨by omega, h2, h3, h4⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨h1, by omega, by omega, fun hk => by have := hKpv x hk; omega⟩
      · exact ⟨by omega, h2, h3, h4⟩
  · omega

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The frame fields a stack handler changes. -/
structure OpSt where
  sp : Word
  cap : Word
  base : Word
  pv : Word
  gl : Word
  used : Word
  pc : Word

/-- The pure side of the frame invariant for stack handlers: the stack bounds,
the stack buffer inside the scratch interval `[pv, M)`, and the tracked cells
`K` above `pv` and outside the stack buffer. -/
structure FrameOk (M : Word) (K : Word → Prop) (fv : Word) (X : OpSt) : Prop where
  ok : StackOk X.sp X.cap X.base X.pv fv
  pb : X.pv.toNat ≤ X.base.toNat
  bM : X.base.toNat + 32 * X.cap.toNat ≤ M.toNat
  Kpv : ∀ x, K x → X.pv.toNat ≤ x.toNat
  Kst : ∀ x, K x → ¬ (X.base.toNat ≤ x.toNat ∧ x.toNat < X.base.toNat + 32 * X.cap.toNat)

/-- What a stack handler owns: `OpW` and the junk of the scratch interval. -/
def FrameOp (M : Word) (K : Word → Prop) (e fv : Word) (X : OpSt) : Assn :=
  OpW e X.sp X.cap X.base X.pv fv X.gl X.used X.pc ⋆ JunkW M K X.pv X.base X.cap

/-- Since `X0`: at least `n` gas spent, and the scratch pointer not raised. -/
def Adv (X X0 : OpSt) (n : Nat) : Prop :=
  X.gl.toNat + n ≤ X0.gl.toNat ∧ X.pv.toNat ≤ X0.pv.toNat

/-- The handler stopped early: a trap, or `EvmErr` raised with the frame
invariant intact. -/
def Abort (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (ffi : FfiState σ) (X0 : OpSt)
    (r : Result σ) : Prop :=
  Trap r ∨ ∃ X n, FrameOk M K fv X ∧ Adv X X0 n ∧ (FrameOp M K e fv X ⋆ R).holds r.st ∧
    ∃ l g m code, r = .raised l g m ffi "EvmErr" (.word code)

/-- What a stack handler guarantees: an abort, or it returned 0 with the frame
invariant intact and strictly less gas left. -/
def HandlerQ (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (ffi : FfiState σ)
    (X0 : OpSt) (r : Result σ) : Prop :=
  Abort M K e fv R ffi X0 r ∨ ∃ X n, FrameOk M K fv X ∧ Adv X X0 n ∧ 0 < n ∧
    (FrameOp M K e fv X ⋆ R).holds r.st ∧ ∃ l g m, r = .returned l g m ffi [.word 0#64]

theorem Abort.restore {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {ffi : FfiState σ}
    {X0 : OpSt} {x : VarName} {old : Option (PanValue Word)} {r : Result σ}
    (h : Abort M K e fv R ffi X0 r) : Abort M K e fv R ffi X0 (restorePanValueFfiLocal x old r) := by
  rcases h with ht | ⟨X, n, hok, hp, hh, hex⟩
  · exact Or.inl ht.restore
  · refine Or.inr ⟨X, n, hok, hp, ?_, ?_⟩
    · unfold Assn.holds at hh ⊢
      rw [restore_view]
      exact hh
    · obtain ⟨l, g, m, code, rfl⟩ := hex
      exact ⟨_, _, _, _, rfl⟩

/-- A postcondition that accepts every abort. -/
def AcceptsAbort (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (ffi : FfiState σ)
    (X0 : OpSt) (Q : Result σ → Prop) : Prop :=
  ∀ r, Abort M K e fv R ffi X0 r → Q r

theorem AcceptsAbort.handler {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {ffi : FfiState σ} {X0 : OpSt} :
    AcceptsAbort M K e fv R ffi X0 (HandlerQ M K e fv R ffi X0) :=
  fun _ h => Or.inl h

theorem AcceptsAbort.restore {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {ffi : FfiState σ} {X0 : OpSt} {x : VarName} {old : Option (PanValue Word)}
    (h : AcceptsAbort M K e fv R ffi X0 Q) :
    AcceptsAbort M K e fv R ffi X0 (fun r => Q (restorePanValueFfiLocal x old r)) :=
  fun _ hr => h _ hr.restore

/-- `charge_gas(G); rest` under the frame invariant. -/
theorem op_charge (hE : GuestEnv E) (G : Word) {q : Prog Word} {M : Word} {K : Word → Prop}
    {e fv : Word} {R : Assn} {X0 X : OpSt} {n : Nat} (hok : FrameOk M K fv X)
    (hp : Adv X X0 n) (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hab : AcceptsAbort M K e fv R s.ffi X0 Q)
    (hq : ∀ g m, FrameOk M K fv { X with gl := X.gl - G, used := X.used + G } →
      Adv { X with gl := X.gl - G, used := X.used + G } X0 (n + G.toNat) →
      (FrameOp M K e fv { X with gl := X.gl - G, used := X.used + G } ⋆ R).holds
        (⟨s.locals, g, m, s.ffi⟩ : St σ) → WPr E ⟨s.locals, g, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "charge_gas" [.const G]) q) Q := by
  refine WPr.seq_charge hE G (Assn.holds_assoc_r h) (fun r ht => hab r (Or.inl ht))
    (fun hlt l g m hk => ?_) (fun hge g m hk => ?_)
  · exact hab _ (Or.inr ⟨X, n, hok, hp, Assn.holds_assoc_l (Assn.holds_congr rfl rfl hk),
      _, _, _, _, rfl⟩)
  · refine hq g m ⟨hok.ok, hok.pb, hok.bM, hok.Kpv, hok.Kst⟩ ⟨?_, hp.2⟩
      (Assn.holds_assoc_l (P := OpW e X.sp X.cap X.base X.pv fv (X.gl - G) (X.used + G) X.pc) hk)
    have h1 := hp.1
    have : (X.gl - G).toNat + G.toNat = X.gl.toNat := by
      have : ¬ X.gl.toNat < G.toNat := fun h => hge (BitVec.lt_def.mpr h)
      bv_omega
    show (X.gl - G).toNat + (n + G.toNat) ≤ X0.gl.toNat
    omega

/-- `var x = stack_pop(); rest` under the frame invariant. -/
theorem op_pop_step (hE : GuestEnv E) {x : VarName} {sh : Shape} {body : Prog Word} {M : Word}
    {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt} {n : Nat}
    (hok : FrameOk M K fv X) (hp : Adv X X0 n) (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hab : AcceptsAbort M K e fv R s.ffi X0 Q)
    (hq : ∀ v g m, FrameOk M K fv { X with sp := X.sp - 1#64 } →
      Adv { X with sp := X.sp - 1#64 } X0 n →
      (FrameOp M K e fv { X with sp := X.sp - 1#64 } ⋆ R).holds
        (⟨updatePanValueMap s.locals x v, g, m, s.ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x v, g, m, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x sh "stack_pop" [] body) Q := by
  refine WPr.decCall_framedT (Assn.holds_focus (OpW_sp ..) (Assn.holds_assoc_r h))
    (fun p b v cl a1 a2 a3 => (stack_pop_hc hE e X.sp p b v cl a1 a2 a3).toT)
    (fun r ht => hab r (Or.inl ht)) ?_ ?_
  · intro l g m ffi v hh
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC
    obtain ⟨⟨hne, _, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
    injection hC with _ _ _ hf _
    subst hf
    have hsp : (X.sp - 1#64).toNat ≤ X.cap.toNat := by
      have := hok.ok.sp_le
      have : X.sp.toNat ≠ 0 := fun h0 => hne (by bv_omega)
      have : (X.sp - 1#64).toNat = X.sp.toNat - 1 := by bv_omega
      omega
    exact hq v g m ⟨⟨hok.ok.cap_pos, hok.ok.cap_le, hsp, hok.ok.base_al, hok.ok.base_hi,
      hok.ok.fp, hok.ok.pv_hi⟩, hok.pb, hok.bM, hok.Kpv, hok.Kst⟩ hp
      (Assn.holds_assoc_l (P := OpW e (X.sp - 1#64) X.cap X.base X.pv fv X.gl X.used X.pc)
        (Assn.holds_unfocus (OpW_sp ..) hk))
  · intro l g m ffi exc v _ hh
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      exact hab _ (Or.inr ⟨X, n, hok, hp, Assn.holds_assoc_l
        (Assn.holds_unfocus (OpW_sp ..) (Assn.holds_congr rfl rfl hk)), _, _, _, _, rfl⟩)
    · obtain ⟨⟨-, _, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC

/-- `pc_add(n); rest` under the frame invariant. -/
theorem op_pc_add (hE : GuestEnv E) {args : List (Exp Word)} {q : Prog Word} {d : Word}
    {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt} {n : Nat}
    (hargs : E.evalArgs s args = some [.word d])
    (hok : FrameOk M K fv X) (hp : Adv X X0 n) (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hab : AcceptsAbort M K e fv R s.ffi X0 Q)
    (hq : ∀ g m, FrameOk M K fv { X with pc := X.pc + d } → Adv { X with pc := X.pc + d } X0 n →
      (FrameOp M K e fv { X with pc := X.pc + d } ⋆ R).holds (⟨s.locals, g, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, g, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "pc_add" args) q) Q := by
  refine WPr.seq_call_framedT (Assn.holds_focus (OpW_pc ..) (Assn.holds_assoc_r h))
    (fun p b v cl a1 a2 a3 => (pc_add_hc hE hargs e X.pc p b v cl a1 a2 a3).toT)
    (fun r ht => hab r (Or.inl ht)) ?_ ?_
  · intro l g m ffi vs hh
    obtain ⟨⟨_, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
    injection hC with _ _ _ hf _
    subst hf
    exact hq g m ⟨hok.ok, hok.pb, hok.bM, hok.Kpv, hok.Kst⟩ hp
      (Assn.holds_assoc_l (P := OpW e X.sp X.cap X.base X.pv fv X.gl X.used (X.pc + d))
        (Assn.holds_unfocus (OpW_pc ..) hk))
  · intro l g m ffi exc v _ hh
    obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
    cases hC

theorem HandlerQ.restore {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {ffi : FfiState σ} {X0 : OpSt} {x : VarName} {old : Option (PanValue Word)} {r : Result σ}
    (h : HandlerQ M K e fv R ffi X0 r) :
    HandlerQ M K e fv R ffi X0 (restorePanValueFfiLocal x old r) := by
  rcases h with ha | ⟨X, n, hok, hp, hn, hh, hex⟩
  · exact Or.inl ha.restore
  · refine Or.inr ⟨X, n, hok, hp, hn, ?_, restore_returned_ex hex⟩
    unfold Assn.holds at hh ⊢
    rw [restore_view]
    exact hh

/-- A postcondition that accepts everything a handler may end with. -/
def AcceptsH (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (ffi : FfiState σ)
    (X0 : OpSt) (Q : Result σ → Prop) : Prop :=
  ∀ r, HandlerQ M K e fv R ffi X0 r → Q r

theorem AcceptsH.refl {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {ffi : FfiState σ} {X0 : OpSt} : AcceptsH M K e fv R ffi X0 (HandlerQ M K e fv R ffi X0) :=
  fun _ h => h

theorem AcceptsH.restore {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {ffi : FfiState σ} {X0 : OpSt} {x : VarName} {old : Option (PanValue Word)}
    (h : AcceptsH M K e fv R ffi X0 Q) :
    AcceptsH M K e fv R ffi X0 (fun r => Q (restorePanValueFfiLocal x old r)) :=
  fun _ hr => h _ hr.restore

theorem AcceptsH.abort {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn}
    {ffi : FfiState σ} {X0 : OpSt} (h : AcceptsH M K e fv R ffi X0 Q) :
    AcceptsAbort M K e fv R ffi X0 Q :=
  fun r ha => h r (Or.inl ha)

/-- `return 0` at the end of a handler that spent gas. -/
theorem op_return {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt} {n : Nat}
    (hok : FrameOk M K fv X) (hp : Adv X X0 n) (hn : 0 < n)
    (h : (FrameOp M K e fv X ⋆ R).holds s) (hQ : AcceptsH M K e fv R s.ffi X0 Q) :
    WPr E s (.return (.const 0#64)) Q :=
  WPr.ret (w := 0#64) (of_eval (eval_const _ _))
    (hQ _ (Or.inr ⟨X, n, hok, hp, hn, Assn.holds_congr rfl rfl h, _, _, _, rfl⟩))

/-- `var x = f(args); rest` for a callee that changes nothing and never raises. -/
theorem op_quiet {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt}
    (hq : FunKeeps (quietKeeper E) f) (hr : FunRaises E (fun _ => false) f)
    (h : (FrameOp M K e fv X ⋆ R).holds s) (hab : AcceptsAbort M K e fv R s.ffi X0 Q)
    (hk : ∀ v, panShapeMatches (panValueShape E.structs v) sh = true →
      (FrameOp M K e fv X ⋆ R).holds
        (⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x sh f args body) Q :=
  WPr.decCall_quiet hq hr (fun r ht => hab r (Or.inl ht))
    (fun v hsh => hk v hsh (Assn.holds_congr rfl rfl h))

/-- `var x = e; rest` under the frame invariant. -/
theorem op_dec {x : VarName} {sh : Shape} {ex : Exp Word} {body : Prog Word} {M : Word}
    {K : Word → Prop} {e fv : Word} {R : Assn} {X : OpSt}
    (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hk : ∀ v, (FrameOp M K e fv X ⋆ R).holds
        (⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.dec x sh ex body) Q :=
  WPr.dec_ev (fun v _ => hk v (Assn.holds_congr rfl rfl h))

/-- A push (`stack_push` or a wrapper of it) under the frame invariant. When
the stack moves, the leftovers are folded into the junk. -/
theorem op_push {pf : FunName} {args : List (Exp Word)} {q : Prog Word}
    {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt} {n : Nat}
    (hok : FrameOk M K fv X) (hp : Adv X X0 n) (h : (FrameOp M K e fv X ⋆ R).holds s)
    (hab : AcceptsAbort M K e fv R s.ffi X0 Q)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction pf E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (StackW e X.sp X.cap X.base X.pv fv)
        (StackPushPost s.ffi e X.sp X.cap X.base X.pv fv))
    (hq : ∀ X' g m, FrameOk M K fv X' → Adv X' X0 n →
      (FrameOp M K e fv X' ⋆ R).holds (⟨s.locals, g, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, g, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) pf args) q) Q := by
  refine WPr.seq_call_framedT (Assn.holds_focus (OpW_stack ..) (Assn.holds_assoc_r h)) hc
    (fun r ht => hab r (Or.inl ht)) ?_ ?_
  · intro l g m ffi vs hh
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨hlt, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
      injection hC with _ _ _ hf _
      subst hf
      have hsp : (X.sp + 1#64).toNat ≤ X.cap.toNat := by
        have := hok.ok.cap_le
        have : (X.sp + 1#64).toNat = X.sp.toNat + 1 := by bv_omega
        omega
      exact hq { X with sp := X.sp + 1#64 } g m
        ⟨⟨hok.ok.cap_pos, hok.ok.cap_le, hsp, hok.ok.base_al, hok.ok.base_hi, hok.ok.fp,
          hok.ok.pv_hi⟩, hok.pb, hok.bM, hok.Kpv, hok.Kst⟩ hp
        (Assn.holds_assoc_l (P := OpW e (X.sp + 1#64) X.cap X.base X.pv fv X.gl X.used X.pc)
          (Assn.holds_unfocus (OpW_stack ..) hk))
    · obtain ⟨qv, hh⟩ := Assn.holdsV_ex.mp hh
      obtain ⟨nc, hh⟩ := Assn.holdsV_ex.mp hh
      obtain ⟨⟨⟨okn, hle, -⟩, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
      injection hC with _ _ _ hf _
      subst hf
      have hT : (qv + 32#64 * nc).toNat = qv.toNat + 32 * nc.toNat := by
        have := okn.cap_le
        have := okn.base_hi
        bv_omega
      have hhi : (X.base + 32#64 * X.cap).toNat = X.base.toNat + 32 * X.cap.toNat := by
        have := hok.ok.cap_le
        have := hok.ok.base_hi
        bv_omega
      have ej := junk_realloc (M := M) (K := K) hT hhi hle hok.pb hok.bM hok.Kpv hok.Kst
      have hpb := hok.pb
      have hbM := hok.bM
      refine hq ⟨X.sp + 1#64, nc, qv, qv, X.gl, X.used, X.pc⟩ g m
        ⟨okn, Nat.le_refl _, by show qv.toNat + 32 * nc.toNat ≤ M.toNat; omega,
          fun x hx => by have := hok.Kpv x hx; show qv.toNat ≤ x.toNat; omega,
          fun x hx hin => by
            have := hok.Kpv x hx
            have h1 : x.toNat < qv.toNat + 32 * nc.toNat := hin.2
            omega⟩
        ⟨hp.1, by show qv.toNat ≤ X0.pv.toNat; have := hp.2; omega⟩ ?_
      show ((OpW e (X.sp + 1#64) nc qv qv fv X.gl X.used X.pc ⋆ JunkW M K qv qv nc) ⋆ R).holds _
      exact Assn.holds_perm hk (by rw [OpW_stack, ← ej]; ac_rfl)
  · intro l g m ffi exc v _ hh
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨-, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      exact hab _ (Or.inr ⟨X, n, hok, hp, Assn.holds_assoc_l
        (Assn.holds_unfocus (OpW_stack ..) (Assn.holds_congr rfl rfl hk)), _, _, _, _, rfl⟩)
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC
    · obtain ⟨qv, hh⟩ := Assn.holdsV_ex.mp hh
      obtain ⟨nc, hh⟩ := Assn.holdsV_ex.mp hh
      obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC

/-- `stack_push(a)` at a call site, when any value of `a` is a four-word struct. -/
theorem stack_push_any_hc (hE : GuestEnv E) {a : Exp Word}
    (harg : ∀ v, E.eval s a = some v →
      ∃ w0 w1 w2 w3 : Word, v = .rStruct [.word w0, .word w1, .word w2, .word w3])
    (e sp cap base pv fv : Word) (ok : StackOk sp cap base pv fv) :
    ∀ parameters cbody values cl,
      lookupPanFunction "stack_push" E.functions = some (parameters, cbody) →
      E.evalArgs s [a] = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (StackW e sp cap base pv fv)
        (StackPushPost s.ffi e sp cap base pv fv) := by
  intro parameters cbody values cl hlk hvalues hbind
  obtain ⟨v, hv, rfl⟩ := evalArgs1_inv hvalues
  obtain ⟨w0, w1, w2, w3, rfl⟩ := harg v hv
  exact stack_push_hc hE (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) hvalues e sp cap base pv
    fv ok parameters cbody _ cl hlk hvalues hbind

/-- A four-word load has a four-word value. -/
theorem arg4_load (hE : GuestEnv E) (a : Exp Word) :
    ∀ v, E.eval s (.load (.comb [.one, .one, .one, .one]) a) = some v →
      ∃ w0 w1 w2 w3 : Word, v = .rStruct [.word w0, .word w1, .word w2, .word w3] := by
  intro v hv
  obtain ⟨addr, w0, w1, w2, w3, -, rfl, -⟩ := eval_load_four hE hv
  exact ⟨w0, w1, w2, w3, rfl⟩

/-- A local holding a four-word value. -/
theorem arg4_local {x : VarName} {w0 w1 w2 w3 : Word}
    (hx : s.locals x = some (.rStruct [.word w0, .word w1, .word w2, .word w3])) :
    ∀ v, E.eval s (.var .local x) = some v →
      ∃ w0 w1 w2 w3 : Word, v = .rStruct [.word w0, .word w1, .word w2, .word w3] := by
  intro v hv
  rw [evalF_local, hx] at hv
  exact ⟨w0, w1, w2, w3, (Option.some.inj hv).symm⟩

/-- A local whose value has the four-word shape. -/
theorem arg4_shape {x : VarName} {v : PanValue Word} (hx : s.locals x = some v)
    (hsh : panShapeMatches (panValueShape E.structs v) (.comb [.one, .one, .one, .one]) = true) :
    ∀ v', E.eval s (.var .local x) = some v' →
      ∃ w0 w1 w2 w3 : Word, v' = .rStruct [.word w0, .word w1, .word w2, .word w3] := by
  obtain ⟨w0, w1, w2, w3, rfl⟩ := struct4_of_shape hsh
  exact arg4_local hx

end InitECandidate.Solver.GuestBound
