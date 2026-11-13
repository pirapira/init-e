import InitECandidate.Solver.GuestBound.LocalOnly
import InitECandidate.Solver.GuestBound.MemFrame

/-!
# `keccak_f1600` writes only the 200-byte state

Generated from the function body: the 25 state words are loaded into locals,
the round loop only computes on locals (`localOnly_sound`), and the 25 stores
go to `stp + 0 … stp + 192`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A word declaration, with the value abstract. -/
theorem WPs.dec_w {x : VarName} {e : Exp Word} {body : Prog Word}
    (h : ∀ w : Word, WPs E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩
      body (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.dec x .one e body) Q := by
  intro r hr
  rw [runs_dec] at hr
  cases hv : E.eval s e with
  | none =>
    rw [hv] at hr
    simp only at hr
    subst hr
    exact Or.inl (Stopped.err s)
  | some v =>
    rw [hv] at hr
    simp only at hr
    split at hr
    · rename_i hsh
      obtain ⟨w, rfl⟩ := word_of_shape_one hsh
      obtain ⟨rb, hrb, rfl⟩ := hr
      rcases h w rb hrb with hs | hq
      · exact Or.inl hs.restore
      · exact Or.inr hq
    · subst hr
      exact Or.inl (Stopped.err s)

/-- A word store at an address inside `[lo, hi)`. -/
theorem WPs.seq_store_rng (hE : GuestEnv E) {a val : Exp Word} {rest : Prog Word}
    {addr : Word} {lo hi : Nat} {m0 : Word → Option (PanValue Word)}
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : ∀ y, E.eval s val = some y → ∃ w : Word, y = .word w)
    (hlo : lo ≤ addr.toNat) (hhi : addr.toNat < hi)
    (hfr : ∀ x : Word, (x.toNat < lo ∨ hi ≤ x.toNat) → s.memory x = m0 x)
    (h : ∀ m, (∀ x : Word, (x.toNat < lo ∨ hi ≤ x.toNat) → m x = m0 x) →
      WPs E ⟨s.locals, s.globals, m, s.ffi⟩ rest Q) :
    WPs E s (.seq (.store a val) rest) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  obtain ⟨fuel, n, hrun⟩ := h1
  rcases store_word_inv hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · cases r1 with
    | error l g m f => simp only at hrest; subst hrest; exact Or.inl trivial
    | _ => cases herr
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  obtain ⟨w, rfl⟩ := hv _ hy
  have hm' := hm w rfl
  subst hm'
  refine h _ (fun x hx => ?_) r hrest
  rw [setCell_ne _ (by intro hh; have := congrArg BitVec.toNat hh; omega)]
  exact hfr x hx

/-- Name the locals of the current state. -/
theorem WPs.named {p : Prog Word}
    (h : ∀ L, L = s.locals → WPs E ⟨L, s.globals, s.memory, s.ffi⟩ p Q) : WPs E s p Q :=
  h s.locals rfl

/-- Postcondition of the keccak state functions: returns 0, memory changed only in the state. -/
def FQ (g : VarName → Option (PanValue Word)) (m0 : Word → Option (PanValue Word))
    (f : FfiState σ) (stp : Word) (r : Result σ) : Prop :=
  ∃ l m', r = .returned l g m' f [.word 0#64] ∧
    ∀ x : Word, (x.toNat < stp.toNat ∨ stp.toNat + 200 ≤ x.toNat) → m' x = m0 x

theorem FQ.restore {g : VarName → Option (PanValue Word)} {m0 : Word → Option (PanValue Word)}
    {f : FfiState σ} {stp : Word} {r : Result σ} (x : VarName)
    (old : Option (PanValue Word)) (h : FQ g m0 f stp r) :
    FQ g m0 f stp (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, m', rfl, hq⟩ := h
  exact ⟨_, m', rfl, hq⟩

/-- A word declaration of a local other than `stp`, with the state kept abstract. -/
theorem decK {g : VarName → Option (PanValue Word)} {m m0 : Word → Option (PanValue Word)}
    {f : FfiState σ} {stp : Word} {x : VarName} {e : Exp Word} {body : Prog Word}
    (hx : (x == "stp") = false)
    (h : ∀ l, l "stp" = some (.word stp) → AllW l → WPs E ⟨l, g, m, f⟩ body (FQ g m0 f stp)) :
    ∀ l, l "stp" = some (.word stp) → AllW l →
      WPs E ⟨l, g, m, f⟩ (.dec x .one e body) (FQ g m0 f stp) := by
  intro l hl ha
  refine WPs.dec_w (fun w => WPs.conseq (h _ ?_ (ha.update x w)) (fun r hr => hr.restore _ _))
  rw [update_lookup]
  have : ("stp" == x) = false := by
    rw [Bool.eq_false_iff] at hx ⊢
    exact fun e => hx (by rw [beq_iff_eq] at e ⊢; exact e.symm)
  rw [this]
  exact hl

/-- A store of a local into the state at a constant offset. -/
theorem storeK (hE : GuestEnv E) {c : Word} {v : VarName} {rest : Prog Word}
    {l g : VarName → Option (PanValue Word)} {m m0 : Word → Option (PanValue Word)}
    {f : FfiState σ} {stp : Word} (hl : l "stp" = some (.word stp)) (hlw : AllW l)
    (hc : c.toNat + 8 ≤ 200) (h64 : stp.toNat + 200 < 2 ^ 64)
    (hfr : ∀ x : Word, (x.toNat < stp.toNat ∨ stp.toNat + 200 ≤ x.toNat) → m x = m0 x)
    (h : ∀ m', (∀ x : Word, (x.toNat < stp.toNat ∨ stp.toNat + 200 ≤ x.toNat) → m' x = m0 x) →
      WPs E ⟨l, g, m', f⟩ rest Q) :
    WPs E ⟨l, g, m, f⟩
      (.seq (.store (.op .add [.var .local "stp", .const c]) (.var .local v)) rest) Q := by
  have e : (stp + c).toNat = stp.toNat + c.toNat := by
    rw [BitVec.toNat_add]
    omega
  exact WPs.seq_store_rng hE (addr := stp + c) (lo := stp.toNat) (hi := stp.toNat + 200)
    (of_eval (eval_addc hE c hl)) (fun y hy => hlw v y (by rwa [evalF_local] at hy))
    (by omega) (by omega) hfr h

set_option maxHeartbeats 16000000 in
/-- The shape of `keccak_f1600`, with the loaded expressions and the round loop abstract. -/
theorem f1600_shape (hE : GuestEnv E) (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 : Exp Word) (loop : Prog Word)
    (hloop : localOnly "stp" loop = true) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (f : FfiState σ) (stp : Word)
    (h64 : stp.toNat + 200 < 2 ^ 64) :
    ∀ l, l "stp" = some (.word stp) → AllW l → WPs E ⟨l, g, m, f⟩ (.dec "a00" .one e0 (.dec "a10" .one e1 (.dec "a20" .one e2 (.dec "a30" .one e3 (.dec "a40" .one e4 (.dec "a01" .one e5 (.dec "a11" .one e6 (.dec "a21" .one e7 (.dec "a31" .one e8 (.dec "a41" .one e9 (.dec "a02" .one e10 (.dec "a12" .one e11 (.dec "a22" .one e12 (.dec "a32" .one e13 (.dec "a42" .one e14 (.dec "a03" .one e15 (.dec "a13" .one e16 (.dec "a23" .one e17 (.dec "a33" .one e18 (.dec "a43" .one e19 (.dec "a04" .one e20 (.dec "a14" .one e21 (.dec "a24" .one e22 (.dec "a34" .one e23 (.dec "a44" .one e24 (.dec "r" .one e25 (.seq loop (.seq (.store (.op .add [.var .local "stp", .const 0#64]) (.var .local "a00")) (.seq (.store (.op .add [.var .local "stp", .const 8#64]) (.var .local "a10")) (.seq (.store (.op .add [.var .local "stp", .const 16#64]) (.var .local "a20")) (.seq (.store (.op .add [.var .local "stp", .const 24#64]) (.var .local "a30")) (.seq (.store (.op .add [.var .local "stp", .const 32#64]) (.var .local "a40")) (.seq (.store (.op .add [.var .local "stp", .const 40#64]) (.var .local "a01")) (.seq (.store (.op .add [.var .local "stp", .const 48#64]) (.var .local "a11")) (.seq (.store (.op .add [.var .local "stp", .const 56#64]) (.var .local "a21")) (.seq (.store (.op .add [.var .local "stp", .const 64#64]) (.var .local "a31")) (.seq (.store (.op .add [.var .local "stp", .const 72#64]) (.var .local "a41")) (.seq (.store (.op .add [.var .local "stp", .const 80#64]) (.var .local "a02")) (.seq (.store (.op .add [.var .local "stp", .const 88#64]) (.var .local "a12")) (.seq (.store (.op .add [.var .local "stp", .const 96#64]) (.var .local "a22")) (.seq (.store (.op .add [.var .local "stp", .const 104#64]) (.var .local "a32")) (.seq (.store (.op .add [.var .local "stp", .const 112#64]) (.var .local "a42")) (.seq (.store (.op .add [.var .local "stp", .const 120#64]) (.var .local "a03")) (.seq (.store (.op .add [.var .local "stp", .const 128#64]) (.var .local "a13")) (.seq (.store (.op .add [.var .local "stp", .const 136#64]) (.var .local "a23")) (.seq (.store (.op .add [.var .local "stp", .const 144#64]) (.var .local "a33")) (.seq (.store (.op .add [.var .local "stp", .const 152#64]) (.var .local "a43")) (.seq (.store (.op .add [.var .local "stp", .const 160#64]) (.var .local "a04")) (.seq (.store (.op .add [.var .local "stp", .const 168#64]) (.var .local "a14")) (.seq (.store (.op .add [.var .local "stp", .const 176#64]) (.var .local "a24")) (.seq (.store (.op .add [.var .local "stp", .const 184#64]) (.var .local "a34")) (.seq (.store (.op .add [.var .local "stp", .const 192#64]) (.var .local "a44")) (.return (.const 0#64))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (FQ g m f stp) := by
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  refine decK (by decide) ?_
  intro l0 hl0 hlw0
  refine WPs.seqG (fun a => ∃ l, a = ⟨l, g, m, f⟩ ∧ l "stp" = some (.word stp) ∧ AllW l)
    (WPs.conseq (localOnly_sound "stp" loop hloop _) (by
      rintro r ⟨l, rfl, hx, hw⟩
      exact ⟨l, rfl, hx.trans hl0, hw hlw0⟩)) ?_
  rintro _ ⟨l, rfl, hl, hlw⟩
  have hfr : ∀ x : Word, (x.toNat < stp.toNat ∨ stp.toNat + 200 ≤ x.toNat) → m x = m x :=
    fun _ _ => rfl
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  refine storeK hE hl hlw (by decide) h64 hfr (fun m' hfr => ?_)
  exact WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ⟨_, _, rfl, hfr⟩

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem keccak_f1600_frame (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "keccak_f1600" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (stp : Word) (hstp : s.locals "stp" = some (.word stp))
    (hall : AllW s.locals) (h64 : stp.toNat + 200 < 2 ^ 64) (h : Runs E s body r) :
    Stopped r ∨ FQ s.globals s.memory s.ffi stp r := by
  have hbody := (fun_of_index 101 hE.functions (by guest_decl_at 101) (by decide +kernel)
    hlookup).1
  subst hbody
  refine f1600_shape hE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ s.globals s.memory s.ffi stp h64
    s.locals hstp hall r h
  decide +kernel

end InitECandidate.Solver.GuestBound
