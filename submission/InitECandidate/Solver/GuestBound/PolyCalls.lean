import InitECandidate.Solver.GuestBound.PolyBuf
import InitECandidate.Solver.GuestBound.Wpc
import InitECandidate.Solver.GuestBound.FqInv
import InitECandidate.Solver.GuestBound.HtabGrow

/-!
# Call rules from "the callee returned" facts

`CalleeRet` says that some run of the callee's body on the evaluated arguments
returned. One lemma per function turns it into that function's specification;
generic rules cover the three ways a call appears (statement, assignment,
declaration).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Some run of a body registered for `f`, on the arguments evaluated in `s`,
returned `vs` with globals `g`, memory `m` and FFI state `ffi`. -/
def CalleeRet (E : Env σ) (s : St σ) (f : FunName) (arguments : List (Exp Word))
    (vs : List (PanValue Word)) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (ffi : FfiState σ) : Prop :=
  ∃ parameters body values calleeLocals l,
    lookupPanFunction f E.functions = some (parameters, body) ∧
    E.evalArgs s arguments = some values ∧
    bindPanValueParameters parameters values = some calleeLocals ∧
    Runs E ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ body (.returned l g m ffi vs)

theorem CalleeReturned.ret {f : FunName} {args : List (Exp Word)} {v : PanValue Word}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} (h : CalleeReturned E s f args v g m ffi) :
    CalleeRet E s f args [v] g m ffi := h

/-- A call statement without destination. -/
theorem WPs.call_ret {f : FunName} {args : List (Exp Word)}
    (h : ∀ vs g m ffi, CalleeRet E s f args vs g m ffi → Q (.normal s.locals g m ffi)) :
    WPs E s (.call (some (none, none)) f args) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  cases rb with
  | returned lr g m ffi vs =>
    simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    · obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
      have : l' = s.locals := funext (fun x => hl x (by simp))
      subst this
      exact Or.inr (h vs _ m ffi ⟨parameters, body, values, cl, lr, hlookup, hvalues, hbind,
        hcallee⟩)
  | raised lr g m f ex v =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m f ev =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inl trivial
  | _ =>
    simp only [CallOutcome] at hout
    exact Or.inl (Stopped.of_error hout)

/-- `x = f(args);` for a local `x`. -/
theorem WPs.callA_ret {f : FunName} {args : List (Exp Word)} {x : VarName}
    (h : ∀ v g m ffi, CalleeRet E s f args [v] g m ffi →
      Q (.normal (updatePanValueMap s.locals x v) g m ffi)) :
    WPs E s (.call (some (some (.local, x), none)) f args) Q := by
  intro r hr
  rcases runs_call_inv (some (some (.local, x))) hr with herr | ⟨parameters, body, values, cl,
    rb, hlookup, hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  cases rb with
  | returned lr g m ffi vs =>
    simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    · cases vs with
      | nil => simp [assignPanValueCallResult] at hassign
      | cons v tl =>
        cases tl with
        | cons _ _ => simp [assignPanValueCallResult] at hassign
        | nil =>
          simp only [assignPanValueCallResult] at hassign
          split at hassign
          · simp only [Option.some.injEq, Prod.mk.injEq] at hassign
            obtain ⟨rfl, rfl⟩ := hassign
            exact Or.inr (h v _ m ffi ⟨parameters, body, values, cl, lr, hlookup, hvalues,
              hbind, hcallee⟩)
          · cases hassign
  | raised lr g m f ex v =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m f ev =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inl trivial
  | _ =>
    simp only [CallOutcome] at hout
    exact Or.inl (Stopped.of_error hout)

/-- A declaring call. -/
theorem WPs.decCall_ret {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word}
    (h : ∀ v g m ffi, CalleeRet E s f args [v] g m ffi →
      WPs E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x sh f args body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  cases rb with
  | returned lr g m ffi vs =>
    cases vs with
    | nil => exact hout.elim
    | cons v rest =>
      cases rest with
      | cons v' rest' => exact hout.elim
      | nil =>
        obtain ⟨r', -, hrun', rfl⟩ := hout
        rcases h v g m ffi ⟨parameters, cbody, values, cl, lr, hlookup, hvalues, hbind,
          hcallee⟩ r' hrun' with hs | hq
        · exact Or.inl hs.restore
        · exact Or.inr hq
  | raised lr g m ffi ex v =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m ffi ev =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | _ => exact hout.elim

/-- A read-only callee leaves globals, memory and the FFI state alone. -/
theorem CalleeRet.quiet {f : FunName} {args : List (Exp Word)} {vs : List (PanValue Word)}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ} (hq : FunKeeps (quietKeeper E) f) (h : CalleeRet E s f args vs g m ffi) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi := by
  obtain ⟨parameters, body, values, cl, l, hlookup, -, -, fuel, n, hrun⟩ := h
  exact hq parameters body hlookup fuel _ _ n hrun

section specs

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem memzero_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {dst nW : Word}
    (h : CalleeRet E s "memzero" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word dst)) (h2 : E.eval s e2 = some (.word nW))
    (hal : dst.toNat % 8 = 0) (hn32 : nW.toNat % 32 = 0)
    (h64 : dst.toNat + nW.toNat + 32 < 2 ^ 64) :
    g = s.globals ∧ ffi = s.ffi ∧ ZeroRel s.memory m dst nW.toNat := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 17 hE.functions (by guest_decl_at 17) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases memzero_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ dst nW
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hal hn32 h64
    hrun with hst | ⟨l', m', heq, hz⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hz⟩

theorem memcpy_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {dst src nW : Word}
    (h : CalleeRet E s "memcpy" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word dst)) (h2 : E.eval s e2 = some (.word src))
    (h3 : E.eval s e3 = some (.word nW)) (P : CpPre dst src nW) :
    g = s.globals ∧ ffi = s.ffi ∧ CopyInv s.memory dst src nW.toNat m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases memcpy_runs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ dst src nW
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) P
    hrun with hst | ⟨l', m', heq, hz⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hz⟩

theorem deg_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {A nW : Word} {c : Nat → Nat}
    (h : CalleeRet E s "fq_poly_deg" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.word A)) (h2 : E.eval s e2 = some (.word nW))
    (hal : A.toNat % 8 = 0) (h64 : A.toNat + 32 * nW.toNat ≤ 2 ^ 64)
    (hpoly : PolyAt s.memory A c nW.toNat) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ d : Word, vs = [.word d] ∧
      ((d = 0#64 - 1#64 ∧ ∀ i, i < nW.toNat → c i = 0) ∨
        (d.toNat < nW.toNat ∧ c d.toNat ≠ 0 ∧ ∀ i, d.toNat < i → i < nW.toNat → c i = 0)) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 680 hE.functions (by guest_decl_at 680) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq_poly_deg_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A nW c
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hal h64 hpoly
    hrun with hst | ⟨l', d, heq, hd⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, d, rfl, hd⟩

theorem fqinv_ret (hE : GuestEnv E) {e1 : Exp Word} {a0 a1 a2 a3 : Word}
    (h : CalleeRet E s "fq_inv" [e1] vs g m ffi)
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hA : limbsVal [a0, a1, a2, a3] ≠ 0) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ d0 d1 d2 d3 : Word,
      vs = [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] < bnP ∧
      limbsVal [d0, d1, d2, d3] * limbsVal [a0, a1, a2, a3] * 2 ^ 256 % bnP = bnR3 % bnP := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 655 hE.functions (by guest_decl_at 655) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq_inv_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ a0 a1 a2 a3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hA
    hrun with hst | ⟨l', d0, d1, d2, d3, heq, hlt, hd⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, d0, d1, d2, d3, rfl, hlt, hd⟩

theorem submul_ret (hE : GuestEnv E) {e1 e2 e3 e4 e5 : Exp Word}
    {A B sW dbW q0 q1 q2 q3 : Word} {ca cb : Nat → Nat}
    (h : CalleeRet E s "fq_poly_submul" [e1, e2, e3, e4, e5] vs g m ffi)
    (h1 : E.eval s e1 = some (.word A)) (h2 : E.eval s e2 = some (.word B))
    (h3 : E.eval s e3 = some (.rStruct [.word q0, .word q1, .word q2, .word q3]))
    (h4 : E.eval s e4 = some (.word sW)) (h5 : E.eval s e5 = some (.word dbW))
    (hQv : limbsVal [q0, q1, q2, q3] < bnP)
    (hA64 : A.toNat + 32 * (sW.toNat + dbW.toNat + 1) ≤ 2 ^ 64)
    (hB64 : B.toNat + 32 * (dbW.toNat + 1) ≤ 2 ^ 64)
    (hdisj : B.toNat + 32 * (dbW.toNat + 1) ≤ A.toNat + 32 * sW.toNat ∨
      A.toNat + 32 * (sW.toNat + dbW.toNat + 1) ≤ B.toNat)
    (hpb : ∀ i, i ≤ dbW.toNat → Fe s.memory (coefAddr B i) (cb i) ∧ cb i < bnP)
    (hpa : ∀ i, i ≤ dbW.toNat → Fe s.memory (coefAddr A (sW.toNat + i)) (ca i) ∧ ca i < bnP) :
    g = s.globals ∧ ffi = s.ffi ∧
      SubMulRel s.memory m A sW.toNat dbW.toNat (limbsVal [q0, q1, q2, q3]) ca cb := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 681 hE.functions (by guest_decl_at 681) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, h4, h5, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq_poly_submul_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    A B sW dbW q0 q1 q2 q3 ca cb
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hQv hA64 hB64 hdisj hpb hpa hrun with hst | ⟨l', m', heq, hz⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hz⟩

theorem heap_mark_ret (hE : GuestEnv E) {pv : Word}
    (h : CalleeRet E s "heap_mark" [] vs g m ffi)
    (hp : s.globals "heap_ptr" = some (.word pv)) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ vs = [.word pv] := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have := heap_mark_runs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ pv hp hrun
  cases this
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem alloc_ret (hE : GuestEnv E) {e : Exp Word} {pv nv : Word}
    (h : CalleeRet E s "alloc" [e] vs g m ffi) (he : E.eval s e = some (.word nv))
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv) :
    vs = [.word pv] ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ qv : Word,
      g = updatePanValueMap s.globals "heap_ptr" (.word qv) ∧
      pv.toNat + nv.toNat ≤ qv.toNat ∧ InHeap qv := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 7 hE.functions (by guest_decl_at 7) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, he, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  obtain ⟨h1, h2, h3, qv, h4, h5, h6, h7⟩ := alloc_runs hE parameters body hlookup
    ⟨cl, s.globals, s.memory, s.ffi⟩ _ pv nv (by rw [← hbind]; simp [updatePanValueMap]) hp
    hpH.1 hrun
  exact ⟨h1, h2, h3, qv, h4, h5, h6, h7⟩

end specs

end InitECandidate.Solver.GuestBound
