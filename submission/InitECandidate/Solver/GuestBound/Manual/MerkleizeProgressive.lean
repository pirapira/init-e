import InitECandidate.Solver.GuestBound.MemCpy
import InitECandidate.Solver.GuestBound.ShapeFrame

/-!
# The first loop of `merkleize_progressive`

Each round calls `merkleize(…, roots + k * 32)` and then increments `k`.
A returning `merkleize` ends with a `memcpy` of 32 bytes to its output, and a
successful store lies below the end of the heap. So the address
`roots + k * 32` stays in the heap while the loop runs, which bounds the
number of rounds by the size of the heap. No assumption on `n` is needed.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Sequencing when the first part may also leave. -/
theorem WPs.seqG {p q : Prog Word} (R : St σ → Prop)
    (hp : WPs E s p (fun r1 => match r1 with
      | .normal l g m f => R ⟨l, g, m, f⟩
      | r1 => Q r1))
    (hq : ∀ s', R s' → WPs E s' q Q) : WPs E s (.seq p q) Q := by
  intro r hr
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hr
  rcases hp r1 h1 with hs | hpost
  · cases r1 with
    | normal l g m f => exact absurd hs Stopped.not_normal
    | _ => simp only at hrest; subst hrest; exact Or.inl hs
  · cases r1 with
    | normal l g m f => exact hq _ hpost r hrest
    | _ => simp only at hrest; subst hrest; exact Or.inr hpost

theorem WPs.of_true {p : Prog Word} (h : ∀ r, Q r) : WPs E s p Q := fun r _ => Or.inr (h r)

/-- A declaring call, whatever the callee does. -/
theorem WPs.decCall_any {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word}
    (h : ∀ v g m ffi, WPs E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body
      (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x sh f args body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, -, -, -, -, hout⟩
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
        rcases h v g m ffi r' hrun' with hs | hq
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

/-- A declaration, whatever its value. -/
theorem WPs.dec_any {x : VarName} {sh : Shape} {e : Exp Word} {body : Prog Word}
    (h : ∀ v, WPs E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body
      (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.dec x sh e body) Q := by
  intro r hr
  rw [runs_dec] at hr
  cases hv : E.eval s e with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some v =>
    rw [hv] at hr
    simp only at hr
    split at hr
    · obtain ⟨rb, hrb, rfl⟩ := hr
      rcases h v rb hrb with hs | hq
      · exact Or.inl hs.restore
      · exact Or.inr hq
    · subst hr
      exact Or.inl (Stopped.err s)

/-- A call statement without destination, whatever the callee does. -/
theorem WPs.call_any {f : FunName} {args : List (Exp Word)}
    (h : ∀ g m ffi, Q (.normal s.locals g m ffi)) :
    WPs E s (.call (some (none, none)) f args) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, -, -, -, -,
    hout⟩
  · exact Or.inl (Stopped.of_error herr)
  cases rb with
  | returned lr g m ffi vs =>
    simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    · obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
      have : l' = s.locals := funext (fun x => hl x (by simp))
      subst this
      exact Or.inr (h _ _ _)
  | raised lr g m ffi ex v =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m ffi ev =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inl trivial
  | _ =>
    simp only [CallOutcome] at hout
    exact Or.inl (Stopped.of_error hout)

/-- An assignment to a local, whatever the value. -/
theorem WPs.assign_any {x : VarName} {e : Exp Word}
    (h : ∀ v, Q (.normal (updatePanValueMap s.locals x v) s.globals s.memory s.ffi)) :
    WPs E s (.assign .local x e) Q := by
  intro r hr
  rw [runs_assign_local] at hr
  subst hr
  split
  · split
    · exact Or.inr (h _)
    · exact Or.inl (Stopped.err s)
  · exact Or.inl (Stopped.err s)

/-- `p` keeps local `x` and does not leave. -/
def Keeps (E : Env σ) (x : VarName) (o : Option (PanValue Word)) (p : Prog Word) : Prop :=
  ∀ s : St σ, s.locals x = o →
    WPs E s p (fun r => ∃ l g m f, r = .normal l g m f ∧ l x = o)

variable {x : VarName} {o : Option (PanValue Word)}

theorem Keeps.call {f : FunName} {args : List (Exp Word)} :
    Keeps E x o (.call (some (none, none)) f args) :=
  fun _ hs => WPs.call_any (fun _ _ _ => ⟨_, _, _, _, rfl, hs⟩)

theorem Keeps.assign {y : VarName} {e : Exp Word} (hy : (x == y) = false) :
    Keeps E x o (.assign .local y e) := by
  intro s hs
  refine WPs.assign_any (fun v => ⟨_, _, _, _, rfl, ?_⟩)
  simp only [update_lookup, hy]
  exact hs

theorem Keeps.seq {p q : Prog Word} (hp : Keeps E x o p) (hq : Keeps E x o q) :
    Keeps E x o (.seq p q) :=
  fun s hs => WPs.seq (fun a => a.locals x = o) (hp s hs) (fun a ha => hq a ha)

theorem Keeps.while {c : Exp Word} {p : Prog Word} (hp : Keeps E x o p) :
    Keeps E x o (.while c p) :=
  fun s hs => WPs.loop (I := fun a => a.locals x = o) hs (fun a ha _ => hp a ha)
    (fun a _ ha _ => ⟨_, _, _, _, rfl, ha⟩)

theorem Keeps.dec {y : VarName} {sh : Shape} {e : Exp Word} {p : Prog Word}
    (hy : (x == y) = false) (hp : Keeps E x o p) : Keeps E x o (.dec y sh e p) := by
  intro s hs
  refine WPs.dec_any (fun v => ?_)
  refine (hp _ (by simp only [update_lookup, hy]; exact hs)).conseq ?_
  rintro r ⟨l, g, m, f, rfl, hl⟩
  refine ⟨_, _, _, _, rfl, ?_⟩
  simp only [restorePanValueLocal, hy]
  exact hl

local notation "MK_LA" => ((Prog.while (Exp.cmp Cmp.less (Exp.const (BitVec.ofNat 64 1)) (Exp.var VarKind.local "cur")) (Prog.dec "half" Shape.one (Exp.shift Shift.lsr (Exp.var VarKind.local "cur") (Exp.const (BitVec.ofNat 64 1))) (Prog.dec "j" Shape.one (Exp.const (BitVec.ofNat 64 0)) (Prog.seq (Prog.while (Exp.cmp Cmp.less (Exp.var VarKind.local "j") (Exp.var VarKind.local "half")) (Prog.seq (Prog.call (some (none, none)) "sha256_pair" [(Exp.op BinOp.add [(Exp.var VarKind.local "buf"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 64))])]), (Exp.op BinOp.add [(Exp.var VarKind.local "buf"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 64))]), (Exp.const (BitVec.ofNat 64 32))]), (Exp.op BinOp.add [(Exp.var VarKind.local "buf"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 32))])])]) (Prog.assign VarKind.local "j" (Exp.op BinOp.add [(Exp.var VarKind.local "j"), (Exp.const (BitVec.ofNat 64 1))])))) (Prog.assign VarKind.local "cur" (Exp.var VarKind.local "half")))))) : Prog Word)

local notation "MK_LB" => ((Prog.while (Exp.cmp Cmp.less (Exp.var VarKind.local "d") (Exp.var VarKind.local "target")) (Prog.seq (Prog.call (some (none, none)) "sha256_pair" [(Exp.var VarKind.local "buf"), (Exp.op BinOp.add [(Exp.var VarKind.global "zero_hashes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "d"), (Exp.const (BitVec.ofNat 64 32))])]), (Exp.var VarKind.local "buf")]) (Prog.assign VarKind.local "d" (Exp.op BinOp.add [(Exp.var VarKind.local "d"), (Exp.const (BitVec.ofNat 64 1))])))) : Prog Word)

theorem merkleize.keepsA : Keeps E "out" o MK_LA := by
  repeat' first
    | exact Keeps.call
    | exact Keeps.assign rfl
    | apply Keeps.seq
    | apply Keeps.while
    | apply Keeps.dec rfl

theorem merkleize.keepsB : Keeps E "out" o MK_LB := by
  repeat' first
    | exact Keeps.call
    | exact Keeps.assign rfl
    | apply Keeps.seq
    | apply Keeps.while
    | apply Keeps.dec rfl

/-- `memcpy(e1, e2, e3)` as a statement: afterwards the cell of the destination
is known to lie in the heap. -/
theorem WPs.call_memcpy_dom (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {dstw nW : Word}
    (h1 : E.eval s e1 = some (.word dstw)) (h3 : E.eval s e3 = some (.word nW))
    (hn1 : 1 ≤ nW.toNat) (hn63 : nW.toNat < 2 ^ 63)
    (h : (al8 dstw).toNat < 33806089704 → ∀ g m ffi, Q (.normal s.locals g m ffi)) :
    WPs E s (.call (some (none, none)) "memcpy" [e1, e2, e3]) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h3] at hvalues
  cases he2 : E.eval s e2 with
  | none => rw [he2] at hvalues; simp at hvalues
  | some v2 =>
    rw [he2] at hvalues
    simp only [Option.map_some, Option.some.injEq] at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    have hdom := memcpy_dom hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb dstw nW
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hn1 hn63 hcallee
    cases rb with
    | returned lr g m ffi vs =>
      rcases hdom with hst | hF
      · exact absurd hst (fun h => h)
      simp only [CallOutcome] at hout
      rcases hout with herr | ⟨l', g', hassign, rfl⟩
      · exact Or.inl (Stopped.of_error herr)
      · obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
        have : l' = s.locals := funext (fun x => hl x (by simp))
        subst this
        exact Or.inr (h hF _ _ _)
    | raised lr g m ffi ex v =>
      simp only [CallOutcome] at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m ffi ev =>
      simp only [CallOutcome] at hout
      subst hout
      exact Or.inl trivial
    | _ =>
      simp only [CallOutcome] at hout
      exact Or.inl (Stopped.of_error hout)

set_option maxHeartbeats 2000000 in
/-- A `merkleize` that is not stopped has written the cell of `out`. -/
theorem merkleize_dom (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "merkleize" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (ow : Word) (hout : s.locals "out" = some (.word ow))
    (h : Runs E s body r) : Stopped r ∨ (al8 ow).toNat < 33806089704 := by
  have hbody := (fun_of_index 186 hE.functions (by guest_decl_at 186) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun _ => (al8 ow).toNat < 33806089704)) r h
  have h32 : (32#64 : Word).toNat = 32 := by decide
  refine WPs.decCall_any (fun v1 g1 m1 f1 => ?_)
  refine WPs.decCall_any (fun v2 g2 m2 f2 => ?_)
  refine WPs.decCall_any (fun v3 g3 m3 f3 => ?_)
  refine WPs.seqG (fun a => a.locals "out" = some (.word ow)) ?_ ?_
  · refine WPs.ite_both (fun w _ => ?_)
    split
    · exact WPs.skip (by lk [hout])
    · refine WPs.seqG (fun _ => (al8 ow).toNat < 33806089704)
        (WPs.call_memcpy_dom hE (dstw := ow) (nW := 32#64) (by lk [hout]) (eval_const _ _)
          (by rw [h32]; omega) (by rw [h32]; omega) (fun hF _ _ _ => hF)) ?_
      intro a hF
      exact WPs.ret (of_eval (eval_const _ _)) hF
  · intro a ha
    refine WPs.decCall_any (fun v4 g4 m4 f4 => ?_)
    refine WPs.dec_any (fun v5 => ?_)
    refine WPs.decCall_any (fun v6 g6 m6 f6 => ?_)
    refine WPs.seq (fun a' => a'.locals "out" = some (.word ow))
      (WPs.call_any (fun _ _ _ => ⟨_, _, _, _, rfl, by lk [ha]⟩)) ?_
    intro a1 ha1
    refine WPs.seq (fun a' => a'.locals "out" = some (.word ow))
      (WPs.call_any (fun _ _ _ => ⟨_, _, _, _, rfl, ha1⟩)) ?_
    intro a2 ha2
    refine WPs.dec_any (fun v7 => ?_)
    refine WPs.seq (fun a' => a'.locals "out" = some (.word ow))
      (merkleize.keepsA _ (by lk [ha2])) ?_
    intro a3 ha3
    refine WPs.dec_any (fun v8 => ?_)
    refine WPs.seq (fun a' => a'.locals "out" = some (.word ow))
      (merkleize.keepsB _ (by lk [ha3])) ?_
    intro a4 ha4
    refine WPs.seqG (fun _ => (al8 ow).toNat < 33806089704)
      (WPs.call_memcpy_dom hE (dstw := ow) (nW := 32#64) (by lk [ha4]) (eval_const _ _)
        (by rw [h32]; omega) (by rw [h32]; omega) (fun hF _ _ _ => hF)) ?_
    intro a5 hF
    exact WPs.of_true (fun _ => hF)

end InitECandidate.Solver.GuestBound
