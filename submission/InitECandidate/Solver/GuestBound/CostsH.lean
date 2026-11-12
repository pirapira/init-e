import InitECandidate.Solver.GuestBound.DecCallAt

/-!
# Step bounds from states whose heap pointer is in the heap

`bn254_pairing_check` is bounded only from states satisfying `HeapOk`. Every
guest function keeps `HeapOk` (`heap_keep`), so the bound travels up the call
graph: `CostsH E G p B` bounds `p` from states with `HeapOk` and the locals
in `G` holding heap marks, and the rules below mirror the unconditional ones
(`X.seq`, `X.ite`, `X.dec`, `X.decCall`, `X.callDest`), with `hk` supplying
the invariant after each statement. Subprograms that reach no conditionally
bounded function enter through `CostsH.of_costs`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {G : List VarName}

/-- The heap pointer is in the heap and the locals in `G` hold heap marks. -/
def HP (G : List VarName) (s : St σ) : Prop := HeapOk s.globals ∧ GoodL G s.locals

/-- A step bound for runs from `HP G` states. -/
def CostsH (E : Env σ) (G : List VarName) (p : Prog Word) (B : Nat) : Prop :=
  Triple E (HP G) p B (fun _ => True)

/-- Every body registered for `f` is bounded from states with `HeapOk`. -/
def FunCostH (E : Env σ) (f : FunName) (B : Nat) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    CostsH E [] body B

theorem CostsH.of_costs {p : Prog Word} {B : Nat} (h : Costs E p B) : CostsH E G p B :=
  fun fuel s r n _ hrun hne => h fuel s r n trivial hrun hne

theorem CostsH.mono {p : Prog Word} {B B' : Nat} (h : CostsH E G p B) (hle : B ≤ B') :
    CostsH E G p B' :=
  fun fuel s r n hP hrun hne => ⟨Nat.le_trans (h fuel s r n hP hrun hne).1 hle, trivial⟩

theorem FunCost.toH {f : FunName} {B : Nat} (h : FunCost E f B) : FunCostH E f B :=
  fun parameters body hlookup => CostsH.of_costs (h parameters body hlookup)

/-- A bound from `HeapOk` states is a bound for every call made from one. -/
theorem FunCostH.at {f : FunName} {B : Nat} (h : FunCostH E f B) {s : St σ}
    (hs : HeapOk s.globals) (arguments : List (Exp Word)) : FunCostAt E f B s arguments := by
  intro parameters body values cl hlookup _ _ fuel r n hrun hne
  exact (h parameters body hlookup fuel ⟨cl, s.globals, s.memory, s.ffi⟩ r n
    ⟨hs, fun _ hx => by cases hx⟩ hrun hne).1

/-- A checked program ends in a state that satisfies the invariant again. -/
theorem CostsH.post (hE : GuestEnv E) {p : Prog Word} {B : Nat} (hp : hk G p = true)
    (h : CostsH E G p B) : Triple E (HP G) p B (HPost G) :=
  fun fuel s r n hP hrun hne =>
    ⟨(h fuel s r n hP hrun hne).1, heap_keep hE fuel p G s r n hp hP.1 hP.2 hrun⟩

theorem CostsH.seq (hE : GuestEnv E) {a b : Prog Word} {B₁ B₂ : Nat} (ha : hk G a = true)
    (h₁ : CostsH E G a B₁) (h₂ : CostsH E G b B₂) : CostsH E G (.seq a b) (B₁ + B₂ + 1) := by
  refine Triple.seq (Mid := HP G) ?_ h₂
  intro fuel s r n hP hrun hne
  obtain ⟨hn, hpost⟩ := CostsH.post hE ha h₁ fuel s r n hP hrun hne
  refine ⟨hn, ?_⟩
  cases r <;> first | exact hpost | trivial

theorem CostsH.ite (c : Exp Word) {a b : Prog Word} {B₁ B₂ : Nat}
    (h₁ : CostsH E G a B₁) (h₂ : CostsH E G b B₂) :
    CostsH E G (.ite c a b) (panValueExpStepCost c + max B₁ B₂ + 1) :=
  Triple.ite (condCost _ c) h₁ h₂

theorem CostsH.dec (x : VarName) (sh : Shape) (e : Exp Word) {body : Prog Word} {B : Nat}
    (h : CostsH E (G.filter (· != x)) body B) :
    CostsH E G (.dec x sh e body) (panValueExpStepCost e + B + 1) :=
  Triple.dec x sh e (fun s v hP _ _ =>
    ⟨hP.1, goodL_bind hP.2 (fun hx => absurd rfl (mem_filter_ne.mp hx).2)
      (fun y hy _ => (mem_filter_ne.mp hy).1)⟩) h

/-- A declaring call of a function other than `heap_mark` and `heap_release`. -/
theorem CostsH.decCall (hE : GuestEnv E) (x : VarName) (sh : Shape) {f : FunName}
    (args : List (Exp Word)) {body : Prog Word} {B C : Nat} (hfr : f ≠ "heap_release")
    (hf : FunCostH E f B) (h : CostsH E (G.filter (· != x)) body C) :
    CostsH E G (.decCall x sh f args body) (panValueExpsStepCost args + B + C + 1) :=
  Triple.decCallAt x sh args (fun s hP => hf.at hP.1 args)
    (fun s v g m ffi hP hret _ =>
      ⟨CalleeRet.heapOk hE hfr hret.ret hP.1,
        goodL_bind hP.2 (fun hx => absurd rfl (mem_filter_ne.mp hx).2)
          (fun y hy _ => (mem_filter_ne.mp hy).1)⟩) h

/-- A call statement without handler. -/
theorem CostsH.call {f : FunName} (args : List (Exp Word)) {B : Nat}
    (d : Option (VarKind × VarName)) (hf : FunCostH E f B) :
    CostsH E G (.call (some (d, none)) f args) (panValueExpsStepCost args + B + 0 + 1) :=
  fun fuel s r n hP hrun hne =>
    call_cost_at (H := 0) (info := some (d, none)) args (hf.at hP.1 args) trivial fuel s r n rfl
      hrun hne

/-- A call statement whose handler reaches no conditionally bounded function. -/
theorem CostsH.callH {f : FunName} (args : List (Exp Word)) {B H : Nat}
    (d : Option (VarKind × VarName)) (exc : ExceptionId) (hv : VarName) {hp : Prog Word}
    (hf : FunCostH E f B) (hh : Costs E hp H) :
    CostsH E G (.call (some (d, some (exc, hv, hp))) f args)
      (panValueExpsStepCost args + B + H + 1) :=
  fun fuel s r n hP hrun hne =>
    call_cost_at (info := some (d, some (exc, hv, hp))) args (hf.at hP.1 args) hh fuel s r n rfl
      hrun hne

end InitECandidate.Solver.GuestBound
